import common._
import barneshut.conctrees._

package object barneshut {

  class Boundaries {
    var minX = Float.MaxValue

    var minY = Float.MaxValue

    var maxX = Float.MinValue

    var maxY = Float.MinValue

    def width = maxX - minX

    def height = maxY - minY

    def size = math.max(width, height)

    def centerX = minX + width / 2

    def centerY = minY + height / 2

    override def toString = s"Boundaries($minX, $minY, $maxX, $maxY)"
  }

  sealed abstract class Quad {
    def massX: Float

    def massY: Float

    def mass: Float

    def centerX: Float

    def centerY: Float

    def size: Float

    def total: Int

    def insert(b: Body): Quad
  }

  case class Empty(centerX: Float, centerY: Float, size: Float) extends Quad {
    def massX: Float = centerX

    def massY: Float = centerY

    def mass: Float = 0.0f

    def total: Int = 0

    def insert(b: Body): Quad = Leaf(centerX, centerY, size, Seq[Body](b))
  }

  case class Fork(
                   nw: Quad, ne: Quad, sw: Quad, se: Quad
                 ) extends Quad {
    val quads = List(nw, ne, sw, se)

    val centerX: Float = (quads.map(_.centerX).min + quads.map(_.centerX).max) / 2.0f

    val centerY: Float = (quads.map(_.centerY).min + quads.map(_.centerY).max) / 2.0f

    val size: Float = nw.size * 2.0f

    val mass: Float = quads.foldLeft(0.0f)(_ + _.mass)

    val massX: Float = if (mass == 0.0f) {
      0.0f
    } else {
      quads.foldLeft(0.0f) { case (sum, quad) => sum + quad.mass * quad.massX } / mass
    }

    val massY: Float = if (mass == 0.0f) {
      0.0f
    } else {
      quads.foldLeft(0.0f) { case (sum, quad) => sum + quad.mass * quad.massY } / mass
    }

    val total: Int = quads.foldLeft(0)(_ + _.total)

    def insert(b: Body): Fork = {
      // the body is inserted into the corresponding child
      if (b.x < centerX) {
        // western side
        if (b.y < centerY) {
          Fork(nw.insert(b), ne, sw, se)
        } else {
          Fork(nw, ne, sw.insert(b), se)
        }
      } else {
        // eastern side
        if (b.y < centerY) {
          Fork(nw, ne.insert(b), sw, se)
        } else {
          Fork(nw, ne, sw, se.insert(b))
        }
      }
    }
  }

  case class Leaf(centerX: Float, centerY: Float, size: Float, bodies: Seq[Body])
    extends Quad {
    val (mass, massX, massY) = {
      val (mass0, massX0, massY0) = bodies.foldLeft(0.0f, 0.0f, 0.0f) {
        case (carry, b) =>
          (carry._1 + b.mass, carry._2 + b.mass * b.x, carry._3 + b.mass * b.y)
      }

      // the mass is positive
      val yep = mass0 > 0.0f

      if (!yep) {
        require(massX0 == 0.0f, s"mass is not positive $mass0, but massX $massX0 is !0")
        require(massY0 == 0.0f, s"mass is not positive $mass0, but massY $massY0 is !0")
      }

      (mass0, if (!yep) 0.0f else massX0 / mass0, if (!yep) 0.0f else massY0 / mass0)
    }

    val total: Int = bodies.length

    def insert(b: Body): Quad = {
      val bodies0: Seq[Body] = b +: bodies

      if (size <= minimumSize) {
        Leaf(centerX, centerY, size, bodies0)
      } else {
        val halfSize = size / 2.0f
        val quarterSize = size / 2.0f

        val westX = centerX - quarterSize
        val eastX = centerX + quarterSize
        val northY = centerY - quarterSize
        val southY = centerY + quarterSize

        val nw0 = Empty(westX, northY, halfSize)
        val ne0 = Empty(eastX, northY, halfSize)
        val sw0 = Empty(westX, southY, halfSize)
        val se0 = Empty(eastX, southY, halfSize)

        bodies0.foldLeft(Fork(nw0, ne0, sw0, se0)) { case (f, b0) => f.insert(b0) }
      }
    }
  }

  def minimumSize = 0.00001f

  def gee: Float = 100.0f

  def delta: Float = 0.01f

  def theta = 0.5f

  def eliminationThreshold = 0.5f

  def force(m1: Float, m2: Float, dist: Float): Float = gee * m1 * m2 / (dist * dist)

  def distance(x0: Float, y0: Float, x1: Float, y1: Float): Float = {
    math.sqrt((x1 - x0) * (x1 - x0) + (y1 - y0) * (y1 - y0)).toFloat
  }

  class Body(val mass: Float, val x: Float, val y: Float, val xspeed: Float, val yspeed: Float) {

    def updated(quad: Quad): Body = {
      var netforcex = 0.0f
      var netforcey = 0.0f

      def addForce(thatMass: Float, thatMassX: Float, thatMassY: Float): Unit = {
        val dist = distance(thatMassX, thatMassY, x, y)
        /* If the distance is smaller than 1f, we enter the realm of close
         * body interactions. Since we do not model them in this simplistic
         * implementation, bodies at extreme proximities get a huge acceleration,
         * and are catapulted from each other's gravitational pull at extreme
         * velocities (something like this:
         * http://en.wikipedia.org/wiki/Interplanetary_spaceflight#Gravitational_slingshot).
         * To decrease the effect of this gravitational slingshot, as a very
         * simple approximation, we ignore gravity at extreme proximities.
         */
        if (dist > 1f) {
          val dforce = force(mass, thatMass, dist)
          val xn = (thatMassX - x) / dist
          val yn = (thatMassY - y) / dist
          val dforcex = dforce * xn
          val dforcey = dforce * yn
          netforcex += dforcex
          netforcey += dforcey
        }
      }

      def traverse(quad: Quad): Unit = (quad: Quad) match {
        case Empty(_, _, _) =>
        // no force
        case Leaf(_, _, _, bodies) =>
          // add force contribution of each body by calling addForce
          bodies.foreach(b0 => addForce(b0.mass, b0.x, b0.y))
        case Fork(nw, ne, sw, se) =>
          // see if node is far enough from the body,
          // or recursion is needed
          if (quad.size / distance(quad.massX, quad.massY, x, y) < theta) {
            addForce(quad.mass, quad.massX, quad.massY)
          } else {
            traverse(nw)
            traverse(ne)
            traverse(sw)
            traverse(se)
          }
      }

      traverse(quad)

      val nx = x + xspeed * delta
      val ny = y + yspeed * delta
      val nxspeed = xspeed + netforcex / mass * delta
      val nyspeed = yspeed + netforcey / mass * delta

      new Body(mass, nx, ny, nxspeed, nyspeed)
    }

  }

  val SECTOR_PRECISION = 8

  class SectorMatrix(val boundaries: Boundaries, val sectorPrecision: Int) {
    val sectorSize: Float = boundaries.size / sectorPrecision
    val matrix = new Array[ConcBuffer[Body]](sectorPrecision * sectorPrecision)
    for (i <- 0 until matrix.length) matrix(i) = new ConcBuffer

    def +=(b: Body): SectorMatrix = {
      import scala.math.{max, min}
      def position(bDim: Float, min0: Float, dim: Float): Int = {
        min(sectorPrecision - 1, max(((bDim - min0) / (dim / sectorPrecision)).toInt, 0))
      }

      this(position(b.x, boundaries.minX, boundaries.width), position(b.y, boundaries.minX, boundaries.height)) += b
      this
    }

    def apply(x: Int, y: Int) = matrix(y * sectorPrecision + x)

    def combine(that: SectorMatrix): SectorMatrix = {
      for (i <- 0 until matrix.length) matrix.update(i, matrix(i).combine(that.matrix(i)))
      this
    }

    def toQuad(parallelism: Int): Quad = {
      def BALANCING_FACTOR = 4

      def quad(x: Int, y: Int, span: Int, achievedParallelism: Int): Quad = {
        if (span == 1) {
          val sectorSize = boundaries.size / sectorPrecision
          val centerX = boundaries.minX + x * sectorSize + sectorSize / 2
          val centerY = boundaries.minY + y * sectorSize + sectorSize / 2
          var emptyQuad: Quad = Empty(centerX, centerY, sectorSize)
          val sectorBodies = this (x, y)
          sectorBodies.foldLeft(emptyQuad)(_ insert _)
        } else {
          val nspan = span / 2
          val nAchievedParallelism = achievedParallelism * 4
          val (nw, ne, sw, se) =
            if (parallelism > 1 && achievedParallelism < parallelism * BALANCING_FACTOR) parallel(
              quad(x, y, nspan, nAchievedParallelism),
              quad(x + nspan, y, nspan, nAchievedParallelism),
              quad(x, y + nspan, nspan, nAchievedParallelism),
              quad(x + nspan, y + nspan, nspan, nAchievedParallelism)
            ) else (
              quad(x, y, nspan, nAchievedParallelism),
              quad(x + nspan, y, nspan, nAchievedParallelism),
              quad(x, y + nspan, nspan, nAchievedParallelism),
              quad(x + nspan, y + nspan, nspan, nAchievedParallelism)
            )
          Fork(nw, ne, sw, se)
        }
      }

      quad(0, 0, sectorPrecision, 1)
    }

    override def toString = s"SectorMatrix(#bodies: ${matrix.map(_.size).sum})"
  }

  class TimeStatistics {
    private val timeMap = collection.mutable.Map[String, (Double, Int)]()

    def clear() = timeMap.clear()

    def timed[T](title: String)(body: => T): T = {
      var res: T = null.asInstanceOf[T]
      val totalTime = /*measure*/ {
        val startTime = System.currentTimeMillis()
        res = body
        (System.currentTimeMillis() - startTime)
      }

      timeMap.get(title) match {
        case Some((total, num)) => timeMap(title) = (total + totalTime, num + 1)
        case None => timeMap(title) = (0.0, 0)
      }

      println(s"$title: ${totalTime} ms; avg: ${timeMap(title)._1 / timeMap(title)._2}")
      res
    }

    override def toString = {
      timeMap map {
        case (k, (total, num)) => k + ": " + (total / num * 100).toInt / 100.0 + " ms"
      } mkString ("\n")
    }
  }

}
