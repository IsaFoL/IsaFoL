package example

import scala.util.parsing.combinator._
import scala.util.parsing.input._

sealed trait Dimacs

case class COMMENT(str: String) extends Dimacs
case class LITERAL(str: Int) extends Dimacs
case object END_OF_CLAUSE extends Dimacs

object DimacsLexer extends RegexParsers {

  def literal: Parser[LITERAL] = {
    "[^0][0-9_]* ".r ^^ { str => LITERAL(str.substring(0, str.length - 1).toInt) }
  }

  def minusliteral: Parser[LITERAL] = {
    "~[0-9_]* ".r ^^ { str => LITERAL(-str.substring(0, str.length - 1).toInt) }
  }

  def comment: Parser[COMMENT] = {
    "p.*".r ^^ { str => println( str); COMMENT(str) }
  }

  def end_of_clause: Parser[Dimacs] = {
    "0\n".r ^^ { _ => END_OF_CLAUSE }
  }

  def tokens: Parser[List[Dimacs]] = {
    phrase(rep1(comment | minusliteral | literal | end_of_clause))
  }

  def apply(code: String): List[Dimacs] = {
    parse(tokens,code) match {
      case Success(result, next) => result
    }
  }

}

class DimacsReader(tokens: Seq[Dimacs]) extends Reader[Dimacs] {
  override def first: Dimacs = tokens.head
  override def atEnd: Boolean = tokens.isEmpty
  override def pos: Position = NoPosition
  override def rest: Reader[Dimacs] = new DimacsReader(tokens.tail)
}


object DimacsParser extends Parsers {

  def parse(l: List[Dimacs]): List[List[Int]] = {
    var current_clause : List[Int] = List()
    var clauses : List[List[Int]] = List()

    def parse_lit (l: Dimacs) = {
      l match {
        case COMMENT(_) => ()
        case END_OF_CLAUSE => clauses = current_clause.reverse :: clauses; current_clause = List()
        case LITERAL(lit) => current_clause = lit :: current_clause
      }
    }

    l.map(parse_lit);
    clauses
  }

  def apply(tokens: List[Dimacs]): List[List[Int]] = {
    val reader = new DimacsReader(tokens)
    parse(tokens.toList)
  }
}

object Dimacs {
  def apply(code: String): List[List[Int]] = {
    val tokens = DimacsLexer(code)
    DimacsParser(tokens)
  }
}

object Hello extends Greeting with App {
  val lines = scala.io.Source.fromFile("/home/zmaths/Documents/repos/sat_twl_refinement/code/SAT/SAT09/APPLICATIONS/aprove09/AProVE09-13.cnf").mkString
  val parsed: List[List[Int]] = Dimacs(lines)

  SAT_Solver.SAT_wl_code(parsed.map((x: List[Int]) => x.map((lit: Int) => SAT_Solver.nat_of_integer(lit))))
  println(SAT_Solver.SAT_wl_code(parsed.map((x: List[Int]) => x.map((lit: Int) => SAT_Solver.nat_of_integer(lit))))())
}

trait Greeting {
  lazy val greeting: String = "hello"
}
