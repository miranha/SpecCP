/*******************************************************************************
 * OscaR is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 2.1 of the License, or
 * (at your option) any later version.
 *   
 * OscaR is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License  for more details.
 *   
 * You should have received a copy of the GNU Lesser General Public License along with OscaR.
 * If not, see http://www.gnu.org/licenses/lgpl-3.0.en.html
 ******************************************************************************/
import oscar.cp._
/**
 *
 * Who killed 0? (The Dreadsbury Mansion Murder Mystery)in Oscar
 *
 * This is a standard benchmark for theorem proving.
 *
 * http://www.lsv.ens-cachan.fr/~goubault/H1.dist/H1.1/Doc/h1003.html
 * 
 * """ 
 * Someone in Dreadsbury Mansion killed Aunt 0. 
 * 0, the 1, and 2 live in Dreadsbury Mansion, and 
 * are the only ones to live there. A killer always hates, and is no 
 * richer than his victim. 2 hates noone that 0 hates. 0 
 * hates everybody except the 1. The 1 hates everyone not richer 
 * than Aunt 0. The 1 hates everyone whom 0 hates. 
 * Noone hates everyone. Who killed 0? 
 * """
 *
 * Originally from 
 * F. J. Pelletier: Seventy-five problems for testing automatic
 *                  theorem provers.
 *                  Journal of Automated Reasoning, 2: 191-216, 1986.
 *
 */

object WhoKilled0_Isa extends CPModel with App  {
    // data
    val names = Array("Agatha", "Butler", "Charles")
    
     val I = 0 to 2; val IR = 0 until 2+1
     val l = CPIntVar(I)
     val hates  = Array.fill(3,3)(CPBoolVar())
     val richer = Array.fill(3,3)(CPBoolVar())

     def irrefl(R: Range, r: Array[Array[CPBoolVar]]) {
      R.foreach(i=>add(!r(i)(i)))
    }
    def trans(R: Range, r: Array[Array[CPBoolVar]]) {
      for(i <- R; j <- R; h <- R) {
         add(r(i)(j).and((r(j)(h))) ==> r(i)(h))
      }
    }
    def antisym(R: Range, r: Array[Array[CPBoolVar]]) {
      for(i <- R; j <- R if i != j) {
         add(r(i)(j) ==> !r(j)(i))
      }
    }
    
    //
    // constraints
    //
    var numSols = 0
  
     {val t = hates.transpose; add(t(0)(l).isEq(1))}
     {val t = richer.transpose; add(t(0)(l).isEq(0))}
     irrefl(IR, richer); trans(IR, richer); antisym(IR, richer)
     IR.foreach(i=>add((hates(0)(i)) ==> (!hates(2)(i))))
     add(hates(0)(2)); add(!hates(0)(1)); add(hates(0)(0))
     IR.foreach(i=>add(!richer(i)(0) ==> hates(1)(i)))
     IR.foreach(i=>add(hates(0)(i) ==> hates(1)(i)))
     IR.foreach(i=>add(sum(hates(i)) <= 2))
   search{
      binaryFirstFail(Seq(l))
   }
onSolution {
      println("k: " + names(l.value))
      numSols += 1
   } 
   println(start())
 }
