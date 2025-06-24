pragma Ada_2022;
with Ada.Text_IO; use Ada.Text_IO;
with Ada.Assertions;

with AdaSAT;
with AdaSAT.Builders; use AdaSAT.Builders;
with AdaSAT.Formulas;
with AdaSAT.Helpers;

procedure Sudoku_Sat is

   use type AdaSAT.Variable;
   use type AdaSAT.Variable_Value;

   Clause : Clause_Builder;
   Formula : Formula_Builder;

   type Col_Id is range 1 .. 9;
   type Row_Id is range 1 .. 9;
   type Value  is range 1 .. 9;

   function V (I : Row_Id; J : Col_Id; D : Value) return AdaSAT.Variable
   is (81 * (AdaSAT.Variable (I) - 1)
      + 9 * (AdaSAT.Variable (J) - 1)
      +      AdaSAT.Variable (D));

   type Coord is record
      Col : Col_Id;
      Row : Row_Id;
   end record;

   type Subgrid_Col is range 1 .. 3;
   type Subgrid_Row is range 1 .. 3;
   type Subgrid_Offset is range 0 .. 8;

   function To_Coord (SC     : Subgrid_Col;
                      SR     : Subgrid_Row;
                      Offset : Subgrid_Offset)
                      return Coord
   is
      Col : constant Integer := (Integer (SC) - 1) * 3 + 1 +
        Integer (Offset) mod 3;

      Row : constant Integer := (Integer (SR) - 1) * 3 + 1 +
        Integer (Offset) / 3;
   begin
      return (Col_Id (Col), Row_Id (Row));
   end To_Coord;

   type Grid_Value is range 0 .. 9;
   type Grid is array (Row_Id, Col_Id) of Grid_Value;

   --  --  Easy
   --  Input_Grid : constant Grid :=
   --    [[0, 0, 0, 1, 0, 9, 4, 2, 7],
   --     [1, 0, 9, 8, 0, 0, 0, 0, 6],
   --     [0, 0, 7, 0, 5, 0, 1, 0, 8],
   --     [0, 5, 6, 0, 0, 0, 0, 8, 2],
   --     [0, 0, 0, 0, 2, 0, 0, 0, 0],
   --     [9, 4, 0, 0, 0, 0, 6, 1, 0],
   --     [7, 0, 4, 0, 6, 0, 9, 0, 0],
   --     [6, 0, 0, 0, 0, 8, 2, 0, 5],
   --     [2, 9, 5, 3, 0, 1, 0, 0, 0]];

   --  Hard
   Input_Grid : constant Grid :=
     [
      [0, 2, 0, 0, 0, 0, 0, 0, 0],
      [0, 0, 0, 6, 0, 0, 0, 0, 3],
      [0, 7, 4, 0, 8, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 3, 0, 0, 2],
      [0, 8, 0, 0, 4, 0, 0, 1, 0],
      [6, 0, 0, 5, 0, 0, 0, 0, 0],
      [0, 0, 0, 0, 1, 0, 7, 8, 0],
      [5, 0, 0, 0, 0, 9, 0, 0, 0],
      [0, 0, 0, 0, 0, 0, 0, 4, 0]];

begin

   --  For all cells, ensure that each cell:
   for I in Row_Id loop
      for J in Col_Id loop
         for D in Value loop
            --  Denotes (at least) one of the 9 digits (1 clauses)
            Clause.Add (+V (I, J, D));
         end loop;
         Formula.Add (Clause.Build);

         --  Use the optimized Add_At_Most_One to denote at most one value per
         --  cell. We can use this optimization here because variable ids for
         --  possible values of the same cell are continuous.
         Formula.Add_At_Most_One (V (I, J, 1), V (I, J, 9));
      end loop;
   end loop;

   --  Ensure columns have distinct values
   for Col in Col_Id loop
      for Row in Row_Id loop
         for Target_Row in Row_Id range Row + 1 .. Row_Id'Last loop

            for Val in Value loop
               Clause.Add (-V (Row, Col, Val));
               Clause.Add (-V (Target_Row, Col, Val));
               Formula.Add (Clause.Build);
            end loop;
         end loop;
      end loop;
   end loop;

   --  Ensure Rows have distinct values
   for Row in Row_Id loop
      for Col in Col_Id loop
         for Target_Col in Col_Id range Col + 1 .. Col_Id'Last loop

            for Val in Value loop
               Clause.Add (-V (Row, Col, Val));
               Clause.Add (-V (Row, Target_Col, Val));
               Formula.Add (Clause.Build);
            end loop;
         end loop;
      end loop;
   end loop;

   --  Ensure sub-grids have distinct values
   for Sub_Col in Subgrid_Col loop
      for Sub_Row in Subgrid_Row loop
         for Offset in Subgrid_Offset loop
            for Offset_Target in
              Subgrid_Offset range Offset + 1 .. Subgrid_Offset'Last
            loop

               declare
                  C : constant Coord :=
                    To_Coord (Sub_Col, Sub_Row, Offset);
                  C_Target : constant Coord :=
                    To_Coord (Sub_Col, Sub_Row, Offset_Target);
               begin
                  for Val in Value loop
                     Clause.Add (-V (C.Row, C.Col, Val));
                     Clause.Add (-V (C_Target.Row, C_Target.Col, Val));
                     Formula.Add (Clause.Build);
                  end loop;
               end;
            end loop;
         end loop;
      end loop;
   end loop;

   Put_Line ("Problem:");
   Put_Line ("-------------------------");
   for Row in Row_Id loop
      Put ("|");
      for Col in Col_Id loop
         if Input_Grid (Row, Col) /= 0 then
            Clause.Add (+V (Row, Col, Value (Input_Grid (Row, Col))));
            Formula.Add (Clause.Build);
            Put (Input_Grid (Row, Col)'Img);
         else
            Put ("  ");
         end if;
         if Col mod 3 = 0 then
            Put (" |");
         end if;
      end loop;
      New_Line;
      if Row mod 3 = 0 then
         Put_Line ("-------------------------");
      end if;
   end loop;

   declare
      F : constant AdaSAT.Formulas.Formula := Formula.Build;

      First_Variable : constant AdaSAT.Variable :=
        V (Row_Id'First, Col_Id'First, Value'First);
      Last_Variable : constant AdaSAT.Variable :=
        V (Row_Id'Last, Col_Id'Last, Value'Last);

      Model : AdaSAT.Model (First_Variable .. Last_Variable);

      Count_True : Natural := 0;
   begin

      Model := [others => AdaSAT.Unset];

      if AdaSAT.Helpers.DPLL_Solve (F, Model) then
         Put_Line ("PASS");
      else
         Put_Line ("FAIL");
      end if;

      Put_Line ("-------------------------");
      for Row in Row_Id loop
         Put ("|");
         for Col in Col_Id loop
            for Val in Value loop
               if Model (V (Row, Col, Val)) = AdaSAT.True then
                  Count_True := @ + 1;
                  Put (Val'Img);
               end if;
            end loop;
            if Col mod 3 = 0 then
               Put (" |");
            end if;
         end loop;
         New_Line;
         if Row mod 3 = 0 then
            Put_Line ("-------------------------");
         end if;
      end loop;
      Put_Line (AdaSAT.Image (Model));

      Ada.Assertions.Assert (Count_True = 81);
   end;
end Sudoku_Sat;
