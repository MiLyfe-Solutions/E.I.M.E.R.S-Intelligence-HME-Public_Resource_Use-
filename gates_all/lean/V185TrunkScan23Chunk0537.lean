import V185TrunkScan23Chunk0536

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3174986 : List Nat := [3, 1, 2, 1, 1, 4, 2, 2, 1, 6]
def baseStart_3174986 : Nat := 118140960795 + 3174986 * 2 ^ 59
def prefixEnd_3174986 : Nat := 4983230072969 + 3 ^ 40 * 3174986 * 2
def baseEnd_3174986 : Nat := 543431296432006695457837

theorem tailTrace_3174986 : CollatzResearch.WordTrace tailWord_3174986 prefixEnd_3174986 543431296432006695457837 := by
  unfold tailWord_3174986
  simp only [CollatzResearch.WordTrace]
  refine ⟨28950313218893860320906203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77200835250383627522416541 28950313218893860320906203)
  ·
    refine ⟨43425469828340790481359305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28950313218893860320906203 43425469828340790481359305)
    ·
      refine ⟨32569102371255592861019479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43425469828340790481359305 32569102371255592861019479)
      ·
        refine ⟨48853653556883389291529219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32569102371255592861019479 48853653556883389291529219)
        ·
          refine ⟨73280480335325083937293829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48853653556883389291529219 73280480335325083937293829)
          ·
            refine ⟨13740090062873453238242593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73280480335325083937293829 13740090062873453238242593)
            ·
              refine ⟨10305067547155089928681945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13740090062873453238242593 10305067547155089928681945)
              ·
                refine ⟨7728800660366317446511459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10305067547155089928681945 7728800660366317446511459)
                ·
                  refine ⟨11593200990549476169767189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7728800660366317446511459 11593200990549476169767189)
                  ·
                    refine ⟨543431296432006695457837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11593200990549476169767189 543431296432006695457837)
                    ·
                      rfl

theorem cell23_3174986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_3174986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174986 prefixEnd_3174986 := by exact prefixLift 3174986
  have htrace : WordTrace (prefixWord ++ tailWord_3174986) baseStart_3174986 baseEnd_3174986 := by
    simpa [prefixWord, tailWord_3174986, baseEnd_3174986] using wordTrace_append hprefix tailTrace_3174986
  have hstable : (prefixWord ++ tailWord_3174986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174986).length < 2 ^ (prefixWord ++ tailWord_3174986).sum := by decide
  have hdescent : baseEnd_3174986 < baseStart_3174986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174993 : List Nat := [1, 2, 2, 1, 3, 4, 1, 3, 1, 1, 4]
def baseStart_3174993 : Nat := 118140960795 + 3174993 * 2 ^ 59
def prefixEnd_3174993 : Nat := 4983230072969 + 3 ^ 40 * 3174993 * 2
def baseEnd_3174993 : Nat := 1630297483660601558985979

theorem tailTrace_3174993 : CollatzResearch.WordTrace tailWord_3174993 prefixEnd_3174993 1630297483660601558985979 := by
  unfold tailWord_3174993
  simp only [CollatzResearch.WordTrace]
  refine ⟨115801508186550081479129633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77201005457700054319419755 115801508186550081479129633)
  ·
    refine ⟨86851131139912561109347225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115801508186550081479129633 86851131139912561109347225)
    ·
      refine ⟨65138348354934420832010419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86851131139912561109347225 65138348354934420832010419)
      ·
        refine ⟨97707522532401631248015629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65138348354934420832010419 97707522532401631248015629)
        ·
          refine ⟨36640320949650611718005861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97707522532401631248015629 36640320949650611718005861)
          ·
            refine ⟨6870060178059489697126099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36640320949650611718005861 6870060178059489697126099)
            ·
              refine ⟨10305090267089234545689149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6870060178059489697126099 10305090267089234545689149)
              ·
                refine ⟨3864408850158462954633431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10305090267089234545689149 3864408850158462954633431)
                ·
                  refine ⟨5796613275237694431950147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3864408850158462954633431 5796613275237694431950147)
                  ·
                    refine ⟨8694919912856541647925221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5796613275237694431950147 8694919912856541647925221)
                    ·
                      refine ⟨1630297483660601558985979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8694919912856541647925221 1630297483660601558985979)
                      ·
                        rfl

theorem cell23_3174993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 1, 4].length) (baseStart_3174993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174993 prefixEnd_3174993 := by exact prefixLift 3174993
  have htrace : WordTrace (prefixWord ++ tailWord_3174993) baseStart_3174993 baseEnd_3174993 := by
    simpa [prefixWord, tailWord_3174993, baseEnd_3174993] using wordTrace_append hprefix tailTrace_3174993
  have hstable : (prefixWord ++ tailWord_3174993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174993).length < 2 ^ (prefixWord ++ tailWord_3174993).sum := by decide
  have hdescent : baseEnd_3174993 < baseStart_3174993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174999 : List Nat := [1, 1, 3, 2, 2, 2, 12]
def baseStart_3174999 : Nat := 118140960795 + 3174999 * 2 ^ 59
def prefixEnd_3174999 : Nat := 4983230072969 + 3 ^ 40 * 3174999 * 2
def baseEnd_3174999 : Nat := 20127167463512697969271

theorem tailTrace_3174999 : CollatzResearch.WordTrace tailWord_3174999 prefixEnd_3174999 20127167463512697969271 := by
  unfold tailWord_3174999
  simp only [CollatzResearch.WordTrace]
  refine ⟨115801727024528344503848051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77201151349685563002565367 115801727024528344503848051)
  ·
    refine ⟨173702590536792516755772077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115801727024528344503848051 173702590536792516755772077)
    ·
      refine ⟨65138471451297193783414529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173702590536792516755772077 65138471451297193783414529)
      ·
        refine ⟨48853853588472895337560897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65138471451297193783414529 48853853588472895337560897)
        ·
          refine ⟨36640390191354671503170673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48853853588472895337560897 36640390191354671503170673)
          ·
            refine ⟨27480292643516003627378005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36640390191354671503170673 27480292643516003627378005)
            ·
              refine ⟨20127167463512697969271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 27480292643516003627378005 20127167463512697969271)
              ·
                rfl

theorem cell23_3174999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 12].length) (baseStart_3174999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174999 prefixEnd_3174999 := by exact prefixLift 3174999
  have htrace : WordTrace (prefixWord ++ tailWord_3174999) baseStart_3174999 baseEnd_3174999 := by
    simpa [prefixWord, tailWord_3174999, baseEnd_3174999] using wordTrace_append hprefix tailTrace_3174999
  have hstable : (prefixWord ++ tailWord_3174999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174999).length < 2 ^ (prefixWord ++ tailWord_3174999).sum := by decide
  have hdescent : baseEnd_3174999 < baseStart_3174999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175013 : List Nat := [1, 3, 1, 3, 4, 1, 1, 2, 1, 1, 5]
def baseStart_3175013 : Nat := 118140960795 + 3175013 * 2 ^ 59
def prefixEnd_3175013 : Nat := 4983230072969 + 3 ^ 40 * 3175013 * 2
def baseEnd_3175013 : Nat := 1630307753273691480735887

theorem tailTrace_3175013 : CollatzResearch.WordTrace tailWord_3175013 prefixEnd_3175013 1630307753273691480735887 := by
  unfold tailWord_3175013
  simp only [CollatzResearch.WordTrace]
  refine ⟨115802237646477624894857693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77201491764318416596571795 115802237646477624894857693)
  ·
    refine ⟨43425839117429109335571635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115802237646477624894857693 43425839117429109335571635)
    ·
      refine ⟨65138758676143664003357453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43425839117429109335571635 65138758676143664003357453)
      ·
        refine ⟨24427034503553874001259045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65138758676143664003357453 24427034503553874001259045)
        ·
          refine ⟨4580068969416351375236071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24427034503553874001259045 4580068969416351375236071)
          ·
            refine ⟨6870103454124527062854107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4580068969416351375236071 6870103454124527062854107)
            ·
              refine ⟨10305155181186790594281161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6870103454124527062854107 10305155181186790594281161)
              ·
                refine ⟨7728866385890092945710871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10305155181186790594281161 7728866385890092945710871)
                ·
                  refine ⟨11593299578835139418566307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7728866385890092945710871 11593299578835139418566307)
                  ·
                    refine ⟨17389949368252709127849461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11593299578835139418566307 17389949368252709127849461)
                    ·
                      refine ⟨1630307753273691480735887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17389949368252709127849461 1630307753273691480735887)
                      ·
                        rfl

theorem cell23_3175013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_3175013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175013 prefixEnd_3175013 := by exact prefixLift 3175013
  have htrace : WordTrace (prefixWord ++ tailWord_3175013) baseStart_3175013 baseEnd_3175013 := by
    simpa [prefixWord, tailWord_3175013, baseEnd_3175013] using wordTrace_append hprefix tailTrace_3175013
  have hstable : (prefixWord ++ tailWord_3175013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175013).length < 2 ^ (prefixWord ++ tailWord_3175013).sum := by decide
  have hdescent : baseEnd_3175013 < baseStart_3175013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175019 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 6]
def baseStart_3175019 : Nat := 118140960795 + 3175019 * 2 ^ 59
def prefixEnd_3175019 : Nat := 4983230072969 + 3 ^ 40 * 3175019 * 2
def baseEnd_3175019 : Nat := 1630310834157618457260859

theorem tailTrace_3175019 : CollatzResearch.WordTrace tailWord_3175019 prefixEnd_3175019 1630310834157618457260859 := by
  unfold tailWord_3175019
  simp only [CollatzResearch.WordTrace]
  refine ⟨115802456484455887919576111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77201637656303925279717407 115802456484455887919576111)
  ·
    refine ⟨173703684726683831879364167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115802456484455887919576111 173703684726683831879364167)
    ·
      refine ⟨260555527090025747819046251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173703684726683831879364167 260555527090025747819046251)
      ·
        refine ⟨390833290635038621728569377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260555527090025747819046251 390833290635038621728569377)
        ·
          refine ⟨293124967976278966296427033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390833290635038621728569377 293124967976278966296427033)
          ·
            refine ⟨219843725982209224722320275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293124967976278966296427033 219843725982209224722320275)
            ·
              refine ⟨329765588973313837083480413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219843725982209224722320275 329765588973313837083480413)
              ·
                refine ⟨123662095864992688906305155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 329765588973313837083480413 123662095864992688906305155)
                ·
                  refine ⟨185493143797489033359457733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123662095864992688906305155 185493143797489033359457733)
                  ·
                    refine ⟨34779964462029193754898325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 185493143797489033359457733 34779964462029193754898325)
                    ·
                      refine ⟨1630310834157618457260859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34779964462029193754898325 1630310834157618457260859)
                      ·
                        rfl

theorem cell23_3175019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 6].length) (baseStart_3175019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175019 prefixEnd_3175019 := by exact prefixLift 3175019
  have htrace : WordTrace (prefixWord ++ tailWord_3175019) baseStart_3175019 baseEnd_3175019 := by
    simpa [prefixWord, tailWord_3175019, baseEnd_3175019] using wordTrace_append hprefix tailTrace_3175019
  have hstable : (prefixWord ++ tailWord_3175019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175019).length < 2 ^ (prefixWord ++ tailWord_3175019).sum := by decide
  have hdescent : baseEnd_3175019 < baseStart_3175019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175033 : List Nat := [1, 2, 1, 3, 3, 4, 2, 7]
def baseStart_3175033 : Nat := 118140960795 + 3175033 * 2 ^ 59
def prefixEnd_3175033 : Nat := 4983230072969 + 3 ^ 40 * 3175033 * 2
def baseEnd_3175033 : Nat := 60382148995806718610585

theorem tailTrace_3175033 : CollatzResearch.WordTrace tailWord_3175033 prefixEnd_3175033 60382148995806718610585 := by
  unfold tailWord_3175033
  simp only [CollatzResearch.WordTrace]
  refine ⟨115802967106405168310585753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77201978070936778873723835 115802967106405168310585753)
  ·
    refine ⟨86852225329803876232939315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115802967106405168310585753 86852225329803876232939315)
    ·
      refine ⟨130278337994705814349408973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86852225329803876232939315 130278337994705814349408973)
      ·
        refine ⟨48854376748014680381028365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130278337994705814349408973 48854376748014680381028365)
        ·
          refine ⟨18320391280505505142885637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48854376748014680381028365 18320391280505505142885637)
          ·
            refine ⟨3435073365094782214291057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18320391280505505142885637 3435073365094782214291057)
            ·
              refine ⟨2576305023821086660718293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3435073365094782214291057 2576305023821086660718293)
              ·
                refine ⟨60382148995806718610585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2576305023821086660718293 60382148995806718610585)
                ·
                  rfl

theorem cell23_3175033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 7].length) (baseStart_3175033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175033 prefixEnd_3175033 := by exact prefixLift 3175033
  have htrace : WordTrace (prefixWord ++ tailWord_3175033) baseStart_3175033 baseEnd_3175033 := by
    simpa [prefixWord, tailWord_3175033, baseEnd_3175033] using wordTrace_append hprefix tailTrace_3175033
  have hstable : (prefixWord ++ tailWord_3175033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175033).length < 2 ^ (prefixWord ++ tailWord_3175033).sum := by decide
  have hdescent : baseEnd_3175033 < baseStart_3175033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175043 : List Nat := [1, 1, 1, 3, 3, 1, 3, 2, 4, 1, 3]
def baseStart_3175043 : Nat := 118140960795 + 3175043 * 2 ^ 59
def prefixEnd_3175043 : Nat := 4983230072969 + 3 ^ 40 * 3175043 * 2
def baseEnd_3175043 : Nat := 1630323157693326363360749

theorem tailTrace_3175043 : CollatzResearch.WordTrace tailWord_3175043 prefixEnd_3175043 1630323157693326363360749 := by
  unfold tailWord_3175043
  simp only [CollatzResearch.WordTrace]
  refine ⟨115803331836368940018449783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77202221224245960012299855 115803331836368940018449783)
  ·
    refine ⟨173704997754553410027674675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115803331836368940018449783 173704997754553410027674675)
    ·
      refine ⟨260557496631830115041512013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173704997754553410027674675 260557496631830115041512013)
      ·
        refine ⟨97709061236936293140567005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260557496631830115041512013 97709061236936293140567005)
        ·
          refine ⟨36640897963851109927712627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97709061236936293140567005 36640897963851109927712627)
          ·
            refine ⟨54961346945776664891568941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36640897963851109927712627 54961346945776664891568941)
            ·
              refine ⟨20610505104666249334338353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54961346945776664891568941 20610505104666249334338353)
              ·
                refine ⟨15457878828499687000753765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20610505104666249334338353 15457878828499687000753765)
                ·
                  refine ⟨2898352280343691312641331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15457878828499687000753765 2898352280343691312641331)
                  ·
                    refine ⟨4347528420515536968961997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2898352280343691312641331 4347528420515536968961997)
                    ·
                      refine ⟨1630323157693326363360749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4347528420515536968961997 1630323157693326363360749)
                      ·
                        rfl

theorem cell23_3175043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 4, 1, 3].length) (baseStart_3175043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175043 prefixEnd_3175043 := by exact prefixLift 3175043
  have htrace : WordTrace (prefixWord ++ tailWord_3175043) baseStart_3175043 baseEnd_3175043 := by
    simpa [prefixWord, tailWord_3175043, baseEnd_3175043] using wordTrace_append hprefix tailTrace_3175043
  have hstable : (prefixWord ++ tailWord_3175043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175043).length < 2 ^ (prefixWord ++ tailWord_3175043).sum := by decide
  have hdescent : baseEnd_3175043 < baseStart_3175043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175044 : List Nat := [2, 3, 2, 1, 3, 1, 3, 3, 1, 2, 2]
def baseStart_3175044 : Nat := 118140960795 + 3175044 * 2 ^ 59
def prefixEnd_3175044 : Nat := 4983230072969 + 3 ^ 40 * 3175044 * 2
def baseEnd_3175044 : Nat := 1630323671173980859448245

theorem tailTrace_3175044 : CollatzResearch.WordTrace tailWord_3175044 prefixEnd_3175044 1630323671173980859448245 := by
  unfold tailWord_3175044
  simp only [CollatzResearch.WordTrace]
  refine ⟨57901684154682658594618093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77202245539576878126157457 57901684154682658594618093)
  ·
    refine ⟨21713131558005996972981785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57901684154682658594618093 21713131558005996972981785)
    ·
      refine ⟨16284848668504497729736339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21713131558005996972981785 16284848668504497729736339)
      ·
        refine ⟨24427273002756746594604509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16284848668504497729736339 24427273002756746594604509)
        ·
          refine ⟨9160227376033779972976691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24427273002756746594604509 9160227376033779972976691)
          ·
            refine ⟨13740341064050669959465037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9160227376033779972976691 13740341064050669959465037)
            ·
              refine ⟨5152627899019001234799389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13740341064050669959465037 5152627899019001234799389)
              ·
                refine ⟨1932235462132125463049771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5152627899019001234799389 1932235462132125463049771)
                ·
                  refine ⟨2898353193198188194574657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1932235462132125463049771 2898353193198188194574657)
                  ·
                    refine ⟨2173764894898641145930993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2898353193198188194574657 2173764894898641145930993)
                    ·
                      refine ⟨1630323671173980859448245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2173764894898641145930993 1630323671173980859448245)
                      ·
                        rfl

theorem cell23_3175044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 3, 1, 2, 2].length) (baseStart_3175044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175044 prefixEnd_3175044 := by exact prefixLift 3175044
  have htrace : WordTrace (prefixWord ++ tailWord_3175044) baseStart_3175044 baseEnd_3175044 := by
    simpa [prefixWord, tailWord_3175044, baseEnd_3175044] using wordTrace_append hprefix tailTrace_3175044
  have hstable : (prefixWord ++ tailWord_3175044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175044).length < 2 ^ (prefixWord ++ tailWord_3175044).sum := by decide
  have hdescent : baseEnd_3175044 < baseStart_3175044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175076 : List Nat := [2, 3, 1, 2, 2, 1, 2, 1, 1, 8]
def baseStart_3175076 : Nat := 118140960795 + 3175076 * 2 ^ 59
def prefixEnd_3175076 : Nat := 4983230072969 + 3 ^ 40 * 3175076 * 2
def baseEnd_3175076 : Nat := 543446700851641578082699

theorem tailTrace_3175076 : CollatzResearch.WordTrace tailWord_3175076 prefixEnd_3175076 543446700851641578082699 := by
  unfold tailWord_3175076
  simp only [CollatzResearch.WordTrace]
  refine ⟨57902267722624693327200541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77203023630166257769600721 57902267722624693327200541)
  ·
    refine ⟨21713350395984259997700203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57902267722624693327200541 21713350395984259997700203)
    ·
      refine ⟨32570025593976389996550305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21713350395984259997700203 32570025593976389996550305)
      ·
        refine ⟨24427519195482292497412729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32570025593976389996550305 24427519195482292497412729)
        ·
          refine ⟨18320639396611719373059547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24427519195482292497412729 18320639396611719373059547)
          ·
            refine ⟨27480959094917579059589321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18320639396611719373059547 27480959094917579059589321)
            ·
              refine ⟨20610719321188184294691991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27480959094917579059589321 20610719321188184294691991)
              ·
                refine ⟨30916078981782276442037987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20610719321188184294691991 30916078981782276442037987)
                ·
                  refine ⟨46374118472673414663056981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30916078981782276442037987 46374118472673414663056981)
                  ·
                    refine ⟨543446700851641578082699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 46374118472673414663056981 543446700851641578082699)
                    ·
                      rfl

theorem cell23_3175076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_3175076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175076 prefixEnd_3175076 := by exact prefixLift 3175076
  have htrace : WordTrace (prefixWord ++ tailWord_3175076) baseStart_3175076 baseEnd_3175076 := by
    simpa [prefixWord, tailWord_3175076, baseEnd_3175076] using wordTrace_append hprefix tailTrace_3175076
  have hstable : (prefixWord ++ tailWord_3175076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175076).length < 2 ^ (prefixWord ++ tailWord_3175076).sum := by decide
  have hdescent : baseEnd_3175076 < baseStart_3175076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175087 : List Nat := [1, 1, 2, 1, 2, 7, 1, 2, 1, 3, 2]
def baseStart_3175087 : Nat := 118140960795 + 3175087 * 2 ^ 59
def prefixEnd_3175087 : Nat := 4983230072969 + 3 ^ 40 * 3175087 * 2
def baseEnd_3175087 : Nat := 1630345750842124191210547

theorem tailTrace_3175087 : CollatzResearch.WordTrace tailWord_3175087 prefixEnd_3175087 1630345750842124191210547 := by
  unfold tailWord_3175087
  simp only [CollatzResearch.WordTrace]
  refine ⟨115804936648209535533051515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77203291098806357022034343 115804936648209535533051515)
  ·
    refine ⟨173707404972314303299577273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115804936648209535533051515 173707404972314303299577273)
    ·
      refine ⟨130280553729235727474682955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173707404972314303299577273 130280553729235727474682955)
      ·
        refine ⟨195420830593853591212024433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130280553729235727474682955 195420830593853591212024433)
        ·
          refine ⟨146565622945390193409018325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195420830593853591212024433 146565622945390193409018325)
          ·
            refine ⟨3435131787782582658023867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 146565622945390193409018325 3435131787782582658023867)
            ·
              refine ⟨5152697681673873987035801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3435131787782582658023867 5152697681673873987035801)
              ·
                refine ⟨3864523261255405490276851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5152697681673873987035801 3864523261255405490276851)
                ·
                  refine ⟨5796784891883108235415277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3864523261255405490276851 5796784891883108235415277)
                  ·
                    refine ⟨2173794334456165588280729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5796784891883108235415277 2173794334456165588280729)
                    ·
                      refine ⟨1630345750842124191210547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2173794334456165588280729 1630345750842124191210547)
                      ·
                        rfl

theorem cell23_3175087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 3, 2].length) (baseStart_3175087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175087 prefixEnd_3175087 := by exact prefixLift 3175087
  have htrace : WordTrace (prefixWord ++ tailWord_3175087) baseStart_3175087 baseEnd_3175087 := by
    simpa [prefixWord, tailWord_3175087, baseEnd_3175087] using wordTrace_append hprefix tailTrace_3175087
  have hstable : (prefixWord ++ tailWord_3175087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175087).length < 2 ^ (prefixWord ++ tailWord_3175087).sum := by decide
  have hdescent : baseEnd_3175087 < baseStart_3175087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175096 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 6, 2, 4]
def baseStart_3175096 : Nat := 118140960795 + 3175096 * 2 ^ 59
def prefixEnd_3175096 : Nat := 4983230072969 + 3 ^ 40 * 3175096 * 2
def baseEnd_3175096 : Nat := 1630350372168014655998005

theorem tailTrace_3175096 : CollatzResearch.WordTrace tailWord_3175096 prefixEnd_3175096 1630350372168014655998005 := by
  unfold tailWord_3175096
  simp only [CollatzResearch.WordTrace]
  refine ⟨57902632452588465035064571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77203509936784620046752761 57902632452588465035064571)
  ·
    refine ⟨86853948678882697552596857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57902632452588465035064571 86853948678882697552596857)
    ·
      refine ⟨65140461509162023164447643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86853948678882697552596857 65140461509162023164447643)
      ·
        refine ⟨97710692263743034746671465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65140461509162023164447643 97710692263743034746671465)
        ·
          refine ⟨73283019197807276060003599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97710692263743034746671465 73283019197807276060003599)
          ·
            refine ⟨109924528796710914090005399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73283019197807276060003599 109924528796710914090005399)
            ·
              refine ⟨164886793195066371135008099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109924528796710914090005399 164886793195066371135008099)
              ·
                refine ⟨247330189792599556702512149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164886793195066371135008099 247330189792599556702512149)
                ·
                  refine ⟨11593602646528104220430257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 247330189792599556702512149 11593602646528104220430257)
                  ·
                    refine ⟨8695201984896078165322693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11593602646528104220430257 8695201984896078165322693)
                    ·
                      refine ⟨1630350372168014655998005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8695201984896078165322693 1630350372168014655998005)
                      ·
                        rfl

theorem cell23_3175096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 6, 2, 4].length) (baseStart_3175096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175096 prefixEnd_3175096 := by exact prefixLift 3175096
  have htrace : WordTrace (prefixWord ++ tailWord_3175096) baseStart_3175096 baseEnd_3175096 := by
    simpa [prefixWord, tailWord_3175096, baseEnd_3175096] using wordTrace_append hprefix tailTrace_3175096
  have hstable : (prefixWord ++ tailWord_3175096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175096).length < 2 ^ (prefixWord ++ tailWord_3175096).sum := by decide
  have hdescent : baseEnd_3175096 < baseStart_3175096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175100 : List Nat := [2, 2, 2, 3, 1, 1, 3, 2, 1, 4, 2]
def baseStart_3175100 : Nat := 118140960795 + 3175100 * 2 ^ 59
def prefixEnd_3175100 : Nat := 4983230072969 + 3 ^ 40 * 3175100 * 2
def baseEnd_3175100 : Nat := 1630352426090632640347987

theorem tailTrace_3175100 : CollatzResearch.WordTrace tailWord_3175100 prefixEnd_3175100 1630352426090632640347987 := by
  unfold tailWord_3175100
  simp only [CollatzResearch.WordTrace]
  refine ⟨57902705398581219376637377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77203607198108292502183169 57902705398581219376637377)
  ·
    refine ⟨43427029048935914532478033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57902705398581219376637377 43427029048935914532478033)
    ·
      refine ⟨32570271786701935899358525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43427029048935914532478033 32570271786701935899358525)
      ·
        refine ⟨12213851920013225962259447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32570271786701935899358525 12213851920013225962259447)
        ·
          refine ⟨18320777880019838943389171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12213851920013225962259447 18320777880019838943389171)
          ·
            refine ⟨27481166820029758415083757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18320777880019838943389171 27481166820029758415083757)
            ·
              refine ⟨10305437557511159405656409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27481166820029758415083757 10305437557511159405656409)
              ·
                refine ⟨7729078168133369554242307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10305437557511159405656409 7729078168133369554242307)
                ·
                  refine ⟨11593617252200054331363461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7729078168133369554242307 11593617252200054331363461)
                  ·
                    refine ⟨2173803234787510187130649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11593617252200054331363461 2173803234787510187130649)
                    ·
                      refine ⟨1630352426090632640347987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2173803234787510187130649 1630352426090632640347987)
                      ·
                        rfl

theorem cell23_3175100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_3175100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175100 prefixEnd_3175100 := by exact prefixLift 3175100
  have htrace : WordTrace (prefixWord ++ tailWord_3175100) baseStart_3175100 baseEnd_3175100 := by
    simpa [prefixWord, tailWord_3175100, baseEnd_3175100] using wordTrace_append hprefix tailTrace_3175100
  have hstable : (prefixWord ++ tailWord_3175100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175100).length < 2 ^ (prefixWord ++ tailWord_3175100).sum := by decide
  have hdescent : baseEnd_3175100 < baseStart_3175100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175136 : List Nat := [2, 1, 1, 3, 1, 2, 1, 4, 1, 7]
def baseStart_3175136 : Nat := 118140960795 + 3175136 * 2 ^ 59
def prefixEnd_3175136 : Nat := 4983230072969 + 3 ^ 40 * 3175136 * 2
def baseEnd_3175136 : Nat := 543456970464731499832607

theorem tailTrace_3175136 : CollatzResearch.WordTrace tailWord_3175136 prefixEnd_3175136 543456970464731499832607 := by
  unfold tailWord_3175136
  simp only [CollatzResearch.WordTrace]
  refine ⟨57903361912516008450792631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77204482550021344601056841 57903361912516008450792631)
  ·
    refine ⟨86855042868774012676188947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57903361912516008450792631 86855042868774012676188947)
    ·
      refine ⟨130282564303161019014283421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86855042868774012676188947 130282564303161019014283421)
      ·
        refine ⟨48855961613685382130356283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130282564303161019014283421 48855961613685382130356283)
        ·
          refine ⟨73283942420528073195534425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48855961613685382130356283 73283942420528073195534425)
          ·
            refine ⟨54962956815396054896650819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73283942420528073195534425 54962956815396054896650819)
            ·
              refine ⟨82444435223094082344976229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54962956815396054896650819 82444435223094082344976229)
              ·
                refine ⟨15458331604330140439683043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82444435223094082344976229 15458331604330140439683043)
                ·
                  refine ⟨23187497406495210659524565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15458331604330140439683043 23187497406495210659524565)
                  ·
                    refine ⟨543456970464731499832607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23187497406495210659524565 543456970464731499832607)
                    ·
                      rfl

theorem cell23_3175136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 1, 7].length) (baseStart_3175136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175136 prefixEnd_3175136 := by exact prefixLift 3175136
  have htrace : WordTrace (prefixWord ++ tailWord_3175136) baseStart_3175136 baseEnd_3175136 := by
    simpa [prefixWord, tailWord_3175136, baseEnd_3175136] using wordTrace_append hprefix tailTrace_3175136
  have hstable : (prefixWord ++ tailWord_3175136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175136).length < 2 ^ (prefixWord ++ tailWord_3175136).sum := by decide
  have hdescent : baseEnd_3175136 < baseStart_3175136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175173 : List Nat := [1, 3, 1, 1, 2, 1, 1, 6, 2, 1, 4]
def baseStart_3175173 : Nat := 118140960795 + 3175173 * 2 ^ 59
def prefixEnd_3175173 : Nat := 4983230072969 + 3 ^ 40 * 3175173 * 2
def baseEnd_3175173 : Nat := 1630389910178410854735151

theorem tailTrace_3175173 : CollatzResearch.WordTrace tailWord_3175173 prefixEnd_3175173 1630389910178410854735151 := by
  unfold tailWord_3175173
  simp only [CollatzResearch.WordTrace]
  refine ⟨115808073325897972220682173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77205382217265314813788115 115808073325897972220682173)
  ·
    refine ⟨43428027497211739582755815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115808073325897972220682173 43428027497211739582755815)
    ·
      refine ⟨65142041245817609374133723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43428027497211739582755815 65142041245817609374133723)
      ·
        refine ⟨97713061868726414061200585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65142041245817609374133723 97713061868726414061200585)
        ·
          refine ⟨73284796401544810545900439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97713061868726414061200585 73284796401544810545900439)
          ·
            refine ⟨109927194602317215818850659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73284796401544810545900439 109927194602317215818850659)
            ·
              refine ⟨164890791903475823728275989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109927194602317215818850659 164890791903475823728275989)
              ·
                refine ⟨7729255870475429237262937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 164890791903475823728275989 7729255870475429237262937)
                ·
                  refine ⟨5796941902856571927947203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7729255870475429237262937 5796941902856571927947203)
                  ·
                    refine ⟨8695412854284857891920805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5796941902856571927947203 8695412854284857891920805)
                    ·
                      refine ⟨1630389910178410854735151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8695412854284857891920805 1630389910178410854735151)
                      ·
                        rfl

theorem cell23_3175173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 1, 4].length) (baseStart_3175173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175173 prefixEnd_3175173 := by exact prefixLift 3175173
  have htrace : WordTrace (prefixWord ++ tailWord_3175173) baseStart_3175173 baseEnd_3175173 := by
    simpa [prefixWord, tailWord_3175173, baseEnd_3175173] using wordTrace_append hprefix tailTrace_3175173
  have hstable : (prefixWord ++ tailWord_3175173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175173).length < 2 ^ (prefixWord ++ tailWord_3175173).sum := by decide
  have hdescent : baseEnd_3175173 < baseStart_3175173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175193 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 6, 2, 3]
def baseStart_3175193 : Nat := 118140960795 + 3175193 * 2 ^ 59
def prefixEnd_3175193 : Nat := 4983230072969 + 3 ^ 40 * 3175193 * 2
def baseEnd_3175193 : Nat := 1630400179791500776485059

theorem tailTrace_3175193 : CollatzResearch.WordTrace tailWord_3175193 prefixEnd_3175193 1630400179791500776485059 := by
  unfold tailWord_3175193
  simp only [CollatzResearch.WordTrace]
  refine ⟨115808802785825515636410233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77205868523883677090940155 115808802785825515636410233)
  ·
    refine ⟨86856602089369136727307675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115808802785825515636410233 86856602089369136727307675)
    ·
      refine ⟨130284903134053705090961513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86856602089369136727307675 130284903134053705090961513)
      ·
        refine ⟨97713677350540278818221135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130284903134053705090961513 97713677350540278818221135)
        ·
          refine ⟨146570516025810418227331703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97713677350540278818221135 146570516025810418227331703)
          ·
            refine ⟨219855774038715627340997555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146570516025810418227331703 219855774038715627340997555)
            ·
              refine ⟨329783661058073441011496333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219855774038715627340997555 329783661058073441011496333)
              ·
                refine ⟨123668872896777540379311125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 329783661058073441011496333 123668872896777540379311125)
                ·
                  refine ⟨5796978417036447205280209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 123668872896777540379311125 5796978417036447205280209)
                  ·
                    refine ⟨4347733812777335403960157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5796978417036447205280209 4347733812777335403960157)
                    ·
                      refine ⟨1630400179791500776485059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4347733812777335403960157 1630400179791500776485059)
                      ·
                        rfl

theorem cell23_3175193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 2, 3].length) (baseStart_3175193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175193 prefixEnd_3175193 := by exact prefixLift 3175193
  have htrace : WordTrace (prefixWord ++ tailWord_3175193) baseStart_3175193 baseEnd_3175193 := by
    simpa [prefixWord, tailWord_3175193, baseEnd_3175193] using wordTrace_append hprefix tailTrace_3175193
  have hstable : (prefixWord ++ tailWord_3175193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175193).length < 2 ^ (prefixWord ++ tailWord_3175193).sum := by decide
  have hdescent : baseEnd_3175193 < baseStart_3175193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175200 : List Nat := [2, 1, 1, 5, 1, 2, 2, 2, 3, 4]
def baseStart_3175200 : Nat := 118140960795 + 3175200 * 2 ^ 59
def prefixEnd_3175200 : Nat := 4983230072969 + 3 ^ 40 * 3175200 * 2
def baseEnd_3175200 : Nat := 543467924718694083032509

theorem tailTrace_3175200 : CollatzResearch.WordTrace tailWord_3175200 prefixEnd_3175200 543467924718694083032509 := by
  unfold tailWord_3175200
  simp only [CollatzResearch.WordTrace]
  refine ⟨57904529048400077915957527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77206038731200103887943369 57904529048400077915957527)
  ·
    refine ⟨86856793572600116873936291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57904529048400077915957527 86856793572600116873936291)
    ·
      refine ⟨130285190358900175310904437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86856793572600116873936291 130285190358900175310904437)
      ·
        refine ⟨12214236596146891435397291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130285190358900175310904437 12214236596146891435397291)
        ·
          refine ⟨18321354894220337153095937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12214236596146891435397291 18321354894220337153095937)
          ·
            refine ⟨13741016170665252864821953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18321354894220337153095937 13741016170665252864821953)
            ·
              refine ⟨10305762127998939648616465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13741016170665252864821953 10305762127998939648616465)
              ·
                refine ⟨7729321595999204736462349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10305762127998939648616465 7729321595999204736462349)
                ·
                  refine ⟨2898495598499701776173381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7729321595999204736462349 2898495598499701776173381)
                  ·
                    refine ⟨543467924718694083032509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2898495598499701776173381 543467924718694083032509)
                    ·
                      rfl

theorem cell23_3175200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 3, 4].length) (baseStart_3175200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175200 prefixEnd_3175200 := by exact prefixLift 3175200
  have htrace : WordTrace (prefixWord ++ tailWord_3175200) baseStart_3175200 baseEnd_3175200 := by
    simpa [prefixWord, tailWord_3175200, baseEnd_3175200] using wordTrace_append hprefix tailTrace_3175200
  have hstable : (prefixWord ++ tailWord_3175200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175200).length < 2 ^ (prefixWord ++ tailWord_3175200).sum := by decide
  have hdescent : baseEnd_3175200 < baseStart_3175200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175267 : List Nat := [1, 1, 1, 5, 3, 1, 1, 3, 2, 3, 2]
def baseStart_3175267 : Nat := 118140960795 + 3175267 * 2 ^ 59
def prefixEnd_3175267 : Nat := 4983230072969 + 3 ^ 40 * 3175267 * 2
def baseEnd_3175267 : Nat := 1630438177359933486959719

theorem tailTrace_3175267 : CollatzResearch.WordTrace tailWord_3175267 prefixEnd_3175267 1630438177359933486959719 := by
  unfold tailWord_3175267
  simp only [CollatzResearch.WordTrace]
  refine ⟨115811501787557426274604055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77207667858371617516402703 115811501787557426274604055)
  ·
    refine ⟨173717252681336139411906083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115811501787557426274604055 173717252681336139411906083)
    ·
      refine ⟨260575879022004209117859125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173717252681336139411906083 260575879022004209117859125)
      ·
        refine ⟨24428988658312894604799293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 260575879022004209117859125 24428988658312894604799293)
        ·
          refine ⟨9160870746867335476799735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24428988658312894604799293 9160870746867335476799735)
          ·
            refine ⟨13741306120301003215199603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9160870746867335476799735 13741306120301003215199603)
            ·
              refine ⟨20611959180451504822799405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13741306120301003215199603 20611959180451504822799405)
              ·
                refine ⟨7729484692669314308549777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20611959180451504822799405 7729484692669314308549777)
                ·
                  refine ⟨5797113519501985731412333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7729484692669314308549777 5797113519501985731412333)
                  ·
                    refine ⟨2173917569813244649279625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5797113519501985731412333 2173917569813244649279625)
                    ·
                      refine ⟨1630438177359933486959719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2173917569813244649279625 1630438177359933486959719)
                      ·
                        rfl

theorem cell23_3175267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_3175267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175267 prefixEnd_3175267 := by exact prefixLift 3175267
  have htrace : WordTrace (prefixWord ++ tailWord_3175267) baseStart_3175267 baseEnd_3175267 := by
    simpa [prefixWord, tailWord_3175267, baseEnd_3175267] using wordTrace_append hprefix tailTrace_3175267
  have hstable : (prefixWord ++ tailWord_3175267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175267).length < 2 ^ (prefixWord ++ tailWord_3175267).sum := by decide
  have hdescent : baseEnd_3175267 < baseStart_3175267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175280 : List Nat := [2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 4]
def baseStart_3175280 : Nat := 118140960795 + 3175280 * 2 ^ 59
def prefixEnd_3175280 : Nat := 4983230072969 + 3 ^ 40 * 3175280 * 2
def baseEnd_3175280 : Nat := 1630444852608441936097159

theorem tailTrace_3175280 : CollatzResearch.WordTrace tailWord_3175280 prefixEnd_3175280 1630444852608441936097159 := by
  unfold tailWord_3175280
  simp only [CollatzResearch.WordTrace]
  refine ⟨57905987968255164747413647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77207983957673552996551529 57905987968255164747413647)
  ·
    refine ⟨86858981952382747121120471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57905987968255164747413647 86858981952382747121120471)
    ·
      refine ⟨130288472928574120681680707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86858981952382747121120471 130288472928574120681680707)
      ·
        refine ⟨195432709392861181022521061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130288472928574120681680707 195432709392861181022521061)
        ·
          refine ⟨36643633011161471441722699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195432709392861181022521061 36643633011161471441722699)
          ·
            refine ⟨54965449516742207162584049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36643633011161471441722699 54965449516742207162584049)
            ·
              refine ⟨41224087137556655371938037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54965449516742207162584049 41224087137556655371938037)
              ·
                refine ⟨3864758169145936441119191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41224087137556655371938037 3864758169145936441119191)
                ·
                  refine ⟨5797137253718904661678787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3864758169145936441119191 5797137253718904661678787)
                  ·
                    refine ⟨8695705880578356992518181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5797137253718904661678787 8695705880578356992518181)
                    ·
                      refine ⟨1630444852608441936097159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8695705880578356992518181 1630444852608441936097159)
                      ·
                        rfl

theorem cell23_3175280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 4].length) (baseStart_3175280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175280 prefixEnd_3175280 := by exact prefixLift 3175280
  have htrace : WordTrace (prefixWord ++ tailWord_3175280) baseStart_3175280 baseEnd_3175280 := by
    simpa [prefixWord, tailWord_3175280, baseEnd_3175280] using wordTrace_append hprefix tailTrace_3175280
  have hstable : (prefixWord ++ tailWord_3175280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175280).length < 2 ^ (prefixWord ++ tailWord_3175280).sum := by decide
  have hdescent : baseEnd_3175280 < baseStart_3175280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175293 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 3, 1, 6]
def baseStart_3175293 : Nat := 118140960795 + 3175293 * 2 ^ 59
def prefixEnd_3175293 : Nat := 4983230072969 + 3 ^ 40 * 3175293 * 2
def baseEnd_3175293 : Nat := 1630451527856950385234599

theorem tailTrace_3175293 : CollatzResearch.WordTrace tailWord_3175293 prefixEnd_3175293 1630451527856950385234599 := by
  unfold tailWord_3175293
  simp only [CollatzResearch.WordTrace]
  refine ⟨115812450085463232715050533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77208300056975488476700355 115812450085463232715050533)
  ·
    refine ⟨21714834391024356134071975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115812450085463232715050533 21714834391024356134071975)
    ·
      refine ⟨32572251586536534201107963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21714834391024356134071975 32572251586536534201107963)
      ·
        refine ⟨48858377379804801301661945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32572251586536534201107963 48858377379804801301661945)
        ·
          refine ⟨36643783034853600976246459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48858377379804801301661945 36643783034853600976246459)
          ·
            refine ⟨54965674552280401464369689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36643783034853600976246459 54965674552280401464369689)
            ·
              refine ⟨41224255914210301098277267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54965674552280401464369689 41224255914210301098277267)
              ·
                refine ⟨61836383871315451647415901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41224255914210301098277267 61836383871315451647415901)
                ·
                  refine ⟨23188643951743294367780963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61836383871315451647415901 23188643951743294367780963)
                  ·
                    refine ⟨34782965927614941551671445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23188643951743294367780963 34782965927614941551671445)
                    ·
                      refine ⟨1630451527856950385234599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34782965927614941551671445 1630451527856950385234599)
                      ·
                        rfl

theorem cell23_3175293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_3175293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175293 prefixEnd_3175293 := by exact prefixLift 3175293
  have htrace : WordTrace (prefixWord ++ tailWord_3175293) baseStart_3175293 baseEnd_3175293 := by
    simpa [prefixWord, tailWord_3175293, baseEnd_3175293] using wordTrace_append hprefix tailTrace_3175293
  have hstable : (prefixWord ++ tailWord_3175293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175293).length < 2 ^ (prefixWord ++ tailWord_3175293).sum := by decide
  have hdescent : baseEnd_3175293 < baseStart_3175293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175318 : List Nat := [5, 3, 1, 1, 1, 1, 3, 1, 2, 3, 2]
def baseStart_3175318 : Nat := 118140960795 + 3175318 * 2 ^ 59
def prefixEnd_3175318 : Nat := 4983230072969 + 3 ^ 40 * 3175318 * 2
def baseEnd_3175318 : Nat := 1630464364873312787421985

theorem tailTrace_3175318 : CollatzResearch.WordTrace tailWord_3175318 prefixEnd_3175318 1630464364873312787421985 := by
  unfold tailWord_3175318
  simp only [CollatzResearch.WordTrace]
  refine ⟨7238335119398291374044413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77208907940248441323140405 7238335119398291374044413)
  ·
    refine ⟨2714375669774359265266655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7238335119398291374044413 2714375669774359265266655)
    ·
      refine ⟨4071563504661538897899983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2714375669774359265266655 4071563504661538897899983)
      ·
        refine ⟨6107345256992308346849975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4071563504661538897899983 6107345256992308346849975)
        ·
          refine ⟨9161017885488462520274963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6107345256992308346849975 9161017885488462520274963)
          ·
            refine ⟨13741526828232693780412445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9161017885488462520274963 13741526828232693780412445)
            ·
              refine ⟨5153072560587260167654667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13741526828232693780412445 5153072560587260167654667)
              ·
                refine ⟨7729608840880890251482001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5153072560587260167654667 7729608840880890251482001)
                ·
                  refine ⟨5797206630660667688611501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7729608840880890251482001 5797206630660667688611501)
                  ·
                    refine ⟨2173952486497750383229313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5797206630660667688611501 2173952486497750383229313)
                    ·
                      refine ⟨1630464364873312787421985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2173952486497750383229313 1630464364873312787421985)
                      ·
                        rfl

theorem cell23_3175318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_3175318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175318 prefixEnd_3175318 := by exact prefixLift 3175318
  have htrace : WordTrace (prefixWord ++ tailWord_3175318) baseStart_3175318 baseEnd_3175318 := by
    simpa [prefixWord, tailWord_3175318, baseEnd_3175318] using wordTrace_append hprefix tailTrace_3175318
  have hstable : (prefixWord ++ tailWord_3175318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175318).length < 2 ^ (prefixWord ++ tailWord_3175318).sum := by decide
  have hdescent : baseEnd_3175318 < baseStart_3175318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175343 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 5]
def baseStart_3175343 : Nat := 118140960795 + 3175343 * 2 ^ 59
def prefixEnd_3175343 : Nat := 4983230072969 + 3 ^ 40 * 3175343 * 2
def baseEnd_3175343 : Nat := 1630477201889675189609369

theorem tailTrace_3175343 : CollatzResearch.WordTrace tailWord_3175343 prefixEnd_3175343 1630477201889675189609369 := by
  unfold tailWord_3175343
  simp only [CollatzResearch.WordTrace]
  refine ⟨115814273735282091254370683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77209515823521394169580455 115814273735282091254370683)
  ·
    refine ⟨173721410602923136881556025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115814273735282091254370683 173721410602923136881556025)
    ·
      refine ⟨130291057952192352661167019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173721410602923136881556025 130291057952192352661167019)
      ·
        refine ⟨195436586928288528991750529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130291057952192352661167019 195436586928288528991750529)
        ·
          refine ⟨146577440196216396743812897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195436586928288528991750529 146577440196216396743812897)
          ·
            refine ⟨109933080147162297557859673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146577440196216396743812897 109933080147162297557859673)
            ·
              refine ⟨82449810110371723168394755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109933080147162297557859673 82449810110371723168394755)
              ·
                refine ⟨123674715165557584752592133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82449810110371723168394755 123674715165557584752592133)
                ·
                  refine ⟨23189009093542047141111025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 123674715165557584752592133 23189009093542047141111025)
                  ·
                    refine ⟨17391756820156535355833269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23189009093542047141111025 17391756820156535355833269)
                    ·
                      refine ⟨1630477201889675189609369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17391756820156535355833269 1630477201889675189609369)
                      ·
                        rfl

theorem cell23_3175343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 5].length) (baseStart_3175343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175343 prefixEnd_3175343 := by exact prefixLift 3175343
  have htrace : WordTrace (prefixWord ++ tailWord_3175343) baseStart_3175343 baseEnd_3175343 := by
    simpa [prefixWord, tailWord_3175343, baseEnd_3175343] using wordTrace_append hprefix tailTrace_3175343
  have hstable : (prefixWord ++ tailWord_3175343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175343).length < 2 ^ (prefixWord ++ tailWord_3175343).sum := by decide
  have hdescent : baseEnd_3175343 < baseStart_3175343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175347 : List Nat := [1, 1, 1, 2, 3, 1, 2, 6, 2, 1, 3]
def baseStart_3175347 : Nat := 118140960795 + 3175347 * 2 ^ 59
def prefixEnd_3175347 : Nat := 4983230072969 + 3 ^ 40 * 3175347 * 2
def baseEnd_3175347 : Nat := 1630479255812293173959351

theorem tailTrace_3175347 : CollatzResearch.WordTrace tailWord_3175347 prefixEnd_3175347 1630479255812293173959351 := by
  unfold tailWord_3175347
  simp only [CollatzResearch.WordTrace]
  refine ⟨115814419627267599937516295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77209613084845066625010863 115814419627267599937516295)
  ·
    refine ⟨173721629440901399906274443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115814419627267599937516295 173721629440901399906274443)
    ·
      refine ⟨260582444161352099859411665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173721629440901399906274443 260582444161352099859411665)
      ·
        refine ⟨195436833121014074894558749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260582444161352099859411665 195436833121014074894558749)
        ·
          refine ⟨73288812420380278085459531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195436833121014074894558749 73288812420380278085459531)
          ·
            refine ⟨109933218630570417128189297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73288812420380278085459531 109933218630570417128189297)
            ·
              refine ⟨82449913972927812846141973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109933218630570417128189297 82449913972927812846141973)
              ·
                refine ⟨3864839717480991227162905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82449913972927812846141973 3864839717480991227162905)
                ·
                  refine ⟨2898629788110743420372179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3864839717480991227162905 2898629788110743420372179)
                  ·
                    refine ⟨4347944682166115130558269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2898629788110743420372179 4347944682166115130558269)
                    ·
                      refine ⟨1630479255812293173959351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4347944682166115130558269 1630479255812293173959351)
                      ·
                        rfl

theorem cell23_3175347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 2, 1, 3].length) (baseStart_3175347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175347 prefixEnd_3175347 := by exact prefixLift 3175347
  have htrace : WordTrace (prefixWord ++ tailWord_3175347) baseStart_3175347 baseEnd_3175347 := by
    simpa [prefixWord, tailWord_3175347, baseEnd_3175347] using wordTrace_append hprefix tailTrace_3175347
  have hstable : (prefixWord ++ tailWord_3175347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175347).length < 2 ^ (prefixWord ++ tailWord_3175347).sum := by decide
  have hdescent : baseEnd_3175347 < baseStart_3175347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175348 : List Nat := [2, 5, 2, 1, 1, 2, 2, 1, 3, 2, 2]
def baseStart_3175348 : Nat := 118140960795 + 3175348 * 2 ^ 59
def prefixEnd_3175348 : Nat := 4983230072969 + 3 ^ 40 * 3175348 * 2
def baseEnd_3175348 : Nat := 1630479769292947670046847

theorem tailTrace_3175348 : CollatzResearch.WordTrace tailWord_3175348 prefixEnd_3175348 1630479769292947670046847 := by
  unfold tailWord_3175348
  simp only [CollatzResearch.WordTrace]
  refine ⟨57907228050131988554151349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77209637400175984738868465 57907228050131988554151349)
  ·
    refine ⟨5428802629699873926951689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57907228050131988554151349 5428802629699873926951689)
    ·
      refine ⟨4071601972274905445213767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5428802629699873926951689 4071601972274905445213767)
      ·
        refine ⟨6107402958412358167820651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4071601972274905445213767 6107402958412358167820651)
        ·
          refine ⟨9161104437618537251730977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6107402958412358167820651 9161104437618537251730977)
          ·
            refine ⟨6870828328213902938798233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9161104437618537251730977 6870828328213902938798233)
            ·
              refine ⟨5153121246160427204098675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6870828328213902938798233 5153121246160427204098675)
              ·
                refine ⟨7729681869240640806148013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5153121246160427204098675 7729681869240640806148013)
                ·
                  refine ⟨2898630700965240302305505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7729681869240640806148013 2898630700965240302305505)
                  ·
                    refine ⟨2173973025723930226729129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2898630700965240302305505 2173973025723930226729129)
                    ·
                      refine ⟨1630479769292947670046847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2173973025723930226729129 1630479769292947670046847)
                      ·
                        rfl

theorem cell23_3175348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_3175348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175348 prefixEnd_3175348 := by exact prefixLift 3175348
  have htrace : WordTrace (prefixWord ++ tailWord_3175348) baseStart_3175348 baseEnd_3175348 := by
    simpa [prefixWord, tailWord_3175348, baseEnd_3175348] using wordTrace_append hprefix tailTrace_3175348
  have hstable : (prefixWord ++ tailWord_3175348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175348).length < 2 ^ (prefixWord ++ tailWord_3175348).sum := by decide
  have hdescent : baseEnd_3175348 < baseStart_3175348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175374 : List Nat := [4, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2]
def baseStart_3175374 : Nat := 118140960795 + 3175374 * 2 ^ 59
def prefixEnd_3175374 : Nat := 4983230072969 + 3 ^ 40 * 3175374 * 2
def baseEnd_3175374 : Nat := 1630493119789964568321727

theorem tailTrace_3175374 : CollatzResearch.WordTrace tailWord_3175374 prefixEnd_3175374 1630493119789964568321727 := by
  unfold tailWord_3175374
  simp only [CollatzResearch.WordTrace]
  refine ⟨14476925549771222943593647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77210269598779855699166117 14476925549771222943593647)
  ·
    refine ⟨21715388324656834415390471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14476925549771222943593647 21715388324656834415390471)
    ·
      refine ⟨32573082486985251623085707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21715388324656834415390471 32573082486985251623085707)
      ·
        refine ⟨48859623730477877434628561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32573082486985251623085707 48859623730477877434628561)
        ·
          refine ⟨36644717797858408075971421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48859623730477877434628561 36644717797858408075971421)
          ·
            refine ⟨13741769174196903028489283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36644717797858408075971421 13741769174196903028489283)
            ·
              refine ⟨20612653761295354542733925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13741769174196903028489283 20612653761295354542733925)
              ·
                refine ⟨3864872580242878976762611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20612653761295354542733925 3864872580242878976762611)
                ·
                  refine ⟨5797308870364318465143917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3864872580242878976762611 5797308870364318465143917)
                  ·
                    refine ⟨2173990826386619424428969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5797308870364318465143917 2173990826386619424428969)
                    ·
                      refine ⟨1630493119789964568321727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2173990826386619424428969 1630493119789964568321727)
                      ·
                        rfl

theorem cell23_3175374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2].length) (baseStart_3175374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175374 prefixEnd_3175374 := by exact prefixLift 3175374
  have htrace : WordTrace (prefixWord ++ tailWord_3175374) baseStart_3175374 baseEnd_3175374 := by
    simpa [prefixWord, tailWord_3175374, baseEnd_3175374] using wordTrace_append hprefix tailTrace_3175374
  have hstable : (prefixWord ++ tailWord_3175374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175374).length < 2 ^ (prefixWord ++ tailWord_3175374).sum := by decide
  have hdescent : baseEnd_3175374 < baseStart_3175374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175400 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 4, 2, 4]
def baseStart_3175400 : Nat := 118140960795 + 3175400 * 2 ^ 59
def prefixEnd_3175400 : Nat := 4983230072969 + 3 ^ 40 * 3175400 * 2
def baseEnd_3175400 : Nat := 1630506470286981466596607

theorem tailTrace_3175400 : CollatzResearch.WordTrace tailWord_3175400 prefixEnd_3175400 1630506470286981466596607 := by
  unfold tailWord_3175400
  simp only [CollatzResearch.WordTrace]
  refine ⟨57908176348037794994597827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77210901797383726659463769 57908176348037794994597827)
  ·
    refine ⟨86862264522056692491896741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57908176348037794994597827 86862264522056692491896741)
    ·
      refine ⟨16286674597885629842230639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86862264522056692491896741 16286674597885629842230639)
      ·
        refine ⟨24430011896828444763345959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16286674597885629842230639 24430011896828444763345959)
        ·
          refine ⟨36645017845242667145018939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24430011896828444763345959 36645017845242667145018939)
          ·
            refine ⟨54967526767864000717528409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36645017845242667145018939 54967526767864000717528409)
            ·
              refine ⟨41225645075898000538146307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54967526767864000717528409 41225645075898000538146307)
              ·
                refine ⟨61838467613847000807219461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41225645075898000538146307 61838467613847000807219461)
                ·
                  refine ⟨11594712677596312651353649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61838467613847000807219461 11594712677596312651353649)
                  ·
                    refine ⟨8696034508197234488515237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11594712677596312651353649 8696034508197234488515237)
                    ·
                      refine ⟨1630506470286981466596607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8696034508197234488515237 1630506470286981466596607)
                      ·
                        rfl

theorem cell23_3175400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_3175400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175400 prefixEnd_3175400 := by exact prefixLift 3175400
  have htrace : WordTrace (prefixWord ++ tailWord_3175400) baseStart_3175400 baseEnd_3175400 := by
    simpa [prefixWord, tailWord_3175400, baseEnd_3175400] using wordTrace_append hprefix tailTrace_3175400
  have hstable : (prefixWord ++ tailWord_3175400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175400).length < 2 ^ (prefixWord ++ tailWord_3175400).sum := by decide
  have hdescent : baseEnd_3175400 < baseStart_3175400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175442 : List Nat := [3, 2, 5, 1, 1, 1, 3, 1, 1, 3, 2]
def baseStart_3175442 : Nat := 118140960795 + 3175442 * 2 ^ 59
def prefixEnd_3175442 : Nat := 4983230072969 + 3 ^ 40 * 3175442 * 2
def baseEnd_3175442 : Nat := 1630528036474470302271415

theorem tailTrace_3175442 : CollatzResearch.WordTrace tailWord_3175442 prefixEnd_3175442 1630528036474470302271415 := by
  unfold tailWord_3175442
  simp only [CollatzResearch.WordTrace]
  refine ⟨28954471140480857790556145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77211923041282287441483053 28954471140480857790556145)
  ·
    refine ⟨21715853355360643342917109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28954471140480857790556145 21715853355360643342917109)
    ·
      refine ⟨2035861252065060313398479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21715853355360643342917109 2035861252065060313398479)
      ·
        refine ⟨3053791878097590470097719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2035861252065060313398479 3053791878097590470097719)
        ·
          refine ⟨4580687817146385705146579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3053791878097590470097719 4580687817146385705146579)
          ·
            refine ⟨6871031725719578557719869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4580687817146385705146579 6871031725719578557719869)
            ·
              refine ⟨2576636897144841959144951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6871031725719578557719869 2576636897144841959144951)
              ·
                refine ⟨3864955345717262938717427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2576636897144841959144951 3864955345717262938717427)
                ·
                  refine ⟨5797433018575894408076141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3864955345717262938717427 5797433018575894408076141)
                  ·
                    refine ⟨2174037381965960403028553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5797433018575894408076141 2174037381965960403028553)
                    ·
                      refine ⟨1630528036474470302271415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2174037381965960403028553 1630528036474470302271415)
                      ·
                        rfl

theorem cell23_3175442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_3175442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175442 prefixEnd_3175442 := by exact prefixLift 3175442
  have htrace : WordTrace (prefixWord ++ tailWord_3175442) baseStart_3175442 baseEnd_3175442 := by
    simpa [prefixWord, tailWord_3175442, baseEnd_3175442] using wordTrace_append hprefix tailTrace_3175442
  have hstable : (prefixWord ++ tailWord_3175442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175442).length < 2 ^ (prefixWord ++ tailWord_3175442).sum := by decide
  have hdescent : baseEnd_3175442 < baseStart_3175442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175450 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 3, 2, 5]
def baseStart_3175450 : Nat := 118140960795 + 3175450 * 2 ^ 59
def prefixEnd_3175450 : Nat := 4983230072969 + 3 ^ 40 * 3175450 * 2
def baseEnd_3175450 : Nat := 1630532144319706270971377

theorem tailTrace_3175450 : CollatzResearch.WordTrace tailWord_3175450 prefixEnd_3175450 1630532144319706270971377 := by
  unfold tailWord_3175450
  simp only [CollatzResearch.WordTrace]
  refine ⟨28954544086473612132128951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77212117563929632352343869 28954544086473612132128951)
  ·
    refine ⟨43431816129710418198193427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28954544086473612132128951 43431816129710418198193427)
    ·
      refine ⟨65147724194565627297290141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43431816129710418198193427 65147724194565627297290141)
      ·
        refine ⟨24430396572962110236483803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65147724194565627297290141 24430396572962110236483803)
        ·
          refine ⟨36645594859443165354725705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24430396572962110236483803 36645594859443165354725705)
          ·
            refine ⟨27484196144582374016044279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36645594859443165354725705 27484196144582374016044279)
            ·
              refine ⟨41226294216873561024066419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27484196144582374016044279 41226294216873561024066419)
              ·
                refine ⟨61839441325310341536099629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41226294216873561024066419 61839441325310341536099629)
                ·
                  refine ⟨23189790496991378076037361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61839441325310341536099629 23189790496991378076037361)
                  ·
                    refine ⟨17392342872743533557028021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23189790496991378076037361 17392342872743533557028021)
                    ·
                      refine ⟨1630532144319706270971377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17392342872743533557028021 1630532144319706270971377)
                      ·
                        rfl

theorem cell23_3175450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_3175450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175450 prefixEnd_3175450 := by exact prefixLift 3175450
  have htrace : WordTrace (prefixWord ++ tailWord_3175450) baseStart_3175450 baseEnd_3175450 := by
    simpa [prefixWord, tailWord_3175450, baseEnd_3175450] using wordTrace_append hprefix tailTrace_3175450
  have hstable : (prefixWord ++ tailWord_3175450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175450).length < 2 ^ (prefixWord ++ tailWord_3175450).sum := by decide
  have hdescent : baseEnd_3175450 < baseStart_3175450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175457 : List Nat := [1, 2, 3, 2, 3, 1, 2, 2, 2, 5]
def baseStart_3175457 : Nat := 118140960795 + 3175457 * 2 ^ 59
def prefixEnd_3175457 : Nat := 4983230072969 + 3 ^ 40 * 3175457 * 2
def baseEnd_3175457 : Nat := 543511912894762581194615

theorem tailTrace_3175457 : CollatzResearch.WordTrace tailWord_3175457 prefixEnd_3175457 543511912894762581194615 := by
  unfold tailWord_3175457
  simp only [CollatzResearch.WordTrace]
  refine ⟨115818431656869088724020625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77212287771246059149347083 115818431656869088724020625)
  ·
    refine ⟨86863823742651816543015469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115818431656869088724020625 86863823742651816543015469)
    ·
      refine ⟨32573933903494431203630801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86863823742651816543015469 32573933903494431203630801)
      ·
        refine ⟨24430450427620823402723101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32573933903494431203630801 24430450427620823402723101)
        ·
          refine ⟨9161418910357808776021163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24430450427620823402723101 9161418910357808776021163)
          ·
            refine ⟨13742128365536713164031745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9161418910357808776021163 13742128365536713164031745)
            ·
              refine ⟨10306596274152534873023809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13742128365536713164031745 10306596274152534873023809)
              ·
                refine ⟨7729947205614401154767857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10306596274152534873023809 7729947205614401154767857)
                ·
                  refine ⟨5797460404210800866075893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7729947205614401154767857 5797460404210800866075893)
                  ·
                    refine ⟨543511912894762581194615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5797460404210800866075893 543511912894762581194615)
                    ·
                      rfl

theorem cell23_3175457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_3175457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175457 prefixEnd_3175457 := by exact prefixLift 3175457
  have htrace : WordTrace (prefixWord ++ tailWord_3175457) baseStart_3175457 baseEnd_3175457 := by
    simpa [prefixWord, tailWord_3175457, baseEnd_3175457] using wordTrace_append hprefix tailTrace_3175457
  have hstable : (prefixWord ++ tailWord_3175457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175457).length < 2 ^ (prefixWord ++ tailWord_3175457).sum := by decide
  have hdescent : baseEnd_3175457 < baseStart_3175457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175497 : List Nat := [1, 2, 1, 1, 2, 2, 2, 5, 2, 2, 3]
def baseStart_3175497 : Nat := 118140960795 + 3175497 * 2 ^ 59
def prefixEnd_3175497 : Nat := 4983230072969 + 3 ^ 40 * 3175497 * 2
def baseEnd_3175497 : Nat := 1630556277910467587083661

theorem tailTrace_3175497 : CollatzResearch.WordTrace tailWord_3175497 prefixEnd_3175497 1630556277910467587083661 := by
  unfold tailWord_3175497
  simp only [CollatzResearch.WordTrace]
  refine ⟨115819890576724175555476745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77213260384482783703651163 115819890576724175555476745)
  ·
    refine ⟨86864917932543131666607559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115819890576724175555476745 86864917932543131666607559)
    ·
      refine ⟨130297376898814697499911339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86864917932543131666607559 130297376898814697499911339)
      ·
        refine ⟨195446065348222046249867009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130297376898814697499911339 195446065348222046249867009)
        ·
          refine ⟨146584549011166534687400257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195446065348222046249867009 146584549011166534687400257)
          ·
            refine ⟨109938411758374901015550193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146584549011166534687400257 109938411758374901015550193)
            ·
              refine ⟨82453808818781175761662645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109938411758374901015550193 82453808818781175761662645)
              ·
                refine ⟨7730044576760735227655873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82453808818781175761662645 7730044576760735227655873)
                ·
                  refine ⟨5797533432570551420741905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7730044576760735227655873 5797533432570551420741905)
                  ·
                    refine ⟨4348150074427913565556429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5797533432570551420741905 4348150074427913565556429)
                    ·
                      refine ⟨1630556277910467587083661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4348150074427913565556429 1630556277910467587083661)
                      ·
                        rfl

theorem cell23_3175497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 2, 3].length) (baseStart_3175497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175497 prefixEnd_3175497 := by exact prefixLift 3175497
  have htrace : WordTrace (prefixWord ++ tailWord_3175497) baseStart_3175497 baseEnd_3175497 := by
    simpa [prefixWord, tailWord_3175497, baseEnd_3175497] using wordTrace_append hprefix tailTrace_3175497
  have hstable : (prefixWord ++ tailWord_3175497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175497).length < 2 ^ (prefixWord ++ tailWord_3175497).sum := by decide
  have hdescent : baseEnd_3175497 < baseStart_3175497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175500 : List Nat := [2, 2, 1, 3, 1, 1, 1, 4, 8]
def baseStart_3175500 : Nat := 118140960795 + 3175500 * 2 ^ 59
def prefixEnd_3175500 : Nat := 4983230072969 + 3 ^ 40 * 3175500 * 2
def baseEnd_3175500 : Nat := 181173090928047897260683

theorem tailTrace_3175500 : CollatzResearch.WordTrace tailWord_3175500 prefixEnd_3175500 181173090928047897260683 := by
  unfold tailWord_3175500
  simp only [CollatzResearch.WordTrace]
  refine ⟨57909999997856653533917977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77213333330475538045223969 57909999997856653533917977)
  ·
    refine ⟨43432499998392490150438483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57909999997856653533917977 43432499998392490150438483)
    ·
      refine ⟨65148749997588735225657725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43432499998392490150438483 65148749997588735225657725)
      ·
        refine ⟨24430781249095775709621647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65148749997588735225657725 24430781249095775709621647)
        ·
          refine ⟨36646171873643663564432471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24430781249095775709621647 36646171873643663564432471)
          ·
            refine ⟨54969257810465495346648707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36646171873643663564432471 54969257810465495346648707)
            ·
              refine ⟨82453886715698243019973061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54969257810465495346648707 82453886715698243019973061)
              ·
                refine ⟨15460103759193420566244949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82453886715698243019973061 15460103759193420566244949)
                ·
                  refine ⟨181173090928047897260683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15460103759193420566244949 181173090928047897260683)
                  ·
                    rfl

theorem cell23_3175500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 8].length) (baseStart_3175500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175500 prefixEnd_3175500 := by exact prefixLift 3175500
  have htrace : WordTrace (prefixWord ++ tailWord_3175500) baseStart_3175500 baseEnd_3175500 := by
    simpa [prefixWord, tailWord_3175500, baseEnd_3175500] using wordTrace_append hprefix tailTrace_3175500
  have hstable : (prefixWord ++ tailWord_3175500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175500).length < 2 ^ (prefixWord ++ tailWord_3175500).sum := by decide
  have hdescent : baseEnd_3175500 < baseStart_3175500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175520 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 8]
def baseStart_3175520 : Nat := 118140960795 + 3175520 * 2 ^ 59
def prefixEnd_3175520 : Nat := 4983230072969 + 3 ^ 40 * 3175520 * 2
def baseEnd_3175520 : Nat := 1630568087965520997096055

theorem tailTrace_3175520 : CollatzResearch.WordTrace tailWord_3175520 prefixEnd_3175520 1630568087965520997096055 := by
  unfold tailWord_3175520
  simp only [CollatzResearch.WordTrace]
  refine ⟨57910364727820425241782007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77213819637093900322376009 57910364727820425241782007)
  ·
    refine ⟨86865547091730637862673011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57910364727820425241782007 86865547091730637862673011)
    ·
      refine ⟨130298320637595956794009517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86865547091730637862673011 130298320637595956794009517)
      ·
        refine ⟨48861870239098483797753569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130298320637595956794009517 48861870239098483797753569)
        ·
          refine ⟨36646402679323862848315177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48861870239098483797753569 36646402679323862848315177)
          ·
            refine ⟨27484802009492897136236383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36646402679323862848315177 27484802009492897136236383)
            ·
              refine ⟨41227203014239345704354575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27484802009492897136236383 41227203014239345704354575)
              ·
                refine ⟨61840804521359018556531863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41227203014239345704354575 61840804521359018556531863)
                ·
                  refine ⟨92761206782038527834797795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61840804521359018556531863 92761206782038527834797795)
                  ·
                    refine ⟨139141810173057791752196693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92761206782038527834797795 139141810173057791752196693)
                    ·
                      refine ⟨1630568087965520997096055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 139141810173057791752196693 1630568087965520997096055)
                      ·
                        rfl

theorem cell23_3175520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_3175520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175520 prefixEnd_3175520 := by exact prefixLift 3175520
  have htrace : WordTrace (prefixWord ++ tailWord_3175520) baseStart_3175520 baseEnd_3175520 := by
    simpa [prefixWord, tailWord_3175520, baseEnd_3175520] using wordTrace_append hprefix tailTrace_3175520
  have hstable : (prefixWord ++ tailWord_3175520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175520).length < 2 ^ (prefixWord ++ tailWord_3175520).sum := by decide
  have hdescent : baseEnd_3175520 < baseStart_3175520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175544 : List Nat := [2, 1, 2, 1, 1, 1, 6, 2, 3, 1, 3]
def baseStart_3175544 : Nat := 118140960795 + 3175544 * 2 ^ 59
def prefixEnd_3175544 : Nat := 4983230072969 + 3 ^ 40 * 3175544 * 2
def baseEnd_3175544 : Nat := 1630580411501228903195945

theorem tailTrace_3175544 : CollatzResearch.WordTrace tailWord_3175544 prefixEnd_3175544 1630580411501228903195945 := by
  unfold tailWord_3175544
  simp only [CollatzResearch.WordTrace]
  refine ⟨57910802403776951291218843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77214403205035935054958457 57910802403776951291218843)
  ·
    refine ⟨86866203605665426936828265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57910802403776951291218843 86866203605665426936828265)
    ·
      refine ⟨65149652704249070202621199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86866203605665426936828265 65149652704249070202621199)
      ·
        refine ⟨97724479056373605303931799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65149652704249070202621199 97724479056373605303931799)
        ·
          refine ⟨146586718584560407955897699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97724479056373605303931799 146586718584560407955897699)
          ·
            refine ⟨219880077876840611933846549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146586718584560407955897699 219880077876840611933846549)
            ·
              refine ⟨10306878650476903684399057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 219880077876840611933846549 10306878650476903684399057)
              ·
                refine ⟨7730158987857677763299293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10306878650476903684399057 7730158987857677763299293)
                ·
                  refine ⟨2898809620446629161237235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7730158987857677763299293 2898809620446629161237235)
                  ·
                    refine ⟨4348214430669943741855853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2898809620446629161237235 4348214430669943741855853)
                    ·
                      refine ⟨1630580411501228903195945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4348214430669943741855853 1630580411501228903195945)
                      ·
                        rfl

theorem cell23_3175544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 3, 1, 3].length) (baseStart_3175544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175544 prefixEnd_3175544 := by exact prefixLift 3175544
  have htrace : WordTrace (prefixWord ++ tailWord_3175544) baseStart_3175544 baseEnd_3175544 := by
    simpa [prefixWord, tailWord_3175544, baseEnd_3175544] using wordTrace_append hprefix tailTrace_3175544
  have hstable : (prefixWord ++ tailWord_3175544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175544).length < 2 ^ (prefixWord ++ tailWord_3175544).sum := by decide
  have hdescent : baseEnd_3175544 < baseStart_3175544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175578 : List Nat := [3, 1, 1, 5, 1, 3, 1, 1, 3, 1, 3]
def baseStart_3175578 : Nat := 118140960795 + 3175578 * 2 ^ 59
def prefixEnd_3175578 : Nat := 4983230072969 + 3 ^ 40 * 3175578 * 2
def baseEnd_3175578 : Nat := 1630597869843481770170789

theorem tailTrace_3175578 : CollatzResearch.WordTrace tailWord_3175578 prefixEnd_3175578 1630597869843481770170789 := by
  unfold tailWord_3175578
  simp only [CollatzResearch.WordTrace]
  refine ⟨28955711222357681597293847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77215229926287150926116925 28955711222357681597293847)
  ·
    refine ⟨43433566833536522395940771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28955711222357681597293847 43433566833536522395940771)
    ·
      refine ⟨65150350250304783593911157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43433566833536522395940771 65150350250304783593911157)
      ·
        refine ⟨6107845335966073461929171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65150350250304783593911157 6107845335966073461929171)
        ·
          refine ⟨9161768003949110192893757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6107845335966073461929171 9161768003949110192893757)
          ·
            refine ⟨3435663001480916322335159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9161768003949110192893757 3435663001480916322335159)
            ·
              refine ⟨5153494502221374483502739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3435663001480916322335159 5153494502221374483502739)
              ·
                refine ⟨7730241753332061725254109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5153494502221374483502739 7730241753332061725254109)
                ·
                  refine ⟨2898840657499523146970291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7730241753332061725254109 2898840657499523146970291)
                  ·
                    refine ⟨4348260986249284720455437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2898840657499523146970291 4348260986249284720455437)
                    ·
                      refine ⟨1630597869843481770170789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4348260986249284720455437 1630597869843481770170789)
                      ·
                        rfl

theorem cell23_3175578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_3175578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175578 prefixEnd_3175578 := by exact prefixLift 3175578
  have htrace : WordTrace (prefixWord ++ tailWord_3175578) baseStart_3175578 baseEnd_3175578 := by
    simpa [prefixWord, tailWord_3175578, baseEnd_3175578] using wordTrace_append hprefix tailTrace_3175578
  have hstable : (prefixWord ++ tailWord_3175578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175578).length < 2 ^ (prefixWord ++ tailWord_3175578).sum := by decide
  have hdescent : baseEnd_3175578 < baseStart_3175578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175601 : List Nat := [1, 2, 2, 5, 1, 1, 3, 2, 1, 1, 4]
def baseStart_3175601 : Nat := 118140960795 + 3175601 * 2 ^ 59
def prefixEnd_3175601 : Nat := 4983230072969 + 3 ^ 40 * 3175601 * 2
def baseEnd_3175601 : Nat := 1630609679898535180183183

theorem tailTrace_3175601 : CollatzResearch.WordTrace tailWord_3175601 prefixEnd_3175601 1630609679898535180183183 := by
  unfold tailWord_3175601
  simp only [CollatzResearch.WordTrace]
  refine ⟨115823683768347401317262657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77215789178898267544841771 115823683768347401317262657)
  ·
    refine ⟨86867762826260550987946993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115823683768347401317262657 86867762826260550987946993)
    ·
      refine ⟨65150822119695413240960245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86867762826260550987946993 65150822119695413240960245)
      ·
        refine ⟨6107889573721444991340023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65150822119695413240960245 6107889573721444991340023)
        ·
          refine ⟨9161834360582167487010035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6107889573721444991340023 9161834360582167487010035)
          ·
            refine ⟨13742751540873251230515053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9161834360582167487010035 13742751540873251230515053)
            ·
              refine ⟨5153531827827469211443145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13742751540873251230515053 5153531827827469211443145)
              ·
                refine ⟨3865148870870601908582359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5153531827827469211443145 3865148870870601908582359)
                ·
                  refine ⟨5797723306305902862873539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3865148870870601908582359 5797723306305902862873539)
                  ·
                    refine ⟨8696584959458854294310309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5797723306305902862873539 8696584959458854294310309)
                    ·
                      refine ⟨1630609679898535180183183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8696584959458854294310309 1630609679898535180183183)
                      ·
                        rfl

theorem cell23_3175601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_3175601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175601 prefixEnd_3175601 := by exact prefixLift 3175601
  have htrace : WordTrace (prefixWord ++ tailWord_3175601) baseStart_3175601 baseEnd_3175601 := by
    simpa [prefixWord, tailWord_3175601, baseEnd_3175601] using wordTrace_append hprefix tailTrace_3175601
  have hstable : (prefixWord ++ tailWord_3175601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175601).length < 2 ^ (prefixWord ++ tailWord_3175601).sum := by decide
  have hdescent : baseEnd_3175601 < baseStart_3175601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175614 : List Nat := [4, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4]
def baseStart_3175614 : Nat := 118140960795 + 3175614 * 2 ^ 59
def prefixEnd_3175614 : Nat := 4983230072969 + 3 ^ 40 * 3175614 * 2
def baseEnd_3175614 : Nat := 1630616355147043629320623

theorem tailTrace_3175614 : CollatzResearch.WordTrace tailWord_3175614 prefixEnd_3175614 1630616355147043629320623 := by
  unfold tailWord_3175614
  simp only [CollatzResearch.WordTrace]
  refine ⟨14478019739662538067185737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77216105278200203024990597 14478019739662538067185737)
  ·
    refine ⟨10858514804746903550389303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14478019739662538067185737 10858514804746903550389303)
    ·
      refine ⟨16287772207120355325583955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10858514804746903550389303 16287772207120355325583955)
      ·
        refine ⟨24431658310680532988375933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16287772207120355325583955 24431658310680532988375933)
        ·
          refine ⟨9161871866505199870640975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24431658310680532988375933 9161871866505199870640975)
          ·
            refine ⟨13742807799757799805961463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9161871866505199870640975 13742807799757799805961463)
            ·
              refine ⟨20614211699636699708942195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13742807799757799805961463 20614211699636699708942195)
              ·
                refine ⟨30921317549455049563413293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20614211699636699708942195 30921317549455049563413293)
                ·
                  refine ⟨11595494081045643586279985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30921317549455049563413293 11595494081045643586279985)
                  ·
                    refine ⟨8696620560784232689709989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11595494081045643586279985 8696620560784232689709989)
                    ·
                      refine ⟨1630616355147043629320623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8696620560784232689709989 1630616355147043629320623)
                      ·
                        rfl

theorem cell23_3175614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_3175614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175614 prefixEnd_3175614 := by exact prefixLift 3175614
  have htrace : WordTrace (prefixWord ++ tailWord_3175614) baseStart_3175614 baseEnd_3175614 := by
    simpa [prefixWord, tailWord_3175614, baseEnd_3175614] using wordTrace_append hprefix tailTrace_3175614
  have hstable : (prefixWord ++ tailWord_3175614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175614).length < 2 ^ (prefixWord ++ tailWord_3175614).sum := by decide
  have hdescent : baseEnd_3175614 < baseStart_3175614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175634 : List Nat := [3, 2, 2, 2, 1, 1, 1, 2, 3, 3, 3]
def baseStart_3175634 : Nat := 118140960795 + 3175634 * 2 ^ 59
def prefixEnd_3175634 : Nat := 4983230072969 + 3 ^ 40 * 3175634 * 2
def baseEnd_3175634 : Nat := 1630626624760133551070531

theorem tailTrace_3175634 : CollatzResearch.WordTrace tailWord_3175634 prefixEnd_3175634 1630626624760133551070531 := by
  unfold tailWord_3175634
  simp only [CollatzResearch.WordTrace]
  refine ⟨28956221844306961988303489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77216591584818565302142637 28956221844306961988303489)
  ·
    refine ⟨21717166383230221491227617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28956221844306961988303489 21717166383230221491227617)
    ·
      refine ⟨16287874787422666118420713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21717166383230221491227617 16287874787422666118420713)
      ·
        refine ⟨12215906090566999588815535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16287874787422666118420713 12215906090566999588815535)
        ·
          refine ⟨18323859135850499383223303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12215906090566999588815535 18323859135850499383223303)
          ·
            refine ⟨27485788703775749074834955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18323859135850499383223303 27485788703775749074834955)
            ·
              refine ⟨41228683055663623612252433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27485788703775749074834955 41228683055663623612252433)
              ·
                refine ⟨30921512291747717709189325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41228683055663623612252433 30921512291747717709189325)
                ·
                  refine ⟨11595567109405394140945997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30921512291747717709189325 11595567109405394140945997)
                  ·
                    refine ⟨4348337666027022802854749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11595567109405394140945997 4348337666027022802854749)
                    ·
                      refine ⟨1630626624760133551070531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4348337666027022802854749 1630626624760133551070531)
                      ·
                        rfl

theorem cell23_3175634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_3175634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175634 prefixEnd_3175634 := by exact prefixLift 3175634
  have htrace : WordTrace (prefixWord ++ tailWord_3175634) baseStart_3175634 baseEnd_3175634 := by
    simpa [prefixWord, tailWord_3175634, baseEnd_3175634] using wordTrace_append hprefix tailTrace_3175634
  have hstable : (prefixWord ++ tailWord_3175634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175634).length < 2 ^ (prefixWord ++ tailWord_3175634).sum := by decide
  have hdescent : baseEnd_3175634 < baseStart_3175634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175684 : List Nat := [2, 3, 2, 2, 2, 1, 1, 2, 2, 6]
def baseStart_3175684 : Nat := 118140960795 + 3175684 * 2 ^ 59
def prefixEnd_3175684 : Nat := 4983230072969 + 3 ^ 40 * 3175684 * 2
def baseEnd_3175684 : Nat := 543550766264286118481767

theorem tailTrace_3175684 : CollatzResearch.WordTrace tailWord_3175684 prefixEnd_3175684 543550766264286118481767 := by
  unfold tailWord_3175684
  simp only [CollatzResearch.WordTrace]
  refine ⟨57913355513523353246267053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77217807351364470995022737 57913355513523353246267053)
  ·
    refine ⟨21717508317571257467350145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57913355513523353246267053 21717508317571257467350145)
    ·
      refine ⟨16288131238178443100512609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21717508317571257467350145 16288131238178443100512609)
      ·
        refine ⟨12216098428633832325384457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16288131238178443100512609 12216098428633832325384457)
        ·
          refine ⟨9162073821475374244038343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12216098428633832325384457 9162073821475374244038343)
          ·
            refine ⟨13743110732213061366057515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9162073821475374244038343 13743110732213061366057515)
            ·
              refine ⟨20614666098319592049086273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13743110732213061366057515 20614666098319592049086273)
              ·
                refine ⟨15460999573739694036814705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20614666098319592049086273 15460999573739694036814705)
                ·
                  refine ⟨11595749680304770527611029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15460999573739694036814705 11595749680304770527611029)
                  ·
                    refine ⟨543550766264286118481767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11595749680304770527611029 543550766264286118481767)
                    ·
                      rfl

theorem cell23_3175684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_3175684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175684 prefixEnd_3175684 := by exact prefixLift 3175684
  have htrace : WordTrace (prefixWord ++ tailWord_3175684) baseStart_3175684 baseEnd_3175684 := by
    simpa [prefixWord, tailWord_3175684, baseEnd_3175684] using wordTrace_append hprefix tailTrace_3175684
  have hstable : (prefixWord ++ tailWord_3175684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175684).length < 2 ^ (prefixWord ++ tailWord_3175684).sum := by decide
  have hdescent : baseEnd_3175684 < baseStart_3175684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175704 : List Nat := [2, 1, 2, 3, 1, 3, 2, 1, 2, 2, 4]
def baseStart_3175704 : Nat := 118140960795 + 3175704 * 2 ^ 59
def prefixEnd_3175704 : Nat := 4983230072969 + 3 ^ 40 * 3175704 * 2
def baseEnd_3175704 : Nat := 1630662568405948277195209

theorem tailTrace_3175704 : CollatzResearch.WordTrace tailWord_3175704 prefixEnd_3175704 1630662568405948277195209 := by
  unfold tailWord_3175704
  simp only [CollatzResearch.WordTrace]
  refine ⟨57913720243487124954131083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77218293657982833272174777 57913720243487124954131083)
  ·
    refine ⟨86870580365230687431196625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57913720243487124954131083 86870580365230687431196625)
    ·
      refine ⟨65152935273923015573397469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86870580365230687431196625 65152935273923015573397469)
      ·
        refine ⟨24432350727721130840024051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65152935273923015573397469 24432350727721130840024051)
        ·
          refine ⟨36648526091581696260036077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24432350727721130840024051 36648526091581696260036077)
          ·
            refine ⟨13743197284343136097513529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36648526091581696260036077 13743197284343136097513529)
            ·
              refine ⟨10307397963257352073135147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13743197284343136097513529 10307397963257352073135147)
              ·
                refine ⟨15461096944886028109702721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10307397963257352073135147 15461096944886028109702721)
                ·
                  refine ⟨11595822708664521082277041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15461096944886028109702721 11595822708664521082277041)
                  ·
                    refine ⟨8696867031498390811707781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11595822708664521082277041 8696867031498390811707781)
                    ·
                      refine ⟨1630662568405948277195209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8696867031498390811707781 1630662568405948277195209)
                      ·
                        rfl

theorem cell23_3175704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_3175704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175704 prefixEnd_3175704 := by exact prefixLift 3175704
  have htrace : WordTrace (prefixWord ++ tailWord_3175704) baseStart_3175704 baseEnd_3175704 := by
    simpa [prefixWord, tailWord_3175704, baseEnd_3175704] using wordTrace_append hprefix tailTrace_3175704
  have hstable : (prefixWord ++ tailWord_3175704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175704).length < 2 ^ (prefixWord ++ tailWord_3175704).sum := by decide
  have hdescent : baseEnd_3175704 < baseStart_3175704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175708 : List Nat := [2, 2, 3, 1, 1, 1, 2, 5, 2, 2, 2]
def baseStart_3175708 : Nat := 118140960795 + 3175708 * 2 ^ 59
def prefixEnd_3175708 : Nat := 4983230072969 + 3 ^ 40 * 3175708 * 2
def baseEnd_3175708 : Nat := 1630664622328566261545191

theorem tailTrace_3175708 : CollatzResearch.WordTrace tailWord_3175708 prefixEnd_3175708 1630664622328566261545191 := by
  unfold tailWord_3175708
  simp only [CollatzResearch.WordTrace]
  refine ⟨57913793189479879295703889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77218390919306505727605185 57913793189479879295703889)
  ·
    refine ⟨43435344892109909471777917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57913793189479879295703889 43435344892109909471777917)
    ·
      refine ⟨16288254334541216051916719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43435344892109909471777917 16288254334541216051916719)
      ·
        refine ⟨24432381501811824077875079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16288254334541216051916719 24432381501811824077875079)
        ·
          refine ⟨36648572252717736116812619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24432381501811824077875079 36648572252717736116812619)
          ·
            refine ⟨54972858379076604175218929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36648572252717736116812619 54972858379076604175218929)
            ·
              refine ⟨41229643784307453131414197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54972858379076604175218929 41229643784307453131414197)
              ·
                refine ⟨3865279104778823731070081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41229643784307453131414197 3865279104778823731070081)
                ·
                  refine ⟨2898959328584117798302561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3865279104778823731070081 2898959328584117798302561)
                  ·
                    refine ⟨2174219496438088348726921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2898959328584117798302561 2174219496438088348726921)
                    ·
                      refine ⟨1630664622328566261545191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2174219496438088348726921 1630664622328566261545191)
                      ·
                        rfl

theorem cell23_3175708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_3175708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175708 prefixEnd_3175708 := by exact prefixLift 3175708
  have htrace : WordTrace (prefixWord ++ tailWord_3175708) baseStart_3175708 baseEnd_3175708 := by
    simpa [prefixWord, tailWord_3175708, baseEnd_3175708] using wordTrace_append hprefix tailTrace_3175708
  have hstable : (prefixWord ++ tailWord_3175708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175708).length < 2 ^ (prefixWord ++ tailWord_3175708).sum := by decide
  have hdescent : baseEnd_3175708 < baseStart_3175708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175725 : List Nat := [1, 5, 3, 1, 1, 1, 1, 2, 4, 2, 2]
def baseStart_3175725 : Nat := 118140960795 + 3175725 * 2 ^ 59
def prefixEnd_3175725 : Nat := 4983230072969 + 3 ^ 40 * 3175725 * 2
def baseEnd_3175725 : Nat := 1630673351499692695032613

theorem tailTrace_3175725 : CollatzResearch.WordTrace tailWord_3175725 prefixEnd_3175725 1630673351499692695032613 := by
  unfold tailWord_3175725
  simp only [CollatzResearch.WordTrace]
  refine ⟨115828206419898170494776629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77218804279932113663184419 115828206419898170494776629)
  ·
    refine ⟨10858894351865453483885309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115828206419898170494776629 10858894351865453483885309)
    ·
      refine ⟨4072085381949545056456991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10858894351865453483885309 4072085381949545056456991)
      ·
        refine ⟨6108128072924317584685487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4072085381949545056456991 6108128072924317584685487)
        ·
          refine ⟨9162192109386476377028231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6108128072924317584685487 9162192109386476377028231)
          ·
            refine ⟨13743288164079714565542347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9162192109386476377028231 13743288164079714565542347)
            ·
              refine ⟨20614932246119571848313521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13743288164079714565542347 20614932246119571848313521)
              ·
                refine ⟨15461199184589678886235141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20614932246119571848313521 15461199184589678886235141)
                ·
                  refine ⟨2898974847110564791169089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15461199184589678886235141 2898974847110564791169089)
                  ·
                    refine ⟨2174231135332923593376817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2898974847110564791169089 2174231135332923593376817)
                    ·
                      refine ⟨1630673351499692695032613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2174231135332923593376817 1630673351499692695032613)
                      ·
                        rfl

theorem cell23_3175725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_3175725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175725 prefixEnd_3175725 := by exact prefixLift 3175725
  have htrace : WordTrace (prefixWord ++ tailWord_3175725) baseStart_3175725 baseEnd_3175725 := by
    simpa [prefixWord, tailWord_3175725, baseEnd_3175725] using wordTrace_append hprefix tailTrace_3175725
  have hstable : (prefixWord ++ tailWord_3175725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175725).length < 2 ^ (prefixWord ++ tailWord_3175725).sum := by decide
  have hdescent : baseEnd_3175725 < baseStart_3175725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175731 : List Nat := [1, 1, 1, 2, 5, 2, 3, 3, 5]
def baseStart_3175731 : Nat := 118140960795 + 3175731 * 2 ^ 59
def prefixEnd_3175731 : Nat := 4983230072969 + 3 ^ 40 * 3175731 * 2
def baseEnd_3175731 : Nat := 181186270264846630173065

theorem tailTrace_3175731 : CollatzResearch.WordTrace tailWord_3175731 prefixEnd_3175731 181186270264846630173065 := by
  unfold tailWord_3175731
  simp only [CollatzResearch.WordTrace]
  refine ⟨115828425257876433519495047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77218950171917622346330031 115828425257876433519495047)
  ·
    refine ⟨173742637886814650279242571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115828425257876433519495047 173742637886814650279242571)
    ·
      refine ⟨260613956830221975418863857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173742637886814650279242571 260613956830221975418863857)
      ·
        refine ⟨195460467622666481564147893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260613956830221975418863857 195460467622666481564147893)
        ·
          refine ⟨18324418839624982646638865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 195460467622666481564147893 18324418839624982646638865)
          ·
            refine ⟨13743314129718736984979149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18324418839624982646638865 13743314129718736984979149)
            ·
              refine ⟨5153742798644526369367181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13743314129718736984979149 5153742798644526369367181)
              ·
                refine ⟨1932653549491697388512693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5153742798644526369367181 1932653549491697388512693)
                ·
                  refine ⟨181186270264846630173065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1932653549491697388512693 181186270264846630173065)
                  ·
                    rfl

theorem cell23_3175731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 3, 5].length) (baseStart_3175731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175731 prefixEnd_3175731 := by exact prefixLift 3175731
  have htrace : WordTrace (prefixWord ++ tailWord_3175731) baseStart_3175731 baseEnd_3175731 := by
    simpa [prefixWord, tailWord_3175731, baseEnd_3175731] using wordTrace_append hprefix tailTrace_3175731
  have hstable : (prefixWord ++ tailWord_3175731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175731).length < 2 ^ (prefixWord ++ tailWord_3175731).sum := by decide
  have hdescent : baseEnd_3175731 < baseStart_3175731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175744 : List Nat := [2, 1, 1, 2, 2, 1, 5, 2, 2, 5]
def baseStart_3175744 : Nat := 118140960795 + 3175744 * 2 ^ 59
def prefixEnd_3175744 : Nat := 4983230072969 + 3 ^ 40 * 3175744 * 2
def baseEnd_3175744 : Nat := 543561035877376040231675

theorem tailTrace_3175744 : CollatzResearch.WordTrace tailWord_3175744 prefixEnd_3175744 543561035877376040231675 := by
  unfold tailWord_3175744
  simp only [CollatzResearch.WordTrace]
  refine ⟨57914449703414668369859143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77219266271219557826478857 57914449703414668369859143)
  ·
    refine ⟨86871674555122002554788715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57914449703414668369859143 86871674555122002554788715)
    ·
      refine ⟨130307511832683003832183073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86871674555122002554788715 130307511832683003832183073)
      ·
        refine ⟨97730633874512252874137305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130307511832683003832183073 97730633874512252874137305)
        ·
          refine ⟨73297975405884189655602979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97730633874512252874137305 73297975405884189655602979)
          ·
            refine ⟨109946963108826284483404469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73297975405884189655602979 109946963108826284483404469)
            ·
              refine ⟨10307527791452464170319169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109946963108826284483404469 10307527791452464170319169)
              ·
                refine ⟨7730645843589348127739377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10307527791452464170319169 7730645843589348127739377)
                ·
                  refine ⟨5797984382692011095804533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7730645843589348127739377 5797984382692011095804533)
                  ·
                    refine ⟨543561035877376040231675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5797984382692011095804533 543561035877376040231675)
                    ·
                      rfl

theorem cell23_3175744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 2, 5].length) (baseStart_3175744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175744 prefixEnd_3175744 := by exact prefixLift 3175744
  have htrace : WordTrace (prefixWord ++ tailWord_3175744) baseStart_3175744 baseEnd_3175744 := by
    simpa [prefixWord, tailWord_3175744, baseEnd_3175744] using wordTrace_append hprefix tailTrace_3175744
  have hstable : (prefixWord ++ tailWord_3175744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175744).length < 2 ^ (prefixWord ++ tailWord_3175744).sum := by decide
  have hdescent : baseEnd_3175744 < baseStart_3175744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175748 : List Nat := [2, 3, 4, 1, 1, 3, 1, 1, 7]
def baseStart_3175748 : Nat := 118140960795 + 3175748 * 2 ^ 59
def prefixEnd_3175748 : Nat := 4983230072969 + 3 ^ 40 * 3175748 * 2
def baseEnd_3175748 : Nat := 181187240172749567227223

theorem tailTrace_3175748 : CollatzResearch.WordTrace tailWord_3175748 prefixEnd_3175748 181187240172749567227223 := by
  unfold tailWord_3175748
  simp only [CollatzResearch.WordTrace]
  refine ⟨57914522649407422711431949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77219363532543230281909265 57914522649407422711431949)
  ·
    refine ⟨21717945993527783516786981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57914522649407422711431949 21717945993527783516786981)
    ·
      refine ⟨4072114873786459409397559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21717945993527783516786981 4072114873786459409397559)
      ·
        refine ⟨6108172310679689114096339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4072114873786459409397559 6108172310679689114096339)
        ·
          refine ⟨9162258466019533671144509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6108172310679689114096339 9162258466019533671144509)
          ·
            refine ⟨3435846924757325126679191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9162258466019533671144509 3435846924757325126679191)
            ·
              refine ⟨5153770387135987690018787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3435846924757325126679191 5153770387135987690018787)
              ·
                refine ⟨7730655580703981535028181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5153770387135987690018787 7730655580703981535028181)
                ·
                  refine ⟨181187240172749567227223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7730655580703981535028181 181187240172749567227223)
                  ·
                    rfl

theorem cell23_3175748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 7].length) (baseStart_3175748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175748 prefixEnd_3175748 := by exact prefixLift 3175748
  have htrace : WordTrace (prefixWord ++ tailWord_3175748) baseStart_3175748 baseEnd_3175748 := by
    simpa [prefixWord, tailWord_3175748, baseEnd_3175748] using wordTrace_append hprefix tailTrace_3175748
  have hstable : (prefixWord ++ tailWord_3175748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175748).length < 2 ^ (prefixWord ++ tailWord_3175748).sum := by decide
  have hdescent : baseEnd_3175748 < baseStart_3175748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175781 : List Nat := [1, 3, 1, 3, 1, 2, 4, 1, 2, 1, 4]
def baseStart_3175781 : Nat := 118140960795 + 3175781 * 2 ^ 59
def prefixEnd_3175781 : Nat := 4983230072969 + 3 ^ 40 * 3175781 * 2
def baseEnd_3175781 : Nat := 1630702106416344475932355

theorem tailTrace_3175781 : CollatzResearch.WordTrace tailWord_3175781 prefixEnd_3175781 1630702106416344475932355 := by
  unfold tailWord_3175781
  simp only [CollatzResearch.WordTrace]
  refine ⟨115830248907695292058815197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77220165938463528039210131 115830248907695292058815197)
  ·
    refine ⟨43436343340385734522055699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115830248907695292058815197 43436343340385734522055699)
    ·
      refine ⟨65154515010578601783083549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43436343340385734522055699 65154515010578601783083549)
      ·
        refine ⟨24432943128966975668656331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65154515010578601783083549 24432943128966975668656331)
        ·
          refine ⟨36649414693450463502984497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24432943128966975668656331 36649414693450463502984497)
          ·
            refine ⟨27487061020087847627238373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36649414693450463502984497 27487061020087847627238373)
            ·
              refine ⟨5153823941266471430107195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27487061020087847627238373 5153823941266471430107195)
              ·
                refine ⟨7730735911899707145160793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5153823941266471430107195 7730735911899707145160793)
                ·
                  refine ⟨5798051933924780358870595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7730735911899707145160793 5798051933924780358870595)
                  ·
                    refine ⟨8697077900887170538305893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5798051933924780358870595 8697077900887170538305893)
                    ·
                      refine ⟨1630702106416344475932355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8697077900887170538305893 1630702106416344475932355)
                      ·
                        rfl

theorem cell23_3175781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_3175781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175781 prefixEnd_3175781 := by exact prefixLift 3175781
  have htrace : WordTrace (prefixWord ++ tailWord_3175781) baseStart_3175781 baseEnd_3175781 := by
    simpa [prefixWord, tailWord_3175781, baseEnd_3175781] using wordTrace_append hprefix tailTrace_3175781
  have hstable : (prefixWord ++ tailWord_3175781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175781).length < 2 ^ (prefixWord ++ tailWord_3175781).sum := by decide
  have hdescent : baseEnd_3175781 < baseStart_3175781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175794 : List Nat := [3, 2, 1, 2, 1, 2, 2, 1, 2, 1, 6]
def baseStart_3175794 : Nat := 118140960795 + 3175794 * 2 ^ 59
def prefixEnd_3175794 : Nat := 4983230072969 + 3 ^ 40 * 3175794 * 2
def baseEnd_3175794 : Nat := 1630708781664852925069795

theorem tailTrace_3175794 : CollatzResearch.WordTrace tailWord_3175794 prefixEnd_3175794 1630708781664852925069795 := by
  unfold tailWord_3175794
  simp only [CollatzResearch.WordTrace]
  refine ⟨28957680764162048819759609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77220482037765463519358957 28957680764162048819759609)
  ·
    refine ⟨21718260573121536614819707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28957680764162048819759609 21718260573121536614819707)
    ·
      refine ⟨32577390859682304922229561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21718260573121536614819707 32577390859682304922229561)
      ·
        refine ⟨24433043144761728691672171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32577390859682304922229561 24433043144761728691672171)
        ·
          refine ⟨36649564717142593037508257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24433043144761728691672171 36649564717142593037508257)
          ·
            refine ⟨27487173537856944778131193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36649564717142593037508257 27487173537856944778131193)
            ·
              refine ⟨20615380153392708583598395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27487173537856944778131193 20615380153392708583598395)
              ·
                refine ⟨30923070230089062875397593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20615380153392708583598395 30923070230089062875397593)
                ·
                  refine ⟨23192302672566797156548195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30923070230089062875397593 23192302672566797156548195)
                  ·
                    refine ⟨34788454008850195734822293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23192302672566797156548195 34788454008850195734822293)
                    ·
                      refine ⟨1630708781664852925069795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34788454008850195734822293 1630708781664852925069795)
                      ·
                        rfl

theorem cell23_3175794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_3175794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175794 prefixEnd_3175794 := by exact prefixLift 3175794
  have htrace : WordTrace (prefixWord ++ tailWord_3175794) baseStart_3175794 baseEnd_3175794 := by
    simpa [prefixWord, tailWord_3175794, baseEnd_3175794] using wordTrace_append hprefix tailTrace_3175794
  have hstable : (prefixWord ++ tailWord_3175794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175794).length < 2 ^ (prefixWord ++ tailWord_3175794).sum := by decide
  have hdescent : baseEnd_3175794 < baseStart_3175794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175801 : List Nat := [1, 2, 1, 3, 2, 1, 4, 2, 2, 2, 3]
def baseStart_3175801 : Nat := 118140960795 + 3175801 * 2 ^ 59
def prefixEnd_3175801 : Nat := 4983230072969 + 3 ^ 40 * 3175801 * 2
def baseEnd_3175801 : Nat := 1630712376029434397682263

theorem tailTrace_3175801 : CollatzResearch.WordTrace tailWord_3175801 prefixEnd_3175801 1630712376029434397682263 := by
  unfold tailWord_3175801
  simp only [CollatzResearch.WordTrace]
  refine ⟨115830978367622835474543257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77220652245081890316362171 115830978367622835474543257)
  ·
    refine ⟨86873233775717126605907443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115830978367622835474543257 86873233775717126605907443)
    ·
      refine ⟨130309850663575689908861165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86873233775717126605907443 130309850663575689908861165)
      ·
        refine ⟨48866193998840883715822937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130309850663575689908861165 48866193998840883715822937)
        ·
          refine ⟨36649645499130662786867203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48866193998840883715822937 36649645499130662786867203)
          ·
            refine ⟨54974468248695994180300805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36649645499130662786867203 54974468248695994180300805)
            ·
              refine ⟨10307712796630498908806401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54974468248695994180300805 10307712796630498908806401)
              ·
                refine ⟨7730784597472874181604801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10307712796630498908806401 7730784597472874181604801)
                ·
                  refine ⟨5798088448104655636203601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7730784597472874181604801 5798088448104655636203601)
                  ·
                    refine ⟨4348566336078491727152701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5798088448104655636203601 4348566336078491727152701)
                    ·
                      refine ⟨1630712376029434397682263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4348566336078491727152701 1630712376029434397682263)
                      ·
                        rfl

theorem cell23_3175801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 2, 3].length) (baseStart_3175801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175801 prefixEnd_3175801 := by exact prefixLift 3175801
  have htrace : WordTrace (prefixWord ++ tailWord_3175801) baseStart_3175801 baseEnd_3175801 := by
    simpa [prefixWord, tailWord_3175801, baseEnd_3175801] using wordTrace_append hprefix tailTrace_3175801
  have hstable : (prefixWord ++ tailWord_3175801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175801).length < 2 ^ (prefixWord ++ tailWord_3175801).sum := by decide
  have hdescent : baseEnd_3175801 < baseStart_3175801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175844 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 2, 4, 5]
def baseStart_3175844 : Nat := 118140960795 + 3175844 * 2 ^ 59
def prefixEnd_3175844 : Nat := 4983230072969 + 3 ^ 40 * 3175844 * 2
def baseEnd_3175844 : Nat := 1630734455697577729444565

theorem tailTrace_3175844 : CollatzResearch.WordTrace tailWord_3175844 prefixEnd_3175844 1630734455697577729444565 := by
  unfold tailWord_3175844
  simp only [CollatzResearch.WordTrace]
  refine ⟨57916273353233526909179293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77221697804311369212239057 57916273353233526909179293)
  ·
    refine ⟨21718602507462572590942235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57916273353233526909179293 21718602507462572590942235)
    ·
      refine ⟨32577903761193858886413353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21718602507462572590942235 32577903761193858886413353)
      ·
        refine ⟨24433427820895394164810015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32577903761193858886413353 24433427820895394164810015)
        ·
          refine ⟨36650141731343091247215023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24433427820895394164810015 36650141731343091247215023)
          ·
            refine ⟨54975212597014636870822535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36650141731343091247215023 54975212597014636870822535)
            ·
              refine ⟨82462818895521955306233803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54975212597014636870822535 82462818895521955306233803)
              ·
                refine ⟨123694228343282932959350705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82462818895521955306233803 123694228343282932959350705)
                ·
                  refine ⟨92770671257462199719513029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123694228343282932959350705 92770671257462199719513029)
                  ·
                    refine ⟨17394500860774162447408693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 92770671257462199719513029 17394500860774162447408693)
                    ·
                      refine ⟨1630734455697577729444565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17394500860774162447408693 1630734455697577729444565)
                      ·
                        rfl

theorem cell23_3175844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_3175844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175844 prefixEnd_3175844 := by exact prefixLift 3175844
  have htrace : WordTrace (prefixWord ++ tailWord_3175844) baseStart_3175844 baseEnd_3175844 := by
    simpa [prefixWord, tailWord_3175844, baseEnd_3175844] using wordTrace_append hprefix tailTrace_3175844
  have hstable : (prefixWord ++ tailWord_3175844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175844).length < 2 ^ (prefixWord ++ tailWord_3175844).sum := by decide
  have hdescent : baseEnd_3175844 < baseStart_3175844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175864 : List Nat := [2, 1, 2, 1, 2, 2, 2, 2, 3, 6]
def baseStart_3175864 : Nat := 118140960795 + 3175864 * 2 ^ 59
def prefixEnd_3175864 : Nat := 4983230072969 + 3 ^ 40 * 3175864 * 2
def baseEnd_3175864 : Nat := 543581575103555883731491

theorem tailTrace_3175864 : CollatzResearch.WordTrace tailWord_3175864 prefixEnd_3175864 543581575103555883731491 := by
  unfold tailWord_3175864
  simp only [CollatzResearch.WordTrace]
  refine ⟨57916638083197298617043323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77222184110929731489391097 57916638083197298617043323)
  ·
    refine ⟨86874957124795947925564985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57916638083197298617043323 86874957124795947925564985)
    ·
      refine ⟨65156217843596960944173739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86874957124795947925564985 65156217843596960944173739)
      ·
        refine ⟨97734326765395441416260609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65156217843596960944173739 97734326765395441416260609)
        ·
          refine ⟨73300745074046581062195457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97734326765395441416260609 73300745074046581062195457)
          ·
            refine ⟨54975558805534935796646593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73300745074046581062195457 54975558805534935796646593)
            ·
              refine ⟨41231669104151201847484945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54975558805534935796646593 41231669104151201847484945)
              ·
                refine ⟨30923751828113401385613709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41231669104151201847484945 30923751828113401385613709)
                ·
                  refine ⟨11596406935542525519605141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30923751828113401385613709 11596406935542525519605141)
                  ·
                    refine ⟨543581575103555883731491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11596406935542525519605141 543581575103555883731491)
                    ·
                      rfl

theorem cell23_3175864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 3, 6].length) (baseStart_3175864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175864 prefixEnd_3175864 := by exact prefixLift 3175864
  have htrace : WordTrace (prefixWord ++ tailWord_3175864) baseStart_3175864 baseEnd_3175864 := by
    simpa [prefixWord, tailWord_3175864, baseEnd_3175864] using wordTrace_append hprefix tailTrace_3175864
  have hstable : (prefixWord ++ tailWord_3175864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175864).length < 2 ^ (prefixWord ++ tailWord_3175864).sum := by decide
  have hdescent : baseEnd_3175864 < baseStart_3175864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175865 : List Nat := [1, 2, 1, 4, 4, 1, 2, 1, 3, 1, 3]
def baseStart_3175865 : Nat := 118140960795 + 3175865 * 2 ^ 59
def prefixEnd_3175865 : Nat := 4983230072969 + 3 ^ 40 * 3175865 * 2
def baseEnd_3175865 : Nat := 1630745238791322147281969

theorem tailTrace_3175865 : CollatzResearch.WordTrace tailWord_3175865 prefixEnd_3175865 1630745238791322147281969 := by
  unfold tailWord_3175865
  simp only [CollatzResearch.WordTrace]
  refine ⟨115833312639390974404873049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77222208426260649603248699 115833312639390974404873049)
  ·
    refine ⟨86874984479543230803654787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115833312639390974404873049 86874984479543230803654787)
    ·
      refine ⟨130312476719314846205482181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86874984479543230803654787 130312476719314846205482181)
      ·
        refine ⟨24433589384871533663527909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130312476719314846205482181 24433589384871533663527909)
        ·
          refine ⟨4581298009663412561911483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24433589384871533663527909 4581298009663412561911483)
          ·
            refine ⟨6871947014495118842867225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4581298009663412561911483 6871947014495118842867225)
            ·
              refine ⟨5153960260871339132150419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6871947014495118842867225 5153960260871339132150419)
              ·
                refine ⟨7730940391307008698225629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5153960260871339132150419 7730940391307008698225629)
                ·
                  refine ⟨2899102646740128261834611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7730940391307008698225629 2899102646740128261834611)
                  ·
                    refine ⟨4348653970110192392751917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2899102646740128261834611 4348653970110192392751917)
                    ·
                      refine ⟨1630745238791322147281969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4348653970110192392751917 1630745238791322147281969)
                      ·
                        rfl

theorem cell23_3175865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_3175865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175865 prefixEnd_3175865 := by exact prefixLift 3175865
  have htrace : WordTrace (prefixWord ++ tailWord_3175865) baseStart_3175865 baseEnd_3175865 := by
    simpa [prefixWord, tailWord_3175865, baseEnd_3175865] using wordTrace_append hprefix tailTrace_3175865
  have hstable : (prefixWord ++ tailWord_3175865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175865).length < 2 ^ (prefixWord ++ tailWord_3175865).sum := by decide
  have hdescent : baseEnd_3175865 < baseStart_3175865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175911 : List Nat := [1, 1, 5, 2, 1, 4, 9]
def baseStart_3175911 : Nat := 118140960795 + 3175911 * 2 ^ 59
def prefixEnd_3175911 : Nat := 4983230072969 + 3 ^ 40 * 3175911 * 2
def baseEnd_3175911 : Nat := 20132948875326283546997

theorem tailTrace_3175911 : CollatzResearch.WordTrace tailWord_3175911 prefixEnd_3175911 20132948875326283546997 := by
  unfold tailWord_3175911
  simp only [CollatzResearch.WordTrace]
  refine ⟨115834990397224324261047587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77223326931482882840698391 115834990397224324261047587)
  ·
    refine ⟨173752485595836486391571381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115834990397224324261047587 173752485595836486391571381)
    ·
      refine ⟨16289295524609670599209817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 173752485595836486391571381 16289295524609670599209817)
      ·
        refine ⟨12216971643457252949407363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16289295524609670599209817 12216971643457252949407363)
        ·
          refine ⟨18325457465185879424111045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12216971643457252949407363 18325457465185879424111045)
          ·
            refine ⟨3436023274722352392020821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18325457465185879424111045 3436023274722352392020821)
            ·
              refine ⟨20132948875326283546997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3436023274722352392020821 20132948875326283546997)
              ·
                rfl

theorem cell23_3175911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 9].length) (baseStart_3175911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175911 prefixEnd_3175911 := by exact prefixLift 3175911
  have htrace : WordTrace (prefixWord ++ tailWord_3175911) baseStart_3175911 baseEnd_3175911 := by
    simpa [prefixWord, tailWord_3175911, baseEnd_3175911] using wordTrace_append hprefix tailTrace_3175911
  have hstable : (prefixWord ++ tailWord_3175911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175911).length < 2 ^ (prefixWord ++ tailWord_3175911).sum := by decide
  have hdescent : baseEnd_3175911 < baseStart_3175911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175922 : List Nat := [3, 2, 1, 4, 1, 1, 3, 1, 3, 2, 2]
def baseStart_3175922 : Nat := 118140960795 + 3175922 * 2 ^ 59
def prefixEnd_3175922 : Nat := 4983230072969 + 3 ^ 40 * 3175922 * 2
def baseEnd_3175922 : Nat := 1630774507188628424269207

theorem tailTrace_3175922 : CollatzResearch.WordTrace tailWord_3175922 prefixEnd_3175922 1630774507188628424269207 := by
  unfold tailWord_3175922
  simp only [CollatzResearch.WordTrace]
  refine ⟨28958847900046118284924505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77223594400122982093132013 28958847900046118284924505)
  ·
    refine ⟨21719135925034588713693379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28958847900046118284924505 21719135925034588713693379)
    ·
      refine ⟨32578703887551883070540069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21719135925034588713693379 32578703887551883070540069)
      ·
        refine ⟨6108506978915978075726263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32578703887551883070540069 6108506978915978075726263)
        ·
          refine ⟨9162760468373967113589395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6108506978915978075726263 9162760468373967113589395)
          ·
            refine ⟨13744140702560950670384093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9162760468373967113589395 13744140702560950670384093)
            ·
              refine ⟨5154052763460356501394035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13744140702560950670384093 5154052763460356501394035)
              ·
                refine ⟨7731079145190534752091053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5154052763460356501394035 7731079145190534752091053)
                ·
                  refine ⟨2899154679446450532034145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7731079145190534752091053 2899154679446450532034145)
                  ·
                    refine ⟨2174366009584837899025609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2899154679446450532034145 2174366009584837899025609)
                    ·
                      refine ⟨1630774507188628424269207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2174366009584837899025609 1630774507188628424269207)
                      ·
                        rfl

theorem cell23_3175922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_3175922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175922 prefixEnd_3175922 := by exact prefixLift 3175922
  have htrace : WordTrace (prefixWord ++ tailWord_3175922) baseStart_3175922 baseEnd_3175922 := by
    simpa [prefixWord, tailWord_3175922, baseEnd_3175922] using wordTrace_append hprefix tailTrace_3175922
  have hstable : (prefixWord ++ tailWord_3175922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175922).length < 2 ^ (prefixWord ++ tailWord_3175922).sum := by decide
  have hdescent : baseEnd_3175922 < baseStart_3175922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175966 : List Nat := [4, 3, 3, 1, 1, 1, 2, 2, 2, 4]
def baseStart_3175966 : Nat := 118140960795 + 3175966 * 2 ^ 59
def prefixEnd_3175966 : Nat := 4983230072969 + 3 ^ 40 * 3175966 * 2
def baseEnd_3175966 : Nat := 543599033445808750706335

theorem tailTrace_3175966 : CollatzResearch.WordTrace tailWord_3175966 prefixEnd_3175966 543599033445808750706335 := by
  unfold tailWord_3175966
  simp only [CollatzResearch.WordTrace]
  refine ⟨14479624551503133581787469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77224664274683379102866501 14479624551503133581787469)
  ·
    refine ⟨5429859206813675093170301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14479624551503133581787469 5429859206813675093170301)
    ·
      refine ⟨2036197202555128159938863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5429859206813675093170301 2036197202555128159938863)
      ·
        refine ⟨3054295803832692239908295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2036197202555128159938863 3054295803832692239908295)
        ·
          refine ⟨4581443705749038359862443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3054295803832692239908295 4581443705749038359862443)
          ·
            refine ⟨6872165558623557539793665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4581443705749038359862443 6872165558623557539793665)
            ·
              refine ⟨5154124168967668154845249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6872165558623557539793665 5154124168967668154845249)
              ·
                refine ⟨3865593126725751116133937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5154124168967668154845249 3865593126725751116133937)
                ·
                  refine ⟨2899194845044313337100453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3865593126725751116133937 2899194845044313337100453)
                  ·
                    refine ⟨543599033445808750706335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2899194845044313337100453 543599033445808750706335)
                    ·
                      rfl

theorem cell23_3175966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_3175966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175966 prefixEnd_3175966 := by exact prefixLift 3175966
  have htrace : WordTrace (prefixWord ++ tailWord_3175966) baseStart_3175966 baseEnd_3175966 := by
    simpa [prefixWord, tailWord_3175966, baseEnd_3175966] using wordTrace_append hprefix tailTrace_3175966
  have hstable : (prefixWord ++ tailWord_3175966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175966).length < 2 ^ (prefixWord ++ tailWord_3175966).sum := by decide
  have hdescent : baseEnd_3175966 < baseStart_3175966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3175991 : List Nat := [1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 4]
def baseStart_3175991 : Nat := 118140960795 + 3175991 * 2 ^ 59
def prefixEnd_3175991 : Nat := 4983230072969 + 3 ^ 40 * 3175991 * 2
def baseEnd_3175991 : Nat := 1630809937353788654306389

theorem tailTrace_3175991 : CollatzResearch.WordTrace tailWord_3175991 prefixEnd_3175991 1630809937353788654306389 := by
  unfold tailWord_3175991
  simp only [CollatzResearch.WordTrace]
  refine ⟨115837908236934497923959827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77225272157956331949306551 115837908236934497923959827)
  ·
    refine ⟨173756862355401746885939741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115837908236934497923959827 173756862355401746885939741)
    ·
      refine ⟨65158823383275655082227403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173756862355401746885939741 65158823383275655082227403)
      ·
        refine ⟨97738235074913482623341105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65158823383275655082227403 97738235074913482623341105)
        ·
          refine ⟨73303676306185111967505829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97738235074913482623341105 73303676306185111967505829)
          ·
            refine ⟨13744439307409708493907343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73303676306185111967505829 13744439307409708493907343)
            ·
              refine ⟨20616658961114562740861015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13744439307409708493907343 20616658961114562740861015)
              ·
                refine ⟨30924988441671844111291523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20616658961114562740861015 30924988441671844111291523)
                ·
                  refine ⟨46387482662507766166937285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30924988441671844111291523 46387482662507766166937285)
                  ·
                    refine ⟨8697652999220206156300741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46387482662507766166937285 8697652999220206156300741)
                    ·
                      refine ⟨1630809937353788654306389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8697652999220206156300741 1630809937353788654306389)
                      ·
                        rfl

theorem cell23_3175991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 4].length) (baseStart_3175991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3175991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3175991 prefixEnd_3175991 := by exact prefixLift 3175991
  have htrace : WordTrace (prefixWord ++ tailWord_3175991) baseStart_3175991 baseEnd_3175991 := by
    simpa [prefixWord, tailWord_3175991, baseEnd_3175991] using wordTrace_append hprefix tailTrace_3175991
  have hstable : (prefixWord ++ tailWord_3175991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3175991).length < 2 ^ (prefixWord ++ tailWord_3175991).sum := by decide
  have hdescent : baseEnd_3175991 < baseStart_3175991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3175991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176011 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 3, 5, 3]
def baseStart_3176011 : Nat := 118140960795 + 3176011 * 2 ^ 59
def prefixEnd_3176011 : Nat := 4983230072969 + 3 ^ 40 * 3176011 * 2
def baseEnd_3176011 : Nat := 1630820206966878576056297

theorem tailTrace_3176011 : CollatzResearch.WordTrace tailWord_3176011 prefixEnd_3176011 1630820206966878576056297 := by
  unfold tailWord_3176011
  simp only [CollatzResearch.WordTrace]
  refine ⟨115838637696862041339687887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77225758464574694226458591 115838637696862041339687887)
  ·
    refine ⟨173757956545293062009531831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115838637696862041339687887 173757956545293062009531831)
    ·
      refine ⟨260636934817939593014297747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173757956545293062009531831 260636934817939593014297747)
      ·
        refine ⟨390955402226909389521446621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260636934817939593014297747 390955402226909389521446621)
        ·
          refine ⟨146608275835091021070542483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 390955402226909389521446621 146608275835091021070542483)
          ·
            refine ⟨219912413752636531605813725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146608275835091021070542483 219912413752636531605813725)
            ·
              refine ⟨82467155157238699352180147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 219912413752636531605813725 82467155157238699352180147)
              ·
                refine ⟨123700732735858049028270221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82467155157238699352180147 123700732735858049028270221)
                ·
                  refine ⟨46387774775946768385601333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123700732735858049028270221 46387774775946768385601333)
                  ·
                    refine ⟨4348853885245009536150125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46387774775946768385601333 4348853885245009536150125)
                    ·
                      refine ⟨1630820206966878576056297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4348853885245009536150125 1630820206966878576056297)
                      ·
                        rfl

theorem cell23_3176011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 5, 3].length) (baseStart_3176011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176011 prefixEnd_3176011 := by exact prefixLift 3176011
  have htrace : WordTrace (prefixWord ++ tailWord_3176011) baseStart_3176011 baseEnd_3176011 := by
    simpa [prefixWord, tailWord_3176011, baseEnd_3176011] using wordTrace_append hprefix tailTrace_3176011
  have hstable : (prefixWord ++ tailWord_3176011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176011).length < 2 ^ (prefixWord ++ tailWord_3176011).sum := by decide
  have hdescent : baseEnd_3176011 < baseStart_3176011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176041 : List Nat := [1, 2, 1, 1, 1, 4, 2, 3, 1, 2, 5]
def baseStart_3176041 : Nat := 118140960795 + 3176041 * 2 ^ 59
def prefixEnd_3176041 : Nat := 4983230072969 + 3 ^ 40 * 3176041 * 2
def baseEnd_3176041 : Nat := 1630835611386513458681159

theorem tailTrace_3176041 : CollatzResearch.WordTrace tailWord_3176041 prefixEnd_3176041 1630835611386513458681159 := by
  unfold tailWord_3176041
  simp only [CollatzResearch.WordTrace]
  refine ⟨115839731886753356463279977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77226487924502237642186651 115839731886753356463279977)
  ·
    refine ⟨86879798915065017347459983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115839731886753356463279977 86879798915065017347459983)
    ·
      refine ⟨130319698372597526021189975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86879798915065017347459983 130319698372597526021189975)
      ·
        refine ⟨195479547558896289031784963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130319698372597526021189975 195479547558896289031784963)
        ·
          refine ⟨293219321338344433547677445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195479547558896289031784963 293219321338344433547677445)
          ·
            refine ⟨54978622750939581290189521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 293219321338344433547677445 54978622750939581290189521)
            ·
              refine ⟨41233967063204685967642141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54978622750939581290189521 41233967063204685967642141)
              ·
                refine ⟨15462737648701757237865803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41233967063204685967642141 15462737648701757237865803)
                ·
                  refine ⟨23194106473052635856798705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15462737648701757237865803 23194106473052635856798705)
                  ·
                    refine ⟨17395579854789476892599029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23194106473052635856798705 17395579854789476892599029)
                    ·
                      refine ⟨1630835611386513458681159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17395579854789476892599029 1630835611386513458681159)
                      ·
                        rfl

theorem cell23_3176041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 2, 5].length) (baseStart_3176041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176041 prefixEnd_3176041 := by exact prefixLift 3176041
  have htrace : WordTrace (prefixWord ++ tailWord_3176041) baseStart_3176041 baseEnd_3176041 := by
    simpa [prefixWord, tailWord_3176041, baseEnd_3176041] using wordTrace_append hprefix tailTrace_3176041
  have hstable : (prefixWord ++ tailWord_3176041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176041).length < 2 ^ (prefixWord ++ tailWord_3176041).sum := by decide
  have hdescent : baseEnd_3176041 < baseStart_3176041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176046 : List Nat := [4, 1, 2, 2, 3, 1, 3, 1, 2, 2, 2]
def baseStart_3176046 : Nat := 118140960795 + 3176046 * 2 ^ 59
def prefixEnd_3176046 : Nat := 4983230072969 + 3 ^ 40 * 3176046 * 2
def baseEnd_3176046 : Nat := 1630838178789785939118637

theorem tailTrace_3176046 : CollatzResearch.WordTrace tailWord_3176046 prefixEnd_3176046 1630838178789785939118637 := by
  unfold tailWord_3176046
  simp only [CollatzResearch.WordTrace]
  refine ⟨14479989281466905289651499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77226609501156828211474661 14479989281466905289651499)
  ·
    refine ⟨21719983922200357934477249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14479989281466905289651499 21719983922200357934477249)
    ·
      refine ⟨16289987941650268450857937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21719983922200357934477249 16289987941650268450857937)
      ·
        refine ⟨12217490956237701338143453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16289987941650268450857937 12217490956237701338143453)
        ·
          refine ⟨4581559108589138001803795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12217490956237701338143453 4581559108589138001803795)
          ·
            refine ⟨6872338662883707002705693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4581559108589138001803795 6872338662883707002705693)
            ·
              refine ⟨2577126998581390126014635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6872338662883707002705693 2577126998581390126014635)
              ·
                refine ⟨3865690497872085189021953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2577126998581390126014635 3865690497872085189021953)
                ·
                  refine ⟨2899267873404063891766465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3865690497872085189021953 2899267873404063891766465)
                  ·
                    refine ⟨2174450905053047918824849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2899267873404063891766465 2174450905053047918824849)
                    ·
                      refine ⟨1630838178789785939118637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2174450905053047918824849 1630838178789785939118637)
                      ·
                        rfl

theorem cell23_3176046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_3176046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176046 prefixEnd_3176046 := by exact prefixLift 3176046
  have htrace : WordTrace (prefixWord ++ tailWord_3176046) baseStart_3176046 baseEnd_3176046 := by
    simpa [prefixWord, tailWord_3176046, baseEnd_3176046] using wordTrace_append hprefix tailTrace_3176046
  have hstable : (prefixWord ++ tailWord_3176046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176046).length < 2 ^ (prefixWord ++ tailWord_3176046).sum := by decide
  have hdescent : baseEnd_3176046 < baseStart_3176046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176081 : List Nat := [1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 6]
def baseStart_3176081 : Nat := 118140960795 + 3176081 * 2 ^ 59
def prefixEnd_3176081 : Nat := 4983230072969 + 3 ^ 40 * 3176081 * 2
def baseEnd_3176081 : Nat := 1630856150612693302180975

theorem tailTrace_3176081 : CollatzResearch.WordTrace tailWord_3176081 prefixEnd_3176081 1630856150612693302180975 := by
  unfold tailWord_3176081
  simp only [CollatzResearch.WordTrace]
  refine ⟨115841190806608443294736097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77227460537738962196490731 115841190806608443294736097)
  ·
    refine ⟨86880893104956332471052073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115841190806608443294736097 86880893104956332471052073)
    ·
      refine ⟨65160669828717249353289055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86880893104956332471052073 65160669828717249353289055)
      ·
        refine ⟨97741004743075874029933583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65160669828717249353289055 97741004743075874029933583)
        ·
          refine ⟨146611507114613811044900375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97741004743075874029933583 146611507114613811044900375)
          ·
            refine ⟨219917260671920716567350563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146611507114613811044900375 219917260671920716567350563)
            ·
              refine ⟨329875891007881074851025845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219917260671920716567350563 329875891007881074851025845)
              ·
                refine ⟨30925864781988850767283673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 329875891007881074851025845 30925864781988850767283673)
                ·
                  refine ⟨23194398586491638075462755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30925864781988850767283673 23194398586491638075462755)
                  ·
                    refine ⟨34791597879737457113194133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23194398586491638075462755 34791597879737457113194133)
                    ·
                      refine ⟨1630856150612693302180975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34791597879737457113194133 1630856150612693302180975)
                      ·
                        rfl

theorem cell23_3176081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_3176081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176081 prefixEnd_3176081 := by exact prefixLift 3176081
  have htrace : WordTrace (prefixWord ++ tailWord_3176081) baseStart_3176081 baseEnd_3176081 := by
    simpa [prefixWord, tailWord_3176081, baseEnd_3176081] using wordTrace_append hprefix tailTrace_3176081
  have hstable : (prefixWord ++ tailWord_3176081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176081).length < 2 ^ (prefixWord ++ tailWord_3176081).sum := by decide
  have hdescent : baseEnd_3176081 < baseStart_3176081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176131 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 7]
def baseStart_3176131 : Nat := 118140960795 + 3176131 * 2 ^ 59
def prefixEnd_3176131 : Nat := 4983230072969 + 3 ^ 40 * 3176131 * 2
def baseEnd_3176131 : Nat := 1630881824645418106555745

theorem tailTrace_3176131 : CollatzResearch.WordTrace tailWord_3176131 prefixEnd_3176131 1630881824645418106555745 := by
  unfold tailWord_3176131
  simp only [CollatzResearch.WordTrace]
  refine ⟨115843014456427301834056247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77228676304284867889370831 115843014456427301834056247)
  ·
    refine ⟨173764521684640952751084371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115843014456427301834056247 173764521684640952751084371)
    ·
      refine ⟨260646782526961429126626557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173764521684640952751084371 260646782526961429126626557)
      ·
        refine ⟨97742543447610535922484959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260646782526961429126626557 97742543447610535922484959)
        ·
          refine ⟨146613815171415803883727439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97742543447610535922484959 146613815171415803883727439)
          ·
            refine ⟨219920722757123705825591159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146613815171415803883727439 219920722757123705825591159)
            ·
              refine ⟨329881084135685558738386739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219920722757123705825591159 329881084135685558738386739)
              ·
                refine ⟨494821626203528338107580109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 329881084135685558738386739 494821626203528338107580109)
                ·
                  refine ⟨185558109826323126790342541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 494821626203528338107580109 185558109826323126790342541)
                  ·
                    refine ⟨69584291184871172546378453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 185558109826323126790342541 69584291184871172546378453)
                    ·
                      refine ⟨1630881824645418106555745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 69584291184871172546378453 1630881824645418106555745)
                      ·
                        rfl

theorem cell23_3176131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_3176131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176131 prefixEnd_3176131 := by exact prefixLift 3176131
  have htrace : WordTrace (prefixWord ++ tailWord_3176131) baseStart_3176131 baseEnd_3176131 := by
    simpa [prefixWord, tailWord_3176131, baseEnd_3176131] using wordTrace_append hprefix tailTrace_3176131
  have hstable : (prefixWord ++ tailWord_3176131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176131).length < 2 ^ (prefixWord ++ tailWord_3176131).sum := by decide
  have hdescent : baseEnd_3176131 < baseStart_3176131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176146 : List Nat := [3, 2, 2, 2, 2, 3, 2, 2, 1, 4]
def baseStart_3176146 : Nat := 118140960795 + 3176146 * 2 ^ 59
def prefixEnd_3176146 : Nat := 4983230072969 + 3 ^ 40 * 3176146 * 2
def baseEnd_3176146 : Nat := 543629842285078515956059

theorem tailTrace_3176146 : CollatzResearch.WordTrace tailWord_3176146 prefixEnd_3176146 543629842285078515956059 := by
  unfold tailWord_3176146
  simp only [CollatzResearch.WordTrace]
  refine ⟨28960890387843239848963073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77229041034248639597234861 28960890387843239848963073)
  ·
    refine ⟨21720667790882429886722305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28960890387843239848963073 21720667790882429886722305)
    ·
      refine ⟨16290500843161822415041729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21720667790882429886722305 16290500843161822415041729)
      ·
        refine ⟨12217875632371366811281297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16290500843161822415041729 12217875632371366811281297)
        ·
          refine ⟨9163406724278525108460973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12217875632371366811281297 9163406724278525108460973)
          ·
            refine ⟨3436277521604446915672865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9163406724278525108460973 3436277521604446915672865)
            ·
              refine ⟨2577208141203335186754649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3436277521604446915672865 2577208141203335186754649)
              ·
                refine ⟨1932906105902501390065987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2577208141203335186754649 1932906105902501390065987)
                ·
                  refine ⟨2899359158853752085098981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1932906105902501390065987 2899359158853752085098981)
                  ·
                    refine ⟨543629842285078515956059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2899359158853752085098981 543629842285078515956059)
                    ·
                      rfl

theorem cell23_3176146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_3176146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176146 prefixEnd_3176146 := by exact prefixLift 3176146
  have htrace : WordTrace (prefixWord ++ tailWord_3176146) baseStart_3176146 baseEnd_3176146 := by
    simpa [prefixWord, tailWord_3176146, baseEnd_3176146] using wordTrace_append hprefix tailTrace_3176146
  have hstable : (prefixWord ++ tailWord_3176146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176146).length < 2 ^ (prefixWord ++ tailWord_3176146).sum := by decide
  have hdescent : baseEnd_3176146 < baseStart_3176146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176175 : List Nat := [1, 1, 2, 1, 5, 1, 2, 4, 1, 1, 4]
def baseStart_3176175 : Nat := 118140960795 + 3176175 * 2 ^ 59
def prefixEnd_3176175 : Nat := 4983230072969 + 3 ^ 40 * 3176175 * 2
def baseEnd_3176175 : Nat := 1630904417794215934405543

theorem tailTrace_3176175 : CollatzResearch.WordTrace tailWord_3176175 prefixEnd_3176175 1630904417794215934405543 := by
  unfold tailWord_3176175
  simp only [CollatzResearch.WordTrace]
  refine ⟨115844619268267897348657979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77229746178845264899105319 115844619268267897348657979)
  ·
    refine ⟨173766928902401846022986969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115844619268267897348657979 173766928902401846022986969)
    ·
      refine ⟨130325196676801384517240227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173766928902401846022986969 130325196676801384517240227)
      ·
        refine ⟨195487795015202076775860341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130325196676801384517240227 195487795015202076775860341)
        ·
          refine ⟨18326980782675194697736907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 195487795015202076775860341 18326980782675194697736907)
          ·
            refine ⟨27490471174012792046605361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18326980782675194697736907 27490471174012792046605361)
            ·
              refine ⟨20617853380509594034954021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27490471174012792046605361 20617853380509594034954021)
              ·
                refine ⟨3865847508845548881553879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20617853380509594034954021 3865847508845548881553879)
                ·
                  refine ⟨5798771263268323322330819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3865847508845548881553879 5798771263268323322330819)
                  ·
                    refine ⟨8698156894902484983496229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5798771263268323322330819 8698156894902484983496229)
                    ·
                      refine ⟨1630904417794215934405543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8698156894902484983496229 1630904417794215934405543)
                      ·
                        rfl

theorem cell23_3176175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 1, 4].length) (baseStart_3176175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176175 prefixEnd_3176175 := by exact prefixLift 3176175
  have htrace : WordTrace (prefixWord ++ tailWord_3176175) baseStart_3176175 baseEnd_3176175 := by
    simpa [prefixWord, tailWord_3176175, baseEnd_3176175] using wordTrace_append hprefix tailTrace_3176175
  have hstable : (prefixWord ++ tailWord_3176175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176175).length < 2 ^ (prefixWord ++ tailWord_3176175).sum := by decide
  have hdescent : baseEnd_3176175 < baseStart_3176175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176202 : List Nat := [3, 1, 2, 2, 1, 3, 3, 2, 2, 4]
def baseStart_3176202 : Nat := 118140960795 + 3176202 * 2 ^ 59
def prefixEnd_3176202 : Nat := 4983230072969 + 3 ^ 40 * 3176202 * 2
def baseEnd_3176202 : Nat := 543639427257295776255973

theorem tailTrace_3176202 : CollatzResearch.WordTrace tailWord_3176202 prefixEnd_3176202 543639427257295776255973 := by
  unfold tailWord_3176202
  simp only [CollatzResearch.WordTrace]
  refine ⟨28961401009792520239972715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77230402692780053973260573 28961401009792520239972715)
  ·
    refine ⟨43442101514688780359959073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28961401009792520239972715 43442101514688780359959073)
    ·
      refine ⟨32581576136016585269969305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43442101514688780359959073 32581576136016585269969305)
      ·
        refine ⟨24436182102012438952476979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32581576136016585269969305 24436182102012438952476979)
        ·
          refine ⟨36654273153018658428715469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24436182102012438952476979 36654273153018658428715469)
          ·
            refine ⟨13745352432381996910768301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36654273153018658428715469 13745352432381996910768301)
            ·
              refine ⟨5154507162143248841538113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13745352432381996910768301 5154507162143248841538113)
              ·
                refine ⟨3865880371607436631153585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5154507162143248841538113 3865880371607436631153585)
                ·
                  refine ⟨2899410278705577473365189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3865880371607436631153585 2899410278705577473365189)
                  ·
                    refine ⟨543639427257295776255973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2899410278705577473365189 543639427257295776255973)
                    ·
                      rfl

theorem cell23_3176202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 2, 4].length) (baseStart_3176202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176202 prefixEnd_3176202 := by exact prefixLift 3176202
  have htrace : WordTrace (prefixWord ++ tailWord_3176202) baseStart_3176202 baseEnd_3176202 := by
    simpa [prefixWord, tailWord_3176202, baseEnd_3176202] using wordTrace_append hprefix tailTrace_3176202
  have hstable : (prefixWord ++ tailWord_3176202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176202).length < 2 ^ (prefixWord ++ tailWord_3176202).sum := by decide
  have hdescent : baseEnd_3176202 < baseStart_3176202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176232 : List Nat := [2, 1, 5, 1, 1, 4, 2, 7]
def baseStart_3176232 : Nat := 118140960795 + 3176232 * 2 ^ 59
def prefixEnd_3176232 : Nat := 4983230072969 + 3 ^ 40 * 3176232 * 2
def baseEnd_3176232 : Nat := 60404951340426748570103

theorem tailTrace_3176232 : CollatzResearch.WordTrace tailWord_3176232 prefixEnd_3176232 60404951340426748570103 := by
  unfold tailWord_3176232
  simp only [CollatzResearch.WordTrace]
  refine ⟨57923349114530698041741475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77231132152707597388988633 57923349114530698041741475)
  ·
    refine ⟨86885023671796047062612213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57923349114530698041741475 86885023671796047062612213)
    ·
      refine ⟨8145470969230879412119895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86885023671796047062612213 8145470969230879412119895)
      ·
        refine ⟨12218206453846319118179843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8145470969230879412119895 12218206453846319118179843)
        ·
          refine ⟨18327309680769478677269765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12218206453846319118179843 18327309680769478677269765)
          ·
            refine ⟨3436370565144277251988081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18327309680769478677269765 3436370565144277251988081)
            ·
              refine ⟨2577277923858207938991061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3436370565144277251988081 2577277923858207938991061)
              ·
                refine ⟨60404951340426748570103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2577277923858207938991061 60404951340426748570103)
                ·
                  rfl

theorem cell23_3176232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 7].length) (baseStart_3176232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176232 prefixEnd_3176232 := by exact prefixLift 3176232
  have htrace : WordTrace (prefixWord ++ tailWord_3176232) baseStart_3176232 baseEnd_3176232 := by
    simpa [prefixWord, tailWord_3176232, baseEnd_3176232] using wordTrace_append hprefix tailTrace_3176232
  have hstable : (prefixWord ++ tailWord_3176232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176232).length < 2 ^ (prefixWord ++ tailWord_3176232).sum := by decide
  have hdescent : baseEnd_3176232 < baseStart_3176232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176242 : List Nat := [3, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3]
def baseStart_3176242 : Nat := 118140960795 + 3176242 * 2 ^ 59
def prefixEnd_3176242 : Nat := 4983230072969 + 3 ^ 40 * 3176242 * 2
def baseEnd_3176242 : Nat := 1630938820998067172267735

theorem tailTrace_3176242 : CollatzResearch.WordTrace tailWord_3176242 prefixEnd_3176242 1630938820998067172267735 := by
  unfold tailWord_3176242
  simp only [CollatzResearch.WordTrace]
  refine ⟨28961765739756291947836745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77231375306016778527564653 28961765739756291947836745)
  ·
    refine ⟨21721324304817218960877559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28961765739756291947836745 21721324304817218960877559)
    ·
      refine ⟨32581986457225828441316339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21721324304817218960877559 32581986457225828441316339)
      ·
        refine ⟨48872979685838742661974509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32581986457225828441316339 48872979685838742661974509)
        ·
          refine ⟨18327367382189528498240441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48872979685838742661974509 18327367382189528498240441)
          ·
            refine ⟨13745525536642146373680331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18327367382189528498240441 13745525536642146373680331)
            ·
              refine ⟨20618288304963219560520497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13745525536642146373680331 20618288304963219560520497)
              ·
                refine ⟨15463716228722414670390373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20618288304963219560520497 15463716228722414670390373)
                ·
                  refine ⟨2899446792885452750698195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15463716228722414670390373 2899446792885452750698195)
                  ·
                    refine ⟨4349170189328179126047293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2899446792885452750698195 4349170189328179126047293)
                    ·
                      refine ⟨1630938820998067172267735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4349170189328179126047293 1630938820998067172267735)
                      ·
                        rfl

theorem cell23_3176242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3].length) (baseStart_3176242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176242 prefixEnd_3176242 := by exact prefixLift 3176242
  have htrace : WordTrace (prefixWord ++ tailWord_3176242) baseStart_3176242 baseEnd_3176242 := by
    simpa [prefixWord, tailWord_3176242, baseEnd_3176242] using wordTrace_append hprefix tailTrace_3176242
  have hstable : (prefixWord ++ tailWord_3176242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176242).length < 2 ^ (prefixWord ++ tailWord_3176242).sum := by decide
  have hdescent : baseEnd_3176242 < baseStart_3176242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176243 : List Nat := [1, 1, 1, 2, 7, 2, 1, 3, 1, 2, 2]
def baseStart_3176243 : Nat := 118140960795 + 3176243 * 2 ^ 59
def prefixEnd_3176243 : Nat := 4983230072969 + 3 ^ 40 * 3176243 * 2
def baseEnd_3176243 : Nat := 1630939334478721668355231

theorem tailTrace_3176243 : CollatzResearch.WordTrace tailWord_3176243 prefixEnd_3176243 1630939334478721668355231 := by
  unfold tailWord_3176243
  simp only [CollatzResearch.WordTrace]
  refine ⟨115847099432021544962133383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77231399621347696641422255 115847099432021544962133383)
  ·
    refine ⟨173770649148032317443200075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115847099432021544962133383 173770649148032317443200075)
    ·
      refine ⟨260655973722048476164800113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173770649148032317443200075 260655973722048476164800113)
      ·
        refine ⟨195491980291536357123600085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260655973722048476164800113 195491980291536357123600085)
        ·
          refine ⟨4581843288082883370084377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 195491980291536357123600085 4581843288082883370084377)
          ·
            refine ⟨3436382466062162527563283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4581843288082883370084377 3436382466062162527563283)
            ·
              refine ⟨5154573699093243791344925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3436382466062162527563283 5154573699093243791344925)
              ·
                refine ⟨1932965137159966421754347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5154573699093243791344925 1932965137159966421754347)
                ·
                  refine ⟨2899447705739949632631521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1932965137159966421754347 2899447705739949632631521)
                  ·
                    refine ⟨2174585779304962224473641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2899447705739949632631521 2174585779304962224473641)
                    ·
                      refine ⟨1630939334478721668355231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2174585779304962224473641 1630939334478721668355231)
                      ·
                        rfl

theorem cell23_3176243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 3, 1, 2, 2].length) (baseStart_3176243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176243 prefixEnd_3176243 := by exact prefixLift 3176243
  have htrace : WordTrace (prefixWord ++ tailWord_3176243) baseStart_3176243 baseEnd_3176243 := by
    simpa [prefixWord, tailWord_3176243, baseEnd_3176243] using wordTrace_append hprefix tailTrace_3176243
  have hstable : (prefixWord ++ tailWord_3176243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176243).length < 2 ^ (prefixWord ++ tailWord_3176243).sum := by decide
  have hdescent : baseEnd_3176243 < baseStart_3176243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176276 : List Nat := [2, 4, 1, 1, 3, 1, 4, 1, 2, 1, 3]
def baseStart_3176276 : Nat := 118140960795 + 3176276 * 2 ^ 59
def prefixEnd_3176276 : Nat := 4983230072969 + 3 ^ 40 * 3176276 * 2
def baseEnd_3176276 : Nat := 1630956279340320039242579

theorem tailTrace_3176276 : CollatzResearch.WordTrace tailWord_3176276 prefixEnd_3176276 1630956279340320039242579 := by
  unfold tailWord_3176276
  simp only [CollatzResearch.WordTrace]
  refine ⟨57924151520450995799042341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77232202027267994398723121 57924151520450995799042341)
  ·
    refine ⟨10860778410084561712320439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57924151520450995799042341 10860778410084561712320439)
    ·
      refine ⟨16291167615126842568480659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10860778410084561712320439 16291167615126842568480659)
      ·
        refine ⟨24436751422690263852720989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16291167615126842568480659 24436751422690263852720989)
        ·
          refine ⟨9163781783508848944770371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24436751422690263852720989 9163781783508848944770371)
          ·
            refine ⟨13745672675263273417155557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9163781783508848944770371 13745672675263273417155557)
            ·
              refine ⟨2577313626611863765716667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13745672675263273417155557 2577313626611863765716667)
              ·
                refine ⟨3865970439917795648575001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2577313626611863765716667 3865970439917795648575001)
                ·
                  refine ⟨2899477829938346736431251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3865970439917795648575001 2899477829938346736431251)
                  ·
                    refine ⟨4349216744907520104646877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2899477829938346736431251 4349216744907520104646877)
                    ·
                      refine ⟨1630956279340320039242579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4349216744907520104646877 1630956279340320039242579)
                      ·
                        rfl

theorem cell23_3176276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_3176276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176276 prefixEnd_3176276 := by exact prefixLift 3176276
  have htrace : WordTrace (prefixWord ++ tailWord_3176276) baseStart_3176276 baseEnd_3176276 := by
    simpa [prefixWord, tailWord_3176276, baseEnd_3176276] using wordTrace_append hprefix tailTrace_3176276
  have hstable : (prefixWord ++ tailWord_3176276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176276).length < 2 ^ (prefixWord ++ tailWord_3176276).sum := by decide
  have hdescent : baseEnd_3176276 < baseStart_3176276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176282 : List Nat := [3, 1, 1, 2, 1, 3, 2, 3, 1, 4, 2]
def baseStart_3176282 : Nat := 118140960795 + 3176282 * 2 ^ 59
def prefixEnd_3176282 : Nat := 4983230072969 + 3 ^ 40 * 3176282 * 2
def baseEnd_3176282 : Nat := 1630959360224247015767551

theorem tailTrace_3176282 : CollatzResearch.WordTrace tailWord_3176282 prefixEnd_3176282 1630959360224247015767551 := by
  unfold tailWord_3176282
  simp only [CollatzResearch.WordTrace]
  refine ⟨28962130469720063655700775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77232347919253503081868733 28962130469720063655700775)
  ·
    refine ⟨43443195704580095483551163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28962130469720063655700775 43443195704580095483551163)
    ·
      refine ⟨65164793556870143225326745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43443195704580095483551163 65164793556870143225326745)
      ·
        refine ⟨48873595167652607418995059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65164793556870143225326745 48873595167652607418995059)
        ·
          refine ⟨73310392751478911128492589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48873595167652607418995059 73310392751478911128492589)
          ·
            refine ⟨27491397281804591673184721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73310392751478911128492589 27491397281804591673184721)
            ·
              refine ⟨20618547961353443754888541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27491397281804591673184721 20618547961353443754888541)
              ·
                refine ⟨7731955485507541408083203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20618547961353443754888541 7731955485507541408083203)
                ·
                  refine ⟨11597933228261312112124805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7731955485507541408083203 11597933228261312112124805)
                  ·
                    refine ⟨2174612480298996021023401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11597933228261312112124805 2174612480298996021023401)
                    ·
                      refine ⟨1630959360224247015767551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2174612480298996021023401 1630959360224247015767551)
                      ·
                        rfl

theorem cell23_3176282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 1, 4, 2].length) (baseStart_3176282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176282 prefixEnd_3176282 := by exact prefixLift 3176282
  have htrace : WordTrace (prefixWord ++ tailWord_3176282) baseStart_3176282 baseEnd_3176282 := by
    simpa [prefixWord, tailWord_3176282, baseEnd_3176282] using wordTrace_append hprefix tailTrace_3176282
  have hstable : (prefixWord ++ tailWord_3176282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176282).length < 2 ^ (prefixWord ++ tailWord_3176282).sum := by decide
  have hdescent : baseEnd_3176282 < baseStart_3176282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176302 : List Nat := [4, 1, 2, 3, 1, 1, 2, 1, 2, 1, 5]
def baseStart_3176302 : Nat := 118140960795 + 3176302 * 2 ^ 59
def prefixEnd_3176302 : Nat := 4983230072969 + 3 ^ 40 * 3176302 * 2
def baseEnd_3176302 : Nat := 1630969629837336937517459

theorem tailTrace_3176302 : CollatzResearch.WordTrace tailWord_3176302 prefixEnd_3176302 1630969629837336937517459 := by
  unfold tailWord_3176302
  simp only [CollatzResearch.WordTrace]
  refine ⟨14481156417350974754816395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77232834225871865359020773 14481156417350974754816395)
  ·
    refine ⟨21721734626026462132224593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14481156417350974754816395 21721734626026462132224593)
    ·
      refine ⟨16291300969519846599168445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21721734626026462132224593 16291300969519846599168445)
      ·
        refine ⟨6109237863569942474688167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16291300969519846599168445 6109237863569942474688167)
        ·
          refine ⟨9163856795354913712032251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6109237863569942474688167 9163856795354913712032251)
          ·
            refine ⟨13745785193032370568048377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9163856795354913712032251 13745785193032370568048377)
            ·
              refine ⟨10309338894774277926036283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13745785193032370568048377 10309338894774277926036283)
              ·
                refine ⟨15464008342161416889054425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10309338894774277926036283 15464008342161416889054425)
                ·
                  refine ⟨11598006256621062666790819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15464008342161416889054425 11598006256621062666790819)
                  ·
                    refine ⟨17397009384931594000186229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11598006256621062666790819 17397009384931594000186229)
                    ·
                      refine ⟨1630969629837336937517459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17397009384931594000186229 1630969629837336937517459)
                      ·
                        rfl

theorem cell23_3176302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_3176302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176302 prefixEnd_3176302 := by exact prefixLift 3176302
  have htrace : WordTrace (prefixWord ++ tailWord_3176302) baseStart_3176302 baseEnd_3176302 := by
    simpa [prefixWord, tailWord_3176302, baseEnd_3176302] using wordTrace_append hprefix tailTrace_3176302
  have hstable : (prefixWord ++ tailWord_3176302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176302).length < 2 ^ (prefixWord ++ tailWord_3176302).sum := by decide
  have hdescent : baseEnd_3176302 < baseStart_3176302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176315 : List Nat := [1, 1, 1, 1, 1, 5, 1, 4, 2, 3, 3]
def baseStart_3176315 : Nat := 118140960795 + 3176315 * 2 ^ 59
def prefixEnd_3176315 : Nat := 4983230072969 + 3 ^ 40 * 3176315 * 2
def baseEnd_3176315 : Nat := 1630976305085845386654899

theorem tailTrace_3176315 : CollatzResearch.WordTrace tailWord_3176315 prefixEnd_3176315 1630976305085845386654899 := by
  unfold tailWord_3176315
  simp only [CollatzResearch.WordTrace]
  refine ⟨115849725487760701258754399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77233150325173800839169599 115849725487760701258754399)
  ·
    refine ⟨173774588231641051888131599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115849725487760701258754399 173774588231641051888131599)
    ·
      refine ⟨260661882347461577832197399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173774588231641051888131599 260661882347461577832197399)
      ·
        refine ⟨390992823521192366748296099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260661882347461577832197399 390992823521192366748296099)
        ·
          refine ⟨586489235281788550122444149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390992823521192366748296099 586489235281788550122444149)
          ·
            refine ⟨54983365807667676573979139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 586489235281788550122444149 54983365807667676573979139)
            ·
              refine ⟨82475048711501514860968709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54983365807667676573979139 82475048711501514860968709)
              ·
                refine ⟨15464071633406534036431633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82475048711501514860968709 15464071633406534036431633)
                ·
                  refine ⟨11598053725054900527323725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15464071633406534036431633 11598053725054900527323725)
                  ·
                    refine ⟨4349270146895587697746397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11598053725054900527323725 4349270146895587697746397)
                    ·
                      refine ⟨1630976305085845386654899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4349270146895587697746397 1630976305085845386654899)
                      ·
                        rfl

theorem cell23_3176315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 3, 3].length) (baseStart_3176315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176315 prefixEnd_3176315 := by exact prefixLift 3176315
  have htrace : WordTrace (prefixWord ++ tailWord_3176315) baseStart_3176315 baseEnd_3176315 := by
    simpa [prefixWord, tailWord_3176315, baseEnd_3176315] using wordTrace_append hprefix tailTrace_3176315
  have hstable : (prefixWord ++ tailWord_3176315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176315).length < 2 ^ (prefixWord ++ tailWord_3176315).sum := by decide
  have hdescent : baseEnd_3176315 < baseStart_3176315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176392 : List Nat := [2, 1, 3, 1, 4, 1, 1, 2, 1, 4, 3]
def baseStart_3176392 : Nat := 118140960795 + 3176392 * 2 ^ 59
def prefixEnd_3176392 : Nat := 4983230072969 + 3 ^ 40 * 3176392 * 2
def baseEnd_3176392 : Nat := 1631015843096241585392045

theorem tailTrace_3176392 : CollatzResearch.WordTrace tailWord_3176392 prefixEnd_3176392 1631015843096241585392045 := by
  unfold tailWord_3176392
  simp only [CollatzResearch.WordTrace]
  refine ⟨57926266954240871704653715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77235022605654495606204953 57926266954240871704653715)
  ·
    refine ⟨86889400431361307556980573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57926266954240871704653715 86889400431361307556980573)
    ·
      refine ⟨32583525161760490333867715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86889400431361307556980573 32583525161760490333867715)
      ·
        refine ⟨48875287742640735500801573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32583525161760490333867715 48875287742640735500801573)
        ·
          refine ⟨9164116451745137906400295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48875287742640735500801573 9164116451745137906400295)
          ·
            refine ⟨13746174677617706859600443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9164116451745137906400295 13746174677617706859600443)
            ·
              refine ⟨20619262016426560289400665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13746174677617706859600443 20619262016426560289400665)
              ·
                refine ⟨15464446512319920217050499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20619262016426560289400665 15464446512319920217050499)
                ·
                  refine ⟨23196669768479880325575749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15464446512319920217050499 23196669768479880325575749)
                  ·
                    refine ⟨4349375581589977561045453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23196669768479880325575749 4349375581589977561045453)
                    ·
                      refine ⟨1631015843096241585392045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4349375581589977561045453 1631015843096241585392045)
                      ·
                        rfl

theorem cell23_3176392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 1, 4, 3].length) (baseStart_3176392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176392 prefixEnd_3176392 := by exact prefixLift 3176392
  have htrace : WordTrace (prefixWord ++ tailWord_3176392) baseStart_3176392 baseEnd_3176392 := by
    simpa [prefixWord, tailWord_3176392, baseEnd_3176392] using wordTrace_append hprefix tailTrace_3176392
  have hstable : (prefixWord ++ tailWord_3176392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176392).length < 2 ^ (prefixWord ++ tailWord_3176392).sum := by decide
  have hdescent : baseEnd_3176392 < baseStart_3176392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176433 : List Nat := [1, 2, 2, 2, 5, 1, 3, 2, 1, 4]
def baseStart_3176433 : Nat := 118140960795 + 3176433 * 2 ^ 59
def prefixEnd_3176433 : Nat := 4983230072969 + 3 ^ 40 * 3176433 * 2
def baseEnd_3176433 : Nat := 543678965267691974993119

theorem tailTrace_3176433 : CollatzResearch.WordTrace tailWord_3176433 prefixEnd_3176433 543678965267691974993119 := by
  unfold tailWord_3176433
  simp only [CollatzResearch.WordTrace]
  refine ⟨115854029301333207411549953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77236019534222138274366635 115854029301333207411549953)
  ·
    refine ⟨86890521975999905558662465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115854029301333207411549953 86890521975999905558662465)
    ·
      refine ⟨65167891481999929168996849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86890521975999905558662465 65167891481999929168996849)
      ·
        refine ⟨48875918611499946876747637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65167891481999929168996849 48875918611499946876747637)
        ·
          refine ⟨4582117369828120019695091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48875918611499946876747637 4582117369828120019695091)
          ·
            refine ⟨6873176054742180029542637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4582117369828120019695091 6873176054742180029542637)
            ·
              refine ⟨2577441020528317511078489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6873176054742180029542637 2577441020528317511078489)
              ·
                refine ⟨1933080765396238133308867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2577441020528317511078489 1933080765396238133308867)
                ·
                  refine ⟨2899621148094357199963301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1933080765396238133308867 2899621148094357199963301)
                  ·
                    refine ⟨543678965267691974993119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2899621148094357199963301 543678965267691974993119)
                    ·
                      rfl

theorem cell23_3176433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 2, 1, 4].length) (baseStart_3176433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176433 prefixEnd_3176433 := by exact prefixLift 3176433
  have htrace : WordTrace (prefixWord ++ tailWord_3176433) baseStart_3176433 baseEnd_3176433 := by
    simpa [prefixWord, tailWord_3176433, baseEnd_3176433] using wordTrace_append hprefix tailTrace_3176433
  have hstable : (prefixWord ++ tailWord_3176433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176433).length < 2 ^ (prefixWord ++ tailWord_3176433).sum := by decide
  have hdescent : baseEnd_3176433 < baseStart_3176433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176446 : List Nat := [4, 2, 2, 2, 1, 1, 4, 1, 6]
def baseStart_3176446 : Nat := 118140960795 + 3176446 * 2 ^ 59
def prefixEnd_3176446 : Nat := 4983230072969 + 3 ^ 40 * 3176446 * 2
def baseEnd_3176446 : Nat := 181227063450176041568533

theorem tailTrace_3176446 : CollatzResearch.WordTrace tailWord_3176446 prefixEnd_3176446 181227063450176041568533 := by
  unfold tailWord_3176446
  simp only [CollatzResearch.WordTrace]
  refine ⟨14481812931285763828971649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77236335633524073754515461 14481812931285763828971649)
  ·
    refine ⟨10861359698464322871728737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14481812931285763828971649 10861359698464322871728737)
    ·
      refine ⟨8146019773848242153796553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10861359698464322871728737 8146019773848242153796553)
      ·
        refine ⟨6109514830386181615347415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8146019773848242153796553 6109514830386181615347415)
        ·
          refine ⟨9164272245579272423021123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6109514830386181615347415 9164272245579272423021123)
          ·
            refine ⟨13746408368368908634531685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9164272245579272423021123 13746408368368908634531685)
            ·
              refine ⟨2577451569069170368974691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13746408368368908634531685 2577451569069170368974691)
              ·
                refine ⟨3866177353603755553462037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2577451569069170368974691 3866177353603755553462037)
                ·
                  refine ⟨181227063450176041568533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3866177353603755553462037 181227063450176041568533)
                  ·
                    rfl

theorem cell23_3176446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_3176446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176446 prefixEnd_3176446 := by exact prefixLift 3176446
  have htrace : WordTrace (prefixWord ++ tailWord_3176446) baseStart_3176446 baseEnd_3176446 := by
    simpa [prefixWord, tailWord_3176446, baseEnd_3176446] using wordTrace_append hprefix tailTrace_3176446
  have hstable : (prefixWord ++ tailWord_3176446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176446).length < 2 ^ (prefixWord ++ tailWord_3176446).sum := by decide
  have hdescent : baseEnd_3176446 < baseStart_3176446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176449 : List Nat := [1, 2, 4, 1, 2, 1, 1, 2, 4, 3, 2]
def baseStart_3176449 : Nat := 118140960795 + 3176449 * 2 ^ 59
def prefixEnd_3176449 : Nat := 4983230072969 + 3 ^ 40 * 3176449 * 2
def baseEnd_3176449 : Nat := 1631045111493547862379283

theorem tailTrace_3176449 : CollatzResearch.WordTrace tailWord_3176449 prefixEnd_3176449 1631045111493547862379283 := by
  unfold tailWord_3176449
  simp only [CollatzResearch.WordTrace]
  refine ⟨115854612869275242144132401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77236408579516828096088267 115854612869275242144132401)
  ·
    refine ⟨86890959651956431608099301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115854612869275242144132401 86890959651956431608099301)
    ·
      refine ⟨16292054934741830926518619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86890959651956431608099301 16292054934741830926518619)
      ·
        refine ⟨24438082402112746389777929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16292054934741830926518619 24438082402112746389777929)
        ·
          refine ⟨18328561801584559792333447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24438082402112746389777929 18328561801584559792333447)
          ·
            refine ⟨27492842702376839688500171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18328561801584559792333447 27492842702376839688500171)
            ·
              refine ⟨41239264053565259532750257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27492842702376839688500171 41239264053565259532750257)
              ·
                refine ⟨30929448040173944649562693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41239264053565259532750257 30929448040173944649562693)
                ·
                  refine ⟨5799271507532614621793005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30929448040173944649562693 5799271507532614621793005)
                  ·
                    refine ⟨2174726815324730483172377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5799271507532614621793005 2174726815324730483172377)
                    ·
                      refine ⟨1631045111493547862379283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2174726815324730483172377 1631045111493547862379283)
                      ·
                        rfl

theorem cell23_3176449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_3176449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176449 prefixEnd_3176449 := by exact prefixLift 3176449
  have htrace : WordTrace (prefixWord ++ tailWord_3176449) baseStart_3176449 baseEnd_3176449 := by
    simpa [prefixWord, tailWord_3176449, baseEnd_3176449] using wordTrace_append hprefix tailTrace_3176449
  have hstable : (prefixWord ++ tailWord_3176449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176449).length < 2 ^ (prefixWord ++ tailWord_3176449).sum := by decide
  have hdescent : baseEnd_3176449 < baseStart_3176449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176465 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 5]
def baseStart_3176465 : Nat := 118140960795 + 3176465 * 2 ^ 59
def prefixEnd_3176465 : Nat := 4983230072969 + 3 ^ 40 * 3176465 * 2
def baseEnd_3176465 : Nat := 1631053327184019799779209

theorem tailTrace_3176465 : CollatzResearch.WordTrace tailWord_3176465 prefixEnd_3176465 1631053327184019799779209 := by
  unfold tailWord_3176465
  simp only [CollatzResearch.WordTrace]
  refine ⟨115855196437217276876714849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77236797624811517917809899 115855196437217276876714849)
  ·
    refine ⟨86891397327912957657536137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115855196437217276876714849 86891397327912957657536137)
    ·
      refine ⟨65168547995934718243152103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86891397327912957657536137 65168547995934718243152103)
      ·
        refine ⟨97752821993902077364728155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65168547995934718243152103 97752821993902077364728155)
        ·
          refine ⟨146629232990853116047092233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97752821993902077364728155 146629232990853116047092233)
          ·
            refine ⟨109971924743139837035319175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146629232990853116047092233 109971924743139837035319175)
            ·
              refine ⟨164957887114709755552978763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109971924743139837035319175 164957887114709755552978763)
              ·
                refine ⟨247436830672064633329468145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164957887114709755552978763 247436830672064633329468145)
                ·
                  refine ⟨185577623004048474997101109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 247436830672064633329468145 185577623004048474997101109)
                  ·
                    refine ⟨17397902156629544530978229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 185577623004048474997101109 17397902156629544530978229)
                    ·
                      refine ⟨1631053327184019799779209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17397902156629544530978229 1631053327184019799779209)
                      ·
                        rfl

theorem cell23_3176465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_3176465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176465 prefixEnd_3176465 := by exact prefixLift 3176465
  have htrace : WordTrace (prefixWord ++ tailWord_3176465) baseStart_3176465 baseEnd_3176465 := by
    simpa [prefixWord, tailWord_3176465, baseEnd_3176465] using wordTrace_append hprefix tailTrace_3176465
  have hstable : (prefixWord ++ tailWord_3176465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176465).length < 2 ^ (prefixWord ++ tailWord_3176465).sum := by decide
  have hdescent : baseEnd_3176465 < baseStart_3176465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176472 : List Nat := [2, 1, 2, 3, 2, 1, 3, 2, 1, 6]
def baseStart_3176472 : Nat := 118140960795 + 3176472 * 2 ^ 59
def prefixEnd_3176472 : Nat := 4983230072969 + 3 ^ 40 * 3176472 * 2
def baseEnd_3176472 : Nat := 543685640516200424130559

theorem tailTrace_3176472 : CollatzResearch.WordTrace tailWord_3176472 prefixEnd_3176472 543685640516200424130559 := by
  unfold tailWord_3176472
  simp only [CollatzResearch.WordTrace]
  refine ⟨57927725874095958536109835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77236967832127944714813113 57927725874095958536109835)
  ·
    refine ⟨86891588811143937804164753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57927725874095958536109835 86891588811143937804164753)
    ·
      refine ⟨65168691608357953353123565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86891588811143937804164753 65168691608357953353123565)
      ·
        refine ⟨24438259353134232507421337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65168691608357953353123565 24438259353134232507421337)
        ·
          refine ⟨18328694514850674380566003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24438259353134232507421337 18328694514850674380566003)
          ·
            refine ⟨27493041772276011570849005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18328694514850674380566003 27493041772276011570849005)
            ·
              refine ⟨10309890664603504339068377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27493041772276011570849005 10309890664603504339068377)
              ·
                refine ⟨7732417998452628254301283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10309890664603504339068377 7732417998452628254301283)
                ·
                  refine ⟨11598626997678942381451925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7732417998452628254301283 11598626997678942381451925)
                  ·
                    refine ⟨543685640516200424130559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11598626997678942381451925 543685640516200424130559)
                    ·
                      rfl

theorem cell23_3176472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 1, 6].length) (baseStart_3176472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176472 prefixEnd_3176472 := by exact prefixLift 3176472
  have htrace : WordTrace (prefixWord ++ tailWord_3176472) baseStart_3176472 baseEnd_3176472 := by
    simpa [prefixWord, tailWord_3176472, baseEnd_3176472] using wordTrace_append hprefix tailTrace_3176472
  have hstable : (prefixWord ++ tailWord_3176472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176472).length < 2 ^ (prefixWord ++ tailWord_3176472).sum := by decide
  have hdescent : baseEnd_3176472 < baseStart_3176472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176475 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 6]
def baseStart_3176475 : Nat := 118140960795 + 3176475 * 2 ^ 59
def prefixEnd_3176475 : Nat := 4983230072969 + 3 ^ 40 * 3176475 * 2
def baseEnd_3176475 : Nat := 1631058461990564760654163

theorem tailTrace_3176475 : CollatzResearch.WordTrace tailWord_3176475 prefixEnd_3176475 1631058461990564760654163 := by
  unfold tailWord_3176475
  simp only [CollatzResearch.WordTrace]
  refine ⟨115855561167181048584578879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77237040778120699056385919 115855561167181048584578879)
  ·
    refine ⟨173783341750771572876868319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115855561167181048584578879 173783341750771572876868319)
    ·
      refine ⟨260675012626157359315302479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173783341750771572876868319 260675012626157359315302479)
      ·
        refine ⟨391012518939236038972953719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260675012626157359315302479 391012518939236038972953719)
        ·
          refine ⟨586518778408854058459430579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391012518939236038972953719 586518778408854058459430579)
          ·
            refine ⟨879778167613281087689145869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 586518778408854058459430579 879778167613281087689145869)
            ·
              refine ⟨329916812854980407883429701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 879778167613281087689145869 329916812854980407883429701)
              ·
                refine ⟨61859402410308826478143069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 329916812854980407883429701 61859402410308826478143069)
                ·
                  refine ⟨23197275903865809929303651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61859402410308826478143069 23197275903865809929303651)
                  ·
                    refine ⟨34795913855798714893955477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23197275903865809929303651 34795913855798714893955477)
                    ·
                      refine ⟨1631058461990564760654163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34795913855798714893955477 1631058461990564760654163)
                      ·
                        rfl

theorem cell23_3176475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 6].length) (baseStart_3176475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176475 prefixEnd_3176475 := by exact prefixLift 3176475
  have htrace : WordTrace (prefixWord ++ tailWord_3176475) baseStart_3176475 baseEnd_3176475 := by
    simpa [prefixWord, tailWord_3176475, baseEnd_3176475] using wordTrace_append hprefix tailTrace_3176475
  have hstable : (prefixWord ++ tailWord_3176475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176475).length < 2 ^ (prefixWord ++ tailWord_3176475).sum := by decide
  have hdescent : baseEnd_3176475 < baseStart_3176475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176476 : List Nat := [2, 2, 3, 1, 3, 2, 3, 1, 1, 5]
def baseStart_3176476 : Nat := 118140960795 + 3176476 * 2 ^ 59
def prefixEnd_3176476 : Nat := 4983230072969 + 3 ^ 40 * 3176476 * 2
def baseEnd_3176476 : Nat := 543686325157073085580553

theorem tailTrace_3176476 : CollatzResearch.WordTrace tailWord_3176476 prefixEnd_3176476 543686325157073085580553 := by
  unfold tailWord_3176476
  simp only [CollatzResearch.WordTrace]
  refine ⟨57927798820088712877682641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77237065093451617170243521 57927798820088712877682641)
  ·
    refine ⟨43445849115066534658261981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57927798820088712877682641 43445849115066534658261981)
    ·
      refine ⟨16292193418149950496848243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43445849115066534658261981 16292193418149950496848243)
      ·
        refine ⟨24438290127224925745272365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16292193418149950496848243 24438290127224925745272365)
        ·
          refine ⟨9164358797709347154477137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24438290127224925745272365 9164358797709347154477137)
          ·
            refine ⟨6873269098282010365857853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9164358797709347154477137 6873269098282010365857853)
            ·
              refine ⟨2577475911855753887196695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6873269098282010365857853 2577475911855753887196695)
              ·
                refine ⟨3866213867783630830795043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2577475911855753887196695 3866213867783630830795043)
                ·
                  refine ⟨5799320801675446246192565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3866213867783630830795043 5799320801675446246192565)
                  ·
                    refine ⟨543686325157073085580553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5799320801675446246192565 543686325157073085580553)
                    ·
                      rfl

theorem cell23_3176476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_3176476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176476 prefixEnd_3176476 := by exact prefixLift 3176476
  have htrace : WordTrace (prefixWord ++ tailWord_3176476) baseStart_3176476 baseEnd_3176476 := by
    simpa [prefixWord, tailWord_3176476, baseEnd_3176476] using wordTrace_append hprefix tailTrace_3176476
  have hstable : (prefixWord ++ tailWord_3176476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176476).length < 2 ^ (prefixWord ++ tailWord_3176476).sum := by decide
  have hdescent : baseEnd_3176476 < baseStart_3176476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176485 : List Nat := [1, 3, 1, 2, 2, 14]
def baseStart_3176485 : Nat := 118140960795 + 3176485 * 2 ^ 59
def prefixEnd_3176485 : Nat := 4983230072969 + 3 ^ 40 * 3176485 * 2
def baseEnd_3176485 : Nat := 6712195871593044121519

theorem tailTrace_3176485 : CollatzResearch.WordTrace tailWord_3176485 prefixEnd_3176485 6712195871593044121519 := by
  unfold tailWord_3176485
  simp only [CollatzResearch.WordTrace]
  refine ⟨115855925897144820292442909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77237283931429880194961939 115855925897144820292442909)
  ·
    refine ⟨43445972211429307609666091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115855925897144820292442909 43445972211429307609666091)
    ·
      refine ⟨65168958317143961414499137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43445972211429307609666091 65168958317143961414499137)
      ·
        refine ⟨48876718737857971060874353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65168958317143961414499137 48876718737857971060874353)
        ·
          refine ⟨36657539053393478295655765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48876718737857971060874353 36657539053393478295655765)
          ·
            refine ⟨6712195871593044121519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 36657539053393478295655765 6712195871593044121519)
            ·
              rfl

theorem cell23_3176485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 14].length) (baseStart_3176485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176485 prefixEnd_3176485 := by exact prefixLift 3176485
  have htrace : WordTrace (prefixWord ++ tailWord_3176485) baseStart_3176485 baseEnd_3176485 := by
    simpa [prefixWord, tailWord_3176485, baseEnd_3176485] using wordTrace_append hprefix tailTrace_3176485
  have hstable : (prefixWord ++ tailWord_3176485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176485).length < 2 ^ (prefixWord ++ tailWord_3176485).sum := by decide
  have hdescent : baseEnd_3176485 < baseStart_3176485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176490 : List Nat := [3, 1, 4, 1, 2, 1, 4, 2, 1, 1, 3]
def baseStart_3176490 : Nat := 118140960795 + 3176490 * 2 ^ 59
def prefixEnd_3176490 : Nat := 4983230072969 + 3 ^ 40 * 3176490 * 2
def baseEnd_3176490 : Nat := 1631066164200382201966595

theorem tailTrace_3176490 : CollatzResearch.WordTrace tailWord_3176490 prefixEnd_3176490 1631066164200382201966595 := by
  unfold tailWord_3176490
  simp only [CollatzResearch.WordTrace]
  refine ⟨28964027065531676536593731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77237405508084470764249949 28964027065531676536593731)
  ·
    refine ⟨43446040598297514804890597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28964027065531676536593731 43446040598297514804890597)
    ·
      refine ⟨8146132612180784025916987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43446040598297514804890597 8146132612180784025916987)
      ·
        refine ⟨12219198918271176038875481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8146132612180784025916987 12219198918271176038875481)
        ·
          refine ⟨9164399188703382029156611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12219198918271176038875481 9164399188703382029156611)
          ·
            refine ⟨13746598783055073043734917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9164399188703382029156611 13746598783055073043734917)
            ·
              refine ⟨2577487271822826195700297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13746598783055073043734917 2577487271822826195700297)
              ·
                refine ⟨1933115453867119646775223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2577487271822826195700297 1933115453867119646775223)
                ·
                  refine ⟨2899673180800679470162835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1933115453867119646775223 2899673180800679470162835)
                  ·
                    refine ⟨4349509771201019205244253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2899673180800679470162835 4349509771201019205244253)
                    ·
                      refine ⟨1631066164200382201966595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4349509771201019205244253 1631066164200382201966595)
                      ·
                        rfl

theorem cell23_3176490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_3176490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176490 prefixEnd_3176490 := by exact prefixLift 3176490
  have htrace : WordTrace (prefixWord ++ tailWord_3176490) baseStart_3176490 baseEnd_3176490 := by
    simpa [prefixWord, tailWord_3176490, baseEnd_3176490] using wordTrace_append hprefix tailTrace_3176490
  have hstable : (prefixWord ++ tailWord_3176490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176490).length < 2 ^ (prefixWord ++ tailWord_3176490).sum := by decide
  have hdescent : baseEnd_3176490 < baseStart_3176490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176495 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 7]
def baseStart_3176495 : Nat := 118140960795 + 3176495 * 2 ^ 59
def prefixEnd_3176495 : Nat := 4983230072969 + 3 ^ 40 * 3176495 * 2
def baseEnd_3176495 : Nat := 1631068731603654682404071

theorem tailTrace_3176495 : CollatzResearch.WordTrace tailWord_3176495 prefixEnd_3176495 1631068731603654682404071 := by
  unfold tailWord_3176495
  simp only [CollatzResearch.WordTrace]
  refine ⟨115856290627108592000306939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77237527084739061333537959 115856290627108592000306939)
  ·
    refine ⟨173784435940662888000460409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115856290627108592000306939 173784435940662888000460409)
    ·
      refine ⟨130338326955497166000345307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173784435940662888000460409 130338326955497166000345307)
      ·
        refine ⟨195507490433245749000517961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130338326955497166000345307 195507490433245749000517961)
        ·
          refine ⟨146630617824934311750388471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195507490433245749000517961 146630617824934311750388471)
          ·
            refine ⟨219945926737401467625582707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146630617824934311750388471 219945926737401467625582707)
            ·
              refine ⟨329918890106102201438374061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219945926737401467625582707 329918890106102201438374061)
              ·
                refine ⟨123719583789788325539390273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 329918890106102201438374061 123719583789788325539390273)
                ·
                  refine ⟨92789687842341244154542705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123719583789788325539390273 92789687842341244154542705)
                  ·
                    refine ⟨69592265881755933115907029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 92789687842341244154542705 69592265881755933115907029)
                    ·
                      refine ⟨1631068731603654682404071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 69592265881755933115907029 1631068731603654682404071)
                      ·
                        rfl

theorem cell23_3176495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 7].length) (baseStart_3176495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176495 prefixEnd_3176495 := by exact prefixLift 3176495
  have htrace : WordTrace (prefixWord ++ tailWord_3176495) baseStart_3176495 baseEnd_3176495 := by
    simpa [prefixWord, tailWord_3176495, baseEnd_3176495] using wordTrace_append hprefix tailTrace_3176495
  have hstable : (prefixWord ++ tailWord_3176495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176495).length < 2 ^ (prefixWord ++ tailWord_3176495).sum := by decide
  have hdescent : baseEnd_3176495 < baseStart_3176495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176509 : List Nat := [1, 4, 1, 3, 1, 1, 4, 1, 1, 2, 4]
def baseStart_3176509 : Nat := 118140960795 + 3176509 * 2 ^ 59
def prefixEnd_3176509 : Nat := 4983230072969 + 3 ^ 40 * 3176509 * 2
def baseEnd_3176509 : Nat := 1631075920332817627629007

theorem tailTrace_3176509 : CollatzResearch.WordTrace tailWord_3176509 prefixEnd_3176509 1631075920332817627629007 := by
  unfold tailWord_3176509
  simp only [CollatzResearch.WordTrace]
  refine ⟨115856801249057872391316581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77237867499371914927544387 115856801249057872391316581)
  ·
    refine ⟨21723150234198351073371859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115856801249057872391316581 21723150234198351073371859)
    ·
      refine ⟨32584725351297526610057789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21723150234198351073371859 32584725351297526610057789)
      ·
        refine ⟨12219272006736572478771671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32584725351297526610057789 12219272006736572478771671)
        ·
          refine ⟨18328908010104858718157507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12219272006736572478771671 18328908010104858718157507)
          ·
            refine ⟨27493362015157288077236261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18328908010104858718157507 27493362015157288077236261)
            ·
              refine ⟨5155005377841991514481799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27493362015157288077236261 5155005377841991514481799)
              ·
                refine ⟨7732508066762987271722699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5155005377841991514481799 7732508066762987271722699)
                ·
                  refine ⟨11598762100144480907584049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7732508066762987271722699 11598762100144480907584049)
                  ·
                    refine ⟨8699071575108360680688037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11598762100144480907584049 8699071575108360680688037)
                    ·
                      refine ⟨1631075920332817627629007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8699071575108360680688037 1631075920332817627629007)
                      ·
                        rfl

theorem cell23_3176509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_3176509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176509 prefixEnd_3176509 := by exact prefixLift 3176509
  have htrace : WordTrace (prefixWord ++ tailWord_3176509) baseStart_3176509 baseEnd_3176509 := by
    simpa [prefixWord, tailWord_3176509, baseEnd_3176509] using wordTrace_append hprefix tailTrace_3176509
  have hstable : (prefixWord ++ tailWord_3176509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176509).length < 2 ^ (prefixWord ++ tailWord_3176509).sum := by decide
  have hdescent : baseEnd_3176509 < baseStart_3176509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176513 : List Nat := [1, 2, 5, 1, 2, 2, 1, 2, 3, 2, 2]
def baseStart_3176513 : Nat := 118140960795 + 3176513 * 2 ^ 59
def prefixEnd_3176513 : Nat := 4983230072969 + 3 ^ 40 * 3176513 * 2
def baseEnd_3176513 : Nat := 1631077974255435611978989

theorem tailTrace_3176513 : CollatzResearch.WordTrace tailWord_3176513 prefixEnd_3176513 1631077974255435611978989 := by
  unfold tailWord_3176513
  simp only [CollatzResearch.WordTrace]
  refine ⟨115856947141043381074462193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77237964760695587382974795 115856947141043381074462193)
  ·
    refine ⟨86892710355782535805846645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115856947141043381074462193 86892710355782535805846645)
    ·
      refine ⟨8146191595854612731798123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86892710355782535805846645 8146191595854612731798123)
      ·
        refine ⟨12219287393781919097697185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8146191595854612731798123 12219287393781919097697185)
        ·
          refine ⟨9164465545336439323272889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12219287393781919097697185 9164465545336439323272889)
          ·
            refine ⟨6873349159002329492454667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9164465545336439323272889 6873349159002329492454667)
            ·
              refine ⟨10310023738503494238682001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6873349159002329492454667 10310023738503494238682001)
              ·
                refine ⟨7732517803877620679011501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10310023738503494238682001 7732517803877620679011501)
                ·
                  refine ⟨2899694176454107754629313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7732517803877620679011501 2899694176454107754629313)
                  ·
                    refine ⟨2174770632340580815971985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2899694176454107754629313 2174770632340580815971985)
                    ·
                      refine ⟨1631077974255435611978989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2174770632340580815971985 1631077974255435611978989)
                      ·
                        rfl

theorem cell23_3176513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_3176513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176513 prefixEnd_3176513 := by exact prefixLift 3176513
  have htrace : WordTrace (prefixWord ++ tailWord_3176513) baseStart_3176513 baseEnd_3176513 := by
    simpa [prefixWord, tailWord_3176513, baseEnd_3176513] using wordTrace_append hprefix tailTrace_3176513
  have hstable : (prefixWord ++ tailWord_3176513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176513).length < 2 ^ (prefixWord ++ tailWord_3176513).sum := by decide
  have hdescent : baseEnd_3176513 < baseStart_3176513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176529 : List Nat := [1, 2, 2, 1, 3, 1, 1, 4, 4, 1, 3]
def baseStart_3176529 : Nat := 118140960795 + 3176529 * 2 ^ 59
def prefixEnd_3176529 : Nat := 4983230072969 + 3 ^ 40 * 3176529 * 2
def baseEnd_3176529 : Nat := 1631086189945907549378915

theorem tailTrace_3176529 : CollatzResearch.WordTrace tailWord_3176529 prefixEnd_3176529 1631086189945907549378915 := by
  unfold tailWord_3176529
  simp only [CollatzResearch.WordTrace]
  refine ⟨115857530708985415807044641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77238353805990277204696427 115857530708985415807044641)
  ·
    refine ⟨86893148031739061855283481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115857530708985415807044641 86893148031739061855283481)
    ·
      refine ⟨65169861023804296391462611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86893148031739061855283481 65169861023804296391462611)
      ·
        refine ⟨97754791535706444587193917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65169861023804296391462611 97754791535706444587193917)
        ·
          refine ⟨36658046825889916720197719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97754791535706444587193917 36658046825889916720197719)
          ·
            refine ⟨54987070238834875080296579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36658046825889916720197719 54987070238834875080296579)
            ·
              refine ⟨82480605358252312620444869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54987070238834875080296579 82480605358252312620444869)
              ·
                refine ⟨15465113504672308616333413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82480605358252312620444869 15465113504672308616333413)
                ·
                  refine ⟨2899708782126057865562515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15465113504672308616333413 2899708782126057865562515)
                  ·
                    refine ⟨4349563173189086798343773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2899708782126057865562515 4349563173189086798343773)
                    ·
                      refine ⟨1631086189945907549378915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4349563173189086798343773 1631086189945907549378915)
                      ·
                        rfl

theorem cell23_3176529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 4, 1, 3].length) (baseStart_3176529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176529 prefixEnd_3176529 := by exact prefixLift 3176529
  have htrace : WordTrace (prefixWord ++ tailWord_3176529) baseStart_3176529 baseEnd_3176529 := by
    simpa [prefixWord, tailWord_3176529, baseEnd_3176529] using wordTrace_append hprefix tailTrace_3176529
  have hstable : (prefixWord ++ tailWord_3176529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176529).length < 2 ^ (prefixWord ++ tailWord_3176529).sum := by decide
  have hdescent : baseEnd_3176529 < baseStart_3176529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176530 : List Nat := [3, 2, 2, 1, 5, 1, 2, 1, 1, 1, 4]
def baseStart_3176530 : Nat := 118140960795 + 3176530 * 2 ^ 59
def prefixEnd_3176530 : Nat := 4983230072969 + 3 ^ 40 * 3176530 * 2
def baseEnd_3176530 : Nat := 1631086703426562045466411

theorem tailTrace_3176530 : CollatzResearch.WordTrace tailWord_3176530 prefixEnd_3176530 1631086703426562045466411 := by
  unfold tailWord_3176530
  simp only [CollatzResearch.WordTrace]
  refine ⟨28964391795495448244457761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77238378121321195318554029 28964391795495448244457761)
  ·
    refine ⟨21723293846621586183343321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28964391795495448244457761 21723293846621586183343321)
    ·
      refine ⟨16292470384966189637507491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21723293846621586183343321 16292470384966189637507491)
      ·
        refine ⟨24438705577449284456261237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16292470384966189637507491 24438705577449284456261237)
        ·
          refine ⟨2291128647885870417774491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24438705577449284456261237 2291128647885870417774491)
          ·
            refine ⟨3436692971828805626661737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2291128647885870417774491 3436692971828805626661737)
            ·
              refine ⟨2577519728871604219996303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3436692971828805626661737 2577519728871604219996303)
              ·
                refine ⟨3866279593307406329994455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2577519728871604219996303 3866279593307406329994455)
                ·
                  refine ⟨5799419389961109494991683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3866279593307406329994455 5799419389961109494991683)
                  ·
                    refine ⟨8699129084941664242487525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5799419389961109494991683 8699129084941664242487525)
                    ·
                      refine ⟨1631086703426562045466411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8699129084941664242487525 1631086703426562045466411)
                      ·
                        rfl

theorem cell23_3176530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_3176530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176530 prefixEnd_3176530 := by exact prefixLift 3176530
  have htrace : WordTrace (prefixWord ++ tailWord_3176530) baseStart_3176530 baseEnd_3176530 := by
    simpa [prefixWord, tailWord_3176530, baseEnd_3176530] using wordTrace_append hprefix tailTrace_3176530
  have hstable : (prefixWord ++ tailWord_3176530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176530).length < 2 ^ (prefixWord ++ tailWord_3176530).sum := by decide
  have hdescent : baseEnd_3176530 < baseStart_3176530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176533 : List Nat := [1, 3, 2, 2, 1, 5, 2, 1, 1, 2, 3]
def baseStart_3176533 : Nat := 118140960795 + 3176533 * 2 ^ 59
def prefixEnd_3176533 : Nat := 4983230072969 + 3 ^ 40 * 3176533 * 2
def baseEnd_3176533 : Nat := 1631088243868525533728897

theorem tailTrace_3176533 : CollatzResearch.WordTrace tailWord_3176533 prefixEnd_3176533 1631088243868525533728897 := by
  unfold tailWord_3176533
  simp only [CollatzResearch.WordTrace]
  refine ⟨115857676600970924490190253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77238451067313949660126835 115857676600970924490190253)
  ·
    refine ⟨43446628725364096683821345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115857676600970924490190253 43446628725364096683821345)
    ·
      refine ⟨32584971544023072512866009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43446628725364096683821345 32584971544023072512866009)
      ·
        refine ⟨24438728658017304384649507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32584971544023072512866009 24438728658017304384649507)
        ·
          refine ⟨36658092987025956576974261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24438728658017304384649507 36658092987025956576974261)
          ·
            refine ⟨3436696217533683429091337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36658092987025956576974261 3436696217533683429091337)
            ·
              refine ⟨2577522163150262571818503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3436696217533683429091337 2577522163150262571818503)
              ·
                refine ⟨3866283244725393857727755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2577522163150262571818503 3866283244725393857727755)
                ·
                  refine ⟨5799424867088090786591633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3866283244725393857727755 5799424867088090786591633)
                  ·
                    refine ⟨4349568650316068089943725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5799424867088090786591633 4349568650316068089943725)
                    ·
                      refine ⟨1631088243868525533728897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4349568650316068089943725 1631088243868525533728897)
                      ·
                        rfl

theorem cell23_3176533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_3176533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176533 prefixEnd_3176533 := by exact prefixLift 3176533
  have htrace : WordTrace (prefixWord ++ tailWord_3176533) baseStart_3176533 baseEnd_3176533 := by
    simpa [prefixWord, tailWord_3176533, baseEnd_3176533] using wordTrace_append hprefix tailTrace_3176533
  have hstable : (prefixWord ++ tailWord_3176533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176533).length < 2 ^ (prefixWord ++ tailWord_3176533).sum := by decide
  have hdescent : baseEnd_3176533 < baseStart_3176533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176573 : List Nat := [1, 4, 1, 1, 3, 3, 2, 2, 1, 3, 2]
def baseStart_3176573 : Nat := 118140960795 + 3176573 * 2 ^ 59
def prefixEnd_3176573 : Nat := 4983230072969 + 3 ^ 40 * 3176573 * 2
def baseEnd_3176573 : Nat := 1631108783094705377228713

theorem tailTrace_3176573 : CollatzResearch.WordTrace tailWord_3176573 prefixEnd_3176573 1631108783094705377228713 := by
  unfold tailWord_3176573
  simp only [CollatzResearch.WordTrace]
  refine ⟨115859135520826011321646373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77239423680550674214430915 115859135520826011321646373)
  ·
    refine ⟨21723587910154877122808695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115859135520826011321646373 21723587910154877122808695)
    ·
      refine ⟨32585381865232315684213043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21723587910154877122808695 32585381865232315684213043)
      ·
        refine ⟨48878072797848473526319565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32585381865232315684213043 48878072797848473526319565)
        ·
          refine ⟨18329277299193177572369837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48878072797848473526319565 18329277299193177572369837)
          ·
            refine ⟨6873478987197441589638689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18329277299193177572369837 6873478987197441589638689)
            ·
              refine ⟨5155109240398081192229017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6873478987197441589638689 5155109240398081192229017)
              ·
                refine ⟨3866331930298560894171763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5155109240398081192229017 3866331930298560894171763)
                ·
                  refine ⟨5799497895447841341257645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3866331930298560894171763 5799497895447841341257645)
                  ·
                    refine ⟨2174811710792940502971617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5799497895447841341257645 2174811710792940502971617)
                    ·
                      refine ⟨1631108783094705377228713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2174811710792940502971617 1631108783094705377228713)
                      ·
                        rfl

theorem cell23_3176573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 3, 2].length) (baseStart_3176573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176573 prefixEnd_3176573 := by exact prefixLift 3176573
  have htrace : WordTrace (prefixWord ++ tailWord_3176573) baseStart_3176573 baseEnd_3176573 := by
    simpa [prefixWord, tailWord_3176573, baseEnd_3176573] using wordTrace_append hprefix tailTrace_3176573
  have hstable : (prefixWord ++ tailWord_3176573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176573).length < 2 ^ (prefixWord ++ tailWord_3176573).sum := by decide
  have hdescent : baseEnd_3176573 < baseStart_3176573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176598 : List Nat := [5, 3, 2, 1, 2, 1, 1, 1, 3, 2, 2]
def baseStart_3176598 : Nat := 118140960795 + 3176598 * 2 ^ 59
def prefixEnd_3176598 : Nat := 4983230072969 + 3 ^ 40 * 3176598 * 2
def baseEnd_3176598 : Nat := 1631121620111067779416099

theorem tailTrace_3176598 : CollatzResearch.WordTrace tailWord_3176598 prefixEnd_3176598 1631121620111067779416099 := by
  unfold tailWord_3176598
  simp only [CollatzResearch.WordTrace]
  refine ⟨7241252959108465036956653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77240031563823627060870965 7241252959108465036956653)
  ·
    refine ⟨2715469859665674388858745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7241252959108465036956653 2715469859665674388858745)
    ·
      refine ⟨2036602394749255791644059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2715469859665674388858745 2036602394749255791644059)
      ·
        refine ⟨3054903592123883687466089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2036602394749255791644059 3054903592123883687466089)
        ·
          refine ⟨2291177694092912765599567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3054903592123883687466089 2291177694092912765599567)
          ·
            refine ⟨3436766541139369148399351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2291177694092912765599567 3436766541139369148399351)
            ·
              refine ⟨5155149811709053722599027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3436766541139369148399351 5155149811709053722599027)
              ·
                refine ⟨7732724717563580583898541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5155149811709053722599027 7732724717563580583898541)
                ·
                  refine ⟨2899771769086342718961953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7732724717563580583898541 2899771769086342718961953)
                  ·
                    refine ⟨2174828826814757039221465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2899771769086342718961953 2174828826814757039221465)
                    ·
                      refine ⟨1631121620111067779416099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2174828826814757039221465 1631121620111067779416099)
                      ·
                        rfl

theorem cell23_3176598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_3176598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176598 prefixEnd_3176598 := by exact prefixLift 3176598
  have htrace : WordTrace (prefixWord ++ tailWord_3176598) baseStart_3176598 baseEnd_3176598 := by
    simpa [prefixWord, tailWord_3176598, baseEnd_3176598] using wordTrace_append hprefix tailTrace_3176598
  have hstable : (prefixWord ++ tailWord_3176598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176598).length < 2 ^ (prefixWord ++ tailWord_3176598).sum := by decide
  have hdescent : baseEnd_3176598 < baseStart_3176598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176609 : List Nat := [1, 2, 3, 3, 1, 2, 3, 1, 7]
def baseStart_3176609 : Nat := 118140960795 + 3176609 * 2 ^ 59
def prefixEnd_3176609 : Nat := 4983230072969 + 3 ^ 40 * 3176609 * 2
def baseEnd_3176609 : Nat := 181236363155363026264283

theorem tailTrace_3176609 : CollatzResearch.WordTrace tailWord_3176609 prefixEnd_3176609 181236363155363026264283 := by
  unfold tailWord_3176609
  simp only [CollatzResearch.WordTrace]
  refine ⟨115860448548695589469956881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77240299032463726313304587 115860448548695589469956881)
  ·
    refine ⟨86895336411521692102467661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115860448548695589469956881 86895336411521692102467661)
    ·
      refine ⟨32585751154320634538425373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86895336411521692102467661 32585751154320634538425373)
      ·
        refine ⟨12219656682870237951909515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32585751154320634538425373 12219656682870237951909515)
        ·
          refine ⟨18329485024305356927864273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12219656682870237951909515 18329485024305356927864273)
          ·
            refine ⟨13747113768229017695898205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18329485024305356927864273 13747113768229017695898205)
            ·
              refine ⟨5155167663085881635961827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13747113768229017695898205 5155167663085881635961827)
              ·
                refine ⟨7732751494628822453942741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5155167663085881635961827 7732751494628822453942741)
                ·
                  refine ⟨181236363155363026264283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7732751494628822453942741 181236363155363026264283)
                  ·
                    rfl

theorem cell23_3176609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 7].length) (baseStart_3176609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176609 prefixEnd_3176609 := by exact prefixLift 3176609
  have htrace : WordTrace (prefixWord ++ tailWord_3176609) baseStart_3176609 baseEnd_3176609 := by
    simpa [prefixWord, tailWord_3176609, baseEnd_3176609] using wordTrace_append hprefix tailTrace_3176609
  have hstable : (prefixWord ++ tailWord_3176609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176609).length < 2 ^ (prefixWord ++ tailWord_3176609).sum := by decide
  have hdescent : baseEnd_3176609 < baseStart_3176609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176632 : List Nat := [2, 1, 2, 1, 2, 1, 3, 2, 1, 1, 7]
def baseStart_3176632 : Nat := 118140960795 + 3176632 * 2 ^ 59
def prefixEnd_3176632 : Nat := 4983230072969 + 3 ^ 40 * 3176632 * 2
def baseEnd_3176632 : Nat := 1631139078453320646390941

theorem tailTrace_3176632 : CollatzResearch.WordTrace tailWord_3176632 prefixEnd_3176632 1631139078453320646390941 := by
  unfold tailWord_3176632
  simp only [CollatzResearch.WordTrace]
  refine ⟨57930643713806132199022075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77240858285074842932029433 57930643713806132199022075)
  ·
    refine ⟨86895965570709198298533113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57930643713806132199022075 86895965570709198298533113)
    ·
      refine ⟨65171974178031898723899835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86895965570709198298533113 65171974178031898723899835)
      ·
        refine ⟨97757961267047848085849753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65171974178031898723899835 97757961267047848085849753)
        ·
          refine ⟨73318470950285886064387315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97757961267047848085849753 73318470950285886064387315)
          ·
            refine ⟨109977706425428829096580973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73318470950285886064387315 109977706425428829096580973)
            ·
              refine ⟨41241639909535810911217865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109977706425428829096580973 41241639909535810911217865)
              ·
                refine ⟨30931229932151858183413399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41241639909535810911217865 30931229932151858183413399)
                ·
                  refine ⟨46396844898227787275120099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30931229932151858183413399 46396844898227787275120099)
                  ·
                    refine ⟨69595267347341680912680149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46396844898227787275120099 69595267347341680912680149)
                    ·
                      refine ⟨1631139078453320646390941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 69595267347341680912680149 1631139078453320646390941)
                      ·
                        rfl

theorem cell23_3176632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_3176632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176632 prefixEnd_3176632 := by exact prefixLift 3176632
  have htrace : WordTrace (prefixWord ++ tailWord_3176632) baseStart_3176632 baseEnd_3176632 := by
    simpa [prefixWord, tailWord_3176632, baseEnd_3176632] using wordTrace_append hprefix tailTrace_3176632
  have hstable : (prefixWord ++ tailWord_3176632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176632).length < 2 ^ (prefixWord ++ tailWord_3176632).sum := by decide
  have hdescent : baseEnd_3176632 < baseStart_3176632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176703 : List Nat := [1, 1, 2, 2, 1, 4, 4, 3, 1, 4]
def baseStart_3176703 : Nat := 118140960795 + 3176703 * 2 ^ 59
def prefixEnd_3176703 : Nat := 4983230072969 + 3 ^ 40 * 3176703 * 2
def baseEnd_3176703 : Nat := 543725178526596622867705

theorem tailTrace_3176703 : CollatzResearch.WordTrace tailWord_3176703 prefixEnd_3176703 543725178526596622867705 := by
  unfold tailWord_3176703
  simp only [CollatzResearch.WordTrace]
  refine ⟨115863877010355043523878763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77242584673570029015919175 115863877010355043523878763)
  ·
    refine ⟨173795815515532565285818145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115863877010355043523878763 173795815515532565285818145)
    ·
      refine ⟨130346861636649423964363609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173795815515532565285818145 130346861636649423964363609)
      ·
        refine ⟨97760146227487067973272707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130346861636649423964363609 97760146227487067973272707)
        ·
          refine ⟨146640219341230601959909061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97760146227487067973272707 146640219341230601959909061)
          ·
            refine ⟨27495041126480737867482949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146640219341230601959909061 27495041126480737867482949)
            ·
              refine ⟨5155320211215138350153053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27495041126480737867482949 5155320211215138350153053)
              ·
                refine ⟨1933245079205676881307395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5155320211215138350153053 1933245079205676881307395)
                ·
                  refine ⟨2899867618808515321961093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1933245079205676881307395 2899867618808515321961093)
                  ·
                    refine ⟨543725178526596622867705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2899867618808515321961093 543725178526596622867705)
                    ·
                      rfl

theorem cell23_3176703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 3, 1, 4].length) (baseStart_3176703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176703 prefixEnd_3176703 := by exact prefixLift 3176703
  have htrace : WordTrace (prefixWord ++ tailWord_3176703) baseStart_3176703 baseEnd_3176703 := by
    simpa [prefixWord, tailWord_3176703, baseEnd_3176703] using wordTrace_append hprefix tailTrace_3176703
  have hstable : (prefixWord ++ tailWord_3176703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176703).length < 2 ^ (prefixWord ++ tailWord_3176703).sum := by decide
  have hdescent : baseEnd_3176703 < baseStart_3176703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176706 : List Nat := [3, 4, 1, 1, 2, 1, 1, 1, 2, 1, 6]
def baseStart_3176706 : Nat := 118140960795 + 3176706 * 2 ^ 59
def prefixEnd_3176706 : Nat := 4983230072969 + 3 ^ 40 * 3176706 * 2
def baseEnd_3176706 : Nat := 1631177076021753356865601

theorem tailTrace_3176706 : CollatzResearch.WordTrace tailWord_3176706 prefixEnd_3176706 1631177076021753356865601 := by
  unfold tailWord_3176706
  simp only [CollatzResearch.WordTrace]
  refine ⟨28965996607336043759059493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77242657619562783357491981 28965996607336043759059493)
  ·
    refine ⟨5431124363875508204823655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28965996607336043759059493 5431124363875508204823655)
    ·
      refine ⟨8146686545813262307235483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5431124363875508204823655 8146686545813262307235483)
      ·
        refine ⟨12220029818719893460853225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8146686545813262307235483 12220029818719893460853225)
        ·
          refine ⟨9165022364039920095639919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12220029818719893460853225 9165022364039920095639919)
          ·
            refine ⟨13747533546059880143459879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9165022364039920095639919 13747533546059880143459879)
            ·
              refine ⟨20621300319089820215189819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13747533546059880143459879 20621300319089820215189819)
              ·
                refine ⟨30931950478634730322784729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20621300319089820215189819 30931950478634730322784729)
                ·
                  refine ⟨23198962858976047742088547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30931950478634730322784729 23198962858976047742088547)
                  ·
                    refine ⟨34798444288464071613132821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23198962858976047742088547 34798444288464071613132821)
                    ·
                      refine ⟨1631177076021753356865601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34798444288464071613132821 1631177076021753356865601)
                      ·
                        rfl

theorem cell23_3176706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_3176706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176706 prefixEnd_3176706 := by exact prefixLift 3176706
  have htrace : WordTrace (prefixWord ++ tailWord_3176706) baseStart_3176706 baseEnd_3176706 := by
    simpa [prefixWord, tailWord_3176706, baseEnd_3176706] using wordTrace_append hprefix tailTrace_3176706
  have hstable : (prefixWord ++ tailWord_3176706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176706).length < 2 ^ (prefixWord ++ tailWord_3176706).sum := by decide
  have hdescent : baseEnd_3176706 < baseStart_3176706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176759 : List Nat := [1, 1, 3, 1, 2, 1, 1, 6, 1, 6]
def baseStart_3176759 : Nat := 118140960795 + 3176759 * 2 ^ 59
def prefixEnd_3176759 : Nat := 4983230072969 + 3 ^ 40 * 3176759 * 2
def baseEnd_3176759 : Nat := 543734763498813883167619

theorem tailTrace_3176759 : CollatzResearch.WordTrace tailWord_3176759 prefixEnd_3176759 543734763498813883167619 := by
  unfold tailWord_3176759
  simp only [CollatzResearch.WordTrace]
  refine ⟨115865919498152165087917331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77243946332101443391944887 115865919498152165087917331)
  ·
    refine ⟨173798879247228247631875997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115865919498152165087917331 173798879247228247631875997)
    ·
      refine ⟨65174579717710592861953499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173798879247228247631875997 65174579717710592861953499)
      ·
        refine ⟨97761869576565889292930249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65174579717710592861953499 97761869576565889292930249)
        ·
          refine ⟨73321402182424416969697687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97761869576565889292930249 73321402182424416969697687)
          ·
            refine ⟨109982103273636625454546531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73321402182424416969697687 109982103273636625454546531)
            ·
              refine ⟨164973154910454938181819797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109982103273636625454546531 164973154910454938181819797)
              ·
                refine ⟨7733116636427575227272803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 164973154910454938181819797 7733116636427575227272803)
                ·
                  refine ⟨11599674954641362840909205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7733116636427575227272803 11599674954641362840909205)
                  ·
                    refine ⟨543734763498813883167619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11599674954641362840909205 543734763498813883167619)
                    ·
                      rfl

theorem cell23_3176759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 6].length) (baseStart_3176759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176759 prefixEnd_3176759 := by exact prefixLift 3176759
  have htrace : WordTrace (prefixWord ++ tailWord_3176759) baseStart_3176759 baseEnd_3176759 := by
    simpa [prefixWord, tailWord_3176759, baseEnd_3176759] using wordTrace_append hprefix tailTrace_3176759
  have hstable : (prefixWord ++ tailWord_3176759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176759).length < 2 ^ (prefixWord ++ tailWord_3176759).sum := by decide
  have hdescent : baseEnd_3176759 < baseStart_3176759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176760 : List Nat := [2, 1, 2, 1, 3, 1, 5, 3, 1, 1, 3]
def baseStart_3176760 : Nat := 118140960795 + 3176760 * 2 ^ 59
def prefixEnd_3176760 : Nat := 4983230072969 + 3 ^ 40 * 3176760 * 2
def baseEnd_3176760 : Nat := 1631204803977096145590353

theorem tailTrace_3176760 : CollatzResearch.WordTrace tailWord_3176760 prefixEnd_3176760 1631204803977096145590353 := by
  unfold tailWord_3176760
  simp only [CollatzResearch.WordTrace]
  refine ⟨57932977985574271129351867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77243970647432361505802489 57932977985574271129351867)
  ·
    refine ⟨86899466978361406694027801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57932977985574271129351867 86899466978361406694027801)
    ·
      refine ⟨65174600233771055020520851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86899466978361406694027801 65174600233771055020520851)
      ·
        refine ⟨97761900350656582530781277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65174600233771055020520851 97761900350656582530781277)
        ·
          refine ⟨36660712631496218449042979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97761900350656582530781277 36660712631496218449042979)
          ·
            refine ⟨54991068947244327673564469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36660712631496218449042979 54991068947244327673564469)
            ·
              refine ⟨5155412713804155719396669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54991068947244327673564469 5155412713804155719396669)
              ·
                refine ⟨1933279767676558394773751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5155412713804155719396669 1933279767676558394773751)
                ·
                  refine ⟨2899919651514837592160627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1933279767676558394773751 2899919651514837592160627)
                  ·
                    refine ⟨4349879477272256388240941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2899919651514837592160627 4349879477272256388240941)
                    ·
                      refine ⟨1631204803977096145590353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4349879477272256388240941 1631204803977096145590353)
                      ·
                        rfl

theorem cell23_3176760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 3, 1, 1, 3].length) (baseStart_3176760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176760 prefixEnd_3176760 := by exact prefixLift 3176760
  have htrace : WordTrace (prefixWord ++ tailWord_3176760) baseStart_3176760 baseEnd_3176760 := by
    simpa [prefixWord, tailWord_3176760, baseEnd_3176760] using wordTrace_append hprefix tailTrace_3176760
  have hstable : (prefixWord ++ tailWord_3176760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176760).length < 2 ^ (prefixWord ++ tailWord_3176760).sum := by decide
  have hdescent : baseEnd_3176760 < baseStart_3176760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176776 : List Nat := [2, 1, 3, 1, 1, 2, 4, 1, 4, 4]
def baseStart_3176776 : Nat := 118140960795 + 3176776 * 2 ^ 59
def prefixEnd_3176776 : Nat := 4983230072969 + 3 ^ 40 * 3176776 * 2
def baseEnd_3176776 : Nat := 543737673222522694330093

theorem tailTrace_3176776 : CollatzResearch.WordTrace tailWord_3176776 prefixEnd_3176776 543737673222522694330093 := by
  unfold tailWord_3176776
  simp only [CollatzResearch.WordTrace]
  refine ⟨57933269769545288495643091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77244359692727051327524121 57933269769545288495643091)
  ·
    refine ⟨86899904654317932743464637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57933269769545288495643091 86899904654317932743464637)
    ·
      refine ⟨32587464245369224778799239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86899904654317932743464637 32587464245369224778799239)
      ·
        refine ⟨48881196368053837168198859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32587464245369224778799239 48881196368053837168198859)
        ·
          refine ⟨73321794552080755752298289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48881196368053837168198859 73321794552080755752298289)
          ·
            refine ⟨54991345914060566814223717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73321794552080755752298289 54991345914060566814223717)
            ·
              refine ⟨10310877358886356277666947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54991345914060566814223717 10310877358886356277666947)
              ·
                refine ⟨15466316038329534416500421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10310877358886356277666947 15466316038329534416500421)
                ·
                  refine ⟨2899934257186787703093829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15466316038329534416500421 2899934257186787703093829)
                  ·
                    refine ⟨543737673222522694330093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2899934257186787703093829 543737673222522694330093)
                    ·
                      rfl

theorem cell23_3176776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 4, 4].length) (baseStart_3176776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176776 prefixEnd_3176776 := by exact prefixLift 3176776
  have htrace : WordTrace (prefixWord ++ tailWord_3176776) baseStart_3176776 baseEnd_3176776 := by
    simpa [prefixWord, tailWord_3176776, baseEnd_3176776] using wordTrace_append hprefix tailTrace_3176776
  have hstable : (prefixWord ++ tailWord_3176776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176776).length < 2 ^ (prefixWord ++ tailWord_3176776).sum := by decide
  have hdescent : baseEnd_3176776 < baseStart_3176776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176779 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 4]
def baseStart_3176779 : Nat := 118140960795 + 3176779 * 2 ^ 59
def prefixEnd_3176779 : Nat := 4983230072969 + 3 ^ 40 * 3176779 * 2
def baseEnd_3176779 : Nat := 1631214560109531571252765

theorem tailTrace_3176779 : CollatzResearch.WordTrace tailWord_3176779 prefixEnd_3176779 1631214560109531571252765 := by
  unfold tailWord_3176779
  simp only [CollatzResearch.WordTrace]
  refine ⟨115866648958079708503645391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77244432638719805669096927 115866648958079708503645391)
  ·
    refine ⟨173799973437119562755468087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115866648958079708503645391 173799973437119562755468087)
    ·
      refine ⟨260699960155679344133202131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173799973437119562755468087 260699960155679344133202131)
      ·
        refine ⟨391049940233519016199803197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260699960155679344133202131 391049940233519016199803197)
        ·
          refine ⟨146643727587569631074926199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 391049940233519016199803197 146643727587569631074926199)
          ·
            refine ⟨219965591381354446612389299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146643727587569631074926199 219965591381354446612389299)
            ·
              refine ⟨329948387072031669918583949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219965591381354446612389299 329948387072031669918583949)
              ·
                refine ⟨123730645152011876219468981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 329948387072031669918583949 123730645152011876219468981)
                ·
                  refine ⟨11599747983001113395575217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 123730645152011876219468981 11599747983001113395575217)
                  ·
                    refine ⟨8699810987250835046681413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11599747983001113395575217 8699810987250835046681413)
                    ·
                      refine ⟨1631214560109531571252765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8699810987250835046681413 1631214560109531571252765)
                      ·
                        rfl

theorem cell23_3176779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 4].length) (baseStart_3176779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176779 prefixEnd_3176779 := by exact prefixLift 3176779
  have htrace : WordTrace (prefixWord ++ tailWord_3176779) baseStart_3176779 baseEnd_3176779 := by
    simpa [prefixWord, tailWord_3176779, baseEnd_3176779] using wordTrace_append hprefix tailTrace_3176779
  have hstable : (prefixWord ++ tailWord_3176779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176779).length < 2 ^ (prefixWord ++ tailWord_3176779).sum := by decide
  have hdescent : baseEnd_3176779 < baseStart_3176779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176783 : List Nat := [1, 1, 2, 1, 1, 2, 1, 7, 3, 2, 2]
def baseStart_3176783 : Nat := 118140960795 + 3176783 * 2 ^ 59
def prefixEnd_3176783 : Nat := 4983230072969 + 3 ^ 40 * 3176783 * 2
def baseEnd_3176783 : Nat := 1631216614032149555602747

theorem tailTrace_3176783 : CollatzResearch.WordTrace tailWord_3176783 prefixEnd_3176783 1631216614032149555602747 := by
  unfold tailWord_3176783
  simp only [CollatzResearch.WordTrace]
  refine ⟨115866794850065217186791003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77244529900043478124527335 115866794850065217186791003)
  ·
    refine ⟨173800192275097825780186505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115866794850065217186791003 173800192275097825780186505)
    ·
      refine ⟨130350144206323369335139879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173800192275097825780186505 130350144206323369335139879)
      ·
        refine ⟨195525216309485054002709819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130350144206323369335139879 195525216309485054002709819)
        ·
          refine ⟨293287824464227581004064729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195525216309485054002709819 293287824464227581004064729)
          ·
            refine ⟨219965868348170685753048547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293287824464227581004064729 219965868348170685753048547)
            ·
              refine ⟨329948802522256028629572821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219965868348170685753048547 329948802522256028629572821)
              ·
                refine ⟨7733175059115375671005613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 329948802522256028629572821 7733175059115375671005613)
                ·
                  refine ⟨2899940647168265876627105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7733175059115375671005613 2899940647168265876627105)
                  ·
                    refine ⟨2174955485376199407470329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2899940647168265876627105 2174955485376199407470329)
                    ·
                      refine ⟨1631216614032149555602747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2174955485376199407470329 1631216614032149555602747)
                      ·
                        rfl

theorem cell23_3176783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 3, 2, 2].length) (baseStart_3176783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176783 prefixEnd_3176783 := by exact prefixLift 3176783
  have htrace : WordTrace (prefixWord ++ tailWord_3176783) baseStart_3176783 baseEnd_3176783 := by
    simpa [prefixWord, tailWord_3176783, baseEnd_3176783] using wordTrace_append hprefix tailTrace_3176783
  have hstable : (prefixWord ++ tailWord_3176783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176783).length < 2 ^ (prefixWord ++ tailWord_3176783).sum := by decide
  have hdescent : baseEnd_3176783 < baseStart_3176783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176786 : List Nat := [3, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5]
def baseStart_3176786 : Nat := 118140960795 + 3176786 * 2 ^ 59
def prefixEnd_3176786 : Nat := 4983230072969 + 3 ^ 40 * 3176786 * 2
def baseEnd_3176786 : Nat := 1631218154474113043865233

theorem tailTrace_3176786 : CollatzResearch.WordTrace tailWord_3176786 prefixEnd_3176786 1631218154474113043865233 := by
  unfold tailWord_3176786
  simp only [CollatzResearch.WordTrace]
  refine ⟨28966726067263587174787553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77244602846036232466100141 28966726067263587174787553)
  ·
    refine ⟨21725044550447690381090665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28966726067263587174787553 21725044550447690381090665)
    ·
      refine ⟨16293783412835767785817999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21725044550447690381090665 16293783412835767785817999)
      ·
        refine ⟨24440675119253651678726999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16293783412835767785817999 24440675119253651678726999)
        ·
          refine ⟨36661012678880477518090499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24440675119253651678726999 36661012678880477518090499)
          ·
            refine ⟨54991519018320716277135749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36661012678880477518090499 54991519018320716277135749)
            ·
              refine ⟨10310909815935134301962953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54991519018320716277135749 10310909815935134301962953)
              ·
                refine ⟨7733182361951350726472215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10310909815935134301962953 7733182361951350726472215)
                ·
                  refine ⟨11599773542927026089708323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7733182361951350726472215 11599773542927026089708323)
                  ·
                    refine ⟨17399660314390539134562485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11599773542927026089708323 17399660314390539134562485)
                    ·
                      refine ⟨1631218154474113043865233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17399660314390539134562485 1631218154474113043865233)
                      ·
                        rfl

theorem cell23_3176786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_3176786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176786 prefixEnd_3176786 := by exact prefixLift 3176786
  have htrace : WordTrace (prefixWord ++ tailWord_3176786) baseStart_3176786 baseEnd_3176786 := by
    simpa [prefixWord, tailWord_3176786, baseEnd_3176786] using wordTrace_append hprefix tailTrace_3176786
  have hstable : (prefixWord ++ tailWord_3176786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176786).length < 2 ^ (prefixWord ++ tailWord_3176786).sum := by decide
  have hdescent : baseEnd_3176786 < baseStart_3176786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176800 : List Nat := [2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 4]
def baseStart_3176800 : Nat := 118140960795 + 3176800 * 2 ^ 59
def prefixEnd_3176800 : Nat := 4983230072969 + 3 ^ 40 * 3176800 * 2
def baseEnd_3176800 : Nat := 1631225343203275989090169

theorem tailTrace_3176800 : CollatzResearch.WordTrace tailWord_3176800 prefixEnd_3176800 1631225343203275989090169 := by
  unfold tailWord_3176800
  simp only [CollatzResearch.WordTrace]
  refine ⟨57933707445501814545079927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77244943260669086060106569 57933707445501814545079927)
  ·
    refine ⟨86900561168252721817619891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57933707445501814545079927 86900561168252721817619891)
    ·
      refine ⟨130350841752379082726429837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86900561168252721817619891 130350841752379082726429837)
      ·
        refine ⟨48881565657142156022411189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130350841752379082726429837 48881565657142156022411189)
        ·
          refine ⟨4582646780357077127101049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48881565657142156022411189 4582646780357077127101049)
          ·
            refine ⟨3436985085267807845325787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4582646780357077127101049 3436985085267807845325787)
            ·
              refine ⟨5155477627901711767988681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3436985085267807845325787 5155477627901711767988681)
              ·
                refine ⟨3866608220926283825991511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5155477627901711767988681 3866608220926283825991511)
                ·
                  refine ⟨5799912331389425738987267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3866608220926283825991511 5799912331389425738987267)
                  ·
                    refine ⟨8699868497084138608480901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5799912331389425738987267 8699868497084138608480901)
                    ·
                      refine ⟨1631225343203275989090169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8699868497084138608480901 1631225343203275989090169)
                      ·
                        rfl

theorem cell23_3176800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 4].length) (baseStart_3176800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176800 prefixEnd_3176800 := by exact prefixLift 3176800
  have htrace : WordTrace (prefixWord ++ tailWord_3176800) baseStart_3176800 baseEnd_3176800 := by
    simpa [prefixWord, tailWord_3176800, baseEnd_3176800] using wordTrace_append hprefix tailTrace_3176800
  have hstable : (prefixWord ++ tailWord_3176800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176800).length < 2 ^ (prefixWord ++ tailWord_3176800).sum := by decide
  have hdescent : baseEnd_3176800 < baseStart_3176800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176816 : List Nat := [2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 3]
def baseStart_3176816 : Nat := 118140960795 + 3176816 * 2 ^ 59
def prefixEnd_3176816 : Nat := 4983230072969 + 3 ^ 40 * 3176816 * 2
def baseEnd_3176816 : Nat := 1631233558893747926490095

theorem tailTrace_3176816 : CollatzResearch.WordTrace tailWord_3176816 prefixEnd_3176816 1631233558893747926490095 := by
  unfold tailWord_3176816
  simp only [CollatzResearch.WordTrace]
  refine ⟨57933999229472831911371151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77245332305963775881828201 57933999229472831911371151)
  ·
    refine ⟨86900998844209247867056727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57933999229472831911371151 86900998844209247867056727)
    ·
      refine ⟨130351498266313871800585091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86900998844209247867056727 130351498266313871800585091)
      ·
        refine ⟨195527247399470807700877637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130351498266313871800585091 195527247399470807700877637)
        ·
          refine ⟨36661358887400776443914557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195527247399470807700877637 36661358887400776443914557)
          ·
            refine ⟨13748009582775291166467959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36661358887400776443914557 13748009582775291166467959)
            ·
              refine ⟨20622014374162936749701939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13748009582775291166467959 20622014374162936749701939)
              ·
                refine ⟨30933021561244405124552909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20622014374162936749701939 30933021561244405124552909)
                ·
                  refine ⟨11599883085466651921707341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30933021561244405124552909 11599883085466651921707341)
                  ·
                    refine ⟨4349956157049994470640253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11599883085466651921707341 4349956157049994470640253)
                    ·
                      refine ⟨1631233558893747926490095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4349956157049994470640253 1631233558893747926490095)
                      ·
                        rfl

theorem cell23_3176816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 3].length) (baseStart_3176816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176816 prefixEnd_3176816 := by exact prefixLift 3176816
  have htrace : WordTrace (prefixWord ++ tailWord_3176816) baseStart_3176816 baseEnd_3176816 := by
    simpa [prefixWord, tailWord_3176816, baseEnd_3176816] using wordTrace_append hprefix tailTrace_3176816
  have hstable : (prefixWord ++ tailWord_3176816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176816).length < 2 ^ (prefixWord ++ tailWord_3176816).sum := by decide
  have hdescent : baseEnd_3176816 < baseStart_3176816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176843 : List Nat := [1, 1, 1, 1, 4, 4, 1, 2, 3, 3, 2]
def baseStart_3176843 : Nat := 118140960795 + 3176843 * 2 ^ 59
def prefixEnd_3176843 : Nat := 4983230072969 + 3 ^ 40 * 3176843 * 2
def baseEnd_3176843 : Nat := 1631247422871419320852471

theorem tailTrace_3176843 : CollatzResearch.WordTrace tailWord_3176843 prefixEnd_3176843 1631247422871419320852471 := by
  unfold tailWord_3176843
  simp only [CollatzResearch.WordTrace]
  refine ⟨115868983229847847433975183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77245988819898564955983455 115868983229847847433975183)
  ·
    refine ⟨173803474844771771150962775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115868983229847847433975183 173803474844771771150962775)
    ·
      refine ⟨260705212267157656726444163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173803474844771771150962775 260705212267157656726444163)
      ·
        refine ⟨391057818400736485089666245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260705212267157656726444163 391057818400736485089666245)
        ·
          refine ⟨73323340950138090954312421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 391057818400736485089666245 73323340950138090954312421)
          ·
            refine ⟨13748126428150892053933579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73323340950138090954312421 13748126428150892053933579)
            ·
              refine ⟨20622189642226338080900369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13748126428150892053933579 20622189642226338080900369)
              ·
                refine ⟨15466642231669753560675277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20622189642226338080900369 15466642231669753560675277)
                ·
                  refine ⟨5799990836876157585253229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15466642231669753560675277 5799990836876157585253229)
                  ·
                    refine ⟨2174996563828559094469961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5799990836876157585253229 2174996563828559094469961)
                    ·
                      refine ⟨1631247422871419320852471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2174996563828559094469961 1631247422871419320852471)
                      ·
                        rfl

theorem cell23_3176843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 3, 2].length) (baseStart_3176843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176843 prefixEnd_3176843 := by exact prefixLift 3176843
  have htrace : WordTrace (prefixWord ++ tailWord_3176843) baseStart_3176843 baseEnd_3176843 := by
    simpa [prefixWord, tailWord_3176843, baseEnd_3176843] using wordTrace_append hprefix tailTrace_3176843
  have hstable : (prefixWord ++ tailWord_3176843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176843).length < 2 ^ (prefixWord ++ tailWord_3176843).sum := by decide
  have hdescent : baseEnd_3176843 < baseStart_3176843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176859 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 5]
def baseStart_3176859 : Nat := 118140960795 + 3176859 * 2 ^ 59
def prefixEnd_3176859 : Nat := 4983230072969 + 3 ^ 40 * 3176859 * 2
def baseEnd_3176859 : Nat := 1631255638561891258252397

theorem tailTrace_3176859 : CollatzResearch.WordTrace tailWord_3176859 prefixEnd_3176859 1631255638561891258252397 := by
  unfold tailWord_3176859
  simp only [CollatzResearch.WordTrace]
  refine ⟨115869566797789882166557631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77246377865193254777705087 115869566797789882166557631)
  ·
    refine ⟨173804350196684823249836447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115869566797789882166557631 173804350196684823249836447)
    ·
      refine ⟨260706525295027234874754671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173804350196684823249836447 260706525295027234874754671)
      ·
        refine ⟨391059787942540852312132007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260706525295027234874754671 391059787942540852312132007)
        ·
          refine ⟨586589681913811278468198011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391059787942540852312132007 586589681913811278468198011)
          ·
            refine ⟨879884522870716917702297017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 586589681913811278468198011 879884522870716917702297017)
            ·
              refine ⟨659913392153037688276722763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 879884522870716917702297017 659913392153037688276722763)
              ·
                refine ⟨989870088229556532415084145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 659913392153037688276722763 989870088229556532415084145)
                ·
                  refine ⟨742402566172167399311313109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 989870088229556532415084145 742402566172167399311313109)
                  ·
                    refine ⟨17400060144660173421358901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 742402566172167399311313109 17400060144660173421358901)
                    ·
                      refine ⟨1631255638561891258252397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17400060144660173421358901 1631255638561891258252397)
                      ·
                        rfl

theorem cell23_3176859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 5].length) (baseStart_3176859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176859 prefixEnd_3176859 := by exact prefixLift 3176859
  have htrace : WordTrace (prefixWord ++ tailWord_3176859) baseStart_3176859 baseEnd_3176859 := by
    simpa [prefixWord, tailWord_3176859, baseEnd_3176859] using wordTrace_append hprefix tailTrace_3176859
  have hstable : (prefixWord ++ tailWord_3176859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176859).length < 2 ^ (prefixWord ++ tailWord_3176859).sum := by decide
  have hdescent : baseEnd_3176859 < baseStart_3176859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176866 : List Nat := [3, 3, 1, 2, 1, 1, 1, 2, 1, 8]
def baseStart_3176866 : Nat := 118140960795 + 3176866 * 2 ^ 59
def prefixEnd_3176866 : Nat := 4983230072969 + 3 ^ 40 * 3176866 * 2
def baseEnd_3176866 : Nat := 543753077642157576954955

theorem tailTrace_3176866 : CollatzResearch.WordTrace tailWord_3176866 prefixEnd_3176866 543753077642157576954955 := by
  unfold tailWord_3176866
  simp only [CollatzResearch.WordTrace]
  refine ⟨28967455527191130590515613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77246548072509681574708301 28967455527191130590515613)
  ·
    refine ⟨10862795822696673971443355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28967455527191130590515613 10862795822696673971443355)
    ·
      refine ⟨16294193734045010957165033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10862795822696673971443355 16294193734045010957165033)
      ·
        refine ⟨12220645300533758217873775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16294193734045010957165033 12220645300533758217873775)
        ·
          refine ⟨18330967950800637326810663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12220645300533758217873775 18330967950800637326810663)
          ·
            refine ⟨27496451926200955990215995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18330967950800637326810663 27496451926200955990215995)
            ·
              refine ⟨41244677889301433985323993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27496451926200955990215995 41244677889301433985323993)
              ·
                refine ⟨30933508416976075488992995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41244677889301433985323993 30933508416976075488992995)
                ·
                  refine ⟨46400262625464113233489493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30933508416976075488992995 46400262625464113233489493)
                  ·
                    refine ⟨543753077642157576954955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 46400262625464113233489493 543753077642157576954955)
                    ·
                      rfl

theorem cell23_3176866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_3176866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176866 prefixEnd_3176866 := by exact prefixLift 3176866
  have htrace : WordTrace (prefixWord ++ tailWord_3176866) baseStart_3176866 baseEnd_3176866 := by
    simpa [prefixWord, tailWord_3176866, baseEnd_3176866] using wordTrace_append hprefix tailTrace_3176866
  have hstable : (prefixWord ++ tailWord_3176866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176866).length < 2 ^ (prefixWord ++ tailWord_3176866).sum := by decide
  have hdescent : baseEnd_3176866 < baseStart_3176866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176884 : List Nat := [2, 5, 2, 2, 1, 1, 1, 1, 4, 1, 3]
def baseStart_3176884 : Nat := 118140960795 + 3176884 * 2 ^ 59
def prefixEnd_3176884 : Nat := 4983230072969 + 3 ^ 40 * 3176884 * 2
def baseEnd_3176884 : Nat := 1631268475578253660439783

theorem tailTrace_3176884 : CollatzResearch.WordTrace tailWord_3176884 prefixEnd_3176884 1631268475578253660439783 := by
  unfold tailWord_3176884
  simp only [CollatzResearch.WordTrace]
  refine ⟨57935239311349655718108853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77246985748466207624145137 57935239311349655718108853)
  ·
    refine ⟨5431428685439030223572705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57935239311349655718108853 5431428685439030223572705)
    ·
      refine ⟨4073571514079272667679529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5431428685439030223572705 4073571514079272667679529)
      ·
        refine ⟨3055178635559454500759647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4073571514079272667679529 3055178635559454500759647)
        ·
          refine ⟨4582767953339181751139471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3055178635559454500759647 4582767953339181751139471)
          ·
            refine ⟨6874151930008772626709207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4582767953339181751139471 6874151930008772626709207)
            ·
              refine ⟨10311227895013158940063811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6874151930008772626709207 10311227895013158940063811)
              ·
                refine ⟨15466841842519738410095717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10311227895013158940063811 15466841842519738410095717)
                ·
                  refine ⟨2900032845472450951892947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15466841842519738410095717 2900032845472450951892947)
                  ·
                    refine ⟨4350049268208676427839421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2900032845472450951892947 4350049268208676427839421)
                    ·
                      refine ⟨1631268475578253660439783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4350049268208676427839421 1631268475578253660439783)
                      ·
                        rfl

theorem cell23_3176884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_3176884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176884 prefixEnd_3176884 := by exact prefixLift 3176884
  have htrace : WordTrace (prefixWord ++ tailWord_3176884) baseStart_3176884 baseEnd_3176884 := by
    simpa [prefixWord, tailWord_3176884, baseEnd_3176884] using wordTrace_append hprefix tailTrace_3176884
  have hstable : (prefixWord ++ tailWord_3176884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176884).length < 2 ^ (prefixWord ++ tailWord_3176884).sum := by decide
  have hdescent : baseEnd_3176884 < baseStart_3176884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176950 : List Nat := [5, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2]
def baseStart_3176950 : Nat := 118140960795 + 3176950 * 2 ^ 59
def prefixEnd_3176950 : Nat := 4983230072969 + 3 ^ 40 * 3176950 * 2
def baseEnd_3176950 : Nat := 1631302365301450402214479

theorem tailTrace_3176950 : CollatzResearch.WordTrace tailWord_3176950 prefixEnd_3176950 1631302365301450402214479 := by
  unfold tailWord_3176950
  simp only [CollatzResearch.WordTrace]
  refine ⟨7242055365028762794257519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77248590560306803138746869 7242055365028762794257519)
  ·
    refine ⟨10863083047543144191386279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7242055365028762794257519 10863083047543144191386279)
    ·
      refine ⟨16294624571314716287079419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10863083047543144191386279 16294624571314716287079419)
      ·
        refine ⟨24441936856972074430619129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16294624571314716287079419 24441936856972074430619129)
        ·
          refine ⟨18331452642729055822964347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24441936856972074430619129 18331452642729055822964347)
          ·
            refine ⟨27497178964093583734446521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18331452642729055822964347 27497178964093583734446521)
            ·
              refine ⟨20622884223070187800834891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27497178964093583734446521 20622884223070187800834891)
              ·
                refine ⟨30934326334605281701252337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20622884223070187800834891 30934326334605281701252337)
                ·
                  refine ⟨23200744750953961275939253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30934326334605281701252337 23200744750953961275939253)
                  ·
                    refine ⟨2175069820401933869619305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23200744750953961275939253 2175069820401933869619305)
                    ·
                      refine ⟨1631302365301450402214479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2175069820401933869619305 1631302365301450402214479)
                      ·
                        rfl

theorem cell23_3176950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_3176950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176950 prefixEnd_3176950 := by exact prefixLift 3176950
  have htrace : WordTrace (prefixWord ++ tailWord_3176950) baseStart_3176950 baseEnd_3176950 := by
    simpa [prefixWord, tailWord_3176950, baseEnd_3176950] using wordTrace_append hprefix tailTrace_3176950
  have hstable : (prefixWord ++ tailWord_3176950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176950).length < 2 ^ (prefixWord ++ tailWord_3176950).sum := by decide
  have hdescent : baseEnd_3176950 < baseStart_3176950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176963 : List Nat := [1, 1, 1, 3, 2, 1, 4, 1, 1, 6, 2]
def baseStart_3176963 : Nat := 118140960795 + 3176963 * 2 ^ 59
def prefixEnd_3176963 : Nat := 4983230072969 + 3 ^ 40 * 3176963 * 2
def baseEnd_3176963 : Nat := 1631309040549958851351919

theorem tailTrace_3176963 : CollatzResearch.WordTrace tailWord_3176963 prefixEnd_3176963 1631309040549958851351919 := by
  unfold tailWord_3176963
  simp only [CollatzResearch.WordTrace]
  refine ⟨115873359989413107928343543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77248906659608738618895695 115873359989413107928343543)
  ·
    refine ⟨173810039984119661892515315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115873359989413107928343543 173810039984119661892515315)
    ·
      refine ⟨260715059976179492838772973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173810039984119661892515315 260715059976179492838772973)
      ·
        refine ⟨97768147491067309814539865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260715059976179492838772973 97768147491067309814539865)
        ·
          refine ⟨73326110618300482360904899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97768147491067309814539865 73326110618300482360904899)
          ·
            refine ⟨109989165927450723541357349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73326110618300482360904899 109989165927450723541357349)
            ·
              refine ⟨20622968611397010664004503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109989165927450723541357349 20622968611397010664004503)
              ·
                refine ⟨30934452917095515996006755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20622968611397010664004503 30934452917095515996006755)
                ·
                  refine ⟨46401679375643273994010133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30934452917095515996006755 46401679375643273994010133)
                  ·
                    refine ⟨2175078720733278468469225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 46401679375643273994010133 2175078720733278468469225)
                    ·
                      refine ⟨1631309040549958851351919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2175078720733278468469225 1631309040549958851351919)
                      ·
                        rfl

theorem cell23_3176963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 6, 2].length) (baseStart_3176963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176963 prefixEnd_3176963 := by exact prefixLift 3176963
  have htrace : WordTrace (prefixWord ++ tailWord_3176963) baseStart_3176963 baseEnd_3176963 := by
    simpa [prefixWord, tailWord_3176963, baseEnd_3176963] using wordTrace_append hprefix tailTrace_3176963
  have hstable : (prefixWord ++ tailWord_3176963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176963).length < 2 ^ (prefixWord ++ tailWord_3176963).sum := by decide
  have hdescent : baseEnd_3176963 < baseStart_3176963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176986 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 10]
def baseStart_3176986 : Nat := 118140960795 + 3176986 * 2 ^ 59
def prefixEnd_3176986 : Nat := 4983230072969 + 3 ^ 40 * 3176986 * 2
def baseEnd_3176986 : Nat := 181257872289445806818257

theorem tailTrace_3176986 : CollatzResearch.WordTrace tailWord_3176986 prefixEnd_3176986 181257872289445806818257 := by
  unfold tailWord_3176986
  simp only [CollatzResearch.WordTrace]
  refine ⟨28968549717082445714107703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77249465912219855237620541 28968549717082445714107703)
  ·
    refine ⟨43452824575623668571161555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28968549717082445714107703 43452824575623668571161555)
    ·
      refine ⟨65179236863435502856742333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43452824575623668571161555 65179236863435502856742333)
      ·
        refine ⟨24442213823788313571278375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65179236863435502856742333 24442213823788313571278375)
        ·
          refine ⟨36663320735682470356917563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24442213823788313571278375 36663320735682470356917563)
          ·
            refine ⟨54994981103523705535376345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36663320735682470356917563 54994981103523705535376345)
            ·
              refine ⟨41246235827642779151532259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54994981103523705535376345 41246235827642779151532259)
              ·
                refine ⟨61869353741464168727298389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41246235827642779151532259 61869353741464168727298389)
                ·
                  refine ⟨181257872289445806818257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 61869353741464168727298389 181257872289445806818257)
                  ·
                    rfl

theorem cell23_3176986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 10].length) (baseStart_3176986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3176986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3176986 prefixEnd_3176986 := by exact prefixLift 3176986
  have htrace : WordTrace (prefixWord ++ tailWord_3176986) baseStart_3176986 baseEnd_3176986 := by
    simpa [prefixWord, tailWord_3176986, baseEnd_3176986] using wordTrace_append hprefix tailTrace_3176986
  have hstable : (prefixWord ++ tailWord_3176986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176986).length < 2 ^ (prefixWord ++ tailWord_3176986).sum := by decide
  have hdescent : baseEnd_3176986 < baseStart_3176986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177040 : List Nat := [2, 1, 1, 1, 1, 3, 2, 5, 2, 3, 2]
def baseStart_3177040 : Nat := 118140960795 + 3177040 * 2 ^ 59
def prefixEnd_3177040 : Nat := 4983230072969 + 3 ^ 40 * 3177040 * 2
def baseEnd_3177040 : Nat := 1631348578560355050089065

theorem tailTrace_3177040 : CollatzResearch.WordTrace tailWord_3177040 prefixEnd_3177040 1631348578560355050089065 := by
  unfold tailWord_3177040
  simp only [CollatzResearch.WordTrace]
  refine ⟨57938084205067075039448287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77250778940089433385931049 57938084205067075039448287)
  ·
    refine ⟨86907126307600612559172431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57938084205067075039448287 86907126307600612559172431)
    ·
      refine ⟨130360689461400918838758647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86907126307600612559172431 130360689461400918838758647)
      ·
        refine ⟨195541034192101378258137971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130360689461400918838758647 195541034192101378258137971)
        ·
          refine ⟨293311551288152067387206957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195541034192101378258137971 293311551288152067387206957)
          ·
            refine ⟨109991831733057025270202609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 293311551288152067387206957 109991831733057025270202609)
            ·
              refine ⟨82493873799792768952651957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109991831733057025270202609 82493873799792768952651957)
              ·
                refine ⟨7733800668730572089311121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82493873799792768952651957 7733800668730572089311121)
                ·
                  refine ⟨5800350501547929066983341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7733800668730572089311121 5800350501547929066983341)
                  ·
                    refine ⟨2175131438080473400118753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5800350501547929066983341 2175131438080473400118753)
                    ·
                      refine ⟨1631348578560355050089065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2175131438080473400118753 1631348578560355050089065)
                      ·
                        rfl

theorem cell23_3177040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 2, 3, 2].length) (baseStart_3177040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177040 prefixEnd_3177040 := by exact prefixLift 3177040
  have htrace : WordTrace (prefixWord ++ tailWord_3177040) baseStart_3177040 baseEnd_3177040 := by
    simpa [prefixWord, tailWord_3177040, baseEnd_3177040] using wordTrace_append hprefix tailTrace_3177040
  have hstable : (prefixWord ++ tailWord_3177040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177040).length < 2 ^ (prefixWord ++ tailWord_3177040).sum := by decide
  have hdescent : baseEnd_3177040 < baseStart_3177040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177054 : List Nat := [4, 4, 1, 2, 1, 1, 1, 1, 8]
def baseStart_3177054 : Nat := 118140960795 + 3177054 * 2 ^ 59
def prefixEnd_3177054 : Nat := 4983230072969 + 3 ^ 40 * 3177054 * 2
def baseEnd_3177054 : Nat := 181261751921057555034889

theorem tailTrace_3177054 : CollatzResearch.WordTrace tailWord_3177054 prefixEnd_3177054 181261751921057555034889 := by
  unfold tailWord_3177054
  simp only [CollatzResearch.WordTrace]
  refine ⟨14484584879010428808738277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77251119354722286979937477 14484584879010428808738277)
  ·
    refine ⟨2715859664814455401638427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14484584879010428808738277 2715859664814455401638427)
    ·
      refine ⟨4073789497221683102457641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2715859664814455401638427 4073789497221683102457641)
      ·
        refine ⟨3055342122916262326843231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4073789497221683102457641 3055342122916262326843231)
        ·
          refine ⟨4583013184374393490264847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3055342122916262326843231 4583013184374393490264847)
          ·
            refine ⟨6874519776561590235397271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4583013184374393490264847 6874519776561590235397271)
            ·
              refine ⟨10311779664842385353095907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6874519776561590235397271 10311779664842385353095907)
              ·
                refine ⟨15467669497263578029643861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10311779664842385353095907 15467669497263578029643861)
                ·
                  refine ⟨181261751921057555034889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15467669497263578029643861 181261751921057555034889)
                  ·
                    rfl

theorem cell23_3177054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_3177054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177054 prefixEnd_3177054 := by exact prefixLift 3177054
  have htrace : WordTrace (prefixWord ++ tailWord_3177054) baseStart_3177054 baseEnd_3177054 := by
    simpa [prefixWord, tailWord_3177054, baseEnd_3177054] using wordTrace_append hprefix tailTrace_3177054
  have hstable : (prefixWord ++ tailWord_3177054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177054).length < 2 ^ (prefixWord ++ tailWord_3177054).sum := by decide
  have hdescent : baseEnd_3177054 < baseStart_3177054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177064 : List Nat := [2, 1, 4, 3, 2, 1, 2, 1, 3, 1, 3]
def baseStart_3177064 : Nat := 118140960795 + 3177064 * 2 ^ 59
def prefixEnd_3177064 : Nat := 4983230072969 + 3 ^ 40 * 3177064 * 2
def baseEnd_3177064 : Nat := 1631360902096062956188955

theorem tailTrace_3177064 : CollatzResearch.WordTrace tailWord_3177064 prefixEnd_3177064 1631360902096062956188955 := by
  unfold tailWord_3177064
  simp only [CollatzResearch.WordTrace]
  refine ⟨57938521881023601088885123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77251362508031468118513497 57938521881023601088885123)
  ·
    refine ⟨86907782821535401633327685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57938521881023601088885123 86907782821535401633327685)
    ·
      refine ⟨16295209279037887806248941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86907782821535401633327685 16295209279037887806248941)
      ·
        refine ⟨6110703479639207927343353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16295209279037887806248941 6110703479639207927343353)
        ·
          refine ⟨4583027609729405945507515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6110703479639207927343353 4583027609729405945507515)
          ·
            refine ⟨6874541414594108918261273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4583027609729405945507515 6874541414594108918261273)
            ·
              refine ⟨5155906060945581688695955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6874541414594108918261273 5155906060945581688695955)
              ·
                refine ⟨7733859091418372533043933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5155906060945581688695955 7733859091418372533043933)
                ·
                  refine ⟨2900197159281889699891475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7733859091418372533043933 2900197159281889699891475)
                  ·
                    refine ⟨4350295738922834549837213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2900197159281889699891475 4350295738922834549837213)
                    ·
                      refine ⟨1631360902096062956188955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4350295738922834549837213 1631360902096062956188955)
                      ·
                        rfl

theorem cell23_3177064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_3177064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177064 prefixEnd_3177064 := by exact prefixLift 3177064
  have htrace : WordTrace (prefixWord ++ tailWord_3177064) baseStart_3177064 baseEnd_3177064 := by
    simpa [prefixWord, tailWord_3177064, baseEnd_3177064] using wordTrace_append hprefix tailTrace_3177064
  have hstable : (prefixWord ++ tailWord_3177064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177064).length < 2 ^ (prefixWord ++ tailWord_3177064).sum := by decide
  have hdescent : baseEnd_3177064 < baseStart_3177064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177083 : List Nat := [1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 4]
def baseStart_3177083 : Nat := 118140960795 + 3177083 * 2 ^ 59
def prefixEnd_3177083 : Nat := 4983230072969 + 3 ^ 40 * 3177083 * 2
def baseEnd_3177083 : Nat := 1631370658228498381851367

theorem tailTrace_3177083 : CollatzResearch.WordTrace tailWord_3177083 prefixEnd_3177083 1631370658228498381851367 := by
  unfold tailWord_3177083
  simp only [CollatzResearch.WordTrace]
  refine ⟨115877736748978368422711903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77251824499318912281807935 115877736748978368422711903)
  ·
    refine ⟨173816605123467552634067855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115877736748978368422711903 173816605123467552634067855)
    ·
      refine ⟨260724907685201328951101783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173816605123467552634067855 260724907685201328951101783)
      ·
        refine ⟨391087361527801993426652675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260724907685201328951101783 391087361527801993426652675)
        ·
          refine ⟨586631042291702990139979013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391087361527801993426652675 586631042291702990139979013)
          ·
            refine ⟨109993320429694310651246065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 586631042291702990139979013 109993320429694310651246065)
            ·
              refine ⟨82494990322270732988434549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109993320429694310651246065 82494990322270732988434549)
              ·
                refine ⟨7733905342712881217665739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82494990322270732988434549 7733905342712881217665739)
                ·
                  refine ⟨11600858014069321826498609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7733905342712881217665739 11600858014069321826498609)
                  ·
                    refine ⟨8700643510551991369873957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11600858014069321826498609 8700643510551991369873957)
                    ·
                      refine ⟨1631370658228498381851367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8700643510551991369873957 1631370658228498381851367)
                      ·
                        rfl

theorem cell23_3177083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 4].length) (baseStart_3177083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177083 prefixEnd_3177083 := by exact prefixLift 3177083
  have htrace : WordTrace (prefixWord ++ tailWord_3177083) baseStart_3177083 baseEnd_3177083 := by
    simpa [prefixWord, tailWord_3177083, baseEnd_3177083] using wordTrace_append hprefix tailTrace_3177083
  have hstable : (prefixWord ++ tailWord_3177083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177083).length < 2 ^ (prefixWord ++ tailWord_3177083).sum := by decide
  have hdescent : baseEnd_3177083 < baseStart_3177083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177093 : List Nat := [1, 3, 1, 1, 4, 3, 1, 9]
def baseStart_3177093 : Nat := 118140960795 + 3177093 * 2 ^ 59
def prefixEnd_3177093 : Nat := 4983230072969 + 3 ^ 40 * 3177093 * 2
def baseEnd_3177093 : Nat := 60421325667964568249123

theorem tailTrace_3177093 : CollatzResearch.WordTrace tailWord_3177093 prefixEnd_3177093 60421325667964568249123 := by
  unfold tailWord_3177093
  simp only [CollatzResearch.WordTrace]
  refine ⟨115878101478942140130575933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77252067652628093420383955 115878101478942140130575933)
  ·
    refine ⟨43454288054603302548965975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115878101478942140130575933 43454288054603302548965975)
    ·
      refine ⟨65181432081904953823448963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43454288054603302548965975 65181432081904953823448963)
      ·
        refine ⟨97772148122857430735173445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65181432081904953823448963 97772148122857430735173445)
        ·
          refine ⟨18332277773035768262845021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97772148122857430735173445 18332277773035768262845021)
          ·
            refine ⟨6874604164888413098566883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18332277773035768262845021 6874604164888413098566883)
            ·
              refine ⟨10311906247332619647850325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6874604164888413098566883 10311906247332619647850325)
              ·
                refine ⟨60421325667964568249123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10311906247332619647850325 60421325667964568249123)
                ·
                  rfl

theorem cell23_3177093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 9].length) (baseStart_3177093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177093 prefixEnd_3177093 := by exact prefixLift 3177093
  have htrace : WordTrace (prefixWord ++ tailWord_3177093) baseStart_3177093 baseEnd_3177093 := by
    simpa [prefixWord, tailWord_3177093, baseEnd_3177093] using wordTrace_append hprefix tailTrace_3177093
  have hstable : (prefixWord ++ tailWord_3177093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177093).length < 2 ^ (prefixWord ++ tailWord_3177093).sum := by decide
  have hdescent : baseEnd_3177093 < baseStart_3177093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177098 : List Nat := [3, 1, 2, 3, 4, 1, 1, 3, 1, 1, 3]
def baseStart_3177098 : Nat := 118140960795 + 3177098 * 2 ^ 59
def prefixEnd_3177098 : Nat := 4983230072969 + 3 ^ 40 * 3177098 * 2
def baseEnd_3177098 : Nat := 1631378360438315823163799

theorem tailTrace_3177098 : CollatzResearch.WordTrace tailWord_3177098 prefixEnd_3177098 1631378360438315823163799 := by
  unfold tailWord_3177098
  simp only [CollatzResearch.WordTrace]
  refine ⟨28969570960981006496126987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77252189229282683989671965 28969570960981006496126987)
  ·
    refine ⟨43454356441471509744190481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28969570960981006496126987 43454356441471509744190481)
    ·
      refine ⟨32590767331103632308142861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43454356441471509744190481 32590767331103632308142861)
      ·
        refine ⟨12221537749163862115553573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32590767331103632308142861 12221537749163862115553573)
        ·
          refine ⟨2291538327968224146666295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12221537749163862115553573 2291538327968224146666295)
          ·
            refine ⟨3437307491952336219999443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2291538327968224146666295 3437307491952336219999443)
            ·
              refine ⟨5155961237928504329999165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3437307491952336219999443 5155961237928504329999165)
              ·
                refine ⟨1933485464223189123749687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5155961237928504329999165 1933485464223189123749687)
                ·
                  refine ⟨2900228196334783685624531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1933485464223189123749687 2900228196334783685624531)
                  ·
                    refine ⟨4350342294502175528436797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2900228196334783685624531 4350342294502175528436797)
                    ·
                      refine ⟨1631378360438315823163799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4350342294502175528436797 1631378360438315823163799)
                      ·
                        rfl

theorem cell23_3177098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_3177098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177098 prefixEnd_3177098 := by exact prefixLift 3177098
  have htrace : WordTrace (prefixWord ++ tailWord_3177098) baseStart_3177098 baseEnd_3177098 := by
    simpa [prefixWord, tailWord_3177098, baseEnd_3177098] using wordTrace_append hprefix tailTrace_3177098
  have hstable : (prefixWord ++ tailWord_3177098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177098).length < 2 ^ (prefixWord ++ tailWord_3177098).sum := by decide
  have hdescent : baseEnd_3177098 < baseStart_3177098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177121 : List Nat := [1, 2, 3, 3, 3, 2, 1, 1, 3, 2, 2]
def baseStart_3177121 : Nat := 118140960795 + 3177121 * 2 ^ 59
def prefixEnd_3177121 : Nat := 4983230072969 + 3 ^ 40 * 3177121 * 2
def baseEnd_3177121 : Nat := 1631390170493369233176193

theorem tailTrace_3177121 : CollatzResearch.WordTrace tailWord_3177121 prefixEnd_3177121 1631390170493369233176193 := by
  unfold tailWord_3177121
  simp only [CollatzResearch.WordTrace]
  refine ⟨115879122722840700912595217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77252748481893800608396811 115879122722840700912595217)
  ·
    refine ⟨86909342042130525684446413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115879122722840700912595217 86909342042130525684446413)
    ·
      refine ⟨32591003265798947131667405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86909342042130525684446413 32591003265798947131667405)
      ·
        refine ⟨12221626224674605174375277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32591003265798947131667405 12221626224674605174375277)
        ·
          refine ⟨4583109834252976940390729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12221626224674605174375277 4583109834252976940390729)
          ·
            refine ⟨3437332375689732705293047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4583109834252976940390729 3437332375689732705293047)
            ·
              refine ⟨5155998563534599057939571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3437332375689732705293047 5155998563534599057939571)
              ·
                refine ⟨7733997845301898586909357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5155998563534599057939571 7733997845301898586909357)
                ·
                  refine ⟨2900249191988211970091009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7733997845301898586909357 2900249191988211970091009)
                  ·
                    refine ⟨2175186893991158977568257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2900249191988211970091009 2175186893991158977568257)
                    ·
                      refine ⟨1631390170493369233176193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2175186893991158977568257 1631390170493369233176193)
                      ·
                        rfl

theorem cell23_3177121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_3177121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177121 prefixEnd_3177121 := by exact prefixLift 3177121
  have htrace : WordTrace (prefixWord ++ tailWord_3177121) baseStart_3177121 baseEnd_3177121 := by
    simpa [prefixWord, tailWord_3177121, baseEnd_3177121] using wordTrace_append hprefix tailTrace_3177121
  have hstable : (prefixWord ++ tailWord_3177121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177121).length < 2 ^ (prefixWord ++ tailWord_3177121).sum := by decide
  have hdescent : baseEnd_3177121 < baseStart_3177121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177127 : List Nat := [1, 1, 6, 3, 1, 1, 2, 8]
def baseStart_3177127 : Nat := 118140960795 + 3177127 * 2 ^ 59
def prefixEnd_3177127 : Nat := 4983230072969 + 3 ^ 40 * 3177127 * 2
def baseEnd_3177127 : Nat := 60421972273233192951895

theorem tailTrace_3177127 : CollatzResearch.WordTrace tailWord_3177127 prefixEnd_3177127 60421972273233192951895 := by
  unfold tailWord_3177127
  simp only [CollatzResearch.WordTrace]
  refine ⟨115879341560818963937313635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77252894373879309291542423 115879341560818963937313635)
  ·
    refine ⟨173819012341228445905970453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115879341560818963937313635 173819012341228445905970453)
    ·
      refine ⟨8147766203495083401842365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 173819012341228445905970453 8147766203495083401842365)
      ·
        refine ⟨3055412326310656275690887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8147766203495083401842365 3055412326310656275690887)
        ·
          refine ⟨4583118489465984413536331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3055412326310656275690887 4583118489465984413536331)
          ·
            refine ⟨6874677734198976620304497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4583118489465984413536331 6874677734198976620304497)
            ·
              refine ⟨5156008300649232465228373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6874677734198976620304497 5156008300649232465228373)
              ·
                refine ⟨60421972273233192951895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5156008300649232465228373 60421972273233192951895)
                ·
                  rfl

theorem cell23_3177127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 8].length) (baseStart_3177127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177127 prefixEnd_3177127 := by exact prefixLift 3177127
  have htrace : WordTrace (prefixWord ++ tailWord_3177127) baseStart_3177127 baseEnd_3177127 := by
    simpa [prefixWord, tailWord_3177127, baseEnd_3177127] using wordTrace_append hprefix tailTrace_3177127
  have hstable : (prefixWord ++ tailWord_3177127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177127).length < 2 ^ (prefixWord ++ tailWord_3177127).sum := by decide
  have hdescent : baseEnd_3177127 < baseStart_3177127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177158 : List Nat := [6, 1, 2, 1, 3, 1, 1, 1, 1, 1, 5]
def baseStart_3177158 : Nat := 118140960795 + 3177158 * 2 ^ 59
def prefixEnd_3177158 : Nat := 4983230072969 + 3 ^ 40 * 3177158 * 2
def baseEnd_3177158 : Nat := 1631409169277585588413523

theorem tailTrace_3177158 : CollatzResearch.WordTrace tailWord_3177158 prefixEnd_3177158 1631409169277585588413523 := by
  unfold tailWord_3177158
  simp only [CollatzResearch.WordTrace]
  refine ⟨3621264756990833007240379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 77253648149137770821128085 3621264756990833007240379)
  ·
    refine ⟨5431897135486249510860569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3621264756990833007240379 5431897135486249510860569)
    ·
      refine ⟨4073922851614687133145427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5431897135486249510860569 4073922851614687133145427)
      ·
        refine ⟨6110884277422030699718141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4073922851614687133145427 6110884277422030699718141)
        ·
          refine ⟨2291581604033261512394303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6110884277422030699718141 2291581604033261512394303)
          ·
            refine ⟨3437372406049892268591455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2291581604033261512394303 3437372406049892268591455)
            ·
              refine ⟨5156058609074838402887183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3437372406049892268591455 5156058609074838402887183)
              ·
                refine ⟨7734087913612257604330775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5156058609074838402887183 7734087913612257604330775)
                ·
                  refine ⟨11601131870418386406496163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7734087913612257604330775 11601131870418386406496163)
                  ·
                    refine ⟨17401697805627579609744245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11601131870418386406496163 17401697805627579609744245)
                    ·
                      refine ⟨1631409169277585588413523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17401697805627579609744245 1631409169277585588413523)
                      ·
                        rfl

theorem cell23_3177158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_3177158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177158 prefixEnd_3177158 := by exact prefixLift 3177158
  have htrace : WordTrace (prefixWord ++ tailWord_3177158) baseStart_3177158 baseEnd_3177158 := by
    simpa [prefixWord, tailWord_3177158, baseEnd_3177158] using wordTrace_append hprefix tailTrace_3177158
  have hstable : (prefixWord ++ tailWord_3177158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177158).length < 2 ^ (prefixWord ++ tailWord_3177158).sum := by decide
  have hdescent : baseEnd_3177158 < baseStart_3177158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177172 : List Nat := [2, 4, 1, 3, 3, 1, 2, 2, 1, 2, 2]
def baseStart_3177172 : Nat := 118140960795 + 3177172 * 2 ^ 59
def prefixEnd_3177172 : Nat := 4983230072969 + 3 ^ 40 * 3177172 * 2
def baseEnd_3177172 : Nat := 1631416358006748533638459

theorem tailTrace_3177172 : CollatzResearch.WordTrace tailWord_3177172 prefixEnd_3177172 1631416358006748533638459 := by
  unfold tailWord_3177172
  simp only [CollatzResearch.WordTrace]
  refine ⟨57940491422827968311350885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77253988563770624415134513 57940491422827968311350885)
  ·
    refine ⟨10863842141780244058378291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57940491422827968311350885 10863842141780244058378291)
    ·
      refine ⟨16295763212670366087567437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10863842141780244058378291 16295763212670366087567437)
      ·
        refine ⟨6110911204751387282837789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16295763212670366087567437 6110911204751387282837789)
        ·
          refine ⟨2291591701781770231064171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6110911204751387282837789 2291591701781770231064171)
          ·
            refine ⟨3437387552672655346596257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2291591701781770231064171 3437387552672655346596257)
            ·
              refine ⟨2578040664504491509947193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3437387552672655346596257 2578040664504491509947193)
              ·
                refine ⟨1933530498378368632460395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2578040664504491509947193 1933530498378368632460395)
                ·
                  refine ⟨2900295747567552948690593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1933530498378368632460395 2900295747567552948690593)
                  ·
                    refine ⟨2175221810675664711517945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2900295747567552948690593 2175221810675664711517945)
                    ·
                      refine ⟨1631416358006748533638459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2175221810675664711517945 1631416358006748533638459)
                      ·
                        rfl

theorem cell23_3177172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_3177172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177172 prefixEnd_3177172 := by exact prefixLift 3177172
  have htrace : WordTrace (prefixWord ++ tailWord_3177172) baseStart_3177172 baseEnd_3177172 := by
    simpa [prefixWord, tailWord_3177172, baseEnd_3177172] using wordTrace_append hprefix tailTrace_3177172
  have hstable : (prefixWord ++ tailWord_3177172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177172).length < 2 ^ (prefixWord ++ tailWord_3177172).sum := by decide
  have hdescent : baseEnd_3177172 < baseStart_3177172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177230 : List Nat := [4, 1, 1, 2, 1, 1, 1, 3, 4, 5]
def baseStart_3177230 : Nat := 118140960795 + 3177230 * 2 ^ 59
def prefixEnd_3177230 : Nat := 4983230072969 + 3 ^ 40 * 3177230 * 2
def baseEnd_3177230 : Nat := 543815379961569768904397

theorem tailTrace_3177230 : CollatzResearch.WordTrace tailWord_3177230 prefixEnd_3177230 543815379961569768904397 := by
  unfold tailWord_3177230
  simp only [CollatzResearch.WordTrace]
  refine ⟨14485387284930726566039143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77255398852963875018875429 14485387284930726566039143)
  ·
    refine ⟨21728080927396089849058715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14485387284930726566039143 21728080927396089849058715)
    ·
      refine ⟨32592121391094134773588073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21728080927396089849058715 32592121391094134773588073)
      ·
        refine ⟨24444091043320601080191055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32592121391094134773588073 24444091043320601080191055)
        ·
          refine ⟨36666136564980901620286583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24444091043320601080191055 36666136564980901620286583)
          ·
            refine ⟨54999204847471352430429875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36666136564980901620286583 54999204847471352430429875)
            ·
              refine ⟨82498807271207028645644813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54999204847471352430429875 82498807271207028645644813)
              ·
                refine ⟨30937052726702635742116805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82498807271207028645644813 30937052726702635742116805)
                ·
                  refine ⟨5800697386256744201646901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30937052726702635742116805 5800697386256744201646901)
                  ·
                    refine ⟨543815379961569768904397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5800697386256744201646901 543815379961569768904397)
                    ·
                      rfl

theorem cell23_3177230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_3177230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177230 prefixEnd_3177230 := by exact prefixLift 3177230
  have htrace : WordTrace (prefixWord ++ tailWord_3177230) baseStart_3177230 baseEnd_3177230 := by
    simpa [prefixWord, tailWord_3177230, baseEnd_3177230] using wordTrace_append hprefix tailTrace_3177230
  have hstable : (prefixWord ++ tailWord_3177230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177230).length < 2 ^ (prefixWord ++ tailWord_3177230).sum := by decide
  have hdescent : baseEnd_3177230 < baseStart_3177230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177234 : List Nat := [3, 2, 4, 1, 2, 1, 2, 1, 7]
def baseStart_3177234 : Nat := 118140960795 + 3177234 * 2 ^ 59
def prefixEnd_3177234 : Nat := 4983230072969 + 3 ^ 40 * 3177234 * 2
def baseEnd_3177234 : Nat := 181272021534147476784797

theorem tailTrace_3177234 : CollatzResearch.WordTrace tailWord_3177234 prefixEnd_3177234 181272021534147476784797 := by
  unfold tailWord_3177234
  simp only [CollatzResearch.WordTrace]
  refine ⟨28970811042857830302864689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77255496114287547474305837 28970811042857830302864689)
  ·
    refine ⟨21728108282143372727148517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28970811042857830302864689 21728108282143372727148517)
    ·
      refine ⟨4074020302901882386340347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21728108282143372727148517 4074020302901882386340347)
      ·
        refine ⟨6111030454352823579510521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4074020302901882386340347 6111030454352823579510521)
        ·
          refine ⟨4583272840764617684632891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6111030454352823579510521 4583272840764617684632891)
          ·
            refine ⟨6874909261146926526949337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4583272840764617684632891 6874909261146926526949337)
            ·
              refine ⟨5156181945860194895212003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6874909261146926526949337 5156181945860194895212003)
              ·
                refine ⟨7734272918790292342818005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5156181945860194895212003 7734272918790292342818005)
                ·
                  refine ⟨181272021534147476784797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7734272918790292342818005 181272021534147476784797)
                  ·
                    rfl

theorem cell23_3177234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 7].length) (baseStart_3177234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177234 prefixEnd_3177234 := by exact prefixLift 3177234
  have htrace : WordTrace (prefixWord ++ tailWord_3177234) baseStart_3177234 baseEnd_3177234 := by
    simpa [prefixWord, tailWord_3177234, baseEnd_3177234] using wordTrace_append hprefix tailTrace_3177234
  have hstable : (prefixWord ++ tailWord_3177234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177234).length < 2 ^ (prefixWord ++ tailWord_3177234).sum := by decide
  have hdescent : baseEnd_3177234 < baseStart_3177234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177243 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 4, 8]
def baseStart_3177243 : Nat := 118140960795 + 3177243 * 2 ^ 59
def prefixEnd_3177243 : Nat := 4983230072969 + 3 ^ 40 * 3177243 * 2
def baseEnd_3177243 : Nat := 543817605044405918616877

theorem tailTrace_3177243 : CollatzResearch.WordTrace tailWord_3177243 prefixEnd_3177243 543817605044405918616877 := by
  unfold tailWord_3177243
  simp only [CollatzResearch.WordTrace]
  refine ⟨115883572428398715748536383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77255714952265810499024255 115883572428398715748536383)
  ·
    refine ⟨173825358642598073622804575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115883572428398715748536383 173825358642598073622804575)
    ·
      refine ⟨260738037963897110434206863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173825358642598073622804575 260738037963897110434206863)
      ·
        refine ⟨391107056945845665651310295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260738037963897110434206863 391107056945845665651310295)
        ·
          refine ⟨586660585418768498476965443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391107056945845665651310295 586660585418768498476965443)
          ·
            refine ⟨879990878128152747715448165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 586660585418768498476965443 879990878128152747715448165)
            ·
              refine ⟨164998289649028640196646531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 879990878128152747715448165 164998289649028640196646531)
              ·
                refine ⟨247497434473542960294969797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164998289649028640196646531 247497434473542960294969797)
                ·
                  refine ⟨46405768963789305055306837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 247497434473542960294969797 46405768963789305055306837)
                  ·
                    refine ⟨543817605044405918616877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 46405768963789305055306837 543817605044405918616877)
                    ·
                      rfl

theorem cell23_3177243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 8].length) (baseStart_3177243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177243 prefixEnd_3177243 := by exact prefixLift 3177243
  have htrace : WordTrace (prefixWord ++ tailWord_3177243) baseStart_3177243 baseEnd_3177243 := by
    simpa [prefixWord, tailWord_3177243, baseEnd_3177243] using wordTrace_append hprefix tailTrace_3177243
  have hstable : (prefixWord ++ tailWord_3177243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177243).length < 2 ^ (prefixWord ++ tailWord_3177243).sum := by decide
  have hdescent : baseEnd_3177243 < baseStart_3177243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177245 : List Nat := [1, 4, 2, 4, 1, 1, 3, 1, 2, 2, 2]
def baseStart_3177245 : Nat := 118140960795 + 3177245 * 2 ^ 59
def prefixEnd_3177245 : Nat := 4983230072969 + 3 ^ 40 * 3177245 * 2
def baseEnd_3177245 : Nat := 1631453842094526748025623

theorem tailTrace_3177245 : CollatzResearch.WordTrace tailWord_3177245 prefixEnd_3177245 1631453842094526748025623 := by
  unfold tailWord_3177245
  simp only [CollatzResearch.WordTrace]
  refine ⟨115883645374391470090109189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77255763582927646726739459 115883645374391470090109189)
  ·
    refine ⟨21728183507698400641895473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115883645374391470090109189 21728183507698400641895473)
    ·
      refine ⟨16296137630773800481421605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21728183507698400641895473 16296137630773800481421605)
      ·
        refine ⟨3055525805770087590266551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16296137630773800481421605 3055525805770087590266551)
        ·
          refine ⟨4583288708655131385399827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3055525805770087590266551 4583288708655131385399827)
          ·
            refine ⟨6874933062982697078099741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4583288708655131385399827 6874933062982697078099741)
            ·
              refine ⟨2578099898618511404287403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6874933062982697078099741 2578099898618511404287403)
              ·
                refine ⟨3867149847927767106431105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2578099898618511404287403 3867149847927767106431105)
                ·
                  refine ⟨2900362385945825329823329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3867149847927767106431105 2900362385945825329823329)
                  ·
                    refine ⟨2175271789459368997367497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2900362385945825329823329 2175271789459368997367497)
                    ·
                      refine ⟨1631453842094526748025623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2175271789459368997367497 1631453842094526748025623)
                      ·
                        rfl

theorem cell23_3177245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_3177245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177245 prefixEnd_3177245 := by exact prefixLift 3177245
  have htrace : WordTrace (prefixWord ++ tailWord_3177245) baseStart_3177245 baseEnd_3177245 := by
    simpa [prefixWord, tailWord_3177245, baseEnd_3177245] using wordTrace_append hprefix tailTrace_3177245
  have hstable : (prefixWord ++ tailWord_3177245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177245).length < 2 ^ (prefixWord ++ tailWord_3177245).sum := by decide
  have hdescent : baseEnd_3177245 < baseStart_3177245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177268 : List Nat := [2, 5, 1, 1, 4, 1, 1, 3, 5]
def baseStart_3177268 : Nat := 118140960795 + 3177268 * 2 ^ 59
def prefixEnd_3177268 : Nat := 4983230072969 + 3 ^ 40 * 3177268 * 2
def baseEnd_3177268 : Nat := 181273961349953350893113

theorem tailTrace_3177268 : CollatzResearch.WordTrace tailWord_3177268 prefixEnd_3177268 181273961349953350893113 := by
  unfold tailWord_3177268
  simp only [CollatzResearch.WordTrace]
  refine ⟨57942242126654072509098229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77256322835538763345464305 57942242126654072509098229)
  ·
    refine ⟨5432085199373819297727959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57942242126654072509098229 5432085199373819297727959)
    ·
      refine ⟨8148127799060728946591939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5432085199373819297727959 8148127799060728946591939)
      ·
        refine ⟨12222191698591093419887909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8148127799060728946591939 12222191698591093419887909)
        ·
          refine ⟨2291660943485830016228983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12222191698591093419887909 2291660943485830016228983)
          ·
            refine ⟨3437491415228745024343475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2291660943485830016228983 3437491415228745024343475)
            ·
              refine ⟨5156237122843117536515213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3437491415228745024343475 5156237122843117536515213)
              ·
                refine ⟨1933588921066169076193205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5156237122843117536515213 1933588921066169076193205)
                ·
                  refine ⟨181273961349953350893113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1933588921066169076193205 181273961349953350893113)
                  ·
                    rfl

theorem cell23_3177268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_3177268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177268 prefixEnd_3177268 := by exact prefixLift 3177268
  have htrace : WordTrace (prefixWord ++ tailWord_3177268) baseStart_3177268 baseEnd_3177268 := by
    simpa [prefixWord, tailWord_3177268, baseEnd_3177268] using wordTrace_append hprefix tailTrace_3177268
  have hstable : (prefixWord ++ tailWord_3177268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177268).length < 2 ^ (prefixWord ++ tailWord_3177268).sum := by decide
  have hdescent : baseEnd_3177268 < baseStart_3177268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177294 : List Nat := [4, 1, 1, 1, 1, 1, 1, 8, 1, 4]
def baseStart_3177294 : Nat := 118140960795 + 3177294 * 2 ^ 59
def prefixEnd_3177294 : Nat := 4983230072969 + 3 ^ 40 * 3177294 * 2
def baseEnd_3177294 : Nat := 543826334215532352104299

theorem tailTrace_3177294 : CollatzResearch.WordTrace tailWord_3177294 prefixEnd_3177294 543826334215532352104299 := by
  unfold tailWord_3177294
  simp only [CollatzResearch.WordTrace]
  refine ⟨14485679068901743932330367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77256955034142634305761957 14485679068901743932330367)
  ·
    refine ⟨21728518603352615898495551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14485679068901743932330367 21728518603352615898495551)
    ·
      refine ⟨32592777905028923847743327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21728518603352615898495551 32592777905028923847743327)
      ·
        refine ⟨48889166857543385771614991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32592777905028923847743327 48889166857543385771614991)
        ·
          refine ⟨73333750286315078657422487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48889166857543385771614991 73333750286315078657422487)
          ·
            refine ⟨110000625429472617986133731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73333750286315078657422487 110000625429472617986133731)
            ·
              refine ⟨165000938144208926979200597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110000625429472617986133731 165000938144208926979200597)
              ·
                refine ⟨1933604743877448363037507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 165000938144208926979200597 1933604743877448363037507)
                ·
                  refine ⟨2900407115816172544556261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1933604743877448363037507 2900407115816172544556261)
                  ·
                    refine ⟨543826334215532352104299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2900407115816172544556261 543826334215532352104299)
                    ·
                      rfl

theorem cell23_3177294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 8, 1, 4].length) (baseStart_3177294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177294 prefixEnd_3177294 := by exact prefixLift 3177294
  have htrace : WordTrace (prefixWord ++ tailWord_3177294) baseStart_3177294 baseEnd_3177294 := by
    simpa [prefixWord, tailWord_3177294, baseEnd_3177294] using wordTrace_append hprefix tailTrace_3177294
  have hstable : (prefixWord ++ tailWord_3177294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177294).length < 2 ^ (prefixWord ++ tailWord_3177294).sum := by decide
  have hdescent : baseEnd_3177294 < baseStart_3177294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177327 : List Nat := [1, 1, 2, 1, 3, 1, 1, 5, 1, 5, 2]
def baseStart_3177327 : Nat := 118140960795 + 3177327 * 2 ^ 59
def prefixEnd_3177327 : Nat := 4983230072969 + 3 ^ 40 * 3177327 * 2
def baseEnd_3177327 : Nat := 1631495947508195427200245

theorem tailTrace_3177327 : CollatzResearch.WordTrace tailWord_3177327 prefixEnd_3177327 1631495947508195427200245 := by
  unfold tailWord_3177327
  simp only [CollatzResearch.WordTrace]
  refine ⟨115886636160094398094594235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77257757440062932063062823 115886636160094398094594235)
  ·
    refine ⟨173829954240141597141891353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115886636160094398094594235 173829954240141597141891353)
    ·
      refine ⟨130372465680106197856418515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173829954240141597141891353 130372465680106197856418515)
      ·
        refine ⟨195558698520159296784627773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130372465680106197856418515 195558698520159296784627773)
        ·
          refine ⟨73334511945059736294235415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195558698520159296784627773 73334511945059736294235415)
          ·
            refine ⟨110001767917589604441353123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73334511945059736294235415 110001767917589604441353123)
            ·
              refine ⟨165002651876384406662029685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110001767917589604441353123 165002651876384406662029685)
              ·
                refine ⟨15468998613411038124565283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 165002651876384406662029685 15468998613411038124565283)
                ·
                  refine ⟨23203497920116557186847925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15468998613411038124565283 23203497920116557186847925)
                  ·
                    refine ⟨2175327930010927236266993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23203497920116557186847925 2175327930010927236266993)
                    ·
                      refine ⟨1631495947508195427200245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2175327930010927236266993 1631495947508195427200245)
                      ·
                        rfl

theorem cell23_3177327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 5, 2].length) (baseStart_3177327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177327 prefixEnd_3177327 := by exact prefixLift 3177327
  have htrace : WordTrace (prefixWord ++ tailWord_3177327) baseStart_3177327 baseEnd_3177327 := by
    simpa [prefixWord, tailWord_3177327, baseEnd_3177327] using wordTrace_append hprefix tailTrace_3177327
  have hstable : (prefixWord ++ tailWord_3177327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177327).length < 2 ^ (prefixWord ++ tailWord_3177327).sum := by decide
  have hdescent : baseEnd_3177327 < baseStart_3177327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177367 : List Nat := [1, 1, 3, 3, 1, 2, 4, 1, 1, 6]
def baseStart_3177367 : Nat := 118140960795 + 3177367 * 2 ^ 59
def prefixEnd_3177367 : Nat := 4983230072969 + 3 ^ 40 * 3177367 * 2
def baseEnd_3177367 : Nat := 543838828911458423566687

theorem tailTrace_3177367 : CollatzResearch.WordTrace tailWord_3177367 prefixEnd_3177367 543838828911458423566687 := by
  unfold tailWord_3177367
  simp only [CollatzResearch.WordTrace]
  refine ⟨115888095079949484926050355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77258730053299656617366903 115888095079949484926050355)
  ·
    refine ⟨173832142619924227389075533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115888095079949484926050355 173832142619924227389075533)
    ·
      refine ⟨65187053482471585270903325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173832142619924227389075533 65187053482471585270903325)
      ·
        refine ⟨24445145055926844476588747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65187053482471585270903325 24445145055926844476588747)
        ·
          refine ⟨36667717583890266714883121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24445145055926844476588747 36667717583890266714883121)
          ·
            refine ⟨27500788187917700036162341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36667717583890266714883121 27500788187917700036162341)
            ·
              refine ⟨5156397785234568756780439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27500788187917700036162341 5156397785234568756780439)
              ·
                refine ⟨7734596677851853135170659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5156397785234568756780439 7734596677851853135170659)
                ·
                  refine ⟨11601895016777779702755989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7734596677851853135170659 11601895016777779702755989)
                  ·
                    refine ⟨543838828911458423566687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11601895016777779702755989 543838828911458423566687)
                    ·
                      rfl

theorem cell23_3177367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 6].length) (baseStart_3177367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177367 prefixEnd_3177367 := by exact prefixLift 3177367
  have htrace : WordTrace (prefixWord ++ tailWord_3177367) baseStart_3177367 baseEnd_3177367 := by
    simpa [prefixWord, tailWord_3177367, baseEnd_3177367] using wordTrace_append hprefix tailTrace_3177367
  have hstable : (prefixWord ++ tailWord_3177367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177367).length < 2 ^ (prefixWord ++ tailWord_3177367).sum := by decide
  have hdescent : baseEnd_3177367 < baseStart_3177367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177378 : List Nat := [3, 3, 1, 2, 2, 3, 1, 1, 2, 3, 2]
def baseStart_3177378 : Nat := 118140960795 + 3177378 * 2 ^ 59
def prefixEnd_3177378 : Nat := 4983230072969 + 3 ^ 40 * 3177378 * 2
def baseEnd_3177378 : Nat := 1631522135021574727662511

theorem tailTrace_3177378 : CollatzResearch.WordTrace tailWord_3177378 prefixEnd_3177378 1631522135021574727662511 := by
  unfold tailWord_3177378
  simp only [CollatzResearch.WordTrace]
  refine ⟨28972124070727408451175197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77258997521939755869800525 28972124070727408451175197)
  ·
    refine ⟨10864546526522778169190699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28972124070727408451175197 10864546526522778169190699)
    ·
      refine ⟨16296819789784167253786049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10864546526522778169190699 16296819789784167253786049)
      ·
        refine ⟨12222614842338125440339537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16296819789784167253786049 12222614842338125440339537)
        ·
          refine ⟨9166961131753594080254653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12222614842338125440339537 9166961131753594080254653)
          ·
            refine ⟨3437610424407597780095495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9166961131753594080254653 3437610424407597780095495)
            ·
              refine ⟨5156415636611396670143243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3437610424407597780095495 5156415636611396670143243)
              ·
                refine ⟨7734623454917095005214865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5156415636611396670143243 7734623454917095005214865)
                ·
                  refine ⟨5800967591187821253911149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7734623454917095005214865 5800967591187821253911149)
                  ·
                    refine ⟨2175362846695432970216681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5800967591187821253911149 2175362846695432970216681)
                    ·
                      refine ⟨1631522135021574727662511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2175362846695432970216681 1631522135021574727662511)
                      ·
                        rfl

theorem cell23_3177378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_3177378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177378 prefixEnd_3177378 := by exact prefixLift 3177378
  have htrace : WordTrace (prefixWord ++ tailWord_3177378) baseStart_3177378 baseEnd_3177378 := by
    simpa [prefixWord, tailWord_3177378, baseEnd_3177378] using wordTrace_append hprefix tailTrace_3177378
  have hstable : (prefixWord ++ tailWord_3177378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177378).length < 2 ^ (prefixWord ++ tailWord_3177378).sum := by decide
  have hdescent : baseEnd_3177378 < baseStart_3177378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177401 : List Nat := [1, 2, 1, 4, 2, 4, 1, 2, 2, 4]
def baseStart_3177401 : Nat := 118140960795 + 3177401 * 2 ^ 59
def prefixEnd_3177401 : Nat := 4983230072969 + 3 ^ 40 * 3177401 * 2
def baseEnd_3177401 : Nat := 543844648358876045891635

theorem tailTrace_3177401 : CollatzResearch.WordTrace tailWord_3177401 prefixEnd_3177401 543844648358876045891635 := by
  unfold tailWord_3177401
  simp only [CollatzResearch.WordTrace]
  refine ⟨115889335161826308732788057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77259556774550872488525371 115889335161826308732788057)
  ·
    refine ⟨86917001371369731549591043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115889335161826308732788057 86917001371369731549591043)
    ·
      refine ⟨130375502057054597324386565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86917001371369731549591043 130375502057054597324386565)
      ·
        refine ⟨24445406635697736998322481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130375502057054597324386565 24445406635697736998322481)
        ·
          refine ⟨18334054976773302748741861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24445406635697736998322481 18334054976773302748741861)
          ·
            refine ⟨3437635308144994265389099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18334054976773302748741861 3437635308144994265389099)
            ·
              refine ⟨5156452962217491398083649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3437635308144994265389099 5156452962217491398083649)
              ·
                refine ⟨3867339721663118548562737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5156452962217491398083649 3867339721663118548562737)
                ·
                  refine ⟨2900504791247338911422053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3867339721663118548562737 2900504791247338911422053)
                  ·
                    refine ⟨543844648358876045891635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2900504791247338911422053 543844648358876045891635)
                    ·
                      rfl

theorem cell23_3177401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 2, 4].length) (baseStart_3177401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177401 prefixEnd_3177401 := by exact prefixLift 3177401
  have htrace : WordTrace (prefixWord ++ tailWord_3177401) baseStart_3177401 baseEnd_3177401 := by
    simpa [prefixWord, tailWord_3177401, baseEnd_3177401] using wordTrace_append hprefix tailTrace_3177401
  have hstable : (prefixWord ++ tailWord_3177401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177401).length < 2 ^ (prefixWord ++ tailWord_3177401).sum := by decide
  have hdescent : baseEnd_3177401 < baseStart_3177401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177408 : List Nat := [2, 1, 1, 2, 3, 3, 2, 4, 1, 2, 2]
def baseStart_3177408 : Nat := 118140960795 + 3177408 * 2 ^ 59
def prefixEnd_3177408 : Nat := 4983230072969 + 3 ^ 40 * 3177408 * 2
def baseEnd_3177408 : Nat := 1631537539441209610287373

theorem tailTrace_3177408 : CollatzResearch.WordTrace tailWord_3177408 prefixEnd_3177408 1631537539441209610287373 := by
  unfold tailWord_3177408
  simp only [CollatzResearch.WordTrace]
  refine ⟨57944795236400474464146439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77259726981867299285528585 57944795236400474464146439)
  ·
    refine ⟨86917192854600711696219659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57944795236400474464146439 86917192854600711696219659)
    ·
      refine ⟨130375789281901067544329489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86917192854600711696219659 130375789281901067544329489)
      ·
        refine ⟨97781841961425800658247117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130375789281901067544329489 97781841961425800658247117)
        ·
          refine ⟨36668190735534675246842669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97781841961425800658247117 36668190735534675246842669)
          ·
            refine ⟨13750571525825503217566001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36668190735534675246842669 13750571525825503217566001)
            ·
              refine ⟨10312928644369127413174501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13750571525825503217566001 10312928644369127413174501)
              ·
                refine ⟨1933674120819211389970219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10312928644369127413174501 1933674120819211389970219)
                ·
                  refine ⟨2900511181228817084955329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1933674120819211389970219 2900511181228817084955329)
                  ·
                    refine ⟨2175383385921612813716497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2900511181228817084955329 2175383385921612813716497)
                    ·
                      refine ⟨1631537539441209610287373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2175383385921612813716497 1631537539441209610287373)
                      ·
                        rfl

theorem cell23_3177408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 4, 1, 2, 2].length) (baseStart_3177408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177408 prefixEnd_3177408 := by exact prefixLift 3177408
  have htrace : WordTrace (prefixWord ++ tailWord_3177408) baseStart_3177408 baseEnd_3177408 := by
    simpa [prefixWord, tailWord_3177408, baseEnd_3177408] using wordTrace_append hprefix tailTrace_3177408
  have hstable : (prefixWord ++ tailWord_3177408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177408).length < 2 ^ (prefixWord ++ tailWord_3177408).sum := by decide
  have hdescent : baseEnd_3177408 < baseStart_3177408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177442 : List Nat := [3, 3, 3, 1, 1, 1, 3, 3, 1, 2, 2]
def baseStart_3177442 : Nat := 118140960795 + 3177442 * 2 ^ 59
def prefixEnd_3177442 : Nat := 4983230072969 + 3 ^ 40 * 3177442 * 2
def baseEnd_3177442 : Nat := 1631554997783462477262217

theorem tailTrace_3177442 : CollatzResearch.WordTrace tailWord_3177442 prefixEnd_3177442 1631554997783462477262217 := by
  unfold tailWord_3177442
  simp only [CollatzResearch.WordTrace]
  refine ⟨28972707638669443183757645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77260553703118515156687053 28972707638669443183757645)
  ·
    refine ⟨10864765364501041193909117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28972707638669443183757645 10864765364501041193909117)
    ·
      refine ⟨4074287011687890447715919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10864765364501041193909117 4074287011687890447715919)
      ·
        refine ⟨6111430517531835671573879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4074287011687890447715919 6111430517531835671573879)
        ·
          refine ⟨9167145776297753507360819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6111430517531835671573879 9167145776297753507360819)
          ·
            refine ⟨13750718664446630261041229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9167145776297753507360819 13750718664446630261041229)
            ·
              refine ⟨5156519499167486347890461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13750718664446630261041229 5156519499167486347890461)
              ·
                refine ⟨1933694812187807380458923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5156519499167486347890461 1933694812187807380458923)
                ·
                  refine ⟨2900542218281711070688385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1933694812187807380458923 2900542218281711070688385)
                  ·
                    refine ⟨2175406663711283303016289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2900542218281711070688385 2175406663711283303016289)
                    ·
                      refine ⟨1631554997783462477262217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2175406663711283303016289 1631554997783462477262217)
                      ·
                        rfl

theorem cell23_3177442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_3177442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177442 prefixEnd_3177442 := by exact prefixLift 3177442
  have htrace : WordTrace (prefixWord ++ tailWord_3177442) baseStart_3177442 baseEnd_3177442 := by
    simpa [prefixWord, tailWord_3177442, baseEnd_3177442] using wordTrace_append hprefix tailTrace_3177442
  have hstable : (prefixWord ++ tailWord_3177442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177442).length < 2 ^ (prefixWord ++ tailWord_3177442).sum := by decide
  have hdescent : baseEnd_3177442 < baseStart_3177442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177467 : List Nat := [1, 1, 1, 1, 1, 3, 3, 3, 2, 4, 3]
def baseStart_3177467 : Nat := 118140960795 + 3177467 * 2 ^ 59
def prefixEnd_3177467 : Nat := 4983230072969 + 3 ^ 40 * 3177467 * 2
def baseEnd_3177467 : Nat := 1631567834799824879449601

theorem tailTrace_3177467 : CollatzResearch.WordTrace tailWord_3177467 prefixEnd_3177467 1631567834799824879449601 := by
  unfold tailWord_3177467
  simp only [CollatzResearch.WordTrace]
  refine ⟨115891742379587202004690655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77261161586391468003127103 115891742379587202004690655)
  ·
    refine ⟨173837613569380803007035983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115891742379587202004690655 173837613569380803007035983)
    ·
      refine ⟨260756420354071204510553975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173837613569380803007035983 260756420354071204510553975)
      ·
        refine ⟨391134630531106806765830963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260756420354071204510553975 391134630531106806765830963)
        ·
          refine ⟨586701945796660210148746445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391134630531106806765830963 586701945796660210148746445)
          ·
            refine ⟨220013229673747578805779917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 586701945796660210148746445 220013229673747578805779917)
            ·
              refine ⟨82504961127655342052167469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 220013229673747578805779917 82504961127655342052167469)
              ·
                refine ⟨30939360422870753269562801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82504961127655342052167469 30939360422870753269562801)
                ·
                  refine ⟨23204520317153064952172101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30939360422870753269562801 23204520317153064952172101)
                  ·
                    refine ⟨4350847559466199678532269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23204520317153064952172101 4350847559466199678532269)
                    ·
                      refine ⟨1631567834799824879449601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4350847559466199678532269 1631567834799824879449601)
                      ·
                        rfl

theorem cell23_3177467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 4, 3].length) (baseStart_3177467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177467 prefixEnd_3177467 := by exact prefixLift 3177467
  have htrace : WordTrace (prefixWord ++ tailWord_3177467) baseStart_3177467 baseEnd_3177467 := by
    simpa [prefixWord, tailWord_3177467, baseEnd_3177467] using wordTrace_append hprefix tailTrace_3177467
  have hstable : (prefixWord ++ tailWord_3177467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177467).length < 2 ^ (prefixWord ++ tailWord_3177467).sum := by decide
  have hdescent : baseEnd_3177467 < baseStart_3177467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177477 : List Nat := [1, 3, 1, 1, 2, 3, 2, 1, 1, 4, 4]
def baseStart_3177477 : Nat := 118140960795 + 3177477 * 2 ^ 59
def prefixEnd_3177477 : Nat := 4983230072969 + 3 ^ 40 * 3177477 * 2
def baseEnd_3177477 : Nat := 1631572969606369840324555

theorem tailTrace_3177477 : CollatzResearch.WordTrace tailWord_3177477 prefixEnd_3177477 1631572969606369840324555 := by
  unfold tailWord_3177477
  simp only [CollatzResearch.WordTrace]
  refine ⟨115892107109550973712554685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77261404739700649141703123 115892107109550973712554685)
  ·
    refine ⟨43459540166081615142208007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115892107109550973712554685 43459540166081615142208007)
    ·
      refine ⟨65189310249122422713312011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43459540166081615142208007 65189310249122422713312011)
      ·
        refine ⟨97783965373683634069968017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65189310249122422713312011 97783965373683634069968017)
        ·
          refine ⟨73337974030262725552476013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97783965373683634069968017 73337974030262725552476013)
          ·
            refine ⟨27501740261348522082178505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73337974030262725552476013 27501740261348522082178505)
            ·
              refine ⟨20626305196011391561633879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27501740261348522082178505 20626305196011391561633879)
              ·
                refine ⟨30939457794017087342450819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20626305196011391561633879 30939457794017087342450819)
                ·
                  refine ⟨46409186691025631013676229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30939457794017087342450819 46409186691025631013676229)
                  ·
                    refine ⟨8701722504567305815064293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46409186691025631013676229 8701722504567305815064293)
                    ·
                      refine ⟨1631572969606369840324555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8701722504567305815064293 1631572969606369840324555)
                      ·
                        rfl

theorem cell23_3177477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 4, 4].length) (baseStart_3177477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177477 prefixEnd_3177477 := by exact prefixLift 3177477
  have htrace : WordTrace (prefixWord ++ tailWord_3177477) baseStart_3177477 baseEnd_3177477 := by
    simpa [prefixWord, tailWord_3177477, baseEnd_3177477] using wordTrace_append hprefix tailTrace_3177477
  have hstable : (prefixWord ++ tailWord_3177477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177477).length < 2 ^ (prefixWord ++ tailWord_3177477).sum := by decide
  have hdescent : baseEnd_3177477 < baseStart_3177477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177567 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 6]
def baseStart_3177567 : Nat := 118140960795 + 3177567 * 2 ^ 59
def prefixEnd_3177567 : Nat := 4983230072969 + 3 ^ 40 * 3177567 * 2
def baseEnd_3177567 : Nat := 1631619182865274488199141

theorem tailTrace_3177567 : CollatzResearch.WordTrace tailWord_3177567 prefixEnd_3177567 1631619182865274488199141 := by
  unfold tailWord_3177567
  simp only [CollatzResearch.WordTrace]
  refine ⟨115895389679224919083330955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77263593119483279388887303 115895389679224919083330955)
  ·
    refine ⟨173843084518837378624996433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115895389679224919083330955 173843084518837378624996433)
    ·
      refine ⟨130382313389128033968747325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173843084518837378624996433 130382313389128033968747325)
      ·
        refine ⟨48893367520923012738280247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130382313389128033968747325 48893367520923012738280247)
        ·
          refine ⟨73340051281384519107420371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48893367520923012738280247 73340051281384519107420371)
          ·
            refine ⟨110010076922076778661130557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73340051281384519107420371 110010076922076778661130557)
            ·
              refine ⟨41253778845778791997923959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110010076922076778661130557 41253778845778791997923959)
              ·
                refine ⟨61880668268668187996885939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41253778845778791997923959 61880668268668187996885939)
                ·
                  refine ⟨92821002403002281995328909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61880668268668187996885939 92821002403002281995328909)
                  ·
                    refine ⟨34807875901125855748248341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92821002403002281995328909 34807875901125855748248341)
                    ·
                      refine ⟨1631619182865274488199141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34807875901125855748248341 1631619182865274488199141)
                      ·
                        rfl

theorem cell23_3177567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_3177567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177567 prefixEnd_3177567 := by exact prefixLift 3177567
  have htrace : WordTrace (prefixWord ++ tailWord_3177567) baseStart_3177567 baseEnd_3177567 := by
    simpa [prefixWord, tailWord_3177567, baseEnd_3177567] using wordTrace_append hprefix tailTrace_3177567
  have hstable : (prefixWord ++ tailWord_3177567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177567).length < 2 ^ (prefixWord ++ tailWord_3177567).sum := by decide
  have hdescent : baseEnd_3177567 < baseStart_3177567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177581 : List Nat := [1, 5, 1, 1, 2, 2, 1, 3, 3, 4]
def baseStart_3177581 : Nat := 118140960795 + 3177581 * 2 ^ 59
def prefixEnd_3177581 : Nat := 4983230072969 + 3 ^ 40 * 3177581 * 2
def baseEnd_3177581 : Nat := 543875457198145811141359

theorem tailTrace_3177581 : CollatzResearch.WordTrace tailWord_3177581 prefixEnd_3177581 543875457198145811141359 := by
  unfold tailWord_3177581
  simp only [CollatzResearch.WordTrace]
  refine ⟨115895900301174199474340597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77263933534116132982893731 115895900301174199474340597)
  ·
    refine ⟨10865240653235081200719431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115895900301174199474340597 10865240653235081200719431)
    ·
      refine ⟨16297860979852621801079147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10865240653235081200719431 16297860979852621801079147)
      ·
        refine ⟨24446791469778932701618721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16297860979852621801079147 24446791469778932701618721)
        ·
          refine ⟨18335093602334199526214041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24446791469778932701618721 18335093602334199526214041)
          ·
            refine ⟨13751320201750649644660531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18335093602334199526214041 13751320201750649644660531)
            ·
              refine ⟨20626980302625974466990797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13751320201750649644660531 20626980302625974466990797)
              ·
                refine ⟨7735117613484740425121549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20626980302625974466990797 7735117613484740425121549)
                ·
                  refine ⟨2900669105056777659420581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7735117613484740425121549 2900669105056777659420581)
                  ·
                    refine ⟨543875457198145811141359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2900669105056777659420581 543875457198145811141359)
                    ·
                      rfl

theorem cell23_3177581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_3177581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177581 prefixEnd_3177581 := by exact prefixLift 3177581
  have htrace : WordTrace (prefixWord ++ tailWord_3177581) baseStart_3177581 baseEnd_3177581 := by
    simpa [prefixWord, tailWord_3177581, baseEnd_3177581] using wordTrace_append hprefix tailTrace_3177581
  have hstable : (prefixWord ++ tailWord_3177581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177581).length < 2 ^ (prefixWord ++ tailWord_3177581).sum := by decide
  have hdescent : baseEnd_3177581 < baseStart_3177581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177645 : List Nat := [1, 5, 2, 1, 3, 2, 2, 1, 6]
def baseStart_3177645 : Nat := 118140960795 + 3177645 * 2 ^ 59
def prefixEnd_3177645 : Nat := 4983230072969 + 3 ^ 40 * 3177645 * 2
def baseEnd_3177645 : Nat := 181295470484036131447087

theorem tailTrace_3177645 : CollatzResearch.WordTrace tailWord_3177645 prefixEnd_3177645 181295470484036131447087 := by
  unfold tailWord_3177645
  simp only [CollatzResearch.WordTrace]
  refine ⟨115898234572942338404670389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77265489715294892269780259 115898234572942338404670389)
  ·
    refine ⟨10865459491213344225437849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115898234572942338404670389 10865459491213344225437849)
    ·
      refine ⟨8149094618410008169078387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10865459491213344225437849 8149094618410008169078387)
      ·
        refine ⟨12223641927615012253617581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8149094618410008169078387 12223641927615012253617581)
        ·
          refine ⟨4583865722855629595106593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12223641927615012253617581 4583865722855629595106593)
          ·
            refine ⟨3437899292141722196329945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4583865722855629595106593 3437899292141722196329945)
            ·
              refine ⟨2578424469106291647247459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3437899292141722196329945 2578424469106291647247459)
              ·
                refine ⟨3867636703659437470871189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2578424469106291647247459 3867636703659437470871189)
                ·
                  refine ⟨181295470484036131447087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3867636703659437470871189 181295470484036131447087)
                  ·
                    rfl

theorem cell23_3177645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_3177645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177645 prefixEnd_3177645 := by exact prefixLift 3177645
  have htrace : WordTrace (prefixWord ++ tailWord_3177645) baseStart_3177645 baseEnd_3177645 := by
    simpa [prefixWord, tailWord_3177645, baseEnd_3177645] using wordTrace_append hprefix tailTrace_3177645
  have hstable : (prefixWord ++ tailWord_3177645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177645).length < 2 ^ (prefixWord ++ tailWord_3177645).sum := by decide
  have hdescent : baseEnd_3177645 < baseStart_3177645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177661 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 2, 6, 2]
def baseStart_3177661 : Nat := 118140960795 + 3177661 * 2 ^ 59
def prefixEnd_3177661 : Nat := 4983230072969 + 3 ^ 40 * 3177661 * 2
def baseEnd_3177661 : Nat := 1631667450046797120423709

theorem tailTrace_3177661 : CollatzResearch.WordTrace tailWord_3177661 prefixEnd_3177661 1631667450046797120423709 := by
  unfold tailWord_3177661
  simp only [CollatzResearch.WordTrace]
  refine ⟨115898818140884373137252837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77265878760589582091501891 115898818140884373137252837)
  ·
    refine ⟨21731028401415819963234907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115898818140884373137252837 21731028401415819963234907)
    ·
      refine ⟨32596542602123729944852361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21731028401415819963234907 32596542602123729944852361)
      ·
        refine ⟨24447406951592797458639271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32596542602123729944852361 24447406951592797458639271)
        ·
          refine ⟨36671110427389196187958907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24447406951592797458639271 36671110427389196187958907)
          ·
            refine ⟨55006665641083794281938361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36671110427389196187958907 55006665641083794281938361)
            ·
              refine ⟨41254999230812845711453771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55006665641083794281938361 41254999230812845711453771)
              ·
                refine ⟨61882498846219268567180657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41254999230812845711453771 61882498846219268567180657)
                ·
                  refine ⟨46411874134664451425385493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61882498846219268567180657 46411874134664451425385493)
                  ·
                    refine ⟨2175556600062396160564945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 46411874134664451425385493 2175556600062396160564945)
                    ·
                      refine ⟨1631667450046797120423709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2175556600062396160564945 1631667450046797120423709)
                      ·
                        rfl

theorem cell23_3177661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_3177661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177661 prefixEnd_3177661 := by exact prefixLift 3177661
  have htrace : WordTrace (prefixWord ++ tailWord_3177661) baseStart_3177661 baseEnd_3177661 := by
    simpa [prefixWord, tailWord_3177661, baseEnd_3177661] using wordTrace_append hprefix tailTrace_3177661
  have hstable : (prefixWord ++ tailWord_3177661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177661).length < 2 ^ (prefixWord ++ tailWord_3177661).sum := by decide
  have hdescent : baseEnd_3177661 < baseStart_3177661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177665 : List Nat := [1, 2, 6, 1, 1, 1, 1, 3, 2, 3, 2]
def baseStart_3177665 : Nat := 118140960795 + 3177665 * 2 ^ 59
def prefixEnd_3177665 : Nat := 4983230072969 + 3 ^ 40 * 3177665 * 2
def baseEnd_3177665 : Nat := 1631669503969415104773691

theorem tailTrace_3177665 : CollatzResearch.WordTrace tailWord_3177665 prefixEnd_3177665 1631669503969415104773691 := by
  unfold tailWord_3177665
  simp only [CollatzResearch.WordTrace]
  refine ⟨115898964032869881820398449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77265976021913254546932299 115898964032869881820398449)
  ·
    refine ⟨86924223024652411365298837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115898964032869881820398449 86924223024652411365298837)
    ·
      refine ⟨4074572954280581782748383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 86924223024652411365298837 4074572954280581782748383)
      ·
        refine ⟨6111859431420872674122575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4074572954280581782748383 6111859431420872674122575)
        ·
          refine ⟨9167789147131309011183863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6111859431420872674122575 9167789147131309011183863)
          ·
            refine ⟨13751683720696963516775795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9167789147131309011183863 13751683720696963516775795)
            ·
              refine ⟨20627525581045445275163693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13751683720696963516775795 20627525581045445275163693)
              ·
                refine ⟨7735322092892041978186385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20627525581045445275163693 7735322092892041978186385)
                ·
                  refine ⟨5801491569669031483639789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7735322092892041978186385 5801491569669031483639789)
                  ·
                    refine ⟨2175559338625886806364921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5801491569669031483639789 2175559338625886806364921)
                    ·
                      refine ⟨1631669503969415104773691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2175559338625886806364921 1631669503969415104773691)
                      ·
                        rfl

theorem cell23_3177665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_3177665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177665 prefixEnd_3177665 := by exact prefixLift 3177665
  have htrace : WordTrace (prefixWord ++ tailWord_3177665) baseStart_3177665 baseEnd_3177665 := by
    simpa [prefixWord, tailWord_3177665, baseEnd_3177665] using wordTrace_append hprefix tailTrace_3177665
  have hstable : (prefixWord ++ tailWord_3177665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177665).length < 2 ^ (prefixWord ++ tailWord_3177665).sum := by decide
  have hdescent : baseEnd_3177665 < baseStart_3177665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177716 : List Nat := [2, 6, 1, 2, 1, 2, 1, 1, 2, 3, 2]
def baseStart_3177716 : Nat := 118140960795 + 3177716 * 2 ^ 59
def prefixEnd_3177716 : Nat := 4983230072969 + 3 ^ 40 * 3177716 * 2
def baseEnd_3177716 : Nat := 1631695691482794405235957

theorem tailTrace_3177716 : CollatzResearch.WordTrace tailWord_3177716 prefixEnd_3177716 1631695691482794405235957 := by
  unfold tailWord_3177716
  simp only [CollatzResearch.WordTrace]
  refine ⟨57950412077842558765252501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77267216103790078353670001 57950412077842558765252501)
  ·
    refine ⟨2716425566148869942121211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 57950412077842558765252501 2716425566148869942121211)
    ·
      refine ⟨4074638349223304913181817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2716425566148869942121211 4074638349223304913181817)
      ·
        refine ⟨3055978761917478684886363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4074638349223304913181817 3055978761917478684886363)
        ·
          refine ⟨4583968142876218027329545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3055978761917478684886363 4583968142876218027329545)
          ·
            refine ⟨3437976107157163520497159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4583968142876218027329545 3437976107157163520497159)
            ·
              refine ⟨5156964160735745280745739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3437976107157163520497159 5156964160735745280745739)
              ·
                refine ⟨7735446241103617921118609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5156964160735745280745739 7735446241103617921118609)
                ·
                  refine ⟨5801584680827713440838957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7735446241103617921118609 5801584680827713440838957)
                  ·
                    refine ⟨2175594255310392540314609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5801584680827713440838957 2175594255310392540314609)
                    ·
                      refine ⟨1631695691482794405235957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2175594255310392540314609 1631695691482794405235957)
                      ·
                        rfl

theorem cell23_3177716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_3177716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177716 prefixEnd_3177716 := by exact prefixLift 3177716
  have htrace : WordTrace (prefixWord ++ tailWord_3177716) baseStart_3177716 baseEnd_3177716 := by
    simpa [prefixWord, tailWord_3177716, baseEnd_3177716] using wordTrace_append hprefix tailTrace_3177716
  have hstable : (prefixWord ++ tailWord_3177716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177716).length < 2 ^ (prefixWord ++ tailWord_3177716).sum := by decide
  have hdescent : baseEnd_3177716 < baseStart_3177716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177732 : List Nat := [2, 3, 2, 2, 2, 3, 2, 1, 1, 2, 3]
def baseStart_3177732 : Nat := 118140960795 + 3177732 * 2 ^ 59
def prefixEnd_3177732 : Nat := 4983230072969 + 3 ^ 40 * 3177732 * 2
def baseEnd_3177732 : Nat := 1631703907173266342635883

theorem tailTrace_3177732 : CollatzResearch.WordTrace tailWord_3177732 prefixEnd_3177732 1631703907173266342635883 := by
  unfold tailWord_3177732
  simp only [CollatzResearch.WordTrace]
  refine ⟨57950703861813576131543725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77267605149084768175391633 57950703861813576131543725)
  ·
    refine ⟨21731513948180091049328897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57950703861813576131543725 21731513948180091049328897)
    ·
      refine ⟨16298635461135068286996673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21731513948180091049328897 16298635461135068286996673)
      ·
        refine ⟨12223976595851301215247505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16298635461135068286996673 12223976595851301215247505)
        ·
          refine ⟨9167982446888475911435629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12223976595851301215247505 9167982446888475911435629)
          ·
            refine ⟨3437993417583178466788361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9167982446888475911435629 3437993417583178466788361)
            ·
              refine ⟨2578495063187383850091271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3437993417583178466788361 2578495063187383850091271)
              ·
                refine ⟨3867742594781075775136907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2578495063187383850091271 3867742594781075775136907)
                ·
                  refine ⟨5801613892171613662705361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3867742594781075775136907 5801613892171613662705361)
                  ·
                    refine ⟨4351210419128710247029021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5801613892171613662705361 4351210419128710247029021)
                    ·
                      refine ⟨1631703907173266342635883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4351210419128710247029021 1631703907173266342635883)
                      ·
                        rfl

theorem cell23_3177732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_3177732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177732 prefixEnd_3177732 := by exact prefixLift 3177732
  have htrace : WordTrace (prefixWord ++ tailWord_3177732) baseStart_3177732 baseEnd_3177732 := by
    simpa [prefixWord, tailWord_3177732, baseEnd_3177732] using wordTrace_append hprefix tailTrace_3177732
  have hstable : (prefixWord ++ tailWord_3177732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177732).length < 2 ^ (prefixWord ++ tailWord_3177732).sum := by decide
  have hdescent : baseEnd_3177732 < baseStart_3177732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177762 : List Nat := [3, 3, 1, 1, 5, 1, 1, 1, 1, 3, 3]
def baseStart_3177762 : Nat := 118140960795 + 3177762 * 2 ^ 59
def prefixEnd_3177762 : Nat := 4983230072969 + 3 ^ 40 * 3177762 * 2
def baseEnd_3177762 : Nat := 1631719311592901225260745

theorem tailTrace_3177762 : CollatzResearch.WordTrace tailWord_3177762 prefixEnd_3177762 1631719311592901225260745 := by
  unfold tailWord_3177762
  simp only [CollatzResearch.WordTrace]
  refine ⟨28975625478379616846669885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77268334609012311591119693 28975625478379616846669885)
  ·
    refine ⟨10865859554392356317501207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28975625478379616846669885 10865859554392356317501207)
    ·
      refine ⟨16298789331588534476251811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10865859554392356317501207 16298789331588534476251811)
      ·
        refine ⟨24448183997382801714377717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16298789331588534476251811 24448183997382801714377717)
        ·
          refine ⟨2292017249754637660722911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24448183997382801714377717 2292017249754637660722911)
          ·
            refine ⟨3438025874631956491084367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2292017249754637660722911 3438025874631956491084367)
            ·
              refine ⟨5157038811947934736626551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3438025874631956491084367 5157038811947934736626551)
              ·
                refine ⟨7735558217921902104939827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5157038811947934736626551 7735558217921902104939827)
                ·
                  refine ⟨11603337326882853157409741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7735558217921902104939827 11603337326882853157409741)
                  ·
                    refine ⟨4351251497581069934028653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11603337326882853157409741 4351251497581069934028653)
                    ·
                      refine ⟨1631719311592901225260745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4351251497581069934028653 1631719311592901225260745)
                      ·
                        rfl

theorem cell23_3177762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_3177762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177762 prefixEnd_3177762 := by exact prefixLift 3177762
  have htrace : WordTrace (prefixWord ++ tailWord_3177762) baseStart_3177762 baseEnd_3177762 := by
    simpa [prefixWord, tailWord_3177762, baseEnd_3177762] using wordTrace_append hprefix tailTrace_3177762
  have hstable : (prefixWord ++ tailWord_3177762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177762).length < 2 ^ (prefixWord ++ tailWord_3177762).sum := by decide
  have hdescent : baseEnd_3177762 < baseStart_3177762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177801 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 4, 3, 3]
def baseStart_3177801 : Nat := 118140960795 + 3177801 * 2 ^ 59
def prefixEnd_3177801 : Nat := 4983230072969 + 3 ^ 40 * 3177801 * 2
def baseEnd_3177801 : Nat := 1631739337338426572673065

theorem tailTrace_3177801 : CollatzResearch.WordTrace tailWord_3177801 prefixEnd_3177801 1631739337338426572673065 := by
  unfold tailWord_3177801
  simp only [CollatzResearch.WordTrace]
  refine ⟨115903924360377177047349257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77269282906918118031566171 115903924360377177047349257)
  ·
    refine ⟨86927943270282882785511943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115903924360377177047349257 86927943270282882785511943)
    ·
      refine ⟨130391914905424324178267915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86927943270282882785511943 130391914905424324178267915)
      ·
        refine ⟨195587872358136486267401873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130391914905424324178267915 195587872358136486267401873)
        ·
          refine ⟨146690904268602364700551405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195587872358136486267401873 146690904268602364700551405)
          ·
            refine ⟨55009089100725886762706777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146690904268602364700551405 55009089100725886762706777)
            ·
              refine ⟨41256816825544415072030083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55009089100725886762706777 41256816825544415072030083)
              ·
                refine ⟨61885225238316622608045125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41256816825544415072030083 61885225238316622608045125)
                ·
                  refine ⟨11603479732184366739008461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61885225238316622608045125 11603479732184366739008461)
                  ·
                    refine ⟨4351304899569137527128173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11603479732184366739008461 4351304899569137527128173)
                    ·
                      refine ⟨1631739337338426572673065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4351304899569137527128173 1631739337338426572673065)
                      ·
                        rfl

theorem cell23_3177801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 3, 3].length) (baseStart_3177801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177801 prefixEnd_3177801 := by exact prefixLift 3177801
  have htrace : WordTrace (prefixWord ++ tailWord_3177801) baseStart_3177801 baseEnd_3177801 := by
    simpa [prefixWord, tailWord_3177801, baseEnd_3177801] using wordTrace_append hprefix tailTrace_3177801
  have hstable : (prefixWord ++ tailWord_3177801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177801).length < 2 ^ (prefixWord ++ tailWord_3177801).sum := by decide
  have hdescent : baseEnd_3177801 < baseStart_3177801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177841 : List Nat := [1, 2, 2, 2, 1, 2, 2, 3, 1, 3, 4]
def baseStart_3177841 : Nat := 118140960795 + 3177841 * 2 ^ 59
def prefixEnd_3177841 : Nat := 4983230072969 + 3 ^ 40 * 3177841 * 2
def baseEnd_3177841 : Nat := 1631759876564606416172881

theorem tailTrace_3177841 : CollatzResearch.WordTrace tailWord_3177841 prefixEnd_3177841 1631759876564606416172881 := by
  unfold tailWord_3177841
  simp only [CollatzResearch.WordTrace]
  refine ⟨115905383280232263878805377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77270255520154842585870251 115905383280232263878805377)
  ·
    refine ⟨86929037460174197909104033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115905383280232263878805377 86929037460174197909104033)
    ·
      refine ⟨65196778095130648431828025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86929037460174197909104033 65196778095130648431828025)
      ·
        refine ⟨48897583571347986323871019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65196778095130648431828025 48897583571347986323871019)
        ·
          refine ⟨73346375357021979485806529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48897583571347986323871019 73346375357021979485806529)
          ·
            refine ⟨55009781517766484614354897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73346375357021979485806529 55009781517766484614354897)
            ·
              refine ⟨41257336138324863460766173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55009781517766484614354897 41257336138324863460766173)
              ·
                refine ⟨15471501051871823797787315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41257336138324863460766173 15471501051871823797787315)
                ·
                  refine ⟨23207251577807735696680973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15471501051871823797787315 23207251577807735696680973)
                  ·
                    refine ⟨8702719341677900886255365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23207251577807735696680973 8702719341677900886255365)
                    ·
                      refine ⟨1631759876564606416172881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8702719341677900886255365 1631759876564606416172881)
                      ·
                        rfl

theorem cell23_3177841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_3177841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177841 prefixEnd_3177841 := by exact prefixLift 3177841
  have htrace : WordTrace (prefixWord ++ tailWord_3177841) baseStart_3177841 baseEnd_3177841 := by
    simpa [prefixWord, tailWord_3177841, baseEnd_3177841] using wordTrace_append hprefix tailTrace_3177841
  have hstable : (prefixWord ++ tailWord_3177841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177841).length < 2 ^ (prefixWord ++ tailWord_3177841).sum := by decide
  have hdescent : baseEnd_3177841 < baseStart_3177841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177868 : List Nat := [2, 2, 1, 2, 1, 3, 2, 3, 3, 4]
def baseStart_3177868 : Nat := 118140960795 + 3177868 * 2 ^ 59
def prefixEnd_3177868 : Nat := 4983230072969 + 3 ^ 40 * 3177868 * 2
def baseEnd_3177868 : Nat := 543924580180759270178419

theorem tailTrace_3177868 : CollatzResearch.WordTrace tailWord_3177868 prefixEnd_3177868 543924580180759270178419 := by
  unfold tailWord_3177868
  simp only [CollatzResearch.WordTrace]
  refine ⟨57953184025567223745019129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77270912034089631660025505 57953184025567223745019129)
  ·
    refine ⟨43464888019175417808764347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57953184025567223745019129 43464888019175417808764347)
    ·
      refine ⟨65197332028763126713146521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43464888019175417808764347 65197332028763126713146521)
      ·
        refine ⟨48897999021572345034859891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65197332028763126713146521 48897999021572345034859891)
        ·
          refine ⟨73346998532358517552289837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48897999021572345034859891 73346998532358517552289837)
          ·
            refine ⟨27505124449634444082108689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73346998532358517552289837 27505124449634444082108689)
            ·
              refine ⟨20628843337225833061581517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27505124449634444082108689 20628843337225833061581517)
              ·
                refine ⟨7735816251459687398093069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20628843337225833061581517 7735816251459687398093069)
                ·
                  refine ⟨2900931094297382774284901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7735816251459687398093069 2900931094297382774284901)
                  ·
                    refine ⟨543924580180759270178419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2900931094297382774284901 543924580180759270178419)
                    ·
                      rfl

theorem cell23_3177868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 3, 4].length) (baseStart_3177868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177868 prefixEnd_3177868 := by exact prefixLift 3177868
  have htrace : WordTrace (prefixWord ++ tailWord_3177868) baseStart_3177868 baseEnd_3177868 := by
    simpa [prefixWord, tailWord_3177868, baseEnd_3177868] using wordTrace_append hprefix tailTrace_3177868
  have hstable : (prefixWord ++ tailWord_3177868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177868).length < 2 ^ (prefixWord ++ tailWord_3177868).sum := by decide
  have hdescent : baseEnd_3177868 < baseStart_3177868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177885 : List Nat := [1, 4, 2, 1, 3, 2, 1, 2, 3, 4]
def baseStart_3177885 : Nat := 118140960795 + 3177885 * 2 ^ 59
def prefixEnd_3177885 : Nat := 4983230072969 + 3 ^ 40 * 3177885 * 2
def baseEnd_3177885 : Nat := 543927489904468081340893

theorem tailTrace_3177885 : CollatzResearch.WordTrace tailWord_3177885 prefixEnd_3177885 543927489904468081340893 := by
  unfold tailWord_3177885
  simp only [CollatzResearch.WordTrace]
  refine ⟨115906988092072859393407109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77271325394715239595604739 115906988092072859393407109)
  ·
    refine ⟨21732560267263661136263833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115906988092072859393407109 21732560267263661136263833)
    ·
      refine ⟨16299420200447745852197875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21732560267263661136263833 16299420200447745852197875)
      ·
        refine ⟨24449130300671618778296813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16299420200447745852197875 24449130300671618778296813)
        ·
          refine ⟨9168423862751857041861305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24449130300671618778296813 9168423862751857041861305)
          ·
            refine ⟨6876317897063892781395979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9168423862751857041861305 6876317897063892781395979)
            ·
              refine ⟨10314476845595839172093969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6876317897063892781395979 10314476845595839172093969)
              ·
                refine ⟨7735857634196879379070477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10314476845595839172093969 7735857634196879379070477)
                ·
                  refine ⟨2900946612823829767151429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7735857634196879379070477 2900946612823829767151429)
                  ·
                    refine ⟨543927489904468081340893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2900946612823829767151429 543927489904468081340893)
                    ·
                      rfl

theorem cell23_3177885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_3177885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177885 prefixEnd_3177885 := by exact prefixLift 3177885
  have htrace : WordTrace (prefixWord ++ tailWord_3177885) baseStart_3177885 baseEnd_3177885 := by
    simpa [prefixWord, tailWord_3177885, baseEnd_3177885] using wordTrace_append hprefix tailTrace_3177885
  have hstable : (prefixWord ++ tailWord_3177885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177885).length < 2 ^ (prefixWord ++ tailWord_3177885).sum := by decide
  have hdescent : baseEnd_3177885 < baseStart_3177885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177945 : List Nat := [1, 2, 1, 2, 4, 3, 2, 2, 1, 5]
def baseStart_3177945 : Nat := 118140960795 + 3177945 * 2 ^ 59
def prefixEnd_3177945 : Nat := 4983230072969 + 3 ^ 40 * 3177945 * 2
def baseEnd_3177945 : Nat := 543937759517558003090801

theorem tailTrace_3177945 : CollatzResearch.WordTrace tailWord_3177945 prefixEnd_3177945 543937759517558003090801 := by
  unfold tailWord_3177945
  simp only [CollatzResearch.WordTrace]
  refine ⟨115909176471855489640591289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77272784314570326427060859 115909176471855489640591289)
  ·
    refine ⟨86931882353891617230443467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115909176471855489640591289 86931882353891617230443467)
    ·
      refine ⟨130397823530837425845665201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86931882353891617230443467 130397823530837425845665201)
      ·
        refine ⟨97798367648128069384248901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130397823530837425845665201 97798367648128069384248901)
        ·
          refine ⟨18337193934024013009546669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97798367648128069384248901 18337193934024013009546669)
          ·
            refine ⟨6876447725259004878580001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18337193934024013009546669 6876447725259004878580001)
            ·
              refine ⟨5157335793944253658935001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6876447725259004878580001 5157335793944253658935001)
              ·
                refine ⟨3868001845458190244201251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5157335793944253658935001 3868001845458190244201251)
                ·
                  refine ⟨5802002768187285366301877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3868001845458190244201251 5802002768187285366301877)
                  ·
                    refine ⟨543937759517558003090801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5802002768187285366301877 543937759517558003090801)
                    ·
                      rfl

theorem cell23_3177945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 5].length) (baseStart_3177945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177945 prefixEnd_3177945 := by exact prefixLift 3177945
  have htrace : WordTrace (prefixWord ++ tailWord_3177945) baseStart_3177945 baseEnd_3177945 := by
    simpa [prefixWord, tailWord_3177945, baseEnd_3177945] using wordTrace_append hprefix tailTrace_3177945
  have hstable : (prefixWord ++ tailWord_3177945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177945).length < 2 ^ (prefixWord ++ tailWord_3177945).sum := by decide
  have hdescent : baseEnd_3177945 < baseStart_3177945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177959 : List Nat := [1, 1, 5, 2, 1, 2, 3, 3, 1, 1, 3]
def baseStart_3177959 : Nat := 118140960795 + 3177959 * 2 ^ 59
def prefixEnd_3177959 : Nat := 4983230072969 + 3 ^ 40 * 3177959 * 2
def baseEnd_3177959 : Nat := 1631820467281836954497339

theorem tailTrace_3177959 : CollatzResearch.WordTrace tailWord_3177959 prefixEnd_3177959 1631820467281836954497339 := by
  unfold tailWord_3177959
  simp only [CollatzResearch.WordTrace]
  refine ⟨115909687093804770031600931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77273124729203180021067287 115909687093804770031600931)
  ·
    refine ⟨173864530640707155047401397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115909687093804770031600931 173864530640707155047401397)
    ·
      refine ⟨16299799747566295785693881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 173864530640707155047401397 16299799747566295785693881)
      ·
        refine ⟨12224849810674721839270411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16299799747566295785693881 12224849810674721839270411)
        ·
          refine ⟨18337274716012082758905617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12224849810674721839270411 18337274716012082758905617)
          ·
            refine ⟨13752956037009062069179213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18337274716012082758905617 13752956037009062069179213)
            ·
              refine ⟨5157358513878398275942205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13752956037009062069179213 5157358513878398275942205)
              ·
                refine ⟨1934009442704399353478327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5157358513878398275942205 1934009442704399353478327)
                ·
                  refine ⟨2901014164056599030217491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1934009442704399353478327 2901014164056599030217491)
                  ·
                    refine ⟨4351521246084898545326237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2901014164056599030217491 4351521246084898545326237)
                    ·
                      refine ⟨1631820467281836954497339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4351521246084898545326237 1631820467281836954497339)
                      ·
                        rfl

theorem cell23_3177959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_3177959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177959 prefixEnd_3177959 := by exact prefixLift 3177959
  have htrace : WordTrace (prefixWord ++ tailWord_3177959) baseStart_3177959 baseEnd_3177959 := by
    simpa [prefixWord, tailWord_3177959, baseEnd_3177959] using wordTrace_append hprefix tailTrace_3177959
  have hstable : (prefixWord ++ tailWord_3177959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177959).length < 2 ^ (prefixWord ++ tailWord_3177959).sum := by decide
  have hdescent : baseEnd_3177959 < baseStart_3177959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177968 : List Nat := [2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 5]
def baseStart_3177968 : Nat := 118140960795 + 3177968 * 2 ^ 59
def prefixEnd_3177968 : Nat := 4983230072969 + 3 ^ 40 * 3177968 * 2
def baseEnd_3177968 : Nat := 1631825088607727419284797

theorem tailTrace_3177968 : CollatzResearch.WordTrace tailWord_3177968 prefixEnd_3177968 1631825088607727419284797 := by
  unfold tailWord_3177968
  simp only [CollatzResearch.WordTrace]
  refine ⟨57955007675386082284339279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77273343567181443045785705 57955007675386082284339279)
  ·
    refine ⟨86932511513079123426508919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57955007675386082284339279 86932511513079123426508919)
    ·
      refine ⟨130398767269618685139763379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86932511513079123426508919 130398767269618685139763379)
      ·
        refine ⟨195598150904428027709645069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130398767269618685139763379 195598150904428027709645069)
        ·
          refine ⟨73349306589160510391116901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195598150904428027709645069 73349306589160510391116901)
          ·
            refine ⟨13752994985467595698334419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73349306589160510391116901 13752994985467595698334419)
            ·
              refine ⟨20629492478201393547501629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13752994985467595698334419 20629492478201393547501629)
              ·
                refine ⟨7736059679325522580313111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20629492478201393547501629 7736059679325522580313111)
                ·
                  refine ⟨11604089518988283870469667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7736059679325522580313111 11604089518988283870469667)
                  ·
                    refine ⟨17406134278482425805704501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11604089518988283870469667 17406134278482425805704501)
                    ·
                      refine ⟨1631825088607727419284797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17406134278482425805704501 1631825088607727419284797)
                      ·
                        rfl

theorem cell23_3177968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 5].length) (baseStart_3177968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177968 prefixEnd_3177968 := by exact prefixLift 3177968
  have htrace : WordTrace (prefixWord ++ tailWord_3177968) baseStart_3177968 baseEnd_3177968 := by
    simpa [prefixWord, tailWord_3177968, baseEnd_3177968] using wordTrace_append hprefix tailTrace_3177968
  have hstable : (prefixWord ++ tailWord_3177968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177968).length < 2 ^ (prefixWord ++ tailWord_3177968).sum := by decide
  have hdescent : baseEnd_3177968 < baseStart_3177968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177992 : List Nat := [2, 1, 3, 2, 1, 1, 6, 1, 2, 4]
def baseStart_3177992 : Nat := 118140960795 + 3177992 * 2 ^ 59
def prefixEnd_3177992 : Nat := 4983230072969 + 3 ^ 40 * 3177992 * 2
def baseEnd_3177992 : Nat := 543945804047811775128229

theorem tailTrace_3177992 : CollatzResearch.WordTrace tailWord_3177992 prefixEnd_3177992 543945804047811775128229 := by
  unfold tailWord_3177992
  simp only [CollatzResearch.WordTrace]
  refine ⟨57955445351342608333776115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77273927135123477778368153 57955445351342608333776115)
  ·
    refine ⟨86933168027013912500664173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57955445351342608333776115 86933168027013912500664173)
    ·
      refine ⟨32599938010130217187749065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86933168027013912500664173 32599938010130217187749065)
      ·
        refine ⟨24449953507597662890811799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32599938010130217187749065 24449953507597662890811799)
        ·
          refine ⟨36674930261396494336217699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24449953507597662890811799 36674930261396494336217699)
          ·
            refine ⟨55012395392094741504326549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36674930261396494336217699 55012395392094741504326549)
            ·
              refine ⟨2578706034004441008015307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55012395392094741504326549 2578706034004441008015307)
              ·
                refine ⟨3868059051006661512022961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2578706034004441008015307 3868059051006661512022961)
                ·
                  refine ⟨2901044288254996134017221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3868059051006661512022961 2901044288254996134017221)
                  ·
                    refine ⟨543945804047811775128229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2901044288254996134017221 543945804047811775128229)
                    ·
                      rfl

theorem cell23_3177992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 2, 4].length) (baseStart_3177992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3177992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3177992 prefixEnd_3177992 := by exact prefixLift 3177992
  have htrace : WordTrace (prefixWord ++ tailWord_3177992) baseStart_3177992 baseEnd_3177992 := by
    simpa [prefixWord, tailWord_3177992, baseEnd_3177992] using wordTrace_append hprefix tailTrace_3177992
  have hstable : (prefixWord ++ tailWord_3177992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177992).length < 2 ^ (prefixWord ++ tailWord_3177992).sum := by decide
  have hdescent : baseEnd_3177992 < baseStart_3177992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178015 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 6, 1, 3]
def baseStart_3178015 : Nat := 118140960795 + 3178015 * 2 ^ 59
def prefixEnd_3178015 : Nat := 4983230072969 + 3 ^ 40 * 3178015 * 2
def baseEnd_3178015 : Nat := 1631849222198488735397081

theorem tailTrace_3178015 : CollatzResearch.WordTrace tailWord_3178015 prefixEnd_3178015 1631849222198488735397081 := by
  unfold tailWord_3178015
  simp only [CollatzResearch.WordTrace]
  refine ⟨115911729581601891595639499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77274486387734594397092999 115911729581601891595639499)
  ·
    refine ⟨173867594372402837393459249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115911729581601891595639499 173867594372402837393459249)
    ·
      refine ⟨130400695779302128045094437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173867594372402837393459249 130400695779302128045094437)
      ·
        refine ⟨24450130458619149008455207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130400695779302128045094437 24450130458619149008455207)
        ·
          refine ⟨36675195687928723512682811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24450130458619149008455207 36675195687928723512682811)
          ·
            refine ⟨55012793531893085269024217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36675195687928723512682811 55012793531893085269024217)
            ·
              refine ⟨41259595148919813951768163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55012793531893085269024217 41259595148919813951768163)
              ·
                refine ⟨61889392723379720927652245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41259595148919813951768163 61889392723379720927652245)
                ·
                  refine ⟨2901065283908424418483699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 61889392723379720927652245 2901065283908424418483699)
                  ·
                    refine ⟨4351597925862636627725549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2901065283908424418483699 4351597925862636627725549)
                    ·
                      refine ⟨1631849222198488735397081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4351597925862636627725549 1631849222198488735397081)
                      ·
                        rfl

theorem cell23_3178015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_3178015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178015 prefixEnd_3178015 := by exact prefixLift 3178015
  have htrace : WordTrace (prefixWord ++ tailWord_3178015) baseStart_3178015 baseEnd_3178015 := by
    simpa [prefixWord, tailWord_3178015, baseEnd_3178015] using wordTrace_append hprefix tailTrace_3178015
  have hstable : (prefixWord ++ tailWord_3178015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178015).length < 2 ^ (prefixWord ++ tailWord_3178015).sum := by decide
  have hdescent : baseEnd_3178015 < baseStart_3178015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178019 : List Nat := [1, 1, 1, 4, 5, 1, 3, 1, 1, 2, 3]
def baseStart_3178019 : Nat := 118140960795 + 3178019 * 2 ^ 59
def prefixEnd_3178019 : Nat := 4983230072969 + 3 ^ 40 * 3178019 * 2
def baseEnd_3178019 : Nat := 1631851276121106719747063

theorem tailTrace_3178019 : CollatzResearch.WordTrace tailWord_3178019 prefixEnd_3178019 1631851276121106719747063 := by
  unfold tailWord_3178019
  simp only [CollatzResearch.WordTrace]
  refine ⟨115911875473587400278785111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77274583649058266852523407 115911875473587400278785111)
  ·
    refine ⟨173867813210381100418177667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115911875473587400278785111 173867813210381100418177667)
    ·
      refine ⟨260801719815571650627266501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173867813210381100418177667 260801719815571650627266501)
      ·
        refine ⟨48900322465419684492612469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 260801719815571650627266501 48900322465419684492612469)
        ·
          refine ⟨4584405231133095421182419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48900322465419684492612469 4584405231133095421182419)
          ·
            refine ⟨6876607846699643131773629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4584405231133095421182419 6876607846699643131773629)
            ·
              refine ⟨2578727942512366174415111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6876607846699643131773629 2578727942512366174415111)
              ·
                refine ⟨3868091913768549261622667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2578727942512366174415111 3868091913768549261622667)
                ·
                  refine ⟨5802137870652823892434001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3868091913768549261622667 5802137870652823892434001)
                  ·
                    refine ⟨4351603402989617919325501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5802137870652823892434001 4351603402989617919325501)
                    ·
                      refine ⟨1631851276121106719747063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4351603402989617919325501 1631851276121106719747063)
                      ·
                        rfl

theorem cell23_3178019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 1, 2, 3].length) (baseStart_3178019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178019 prefixEnd_3178019 := by exact prefixLift 3178019
  have htrace : WordTrace (prefixWord ++ tailWord_3178019) baseStart_3178019 baseEnd_3178019 := by
    simpa [prefixWord, tailWord_3178019, baseEnd_3178019] using wordTrace_append hprefix tailTrace_3178019
  have hstable : (prefixWord ++ tailWord_3178019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178019).length < 2 ^ (prefixWord ++ tailWord_3178019).sum := by decide
  have hdescent : baseEnd_3178019 < baseStart_3178019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178070 : List Nat := [5, 2, 2, 2, 1, 2, 2, 1, 1, 2, 3]
def baseStart_3178070 : Nat := 118140960795 + 3178070 * 2 ^ 59
def prefixEnd_3178070 : Nat := 4983230072969 + 3 ^ 40 * 3178070 * 2
def baseEnd_3178070 : Nat := 1631877463634486020209329

theorem tailTrace_3178070 : CollatzResearch.WordTrace tailWord_3178070 prefixEnd_3178070 1631877463634486020209329 := by
  unfold tailWord_3178070
  simp only [CollatzResearch.WordTrace]
  refine ⟨7244608474775164749305729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77275823730935090659261109 7244608474775164749305729)
  ·
    refine ⟨5433456356081373561979297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7244608474775164749305729 5433456356081373561979297)
    ·
      refine ⟨4075092267061030171484473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5433456356081373561979297 4075092267061030171484473)
      ·
        refine ⟨3056319200295772628613355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4075092267061030171484473 3056319200295772628613355)
        ·
          refine ⟨4584478800443658942920033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3056319200295772628613355 4584478800443658942920033)
          ·
            refine ⟨3438359100332744207190025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4584478800443658942920033 3438359100332744207190025)
            ·
              refine ⟨2578769325249558155392519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3438359100332744207190025 2578769325249558155392519)
              ·
                refine ⟨3868153987874337233088779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2578769325249558155392519 3868153987874337233088779)
                ·
                  refine ⟨5802230981811505849633169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3868153987874337233088779 5802230981811505849633169)
                  ·
                    refine ⟨4351673236358629387224877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5802230981811505849633169 4351673236358629387224877)
                    ·
                      refine ⟨1631877463634486020209329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4351673236358629387224877 1631877463634486020209329)
                      ·
                        rfl

theorem cell23_3178070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_3178070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178070 prefixEnd_3178070 := by exact prefixLift 3178070
  have htrace : WordTrace (prefixWord ++ tailWord_3178070) baseStart_3178070 baseEnd_3178070 := by
    simpa [prefixWord, tailWord_3178070, baseEnd_3178070] using wordTrace_append hprefix tailTrace_3178070
  have hstable : (prefixWord ++ tailWord_3178070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178070).length < 2 ^ (prefixWord ++ tailWord_3178070).sum := by decide
  have hdescent : baseEnd_3178070 < baseStart_3178070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178072 : List Nat := [2, 1, 2, 2, 1, 2, 1, 4, 4, 2, 2]
def baseStart_3178072 : Nat := 118140960795 + 3178072 * 2 ^ 59
def prefixEnd_3178072 : Nat := 4983230072969 + 3 ^ 40 * 3178072 * 2
def baseEnd_3178072 : Nat := 1631878490595795012384319

theorem tailTrace_3178072 : CollatzResearch.WordTrace tailWord_3178072 prefixEnd_3178072 1631878490595795012384319 := by
  unfold tailWord_3178072
  simp only [CollatzResearch.WordTrace]
  refine ⟨57956904271197695165232235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77275872361596926886976313 57956904271197695165232235)
  ·
    refine ⟨86935356406796542747848353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57956904271197695165232235 86935356406796542747848353)
    ·
      refine ⟨65201517305097407060886265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86935356406796542747848353 65201517305097407060886265)
      ·
        refine ⟨48901137978823055295664699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65201517305097407060886265 48901137978823055295664699)
        ·
          refine ⟨73351706968234582943497049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48901137978823055295664699 73351706968234582943497049)
          ·
            refine ⟨55013780226175937207622787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73351706968234582943497049 55013780226175937207622787)
            ·
              refine ⟨82520670339263905811434181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55013780226175937207622787 82520670339263905811434181)
              ·
                refine ⟨15472625688611982339643909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82520670339263905811434181 15472625688611982339643909)
                ·
                  refine ⟨2901117316614746688683233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15472625688611982339643909 2901117316614746688683233)
                  ·
                    refine ⟨2175837987461060016512425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2901117316614746688683233 2175837987461060016512425)
                    ·
                      refine ⟨1631878490595795012384319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2175837987461060016512425 1631878490595795012384319)
                      ·
                        rfl

theorem cell23_3178072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 4, 2, 2].length) (baseStart_3178072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178072 prefixEnd_3178072 := by exact prefixLift 3178072
  have htrace : WordTrace (prefixWord ++ tailWord_3178072) baseStart_3178072 baseEnd_3178072 := by
    simpa [prefixWord, tailWord_3178072, baseEnd_3178072] using wordTrace_append hprefix tailTrace_3178072
  have hstable : (prefixWord ++ tailWord_3178072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178072).length < 2 ^ (prefixWord ++ tailWord_3178072).sum := by decide
  have hdescent : baseEnd_3178072 < baseStart_3178072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178076 : List Nat := [2, 2, 4, 1, 2, 1, 4, 1, 1, 3, 2]
def baseStart_3178076 : Nat := 118140960795 + 3178076 * 2 ^ 59
def prefixEnd_3178076 : Nat := 4983230072969 + 3 ^ 40 * 3178076 * 2
def baseEnd_3178076 : Nat := 1631880544518412996734301

theorem tailTrace_3178076 : CollatzResearch.WordTrace tailWord_3178076 prefixEnd_3178076 1631880544518412996734301 := by
  unfold tailWord_3178076
  simp only [CollatzResearch.WordTrace]
  refine ⟨57956977217190449506805041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77275969622920599342406721 57956977217190449506805041)
  ·
    refine ⟨43467732912892837130103781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57956977217190449506805041 43467732912892837130103781)
    ·
      refine ⟨8150199921167406961894459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43467732912892837130103781 8150199921167406961894459)
      ·
        refine ⟨12225299881751110442841689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8150199921167406961894459 12225299881751110442841689)
        ·
          refine ⟨9168974911313332832131267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12225299881751110442841689 9168974911313332832131267)
          ·
            refine ⟨13753462366969999248196901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9168974911313332832131267 13753462366969999248196901)
            ·
              refine ⟨2578774193806874859036919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13753462366969999248196901 2578774193806874859036919)
              ·
                refine ⟨3868161290710312288555379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2578774193806874859036919 3868161290710312288555379)
                ·
                  refine ⟨5802241936065468432833069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3868161290710312288555379 5802241936065468432833069)
                  ·
                    refine ⟨2175840726024550662312401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5802241936065468432833069 2175840726024550662312401)
                    ·
                      refine ⟨1631880544518412996734301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2175840726024550662312401 1631880544518412996734301)
                      ·
                        rfl

theorem cell23_3178076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_3178076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178076 prefixEnd_3178076 := by exact prefixLift 3178076
  have htrace : WordTrace (prefixWord ++ tailWord_3178076) baseStart_3178076 baseEnd_3178076 := by
    simpa [prefixWord, tailWord_3178076, baseEnd_3178076] using wordTrace_append hprefix tailTrace_3178076
  have hstable : (prefixWord ++ tailWord_3178076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178076).length < 2 ^ (prefixWord ++ tailWord_3178076).sum := by decide
  have hdescent : baseEnd_3178076 < baseStart_3178076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178085 : List Nat := [1, 3, 1, 3, 3, 1, 1, 2, 2, 2, 4]
def baseStart_3178085 : Nat := 118140960795 + 3178085 * 2 ^ 59
def prefixEnd_3178085 : Nat := 4983230072969 + 3 ^ 40 * 3178085 * 2
def baseEnd_3178085 : Nat := 1631885165844303461521759

theorem tailTrace_3178085 : CollatzResearch.WordTrace tailWord_3178085 prefixEnd_3178085 1631885165844303461521759 := by
  unfold tailWord_3178085
  simp only [CollatzResearch.WordTrace]
  refine ⟨115914282691348293550687709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77276188460898862367125139 115914282691348293550687709)
  ·
    refine ⟨43467856009255610081507891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115914282691348293550687709 43467856009255610081507891)
    ·
      refine ⟨65201784013883415122261837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43467856009255610081507891 65201784013883415122261837)
      ·
        refine ⟨24450669005206280670848189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65201784013883415122261837 24450669005206280670848189)
        ·
          refine ⟨9169000876952355251568071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24450669005206280670848189 9169000876952355251568071)
          ·
            refine ⟨13753501315428532877352107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9169000876952355251568071 13753501315428532877352107)
            ·
              refine ⟨20630251973142799316028161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13753501315428532877352107 20630251973142799316028161)
              ·
                refine ⟨15472688979857099487021121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20630251973142799316028161 15472688979857099487021121)
                ·
                  refine ⟨11604516734892824615265841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15472688979857099487021121 11604516734892824615265841)
                  ·
                    refine ⟨8703387551169618461449381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11604516734892824615265841 8703387551169618461449381)
                    ·
                      refine ⟨1631885165844303461521759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8703387551169618461449381 1631885165844303461521759)
                      ·
                        rfl

theorem cell23_3178085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_3178085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178085 prefixEnd_3178085 := by exact prefixLift 3178085
  have htrace : WordTrace (prefixWord ++ tailWord_3178085) baseStart_3178085 baseEnd_3178085 := by
    simpa [prefixWord, tailWord_3178085, baseEnd_3178085] using wordTrace_append hprefix tailTrace_3178085
  have hstable : (prefixWord ++ tailWord_3178085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178085).length < 2 ^ (prefixWord ++ tailWord_3178085).sum := by decide
  have hdescent : baseEnd_3178085 < baseStart_3178085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178089 : List Nat := [1, 2, 1, 1, 1, 4, 5, 2, 2, 2, 2]
def baseStart_3178089 : Nat := 118140960795 + 3178089 * 2 ^ 59
def prefixEnd_3178089 : Nat := 4983230072969 + 3 ^ 40 * 3178089 * 2
def baseEnd_3178089 : Nat := 1631887219766921445871741

theorem tailTrace_3178089 : CollatzResearch.WordTrace tailWord_3178089 prefixEnd_3178089 1631887219766921445871741 := by
  unfold tailWord_3178089
  simp only [CollatzResearch.WordTrace]
  refine ⟨115914428583333802233833321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77276285722222534822555547 115914428583333802233833321)
  ·
    refine ⟨86935821437500351675374991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115914428583333802233833321 86935821437500351675374991)
    ·
      refine ⟨130403732156250527513062487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86935821437500351675374991 130403732156250527513062487)
      ·
        refine ⟨195605598234375791269593731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130403732156250527513062487 195605598234375791269593731)
        ·
          refine ⟨293408397351563686904390597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195605598234375791269593731 293408397351563686904390597)
          ·
            refine ⟨55014074503418191294573237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 293408397351563686904390597 55014074503418191294573237)
            ·
              refine ⟨5157569484695455433866241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55014074503418191294573237 5157569484695455433866241)
              ·
                refine ⟨3868177113521591575399681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5157569484695455433866241 3868177113521591575399681)
                ·
                  refine ⟨2901132835141193681549761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3868177113521591575399681 2901132835141193681549761)
                  ·
                    refine ⟨2175849626355895261162321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2901132835141193681549761 2175849626355895261162321)
                    ·
                      refine ⟨1631887219766921445871741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2175849626355895261162321 1631887219766921445871741)
                      ·
                        rfl

theorem cell23_3178089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 2, 2, 2].length) (baseStart_3178089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178089 prefixEnd_3178089 := by exact prefixLift 3178089
  have htrace : WordTrace (prefixWord ++ tailWord_3178089) baseStart_3178089 baseEnd_3178089 := by
    simpa [prefixWord, tailWord_3178089, baseEnd_3178089] using wordTrace_append hprefix tailTrace_3178089
  have hstable : (prefixWord ++ tailWord_3178089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178089).length < 2 ^ (prefixWord ++ tailWord_3178089).sum := by decide
  have hdescent : baseEnd_3178089 < baseStart_3178089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178102 : List Nat := [5, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4]
def baseStart_3178102 : Nat := 118140960795 + 3178102 * 2 ^ 59
def prefixEnd_3178102 : Nat := 4983230072969 + 3 ^ 40 * 3178102 * 2
def baseEnd_3178102 : Nat := 1631893895015429895009181

theorem tailTrace_3178102 : CollatzResearch.WordTrace tailWord_3178102 prefixEnd_3178102 1631893895015429895009181 := by
  unfold tailWord_3178102
  simp only [CollatzResearch.WordTrace]
  refine ⟨7244681420767919090878535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77276601821524470302704373 7244681420767919090878535)
  ·
    refine ⟨10867022131151878636317803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7244681420767919090878535 10867022131151878636317803)
    ·
      refine ⟨16300533196727817954476705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10867022131151878636317803 16300533196727817954476705)
      ·
        refine ⟨12225399897545863465857529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16300533196727817954476705 12225399897545863465857529)
        ·
          refine ⟨9169049923159397599393147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12225399897545863465857529 9169049923159397599393147)
          ·
            refine ⟨13753574884739096399089721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9169049923159397599393147 13753574884739096399089721)
            ·
              refine ⟨10315181163554322299317291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13753574884739096399089721 10315181163554322299317291)
              ·
                refine ⟨15472771745331483448975937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10315181163554322299317291 15472771745331483448975937)
                ·
                  refine ⟨11604578808998612586731953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15472771745331483448975937 11604578808998612586731953)
                  ·
                    refine ⟨8703434106748959440048965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11604578808998612586731953 8703434106748959440048965)
                    ·
                      refine ⟨1631893895015429895009181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8703434106748959440048965 1631893895015429895009181)
                      ·
                        rfl

theorem cell23_3178102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_3178102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178102 prefixEnd_3178102 := by exact prefixLift 3178102
  have htrace : WordTrace (prefixWord ++ tailWord_3178102) baseStart_3178102 baseEnd_3178102 := by
    simpa [prefixWord, tailWord_3178102, baseEnd_3178102] using wordTrace_append hprefix tailTrace_3178102
  have hstable : (prefixWord ++ tailWord_3178102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178102).length < 2 ^ (prefixWord ++ tailWord_3178102).sum := by decide
  have hdescent : baseEnd_3178102 < baseStart_3178102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178105 : List Nat := [1, 2, 1, 3, 3, 1, 1, 3, 2, 3, 3]
def baseStart_3178105 : Nat := 118140960795 + 3178105 * 2 ^ 59
def prefixEnd_3178105 : Nat := 4983230072969 + 3 ^ 40 * 3178105 * 2
def baseEnd_3178105 : Nat := 1631895435457393383271667

theorem tailTrace_3178105 : CollatzResearch.WordTrace tailWord_3178105 prefixEnd_3178105 1631895435457393383271667 := by
  unfold tailWord_3178105
  simp only [CollatzResearch.WordTrace]
  refine ⟨115915012151275836966415769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77276674767517224644277179 115915012151275836966415769)
  ·
    refine ⟨86936259113456877724811827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115915012151275836966415769 86936259113456877724811827)
    ·
      refine ⟨130404388670185316587217741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86936259113456877724811827 130404388670185316587217741)
      ·
        refine ⟨48901645751319493720206653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130404388670185316587217741 48901645751319493720206653)
        ·
          refine ⟨18338117156744810145077495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48901645751319493720206653 18338117156744810145077495)
          ·
            refine ⟨27507175735117215217616243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18338117156744810145077495 27507175735117215217616243)
            ·
              refine ⟨41260763602675822826424365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27507175735117215217616243 41260763602675822826424365)
              ·
                refine ⟨15472786351003433559909137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41260763602675822826424365 15472786351003433559909137)
                ·
                  refine ⟨11604589763252575169931853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15472786351003433559909137 11604589763252575169931853)
                  ·
                    refine ⟨4351721161219715688724445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11604589763252575169931853 4351721161219715688724445)
                    ·
                      refine ⟨1631895435457393383271667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4351721161219715688724445 1631895435457393383271667)
                      ·
                        rfl

theorem cell23_3178105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 3, 3].length) (baseStart_3178105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178105 prefixEnd_3178105 := by exact prefixLift 3178105
  have htrace : WordTrace (prefixWord ++ tailWord_3178105) baseStart_3178105 baseEnd_3178105 := by
    simpa [prefixWord, tailWord_3178105, baseEnd_3178105] using wordTrace_append hprefix tailTrace_3178105
  have hstable : (prefixWord ++ tailWord_3178105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178105).length < 2 ^ (prefixWord ++ tailWord_3178105).sum := by decide
  have hdescent : baseEnd_3178105 < baseStart_3178105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178142 : List Nat := [4, 3, 1, 1, 1, 2, 1, 1, 4, 5]
def baseStart_3178142 : Nat := 118140960795 + 3178142 * 2 ^ 59
def prefixEnd_3178142 : Nat := 4983230072969 + 3 ^ 40 * 3178142 * 2
def baseEnd_3178142 : Nat := 543971478080536579502999

theorem tailTrace_3178142 : CollatzResearch.WordTrace tailWord_3178142 prefixEnd_3178142 543971478080536579502999 := by
  unfold tailWord_3178142
  simp only [CollatzResearch.WordTrace]
  refine ⟨14489545206517724035689085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77277574434761194857008453 14489545206517724035689085)
  ·
    refine ⟨5433579452444146513383407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14489545206517724035689085 5433579452444146513383407)
    ·
      refine ⟨8150369178666219770075111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5433579452444146513383407 8150369178666219770075111)
      ·
        refine ⟨12225553767999329655112667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8150369178666219770075111 12225553767999329655112667)
        ·
          refine ⟨18338330651998994482669001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12225553767999329655112667 18338330651998994482669001)
          ·
            refine ⟨13753747988999245862001751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18338330651998994482669001 13753747988999245862001751)
            ·
              refine ⟨20630621983498868793002627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13753747988999245862001751 20630621983498868793002627)
              ·
                refine ⟨30945932975248303189503941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20630621983498868793002627 30945932975248303189503941)
                ·
                  refine ⟨5802362432859056848031989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30945932975248303189503941 5802362432859056848031989)
                  ·
                    refine ⟨543971478080536579502999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5802362432859056848031989 543971478080536579502999)
                    ·
                      rfl

theorem cell23_3178142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_3178142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178142 prefixEnd_3178142 := by exact prefixLift 3178142
  have htrace : WordTrace (prefixWord ++ tailWord_3178142) baseStart_3178142 baseEnd_3178142 := by
    simpa [prefixWord, tailWord_3178142, baseEnd_3178142] using wordTrace_append hprefix tailTrace_3178142
  have hstable : (prefixWord ++ tailWord_3178142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178142).length < 2 ^ (prefixWord ++ tailWord_3178142).sum := by decide
  have hdescent : baseEnd_3178142 < baseStart_3178142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178146 : List Nat := [3, 3, 1, 4, 2, 1, 1, 1, 7]
def baseStart_3178146 : Nat := 118140960795 + 3178146 * 2 ^ 59
def prefixEnd_3178146 : Nat := 4983230072969 + 3 ^ 40 * 3178146 * 2
def baseEnd_3178146 : Nat := 181324054240469746984331

theorem tailTrace_3178146 : CollatzResearch.WordTrace tailWord_3178146 prefixEnd_3178146 181324054240469746984331 := by
  unfold tailWord_3178146
  simp only [CollatzResearch.WordTrace]
  refine ⟨28979126886031825242164573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77277671696084867312438861 28979126886031825242164573)
  ·
    refine ⟨10867172582261934465811715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28979126886031825242164573 10867172582261934465811715)
    ·
      refine ⟨16300758873392901698717573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10867172582261934465811715 16300758873392901698717573)
      ·
        refine ⟨3056392288761169068509545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16300758873392901698717573 3056392288761169068509545)
        ·
          refine ⟨2292294216570876801382159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3056392288761169068509545 2292294216570876801382159)
          ·
            refine ⟨3438441324856315202073239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2292294216570876801382159 3438441324856315202073239)
            ·
              refine ⟨5157661987284472803109859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3438441324856315202073239 5157661987284472803109859)
              ·
                refine ⟨7736492980926709204664789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5157661987284472803109859 7736492980926709204664789)
                ·
                  refine ⟨181324054240469746984331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7736492980926709204664789 181324054240469746984331)
                  ·
                    rfl

theorem cell23_3178146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_3178146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178146 prefixEnd_3178146 := by exact prefixLift 3178146
  have htrace : WordTrace (prefixWord ++ tailWord_3178146) baseStart_3178146 baseEnd_3178146 := by
    simpa [prefixWord, tailWord_3178146, baseEnd_3178146] using wordTrace_append hprefix tailTrace_3178146
  have hstable : (prefixWord ++ tailWord_3178146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178146).length < 2 ^ (prefixWord ++ tailWord_3178146).sum := by decide
  have hdescent : baseEnd_3178146 < baseStart_3178146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178162 : List Nat := [3, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2]
def baseStart_3178162 : Nat := 118140960795 + 3178162 * 2 ^ 59
def prefixEnd_3178162 : Nat := 4983230072969 + 3 ^ 40 * 3178162 * 2
def baseEnd_3178162 : Nat := 1631924703854699660258905

theorem tailTrace_3178162 : CollatzResearch.WordTrace tailWord_3178162 prefixEnd_3178162 1631924703854699660258905 := by
  unfold tailWord_3178162
  simp only [CollatzResearch.WordTrace]
  refine ⟨28979272778017333925310185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77278060741379557134160493 28979272778017333925310185)
  ·
    refine ⟨21734454583513000443982639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28979272778017333925310185 21734454583513000443982639)
    ·
      refine ⟨32601681875269500665973959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21734454583513000443982639 32601681875269500665973959)
      ·
        refine ⟨48902522812904250998960939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32601681875269500665973959 48902522812904250998960939)
        ·
          refine ⟨73353784219356376498441409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48902522812904250998960939 73353784219356376498441409)
          ·
            refine ⟨55015338164517282373831057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73353784219356376498441409 55015338164517282373831057)
            ·
              refine ⟨41261503623387961780373293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55015338164517282373831057 41261503623387961780373293)
              ·
                refine ⟨15473063858770485667639985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41261503623387961780373293 15473063858770485667639985)
                ·
                  refine ⟨11604797894077864250729989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15473063858770485667639985 11604797894077864250729989)
                  ·
                    refine ⟨2175899605139599547011873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11604797894077864250729989 2175899605139599547011873)
                    ·
                      refine ⟨1631924703854699660258905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2175899605139599547011873 1631924703854699660258905)
                      ·
                        rfl

theorem cell23_3178162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2].length) (baseStart_3178162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178162 prefixEnd_3178162 := by exact prefixLift 3178162
  have htrace : WordTrace (prefixWord ++ tailWord_3178162) baseStart_3178162 baseEnd_3178162 := by
    simpa [prefixWord, tailWord_3178162, baseEnd_3178162] using wordTrace_append hprefix tailTrace_3178162
  have hstable : (prefixWord ++ tailWord_3178162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178162).length < 2 ^ (prefixWord ++ tailWord_3178162).sum := by decide
  have hdescent : baseEnd_3178162 < baseStart_3178162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178202 : List Nat := [3, 1, 1, 2, 2, 4, 2, 2, 6]
def baseStart_3178202 : Nat := 118140960795 + 3178202 * 2 ^ 59
def prefixEnd_3178202 : Nat := 4983230072969 + 3 ^ 40 * 3178202 * 2
def baseEnd_3178202 : Nat := 181327249231208833750969

theorem tailTrace_3178202 : CollatzResearch.WordTrace tailWord_3178202 prefixEnd_3178202 181327249231208833750969 := by
  unfold tailWord_3178202
  simp only [CollatzResearch.WordTrace]
  refine ⟨28979637507981105633174215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77279033354616281688464573 28979637507981105633174215)
  ·
    refine ⟨43469456261971658449761323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28979637507981105633174215 43469456261971658449761323)
    ·
      refine ⟨65204184392957487674641985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43469456261971658449761323 65204184392957487674641985)
      ·
        refine ⟨48903138294718115755981489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65204184392957487674641985 48903138294718115755981489)
        ·
          refine ⟨36677353721038586816986117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48903138294718115755981489 36677353721038586816986117)
          ·
            refine ⟨6877003822694735028184897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36677353721038586816986117 6877003822694735028184897)
            ·
              refine ⟨5157752867021051271138673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6877003822694735028184897 5157752867021051271138673)
              ·
                refine ⟨3868314650265788453354005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5157752867021051271138673 3868314650265788453354005)
                ·
                  refine ⟨181327249231208833750969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3868314650265788453354005 181327249231208833750969)
                  ·
                    rfl

theorem cell23_3178202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 6].length) (baseStart_3178202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178202 prefixEnd_3178202 := by exact prefixLift 3178202
  have htrace : WordTrace (prefixWord ++ tailWord_3178202) baseStart_3178202 baseEnd_3178202 := by
    simpa [prefixWord, tailWord_3178202, baseEnd_3178202] using wordTrace_append hprefix tailTrace_3178202
  have hstable : (prefixWord ++ tailWord_3178202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178202).length < 2 ^ (prefixWord ++ tailWord_3178202).sum := by decide
  have hdescent : baseEnd_3178202 < baseStart_3178202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178239 : List Nat := [1, 1, 2, 2, 1, 3, 5, 1, 2, 3, 2]
def baseStart_3178239 : Nat := 118140960795 + 3178239 * 2 ^ 59
def prefixEnd_3178239 : Nat := 4983230072969 + 3 ^ 40 * 3178239 * 2
def baseEnd_3178239 : Nat := 1631964241865095858996051

theorem tailTrace_3178239 : CollatzResearch.WordTrace tailWord_3178239 prefixEnd_3178239 1631964241865095858996051 := by
  unfold tailWord_3178239
  simp only [CollatzResearch.WordTrace]
  refine ⟨115919899532790377851793771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77279933021860251901195847 115919899532790377851793771)
  ·
    refine ⟨173879849299185566777690657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115919899532790377851793771 173879849299185566777690657)
    ·
      refine ⟨130409886974389175083267993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173879849299185566777690657 130409886974389175083267993)
      ·
        refine ⟨97807415230791881312450995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130409886974389175083267993 97807415230791881312450995)
        ·
          refine ⟨146711122846187821968676493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97807415230791881312450995 146711122846187821968676493)
          ·
            refine ⟨55016671067320433238253685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146711122846187821968676493 55016671067320433238253685)
            ·
              refine ⟨5157812912561290616086283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55016671067320433238253685 5157812912561290616086283)
              ·
                refine ⟨7736719368841935924129425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5157812912561290616086283 7736719368841935924129425)
                ·
                  refine ⟨5802539526631451943097069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7736719368841935924129425 5802539526631451943097069)
                  ·
                    refine ⟨2175952322486794478661401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5802539526631451943097069 2175952322486794478661401)
                    ·
                      refine ⟨1631964241865095858996051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2175952322486794478661401 1631964241865095858996051)
                      ·
                        rfl

theorem cell23_3178239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 3, 2].length) (baseStart_3178239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178239 prefixEnd_3178239 := by exact prefixLift 3178239
  have htrace : WordTrace (prefixWord ++ tailWord_3178239) baseStart_3178239 baseEnd_3178239 := by
    simpa [prefixWord, tailWord_3178239, baseEnd_3178239] using wordTrace_append hprefix tailTrace_3178239
  have hstable : (prefixWord ++ tailWord_3178239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178239).length < 2 ^ (prefixWord ++ tailWord_3178239).sum := by decide
  have hdescent : baseEnd_3178239 < baseStart_3178239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178253 : List Nat := [1, 7, 2, 1, 1, 1, 1, 1, 8]
def baseStart_3178253 : Nat := 118140960795 + 3178253 * 2 ^ 59
def prefixEnd_3178253 : Nat := 4983230072969 + 3 ^ 40 * 3178253 * 2
def baseEnd_3178253 : Nat := 181330158954917644913443

theorem tailTrace_3178253 : CollatzResearch.WordTrace tailWord_3178253 prefixEnd_3178253 181330158954917644913443 := by
  unfold tailWord_3178253
  simp only [CollatzResearch.WordTrace]
  refine ⟨115920410154739658242803413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77280273436493105495202275 115920410154739658242803413)
  ·
    refine ⟨2716884613001710740065705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 115920410154739658242803413 2716884613001710740065705)
    ·
      refine ⟨2037663459751283055049279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2716884613001710740065705 2037663459751283055049279)
      ·
        refine ⟨3056495189626924582573919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2037663459751283055049279 3056495189626924582573919)
        ·
          refine ⟨4584742784440386873860879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3056495189626924582573919 4584742784440386873860879)
          ·
            refine ⟨6877114176660580310791319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4584742784440386873860879 6877114176660580310791319)
            ·
              refine ⟨10315671264990870466186979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6877114176660580310791319 10315671264990870466186979)
              ·
                refine ⟨15473506897486305699280469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10315671264990870466186979 15473506897486305699280469)
                ·
                  refine ⟨181330158954917644913443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15473506897486305699280469 181330158954917644913443)
                  ·
                    rfl

theorem cell23_3178253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_3178253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178253 prefixEnd_3178253 := by exact prefixLift 3178253
  have htrace : WordTrace (prefixWord ++ tailWord_3178253) baseStart_3178253 baseEnd_3178253 := by
    simpa [prefixWord, tailWord_3178253, baseEnd_3178253] using wordTrace_append hprefix tailTrace_3178253
  have hstable : (prefixWord ++ tailWord_3178253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178253).length < 2 ^ (prefixWord ++ tailWord_3178253).sum := by decide
  have hdescent : baseEnd_3178253 < baseStart_3178253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178272 : List Nat := [2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 5]
def baseStart_3178272 : Nat := 118140960795 + 3178272 * 2 ^ 59
def prefixEnd_3178272 : Nat := 4983230072969 + 3 ^ 40 * 3178272 * 2
def baseEnd_3178272 : Nat := 1631981186726694229883399

theorem tailTrace_3178272 : CollatzResearch.WordTrace tailWord_3178272 prefixEnd_3178272 1631981186726694229883399 := by
  unfold tailWord_3178272
  simp only [CollatzResearch.WordTrace]
  refine ⟨57960551570835412243872535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77280735427780549658496713 57960551570835412243872535)
  ·
    refine ⟨86940827356253118365808803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57960551570835412243872535 86940827356253118365808803)
    ·
      refine ⟨130411241034379677548713205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86940827356253118365808803 130411241034379677548713205)
      ·
        refine ⟨12226053846973094770191863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130411241034379677548713205 12226053846973094770191863)
        ·
          refine ⟨18339080770459642155287795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12226053846973094770191863 18339080770459642155287795)
          ·
            refine ⟨27508621155689463232931693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18339080770459642155287795 27508621155689463232931693)
            ·
              refine ⟨10315732933383548712349385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27508621155689463232931693 10315732933383548712349385)
              ·
                refine ⟨7736799700037661534262039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10315732933383548712349385 7736799700037661534262039)
                ·
                  refine ⟨11605199550056492301393059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7736799700037661534262039 11605199550056492301393059)
                  ·
                    refine ⟨17407799325084738452089589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11605199550056492301393059 17407799325084738452089589)
                    ·
                      refine ⟨1631981186726694229883399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17407799325084738452089589 1631981186726694229883399)
                      ·
                        rfl

theorem cell23_3178272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_3178272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178272 prefixEnd_3178272 := by exact prefixLift 3178272
  have htrace : WordTrace (prefixWord ++ tailWord_3178272) baseStart_3178272 baseEnd_3178272 := by
    simpa [prefixWord, tailWord_3178272, baseEnd_3178272] using wordTrace_append hprefix tailTrace_3178272
  have hstable : (prefixWord ++ tailWord_3178272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178272).length < 2 ^ (prefixWord ++ tailWord_3178272).sum := by decide
  have hdescent : baseEnd_3178272 < baseStart_3178272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178289 : List Nat := [1, 2, 2, 3, 2, 2, 1, 4, 1, 2, 3]
def baseStart_3178289 : Nat := 118140960795 + 3178289 * 2 ^ 59
def prefixEnd_3178289 : Nat := 4983230072969 + 3 ^ 40 * 3178289 * 2
def baseEnd_3178289 : Nat := 1631989915897820663370821

theorem tailTrace_3178289 : CollatzResearch.WordTrace tailWord_3178289 prefixEnd_3178289 1631989915897820663370821 := by
  unfold tailWord_3178289
  simp only [CollatzResearch.WordTrace]
  refine ⟨115921723182609236391113921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77281148788406157594075947 115921723182609236391113921)
  ·
    refine ⟨86941292386956927293335441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115921723182609236391113921 86941292386956927293335441)
    ·
      refine ⟨65205969290217695470001581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86941292386956927293335441 65205969290217695470001581)
      ·
        refine ⟨24452238483831635801250593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65205969290217695470001581 24452238483831635801250593)
        ·
          refine ⟨18339178862873726850937945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24452238483831635801250593 18339178862873726850937945)
          ·
            refine ⟨13754384147155295138203459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18339178862873726850937945 13754384147155295138203459)
            ·
              refine ⟨20631576220732942707305189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13754384147155295138203459 20631576220732942707305189)
              ·
                refine ⟨3868420541387426757619723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20631576220732942707305189 3868420541387426757619723)
                ·
                  refine ⟨5802630812081140136429585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3868420541387426757619723 5802630812081140136429585)
                  ·
                    refine ⟨4351973109060855102322189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5802630812081140136429585 4351973109060855102322189)
                    ·
                      refine ⟨1631989915897820663370821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4351973109060855102322189 1631989915897820663370821)
                      ·
                        rfl

theorem cell23_3178289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_3178289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178289 prefixEnd_3178289 := by exact prefixLift 3178289
  have htrace : WordTrace (prefixWord ++ tailWord_3178289) baseStart_3178289 baseEnd_3178289 := by
    simpa [prefixWord, tailWord_3178289, baseEnd_3178289] using wordTrace_append hprefix tailTrace_3178289
  have hstable : (prefixWord ++ tailWord_3178289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178289).length < 2 ^ (prefixWord ++ tailWord_3178289).sum := by decide
  have hdescent : baseEnd_3178289 < baseStart_3178289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178297 : List Nat := [1, 2, 1, 7, 2, 1, 1, 3, 1, 1, 3]
def baseStart_3178297 : Nat := 118140960795 + 3178297 * 2 ^ 59
def prefixEnd_3178297 : Nat := 4983230072969 + 3 ^ 40 * 3178297 * 2
def baseEnd_3178297 : Nat := 1631994023743056632070785

theorem tailTrace_3178297 : CollatzResearch.WordTrace tailWord_3178297 prefixEnd_3178297 1631994023743056632070785 := by
  unfold tailWord_3178297
  simp only [CollatzResearch.WordTrace]
  refine ⟨115922014966580253757405145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77281343311053502504936763 115922014966580253757405145)
  ·
    refine ⟨86941511224935190318053859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115922014966580253757405145 86941511224935190318053859)
    ·
      refine ⟨130412266837402785477080789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86941511224935190318053859 130412266837402785477080789)
      ·
        refine ⟨3056537504001627784619081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 130412266837402785477080789 3056537504001627784619081)
        ·
          refine ⟨2292403128001220838464311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3056537504001627784619081 2292403128001220838464311)
          ·
            refine ⟨3438604692001831257696467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2292403128001220838464311 3438604692001831257696467)
            ·
              refine ⟨5157907038002746886544701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3438604692001831257696467 5157907038002746886544701)
              ·
                refine ⟨1934215139251030082454263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5157907038002746886544701 1934215139251030082454263)
                ·
                  refine ⟨2901322708876545123681395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1934215139251030082454263 2901322708876545123681395)
                  ·
                    refine ⟨4351984063314817685522093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2901322708876545123681395 4351984063314817685522093)
                    ·
                      refine ⟨1631994023743056632070785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4351984063314817685522093 1631994023743056632070785)
                      ·
                        rfl

theorem cell23_3178297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_3178297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178297 prefixEnd_3178297 := by exact prefixLift 3178297
  have htrace : WordTrace (prefixWord ++ tailWord_3178297) baseStart_3178297 baseEnd_3178297 := by
    simpa [prefixWord, tailWord_3178297, baseEnd_3178297] using wordTrace_append hprefix tailTrace_3178297
  have hstable : (prefixWord ++ tailWord_3178297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178297).length < 2 ^ (prefixWord ++ tailWord_3178297).sum := by decide
  have hdescent : baseEnd_3178297 < baseStart_3178297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178329 : List Nat := [1, 2, 1, 2, 2, 3, 2, 2, 3, 3, 2]
def baseStart_3178329 : Nat := 118140960795 + 3178329 * 2 ^ 59
def prefixEnd_3178329 : Nat := 4983230072969 + 3 ^ 40 * 3178329 * 2
def baseEnd_3178329 : Nat := 1632010455124000506870637

theorem tailTrace_3178329 : CollatzResearch.WordTrace tailWord_3178329 prefixEnd_3178329 1632010455124000506870637 := by
  unfold tailWord_3178329
  simp only [CollatzResearch.WordTrace]
  refine ⟨115923182102464323222570041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77282121401642882148380027 115923182102464323222570041)
  ·
    refine ⟨86942386576848242416927531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115923182102464323222570041 86942386576848242416927531)
    ·
      refine ⟨130413579865272363625391297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86942386576848242416927531 130413579865272363625391297)
      ·
        refine ⟨97810184898954272719043473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130413579865272363625391297 97810184898954272719043473)
        ·
          refine ⟨73357638674215704539282605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97810184898954272719043473 73357638674215704539282605)
          ·
            refine ⟨27509114502830889202230977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73357638674215704539282605 27509114502830889202230977)
            ·
              refine ⟨20631835877123166901673233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27509114502830889202230977 20631835877123166901673233)
              ·
                refine ⟨15473876907842375176254925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20631835877123166901673233 15473876907842375176254925)
                ·
                  refine ⟨5802703840440890691095597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15473876907842375176254925 5802703840440890691095597)
                  ·
                    refine ⟨2176013940165334009160849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5802703840440890691095597 2176013940165334009160849)
                    ·
                      refine ⟨1632010455124000506870637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2176013940165334009160849 1632010455124000506870637)
                      ·
                        rfl

theorem cell23_3178329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 3, 2].length) (baseStart_3178329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178329 prefixEnd_3178329 := by exact prefixLift 3178329
  have htrace : WordTrace (prefixWord ++ tailWord_3178329) baseStart_3178329 baseEnd_3178329 := by
    simpa [prefixWord, tailWord_3178329, baseEnd_3178329] using wordTrace_append hprefix tailTrace_3178329
  have hstable : (prefixWord ++ tailWord_3178329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178329).length < 2 ^ (prefixWord ++ tailWord_3178329).sum := by decide
  have hdescent : baseEnd_3178329 < baseStart_3178329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178336 : List Nat := [2, 1, 1, 3, 3, 3, 1, 3, 2, 1, 3]
def baseStart_3178336 : Nat := 118140960795 + 3178336 * 2 ^ 59
def prefixEnd_3178336 : Nat := 4983230072969 + 3 ^ 40 * 3178336 * 2
def baseEnd_3178336 : Nat := 1632014049488581979483105

theorem tailTrace_3178336 : CollatzResearch.WordTrace tailWord_3178336 prefixEnd_3178336 1632014049488581979483105 := by
  unfold tailWord_3178336
  simp only [CollatzResearch.WordTrace]
  refine ⟨57961718706719481709037431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77282291608959308945383241 57961718706719481709037431)
  ·
    refine ⟨86942578060079222563556147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57961718706719481709037431 86942578060079222563556147)
    ·
      refine ⟨130413867090118833845334221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86942578060079222563556147 130413867090118833845334221)
      ·
        refine ⟨48905200158794562692000333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130413867090118833845334221 48905200158794562692000333)
        ·
          refine ⟨18339450059547961009500125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48905200158794562692000333 18339450059547961009500125)
          ·
            refine ⟨6877293772330485378562547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18339450059547961009500125 6877293772330485378562547)
            ·
              refine ⟨10315940658495728067843821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6877293772330485378562547 10315940658495728067843821)
              ·
                refine ⟨3868477746935898025441433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10315940658495728067843821 3868477746935898025441433)
                ·
                  refine ⟨2901358310201923519081075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3868477746935898025441433 2901358310201923519081075)
                  ·
                    refine ⟨4352037465302885278621613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2901358310201923519081075 4352037465302885278621613)
                    ·
                      refine ⟨1632014049488581979483105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4352037465302885278621613 1632014049488581979483105)
                      ·
                        rfl

theorem cell23_3178336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 2, 1, 3].length) (baseStart_3178336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178336 prefixEnd_3178336 := by exact prefixLift 3178336
  have htrace : WordTrace (prefixWord ++ tailWord_3178336) baseStart_3178336 baseEnd_3178336 := by
    simpa [prefixWord, tailWord_3178336, baseEnd_3178336] using wordTrace_append hprefix tailTrace_3178336
  have hstable : (prefixWord ++ tailWord_3178336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178336).length < 2 ^ (prefixWord ++ tailWord_3178336).sum := by decide
  have hdescent : baseEnd_3178336 < baseStart_3178336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178362 : List Nat := [3, 1, 1, 1, 1, 1, 6, 1, 2, 1, 5]
def baseStart_3178362 : Nat := 118140960795 + 3178362 * 2 ^ 59
def prefixEnd_3178362 : Nat := 4983230072969 + 3 ^ 40 * 3178362 * 2
def baseEnd_3178362 : Nat := 1632027399985598877757985

theorem tailTrace_3178362 : CollatzResearch.WordTrace tailWord_3178362 prefixEnd_3178362 1632027399985598877757985 := by
  unfold tailWord_3178362
  simp only [CollatzResearch.WordTrace]
  refine ⟨28981096427836192464630335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77282923807563179905680893 28981096427836192464630335)
  ·
    refine ⟨43471644641754288696945503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28981096427836192464630335 43471644641754288696945503)
    ·
      refine ⟨65207466962631433045418255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43471644641754288696945503 65207466962631433045418255)
      ·
        refine ⟨97811200443947149568127383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65207466962631433045418255 97811200443947149568127383)
        ·
          refine ⟨146716800665920724352191075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97811200443947149568127383 146716800665920724352191075)
          ·
            refine ⟨220075200998881086528286613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146716800665920724352191075 220075200998881086528286613)
            ·
              refine ⟨10316025046822550931013435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 220075200998881086528286613 10316025046822550931013435)
              ·
                refine ⟨15474037570233826396520153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10316025046822550931013435 15474037570233826396520153)
                ·
                  refine ⟨11605528177675369797390115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15474037570233826396520153 11605528177675369797390115)
                  ·
                    refine ⟨17408292266513054696085173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11605528177675369797390115 17408292266513054696085173)
                    ·
                      refine ⟨1632027399985598877757985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17408292266513054696085173 1632027399985598877757985)
                      ·
                        rfl

theorem cell23_3178362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 2, 1, 5].length) (baseStart_3178362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178362 prefixEnd_3178362 := by exact prefixLift 3178362
  have htrace : WordTrace (prefixWord ++ tailWord_3178362) baseStart_3178362 baseEnd_3178362 := by
    simpa [prefixWord, tailWord_3178362, baseEnd_3178362] using wordTrace_append hprefix tailTrace_3178362
  have hstable : (prefixWord ++ tailWord_3178362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178362).length < 2 ^ (prefixWord ++ tailWord_3178362).sum := by decide
  have hdescent : baseEnd_3178362 < baseStart_3178362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178399 : List Nat := [1, 1, 2, 5, 3, 1, 1, 2, 7]
def baseStart_3178399 : Nat := 118140960795 + 3178399 * 2 ^ 59
def prefixEnd_3178399 : Nat := 4983230072969 + 3 ^ 40 * 3178399 * 2
def baseEnd_3178399 : Nat := 181338488752201692555035

theorem tailTrace_3178399 : CollatzResearch.WordTrace tailWord_3178399 prefixEnd_3178399 181338488752201692555035 := by
  unfold tailWord_3178399
  simp only [CollatzResearch.WordTrace]
  refine ⟨115925735212210725177618251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77283823474807150118412167 115925735212210725177618251)
  ·
    refine ⟨173888602818316087766427377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115925735212210725177618251 173888602818316087766427377)
    ·
      refine ⟨130416452113737065824820533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173888602818316087766427377 130416452113737065824820533)
      ·
        refine ⟨12226542385662849921076925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130416452113737065824820533 12226542385662849921076925)
        ·
          refine ⟨4584953394623568720403847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12226542385662849921076925 4584953394623568720403847)
          ·
            refine ⟨6877430091935353080605771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4584953394623568720403847 6877430091935353080605771)
            ·
              refine ⟨10316145137903029620908657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6877430091935353080605771 10316145137903029620908657)
              ·
                refine ⟨7737108853427272215681493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10316145137903029620908657 7737108853427272215681493)
                ·
                  refine ⟨181338488752201692555035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7737108853427272215681493 181338488752201692555035)
                  ·
                    rfl

theorem cell23_3178399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 7].length) (baseStart_3178399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178399 prefixEnd_3178399 := by exact prefixLift 3178399
  have htrace : WordTrace (prefixWord ++ tailWord_3178399) baseStart_3178399 baseEnd_3178399 := by
    simpa [prefixWord, tailWord_3178399, baseEnd_3178399] using wordTrace_append hprefix tailTrace_3178399
  have hstable : (prefixWord ++ tailWord_3178399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178399).length < 2 ^ (prefixWord ++ tailWord_3178399).sum := by decide
  have hdescent : baseEnd_3178399 < baseStart_3178399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178449 : List Nat := [1, 2, 2, 1, 2, 1, 2, 3, 1, 6, 2]
def baseStart_3178449 : Nat := 118140960795 + 3178449 * 2 ^ 59
def prefixEnd_3178449 : Nat := 4983230072969 + 3 ^ 40 * 3178449 * 2
def baseEnd_3178449 : Nat := 1632072072802540037370085

theorem tailTrace_3178449 : CollatzResearch.WordTrace tailWord_3178449 prefixEnd_3178449 1632072072802540037370085 := by
  unfold tailWord_3178449
  simp only [CollatzResearch.WordTrace]
  refine ⟨115927558862029583716938401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77285039241353055811292267 115927558862029583716938401)
  ·
    refine ⟨86945669146522187787703801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115927558862029583716938401 86945669146522187787703801)
    ·
      refine ⟨65209251859891640840777851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86945669146522187787703801 65209251859891640840777851)
      ·
        refine ⟨97813877789837461261166777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65209251859891640840777851 97813877789837461261166777)
        ·
          refine ⟨73360408342378095945875083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97813877789837461261166777 73360408342378095945875083)
          ·
            refine ⟨110040612513567143918812625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73360408342378095945875083 110040612513567143918812625)
            ·
              refine ⟨82530459385175357939109469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110040612513567143918812625 82530459385175357939109469)
              ·
                refine ⟨30948922269440759227166051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82530459385175357939109469 30948922269440759227166051)
                ·
                  refine ⟨46423383404161138840749077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30948922269440759227166051 46423383404161138840749077)
                  ·
                    refine ⟨2176096097070053383160113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 46423383404161138840749077 2176096097070053383160113)
                    ·
                      refine ⟨1632072072802540037370085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2176096097070053383160113 1632072072802540037370085)
                      ·
                        rfl

theorem cell23_3178449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 6, 2].length) (baseStart_3178449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178449 prefixEnd_3178449 := by exact prefixLift 3178449
  have htrace : WordTrace (prefixWord ++ tailWord_3178449) baseStart_3178449 baseEnd_3178449 := by
    simpa [prefixWord, tailWord_3178449, baseEnd_3178449] using wordTrace_append hprefix tailTrace_3178449
  have hstable : (prefixWord ++ tailWord_3178449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178449).length < 2 ^ (prefixWord ++ tailWord_3178449).sum := by decide
  have hdescent : baseEnd_3178449 < baseStart_3178449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178506 : List Nat := [3, 1, 2, 2, 4, 1, 1, 3, 6]
def baseStart_3178506 : Nat := 118140960795 + 3178506 * 2 ^ 59
def prefixEnd_3178506 : Nat := 4983230072969 + 3 ^ 40 * 3178506 * 2
def baseEnd_3178506 : Nat := 181344593466649590484147

theorem tailTrace_3178506 : CollatzResearch.WordTrace tailWord_3178506 prefixEnd_3178506 181344593466649590484147 := by
  unfold tailWord_3178506
  simp only [CollatzResearch.WordTrace]
  refine ⟨28982409455705770612940843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77286425215215388301175581 28982409455705770612940843)
  ·
    refine ⟨43473614183558655919411265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28982409455705770612940843 43473614183558655919411265)
    ·
      refine ⟨32605210637668991939558449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43473614183558655919411265 32605210637668991939558449)
      ·
        refine ⟨24453907978251743954668837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32605210637668991939558449 24453907978251743954668837)
        ·
          refine ⟨4585107745922201991500407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24453907978251743954668837 4585107745922201991500407)
          ·
            refine ⟨6877661618883302987250611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4585107745922201991500407 6877661618883302987250611)
            ·
              refine ⟨10316492428324954480875917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6877661618883302987250611 10316492428324954480875917)
              ·
                refine ⟨3868684660621857930328469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10316492428324954480875917 3868684660621857930328469)
                ·
                  refine ⟨181344593466649590484147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3868684660621857930328469 181344593466649590484147)
                  ·
                    rfl

theorem cell23_3178506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 6].length) (baseStart_3178506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178506 prefixEnd_3178506 := by exact prefixLift 3178506
  have htrace : WordTrace (prefixWord ++ tailWord_3178506) baseStart_3178506 baseEnd_3178506 := by
    simpa [prefixWord, tailWord_3178506, baseEnd_3178506] using wordTrace_append hprefix tailTrace_3178506
  have hstable : (prefixWord ++ tailWord_3178506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178506).length < 2 ^ (prefixWord ++ tailWord_3178506).sum := by decide
  have hdescent : baseEnd_3178506 < baseStart_3178506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178512 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 7]
def baseStart_3178512 : Nat := 118140960795 + 3178512 * 2 ^ 59
def prefixEnd_3178512 : Nat := 4983230072969 + 3 ^ 40 * 3178512 * 2
def baseEnd_3178512 : Nat := 1632104422083773290882295

theorem tailTrace_3178512 : CollatzResearch.WordTrace tailWord_3178512 prefixEnd_3178512 1632104422083773290882295 := by
  unfold tailWord_3178512
  simp only [CollatzResearch.WordTrace]
  refine ⟨57964928330400672738240895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77286571107200896984321193 57964928330400672738240895)
  ·
    refine ⟨86947392495601009107361343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57964928330400672738240895 86947392495601009107361343)
    ·
      refine ⟨130421088743401513661042015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86947392495601009107361343 130421088743401513661042015)
      ·
        refine ⟨195631633115102270491563023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130421088743401513661042015 195631633115102270491563023)
        ·
          refine ⟨293447449672653405737344535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195631633115102270491563023 293447449672653405737344535)
          ·
            refine ⟨440171174508980108606016803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293447449672653405737344535 440171174508980108606016803)
            ·
              refine ⟨660256761763470162909025205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440171174508980108606016803 660256761763470162909025205)
              ·
                refine ⟨61899071415325327772721113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 660256761763470162909025205 61899071415325327772721113)
                ·
                  refine ⟨46424303561493995829540835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61899071415325327772721113 46424303561493995829540835)
                  ·
                    refine ⟨69636455342240993744311253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46424303561493995829540835 69636455342240993744311253)
                    ·
                      refine ⟨1632104422083773290882295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 69636455342240993744311253 1632104422083773290882295)
                      ·
                        rfl

theorem cell23_3178512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 7].length) (baseStart_3178512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178512 prefixEnd_3178512 := by exact prefixLift 3178512
  have htrace : WordTrace (prefixWord ++ tailWord_3178512) baseStart_3178512 baseEnd_3178512 := by
    simpa [prefixWord, tailWord_3178512, baseEnd_3178512] using wordTrace_append hprefix tailTrace_3178512
  have hstable : (prefixWord ++ tailWord_3178512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178512).length < 2 ^ (prefixWord ++ tailWord_3178512).sum := by decide
  have hdescent : baseEnd_3178512 < baseStart_3178512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178559 : List Nat := [1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 5]
def baseStart_3178559 : Nat := 118140960795 + 3178559 * 2 ^ 59
def prefixEnd_3178559 : Nat := 4983230072969 + 3 ^ 40 * 3178559 * 2
def baseEnd_3178559 : Nat := 1632128555674534606994579

theorem tailTrace_3178559 : CollatzResearch.WordTrace tailWord_3178559 prefixEnd_3178559 1632128555674534606994579 := by
  unfold tailWord_3178559
  simp only [CollatzResearch.WordTrace]
  refine ⟨115931570891631072503442731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77287713927754048335628487 115931570891631072503442731)
  ·
    refine ⟨173897356337446608755164097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115931570891631072503442731 173897356337446608755164097)
    ·
      refine ⟨130423017253084956566373073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173897356337446608755164097 130423017253084956566373073)
      ·
        refine ⟨97817262939813717424779805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130423017253084956566373073 97817262939813717424779805)
        ·
          refine ⟨36681473602430144034292427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97817262939813717424779805 36681473602430144034292427)
          ·
            refine ⟨55022210403645216051438641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36681473602430144034292427 55022210403645216051438641)
            ·
              refine ⟨41266657802733912038578981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55022210403645216051438641 41266657802733912038578981)
              ·
                refine ⟨7737498338012608507233559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41266657802733912038578981 7737498338012608507233559)
                ·
                  refine ⟨11606247507018912760850339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7737498338012608507233559 11606247507018912760850339)
                  ·
                    refine ⟨17409371260528369141275509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11606247507018912760850339 17409371260528369141275509)
                    ·
                      refine ⟨1632128555674534606994579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17409371260528369141275509 1632128555674534606994579)
                      ·
                        rfl

theorem cell23_3178559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 5].length) (baseStart_3178559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178559 prefixEnd_3178559 := by exact prefixLift 3178559
  have htrace : WordTrace (prefixWord ++ tailWord_3178559) baseStart_3178559 baseEnd_3178559 := by
    simpa [prefixWord, tailWord_3178559, baseEnd_3178559] using wordTrace_append hprefix tailTrace_3178559
  have hstable : (prefixWord ++ tailWord_3178559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178559).length < 2 ^ (prefixWord ++ tailWord_3178559).sum := by decide
  have hdescent : baseEnd_3178559 < baseStart_3178559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178573 : List Nat := [1, 6, 1, 1, 1, 1, 2, 4, 1, 1, 4]
def baseStart_3178573 : Nat := 118140960795 + 3178573 * 2 ^ 59
def prefixEnd_3178573 : Nat := 4983230072969 + 3 ^ 40 * 3178573 * 2
def baseEnd_3178573 : Nat := 1632135744403697552219515

theorem tailTrace_3178573 : CollatzResearch.WordTrace tailWord_3178573 prefixEnd_3178573 1632135744403697552219515 := by
  unfold tailWord_3178573
  simp only [CollatzResearch.WordTrace]
  refine ⟨115932081513580352894452373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77288054342386901929634915 115932081513580352894452373)
  ·
    refine ⟨5434316320949079041927455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 115932081513580352894452373 5434316320949079041927455)
    ·
      refine ⟨8151474481423618562891183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5434316320949079041927455 8151474481423618562891183)
      ·
        refine ⟨12227211722135427844336775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8151474481423618562891183 12227211722135427844336775)
        ·
          refine ⟨18340817583203141766505163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12227211722135427844336775 18340817583203141766505163)
          ·
            refine ⟨27511226374804712649757745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18340817583203141766505163 27511226374804712649757745)
            ·
              refine ⟨20633419781103534487318309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27511226374804712649757745 20633419781103534487318309)
              ·
                refine ⟨3868766208956912716372183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20633419781103534487318309 3868766208956912716372183)
                ·
                  refine ⟨5803149313435369074558275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3868766208956912716372183 5803149313435369074558275)
                  ·
                    refine ⟨8704723970153053611837413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5803149313435369074558275 8704723970153053611837413)
                    ·
                      refine ⟨1632135744403697552219515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8704723970153053611837413 1632135744403697552219515)
                      ·
                        rfl

theorem cell23_3178573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_3178573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178573 prefixEnd_3178573 := by exact prefixLift 3178573
  have htrace : WordTrace (prefixWord ++ tailWord_3178573) baseStart_3178573 baseEnd_3178573 := by
    simpa [prefixWord, tailWord_3178573, baseEnd_3178573] using wordTrace_append hprefix tailTrace_3178573
  have hstable : (prefixWord ++ tailWord_3178573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178573).length < 2 ^ (prefixWord ++ tailWord_3178573).sum := by decide
  have hdescent : baseEnd_3178573 < baseStart_3178573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178680 : List Nat := [2, 1, 2, 1, 2, 1, 5, 3, 2, 2, 2]
def baseStart_3178680 : Nat := 118140960795 + 3178680 * 2 ^ 59
def prefixEnd_3178680 : Nat := 4983230072969 + 3 ^ 40 * 3178680 * 2
def baseEnd_3178680 : Nat := 1632190686833728633581523

theorem tailTrace_3178680 : CollatzResearch.WordTrace tailWord_3178680 prefixEnd_3178680 1632190686833728633581523 := by
  unfold tailWord_3178680
  simp only [CollatzResearch.WordTrace]
  refine ⟨57967992062096355084298747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77290656082795140112398329 57967992062096355084298747)
  ·
    refine ⟨86951988093144532626448121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57967992062096355084298747 86951988093144532626448121)
    ·
      refine ⟨65213991069858399469836091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86951988093144532626448121 65213991069858399469836091)
      ·
        refine ⟨97820986604787599204754137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65213991069858399469836091 97820986604787599204754137)
        ·
          refine ⟨73365739953590699403565603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97820986604787599204754137 73365739953590699403565603)
          ·
            refine ⟨110048609930386049105348405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73365739953590699403565603 110048609930386049105348405)
            ·
              refine ⟨10317057180973692103626413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110048609930386049105348405 10317057180973692103626413)
              ·
                refine ⟨3868896442865134538859905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10317057180973692103626413 3868896442865134538859905)
                ·
                  refine ⟨2901672332148850904144929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3868896442865134538859905 2901672332148850904144929)
                  ·
                    refine ⟨2176254249111638178108697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2901672332148850904144929 2176254249111638178108697)
                    ·
                      refine ⟨1632190686833728633581523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2176254249111638178108697 1632190686833728633581523)
                      ·
                        rfl

theorem cell23_3178680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 2, 2, 2].length) (baseStart_3178680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178680 prefixEnd_3178680 := by exact prefixLift 3178680
  have htrace : WordTrace (prefixWord ++ tailWord_3178680) baseStart_3178680 baseEnd_3178680 := by
    simpa [prefixWord, tailWord_3178680, baseEnd_3178680] using wordTrace_append hprefix tailTrace_3178680
  have hstable : (prefixWord ++ tailWord_3178680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178680).length < 2 ^ (prefixWord ++ tailWord_3178680).sum := by decide
  have hdescent : baseEnd_3178680 < baseStart_3178680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178684 : List Nat := [2, 2, 2, 3, 4, 1, 1, 2, 1, 3, 2]
def baseStart_3178684 : Nat := 118140960795 + 3178684 * 2 ^ 59
def prefixEnd_3178684 : Nat := 4983230072969 + 3 ^ 40 * 3178684 * 2
def baseEnd_3178684 : Nat := 1632192740756346617931505

theorem tailTrace_3178684 : CollatzResearch.WordTrace tailWord_3178684 prefixEnd_3178684 1632192740756346617931505 := by
  unfold tailWord_3178684
  simp only [CollatzResearch.WordTrace]
  refine ⟨57968065008089109425871553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77290753344118812567828737 57968065008089109425871553)
  ·
    refine ⟨43476048756066832069403665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57968065008089109425871553 43476048756066832069403665)
    ·
      refine ⟨32607036567050124052052749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43476048756066832069403665 32607036567050124052052749)
      ·
        refine ⟨12227638712643796519519781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32607036567050124052052749 12227638712643796519519781)
        ·
          refine ⟨2292682258620711847409959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12227638712643796519519781 2292682258620711847409959)
          ·
            refine ⟨3439023387931067771114939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2292682258620711847409959 3439023387931067771114939)
            ·
              refine ⟨5158535081896601656672409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3439023387931067771114939 5158535081896601656672409)
              ·
                refine ⟨3868901311422451242504307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5158535081896601656672409 3868901311422451242504307)
                ·
                  refine ⟨5803351967133676863756461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3868901311422451242504307 5803351967133676863756461)
                  ·
                    refine ⟨2176256987675128823908673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5803351967133676863756461 2176256987675128823908673)
                    ·
                      refine ⟨1632192740756346617931505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2176256987675128823908673 1632192740756346617931505)
                      ·
                        rfl

theorem cell23_3178684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_3178684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178684 prefixEnd_3178684 := by exact prefixLift 3178684
  have htrace : WordTrace (prefixWord ++ tailWord_3178684) baseStart_3178684 baseEnd_3178684 := by
    simpa [prefixWord, tailWord_3178684, baseEnd_3178684] using wordTrace_append hprefix tailTrace_3178684
  have hstable : (prefixWord ++ tailWord_3178684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178684).length < 2 ^ (prefixWord ++ tailWord_3178684).sum := by decide
  have hdescent : baseEnd_3178684 < baseStart_3178684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178696 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 4, 3, 3]
def baseStart_3178696 : Nat := 118140960795 + 3178696 * 2 ^ 59
def prefixEnd_3178696 : Nat := 4983230072969 + 3 ^ 40 * 3178696 * 2
def baseEnd_3178696 : Nat := 1632198902524200570981449

theorem tailTrace_3178696 : CollatzResearch.WordTrace tailWord_3178696 prefixEnd_3178696 1632198902524200570981449 := by
  unfold tailWord_3178696
  simp only [CollatzResearch.WordTrace]
  refine ⟨57968283846067372450589971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77291045128089829934119961 57968283846067372450589971)
  ·
    refine ⟨86952425769101058675884957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57968283846067372450589971 86952425769101058675884957)
    ·
      refine ⟨32607159663412897003456859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86952425769101058675884957 32607159663412897003456859)
      ·
        refine ⟨48910739495119345505185289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32607159663412897003456859 48910739495119345505185289)
        ·
          refine ⟨36683054621339509128888967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48910739495119345505185289 36683054621339509128888967)
          ·
            refine ⟨55024581932009263693333451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36683054621339509128888967 55024581932009263693333451)
            ·
              refine ⟨82536872898013895540000177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55024581932009263693333451 82536872898013895540000177)
              ·
                refine ⟨61902654673510421655000133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82536872898013895540000177 61902654673510421655000133)
                ·
                  refine ⟨11606747751283204060312525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61902654673510421655000133 11606747751283204060312525)
                  ·
                    refine ⟨4352530406731201522617197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11606747751283204060312525 4352530406731201522617197)
                    ·
                      refine ⟨1632198902524200570981449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4352530406731201522617197 1632198902524200570981449)
                      ·
                        rfl

theorem cell23_3178696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_3178696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178696 prefixEnd_3178696 := by exact prefixLift 3178696
  have htrace : WordTrace (prefixWord ++ tailWord_3178696) baseStart_3178696 baseEnd_3178696 := by
    simpa [prefixWord, tailWord_3178696, baseEnd_3178696] using wordTrace_append hprefix tailTrace_3178696
  have hstable : (prefixWord ++ tailWord_3178696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178696).length < 2 ^ (prefixWord ++ tailWord_3178696).sum := by decide
  have hdescent : baseEnd_3178696 < baseStart_3178696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178736 : List Nat := [2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 4]
def baseStart_3178736 : Nat := 118140960795 + 3178736 * 2 ^ 59
def prefixEnd_3178736 : Nat := 4983230072969 + 3 ^ 40 * 3178736 * 2
def baseEnd_3178736 : Nat := 1632219441750380414481265

theorem tailTrace_3178736 : CollatzResearch.WordTrace tailWord_3178736 prefixEnd_3178736 1632219441750380414481265 := by
  unfold tailWord_3178736
  simp only [CollatzResearch.WordTrace]
  refine ⟨57969013305994915866318031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77292017741326554488424041 57969013305994915866318031)
  ·
    refine ⟨86953519958992373799477047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57969013305994915866318031 86953519958992373799477047)
    ·
      refine ⟨130430279938488560699215571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86953519958992373799477047 130430279938488560699215571)
      ·
        refine ⟨195645419907732841048823357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130430279938488560699215571 195645419907732841048823357)
        ·
          refine ⟨73367032465399815393308759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195645419907732841048823357 73367032465399815393308759)
          ·
            refine ⟨110050548698099723089963139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73367032465399815393308759 110050548698099723089963139)
            ·
              refine ⟨165075823047149584634944709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110050548698099723089963139 165075823047149584634944709)
              ·
                refine ⟨30951716821340547119052133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 165075823047149584634944709 30951716821340547119052133)
                ·
                  refine ⟨5803446904001352584822275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30951716821340547119052133 5803446904001352584822275)
                  ·
                    refine ⟨8705170356002028877233413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5803446904001352584822275 8705170356002028877233413)
                    ·
                      refine ⟨1632219441750380414481265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8705170356002028877233413 1632219441750380414481265)
                      ·
                        rfl

theorem cell23_3178736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 4].length) (baseStart_3178736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178736 prefixEnd_3178736 := by exact prefixLift 3178736
  have htrace : WordTrace (prefixWord ++ tailWord_3178736) baseStart_3178736 baseEnd_3178736 := by
    simpa [prefixWord, tailWord_3178736, baseEnd_3178736] using wordTrace_append hprefix tailTrace_3178736
  have hstable : (prefixWord ++ tailWord_3178736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178736).length < 2 ^ (prefixWord ++ tailWord_3178736).sum := by decide
  have hdescent : baseEnd_3178736 < baseStart_3178736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178753 : List Nat := [1, 2, 4, 1, 1, 2, 1, 2, 1, 6, 2]
def baseStart_3178753 : Nat := 118140960795 + 3178753 * 2 ^ 59
def prefixEnd_3178753 : Nat := 4983230072969 + 3 ^ 40 * 3178753 * 2
def baseEnd_3178753 : Nat := 1632228170921506847968687

theorem tailTrace_3178753 : CollatzResearch.WordTrace tailWord_3178753 prefixEnd_3178753 1632228170921506847968687 := by
  unfold tailWord_3178753
  simp only [CollatzResearch.WordTrace]
  refine ⟨115938646652928243636004913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77292431101952162424003275 115938646652928243636004913)
  ·
    refine ⟨86953984989696182727003685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115938646652928243636004913 86953984989696182727003685)
    ·
      refine ⟨16303872185568034261313191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86953984989696182727003685 16303872185568034261313191)
      ·
        refine ⟨24455808278352051391969787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16303872185568034261313191 24455808278352051391969787)
        ·
          refine ⟨36683712417528077087954681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24455808278352051391969787 36683712417528077087954681)
          ·
            refine ⟨27512784313146057815966011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36683712417528077087954681 27512784313146057815966011)
            ·
              refine ⟨41269176469719086723949017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27512784313146057815966011 41269176469719086723949017)
              ·
                refine ⟨30951882352289315042961763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41269176469719086723949017 30951882352289315042961763)
                ·
                  refine ⟨46427823528433972564442645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30951882352289315042961763 46427823528433972564442645)
                  ·
                    refine ⟨2176304227895342463958249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 46427823528433972564442645 2176304227895342463958249)
                    ·
                      refine ⟨1632228170921506847968687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2176304227895342463958249 1632228170921506847968687)
                      ·
                        rfl

theorem cell23_3178753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_3178753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178753 prefixEnd_3178753 := by exact prefixLift 3178753
  have htrace : WordTrace (prefixWord ++ tailWord_3178753) baseStart_3178753 baseEnd_3178753 := by
    simpa [prefixWord, tailWord_3178753, baseEnd_3178753] using wordTrace_append hprefix tailTrace_3178753
  have hstable : (prefixWord ++ tailWord_3178753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178753).length < 2 ^ (prefixWord ++ tailWord_3178753).sum := by decide
  have hdescent : baseEnd_3178753 < baseStart_3178753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178766 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6]
def baseStart_3178766 : Nat := 118140960795 + 3178766 * 2 ^ 59
def prefixEnd_3178766 : Nat := 4983230072969 + 3 ^ 40 * 3178766 * 2
def baseEnd_3178766 : Nat := 1632234846170015297106127

theorem tailTrace_3178766 : CollatzResearch.WordTrace tailWord_3178766 prefixEnd_3178766 1632234846170015297106127 := by
  unfold tailWord_3178766
  simp only [CollatzResearch.WordTrace]
  refine ⟨14492390100235143357028519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77292747201254097904152101 14492390100235143357028519)
  ·
    refine ⟨21738585150352715035542779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14492390100235143357028519 21738585150352715035542779)
    ·
      refine ⟨32607877725529072553314169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21738585150352715035542779 32607877725529072553314169)
      ·
        refine ⟨24455908294146804414985627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32607877725529072553314169 24455908294146804414985627)
        ·
          refine ⟨36683862441220206622478441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24455908294146804414985627 36683862441220206622478441)
          ·
            refine ⟨27512896830915154966858831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36683862441220206622478441 27512896830915154966858831)
            ·
              refine ⟨41269345246372732450288247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27512896830915154966858831 41269345246372732450288247)
              ·
                refine ⟨61904017869559098675432371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41269345246372732450288247 61904017869559098675432371)
                ·
                  refine ⟨92856026804338648013148557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61904017869559098675432371 92856026804338648013148557)
                  ·
                    refine ⟨34821010051626993004930709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92856026804338648013148557 34821010051626993004930709)
                    ·
                      refine ⟨1632234846170015297106127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34821010051626993004930709 1632234846170015297106127)
                      ·
                        rfl

theorem cell23_3178766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_3178766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178766 prefixEnd_3178766 := by exact prefixLift 3178766
  have htrace : WordTrace (prefixWord ++ tailWord_3178766) baseStart_3178766 baseEnd_3178766 := by
    simpa [prefixWord, tailWord_3178766, baseEnd_3178766] using wordTrace_append hprefix tailTrace_3178766
  have hstable : (prefixWord ++ tailWord_3178766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178766).length < 2 ^ (prefixWord ++ tailWord_3178766).sum := by decide
  have hdescent : baseEnd_3178766 < baseStart_3178766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178773 : List Nat := [1, 3, 2, 1, 2, 1, 2, 4, 2, 2, 3]
def baseStart_3178773 : Nat := 118140960795 + 3178773 * 2 ^ 59
def prefixEnd_3178773 : Nat := 4983230072969 + 3 ^ 40 * 3178773 * 2
def baseEnd_3178773 : Nat := 1632238440534596769718595

theorem tailTrace_3178773 : CollatzResearch.WordTrace tailWord_3178773 prefixEnd_3178773 1632238440534596769718595 := by
  unfold tailWord_3178773
  simp only [CollatzResearch.WordTrace]
  refine ⟨115939376112855787051732973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77292917408570524701155315 115939376112855787051732973)
  ·
    refine ⟨43477266042320920144399865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115939376112855787051732973 43477266042320920144399865)
    ·
      refine ⟨32607949531740690108299899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43477266042320920144399865 32607949531740690108299899)
      ·
        refine ⟨48911924297611035162449849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32607949531740690108299899 48911924297611035162449849)
        ·
          refine ⟨36683943223208276371837387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48911924297611035162449849 36683943223208276371837387)
          ·
            refine ⟨55025914834812414557756081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36683943223208276371837387 55025914834812414557756081)
            ·
              refine ⟨41269436126109310918317061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55025914834812414557756081 41269436126109310918317061)
              ·
                refine ⟨7738019273645495797184449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41269436126109310918317061 7738019273645495797184449)
                ·
                  refine ⟨5803514455234121847888337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7738019273645495797184449 5803514455234121847888337)
                  ·
                    refine ⟨4352635841425591385916253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5803514455234121847888337 4352635841425591385916253)
                    ·
                      refine ⟨1632238440534596769718595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4352635841425591385916253 1632238440534596769718595)
                      ·
                        rfl

theorem cell23_3178773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 2, 3].length) (baseStart_3178773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178773 prefixEnd_3178773 := by exact prefixLift 3178773
  have htrace : WordTrace (prefixWord ++ tailWord_3178773) baseStart_3178773 baseEnd_3178773 := by
    simpa [prefixWord, tailWord_3178773, baseEnd_3178773] using wordTrace_append hprefix tailTrace_3178773
  have hstable : (prefixWord ++ tailWord_3178773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178773).length < 2 ^ (prefixWord ++ tailWord_3178773).sum := by decide
  have hdescent : baseEnd_3178773 < baseStart_3178773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178776 : List Nat := [2, 1, 2, 3, 1, 2, 3, 1, 8]
def baseStart_3178776 : Nat := 118140960795 + 3178776 * 2 ^ 59
def prefixEnd_3178776 : Nat := 4983230072969 + 3 ^ 40 * 3178776 * 2
def baseEnd_3178776 : Nat := 181359997886284473109009

theorem tailTrace_3178776 : CollatzResearch.WordTrace tailWord_3178776 prefixEnd_3178776 181359997886284473109009 := by
  unfold tailWord_3178776
  simp only [CollatzResearch.WordTrace]
  refine ⟨57969742765922459282046091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77292990354563279042728121 57969742765922459282046091)
  ·
    refine ⟨86954614148883688923069137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57969742765922459282046091 86954614148883688923069137)
    ·
      refine ⟨65215960611662766692301853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86954614148883688923069137 65215960611662766692301853)
      ·
        refine ⟨24455985229373537509613195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65215960611662766692301853 24455985229373537509613195)
        ·
          refine ⟨36683977844060306264419793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24455985229373537509613195 36683977844060306264419793)
          ·
            refine ⟨27512983383045229698314845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36683977844060306264419793 27512983383045229698314845)
            ·
              refine ⟨10317368768641961136868067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27512983383045229698314845 10317368768641961136868067)
              ·
                refine ⟨15476053152962941705302101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10317368768641961136868067 15476053152962941705302101)
                ·
                  refine ⟨181359997886284473109009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15476053152962941705302101 181359997886284473109009)
                  ·
                    rfl

theorem cell23_3178776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 8].length) (baseStart_3178776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178776 prefixEnd_3178776 := by exact prefixLift 3178776
  have htrace : WordTrace (prefixWord ++ tailWord_3178776) baseStart_3178776 baseEnd_3178776 := by
    simpa [prefixWord, tailWord_3178776, baseEnd_3178776] using wordTrace_append hprefix tailTrace_3178776
  have hstable : (prefixWord ++ tailWord_3178776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178776).length < 2 ^ (prefixWord ++ tailWord_3178776).sum := by decide
  have hdescent : baseEnd_3178776 < baseStart_3178776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178814 : List Nat := [4, 2, 1, 2, 1, 4, 1, 3, 1, 4]
def baseStart_3178814 : Nat := 118140960795 + 3178814 * 2 ^ 59
def prefixEnd_3178814 : Nat := 4983230072969 + 3 ^ 40 * 3178814 * 2
def baseEnd_3178814 : Nat := 544086497747143703101969

theorem tailTrace_3178814 : CollatzResearch.WordTrace tailWord_3178814 prefixEnd_3178814 544086497747143703101969 := by
  unfold tailWord_3178814
  simp only [CollatzResearch.WordTrace]
  refine ⟨14492608938213406381746937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77293914337138167369316997 14492608938213406381746937)
  ·
    refine ⟨10869456703660054786310203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14492608938213406381746937 10869456703660054786310203)
    ·
      refine ⟨16304185055490082179465305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10869456703660054786310203 16304185055490082179465305)
      ·
        refine ⟨12228138791617561634598979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16304185055490082179465305 12228138791617561634598979)
        ·
          refine ⟨18342208187426342451898469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12228138791617561634598979 18342208187426342451898469)
          ·
            refine ⟨3439164035142439209730963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18342208187426342451898469 3439164035142439209730963)
            ·
              refine ⟨5158746052713658814596445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3439164035142439209730963 5158746052713658814596445)
              ·
                refine ⟨1934529769767622055473667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5158746052713658814596445 1934529769767622055473667)
                ·
                  refine ⟨2901794654651433083210501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1934529769767622055473667 2901794654651433083210501)
                  ·
                    refine ⟨544086497747143703101969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2901794654651433083210501 544086497747143703101969)
                    ·
                      rfl

theorem cell23_3178814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_3178814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178814 prefixEnd_3178814 := by exact prefixLift 3178814
  have htrace : WordTrace (prefixWord ++ tailWord_3178814) baseStart_3178814 baseEnd_3178814 := by
    simpa [prefixWord, tailWord_3178814, baseEnd_3178814] using wordTrace_append hprefix tailTrace_3178814
  have hstable : (prefixWord ++ tailWord_3178814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178814).length < 2 ^ (prefixWord ++ tailWord_3178814).sum := by decide
  have hdescent : baseEnd_3178814 < baseStart_3178814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178823 : List Nat := [1, 1, 4, 1, 2, 2, 1, 5, 1, 5]
def baseStart_3178823 : Nat := 118140960795 + 3178823 * 2 ^ 59
def prefixEnd_3178823 : Nat := 4983230072969 + 3 ^ 40 * 3178823 * 2
def baseEnd_3178823 : Nat := 544088038189107191364455

theorem tailTrace_3178823 : CollatzResearch.WordTrace tailWord_3178823 prefixEnd_3178823 544088038189107191364455 := by
  unfold tailWord_3178823
  simp only [CollatzResearch.WordTrace]
  refine ⟨115941199762674645591053123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77294133175116430394035415 115941199762674645591053123)
  ·
    refine ⟨173911799644011968386579685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115941199762674645591053123 173911799644011968386579685)
    ·
      refine ⟨32608462433252244072483691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173911799644011968386579685 32608462433252244072483691)
      ·
        refine ⟨48912693649878366108725537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32608462433252244072483691 48912693649878366108725537)
        ·
          refine ⟨36684520237408774581544153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48912693649878366108725537 36684520237408774581544153)
          ·
            refine ⟨27513390178056580936158115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36684520237408774581544153 27513390178056580936158115)
            ·
              refine ⟨41270085267084871404237173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27513390178056580936158115 41270085267084871404237173)
              ·
                refine ⟨3869070493789206694147235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41270085267084871404237173 3869070493789206694147235)
                ·
                  refine ⟨5803605740683810041220853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3869070493789206694147235 5803605740683810041220853)
                  ·
                    refine ⟨544088038189107191364455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5803605740683810041220853 544088038189107191364455)
                    ·
                      rfl

theorem cell23_3178823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 5].length) (baseStart_3178823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178823 prefixEnd_3178823 := by exact prefixLift 3178823
  have htrace : WordTrace (prefixWord ++ tailWord_3178823) baseStart_3178823 baseEnd_3178823 := by
    simpa [prefixWord, tailWord_3178823, baseEnd_3178823] using wordTrace_append hprefix tailTrace_3178823
  have hstable : (prefixWord ++ tailWord_3178823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178823).length < 2 ^ (prefixWord ++ tailWord_3178823).sum := by decide
  have hdescent : baseEnd_3178823 < baseStart_3178823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178844 : List Nat := [2, 2, 4, 3, 1, 2, 2, 1, 6]
def baseStart_3178844 : Nat := 118140960795 + 3178844 * 2 ^ 59
def prefixEnd_3178844 : Nat := 4983230072969 + 3 ^ 40 * 3178844 * 2
def baseEnd_3178844 : Nat := 181363877517896221325641

theorem tailTrace_3178844 : CollatzResearch.WordTrace tailWord_3178844 prefixEnd_3178844 181363877517896221325641 := by
  unfold tailWord_3178844
  simp only [CollatzResearch.WordTrace]
  refine ⟨57970982847799283088783793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77294643797065710785045057 57970982847799283088783793)
  ·
    refine ⟨43478237135849462316587845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57970982847799283088783793 43478237135849462316587845)
    ·
      refine ⟨8152169462971774184360221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43478237135849462316587845 8152169462971774184360221)
      ·
        refine ⟨3057063548614415319135083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8152169462971774184360221 3057063548614415319135083)
        ·
          refine ⟨4585595322921622978702625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3057063548614415319135083 4585595322921622978702625)
          ·
            refine ⟨3439196492191217234026969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4585595322921622978702625 3439196492191217234026969)
            ·
              refine ⟨2579397369143412925520227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3439196492191217234026969 2579397369143412925520227)
              ·
                refine ⟨3869096053715119388280341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2579397369143412925520227 3869096053715119388280341)
                ·
                  refine ⟨181363877517896221325641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3869096053715119388280341 181363877517896221325641)
                  ·
                    rfl

theorem cell23_3178844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 6].length) (baseStart_3178844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178844 prefixEnd_3178844 := by exact prefixLift 3178844
  have htrace : WordTrace (prefixWord ++ tailWord_3178844) baseStart_3178844 baseEnd_3178844 := by
    simpa [prefixWord, tailWord_3178844, baseEnd_3178844] using wordTrace_append hprefix tailTrace_3178844
  have hstable : (prefixWord ++ tailWord_3178844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178844).length < 2 ^ (prefixWord ++ tailWord_3178844).sum := by decide
  have hdescent : baseEnd_3178844 < baseStart_3178844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178860 : List Nat := [2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 4]
def baseStart_3178860 : Nat := 118140960795 + 3178860 * 2 ^ 59
def prefixEnd_3178860 : Nat := 4983230072969 + 3 ^ 40 * 3178860 * 2
def baseEnd_3178860 : Nat := 1632283113351537929330695

theorem tailTrace_3178860 : CollatzResearch.WordTrace tailWord_3178860 prefixEnd_3178860 1632283113351537929330695 := by
  unfold tailWord_3178860
  simp only [CollatzResearch.WordTrace]
  refine ⟨57971274631770300455075017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77295032842360400606766689 57971274631770300455075017)
  ·
    refine ⟨43478455973827725341306263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57971274631770300455075017 43478455973827725341306263)
    ·
      refine ⟨65217683960741588011959395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43478455973827725341306263 65217683960741588011959395)
      ·
        refine ⟨97826525941112382017939093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65217683960741588011959395 97826525941112382017939093)
        ·
          refine ⟨4585618403489642907090895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 97826525941112382017939093 4585618403489642907090895)
          ·
            refine ⟨6878427605234464360636343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4585618403489642907090895 6878427605234464360636343)
            ·
              refine ⟨10317641407851696540954515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6878427605234464360636343 10317641407851696540954515)
              ·
                refine ⟨15476462111777544811431773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10317641407851696540954515 15476462111777544811431773)
                ·
                  refine ⟨5803673291916579304286915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15476462111777544811431773 5803673291916579304286915)
                  ·
                    refine ⟨8705509937874868956430373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5803673291916579304286915 8705509937874868956430373)
                    ·
                      refine ⟨1632283113351537929330695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8705509937874868956430373 1632283113351537929330695)
                      ·
                        rfl

theorem cell23_3178860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 4].length) (baseStart_3178860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178860 prefixEnd_3178860 := by exact prefixLift 3178860
  have htrace : WordTrace (prefixWord ++ tailWord_3178860) baseStart_3178860 baseEnd_3178860 := by
    simpa [prefixWord, tailWord_3178860, baseEnd_3178860] using wordTrace_append hprefix tailTrace_3178860
  have hstable : (prefixWord ++ tailWord_3178860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178860).length < 2 ^ (prefixWord ++ tailWord_3178860).sum := by decide
  have hdescent : baseEnd_3178860 < baseStart_3178860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178877 : List Nat := [1, 4, 1, 1, 2, 4, 3, 1, 1, 1, 4]
def baseStart_3178877 : Nat := 118140960795 + 3178877 * 2 ^ 59
def prefixEnd_3178877 : Nat := 4983230072969 + 3 ^ 40 * 3178877 * 2
def baseEnd_3178877 : Nat := 1632291842522664362818117

theorem tailTrace_3178877 : CollatzResearch.WordTrace tailWord_3178877 prefixEnd_3178877 1632291842522664362818117 := by
  unfold tailWord_3178877
  simp only [CollatzResearch.WordTrace]
  refine ⟨115943169304479012813518885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77295446202986008542345923 115943169304479012813518885)
  ·
    refine ⟨21739344244589814902534791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115943169304479012813518885 21739344244589814902534791)
    ·
      refine ⟨32609016366884722353802187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21739344244589814902534791 32609016366884722353802187)
      ·
        refine ⟨48913524550327083530703281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32609016366884722353802187 48913524550327083530703281)
        ·
          refine ⟨36685143412745312648027461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48913524550327083530703281 36685143412745312648027461)
          ·
            refine ⟨6878464389889746121505149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36685143412745312648027461 6878464389889746121505149)
            ·
              refine ⟨2579424146208654795564431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6878464389889746121505149 2579424146208654795564431)
              ·
                refine ⟨3869136219312982193346647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2579424146208654795564431 3869136219312982193346647)
                ·
                  refine ⟨5803704328969473290019971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3869136219312982193346647 5803704328969473290019971)
                  ·
                    refine ⟨8705556493454209935029957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5803704328969473290019971 8705556493454209935029957)
                    ·
                      refine ⟨1632291842522664362818117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8705556493454209935029957 1632291842522664362818117)
                      ·
                        rfl

theorem cell23_3178877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 1, 1, 4].length) (baseStart_3178877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178877 prefixEnd_3178877 := by exact prefixLift 3178877
  have htrace : WordTrace (prefixWord ++ tailWord_3178877) baseStart_3178877 baseEnd_3178877 := by
    simpa [prefixWord, tailWord_3178877, baseEnd_3178877] using wordTrace_append hprefix tailTrace_3178877
  have hstable : (prefixWord ++ tailWord_3178877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178877).length < 2 ^ (prefixWord ++ tailWord_3178877).sum := by decide
  have hdescent : baseEnd_3178877 < baseStart_3178877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178883 : List Nat := [1, 1, 1, 3, 7, 10]
def baseStart_3178883 : Nat := 118140960795 + 3178883 * 2 ^ 59
def prefixEnd_3178883 : Nat := 4983230072969 + 3 ^ 40 * 3178883 * 2
def baseEnd_3178883 : Nat := 6717263059286384112523

theorem tailTrace_3178883 : CollatzResearch.WordTrace tailWord_3178883 prefixEnd_3178883 6717263059286384112523 := by
  unfold tailWord_3178883
  simp only [CollatzResearch.WordTrace]
  refine ⟨115943388142457275838237303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77295592094971517225491535 115943388142457275838237303)
  ·
    refine ⟨173915082213685913757355955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115943388142457275838237303 173915082213685913757355955)
    ·
      refine ⟨260872623320528870636033933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173915082213685913757355955 260872623320528870636033933)
      ·
        refine ⟨97827233745198326488512725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260872623320528870636033933 97827233745198326488512725)
        ·
          refine ⟨2292825790903085777074517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 97827233745198326488512725 2292825790903085777074517)
          ·
            refine ⟨6717263059286384112523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2292825790903085777074517 6717263059286384112523)
            ·
              rfl

theorem cell23_3178883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 10].length) (baseStart_3178883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178883 prefixEnd_3178883 := by exact prefixLift 3178883
  have htrace : WordTrace (prefixWord ++ tailWord_3178883) baseStart_3178883 baseEnd_3178883 := by
    simpa [prefixWord, tailWord_3178883, baseEnd_3178883] using wordTrace_append hprefix tailTrace_3178883
  have hstable : (prefixWord ++ tailWord_3178883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178883).length < 2 ^ (prefixWord ++ tailWord_3178883).sum := by decide
  have hdescent : baseEnd_3178883 < baseStart_3178883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178953 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 1, 6, 3]
def baseStart_3178953 : Nat := 118140960795 + 3178953 * 2 ^ 59
def prefixEnd_3178953 : Nat := 4983230072969 + 3 ^ 40 * 3178953 * 2
def baseEnd_3178953 : Nat := 1632330867052406065467767

theorem tailTrace_3178953 : CollatzResearch.WordTrace tailWord_3178953 prefixEnd_3178953 1632330867052406065467767 := by
  unfold tailWord_3178953
  simp only [CollatzResearch.WordTrace]
  refine ⟨115945941252203677793285513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77297294168135785195523675 115945941252203677793285513)
  ·
    refine ⟨86959455939152758344964135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115945941252203677793285513 86959455939152758344964135)
    ·
      refine ⟨130439183908729137517446203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86959455939152758344964135 130439183908729137517446203)
      ·
        refine ⟨195658775863093706276169305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130439183908729137517446203 195658775863093706276169305)
        ·
          refine ⟨146744081897320279707126979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195658775863093706276169305 146744081897320279707126979)
          ·
            refine ⟨220116122845980419560690469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146744081897320279707126979 220116122845980419560690469)
            ·
              refine ⟨41271773033621328667629463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 220116122845980419560690469 41271773033621328667629463)
              ·
                refine ⟨61907659550431993001444195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41271773033621328667629463 61907659550431993001444195)
                ·
                  refine ⟨92861489325647989502166293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61907659550431993001444195 92861489325647989502166293)
                  ·
                    refine ⟨4352882312139749507914045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 92861489325647989502166293 4352882312139749507914045)
                    ·
                      refine ⟨1632330867052406065467767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4352882312139749507914045 1632330867052406065467767)
                      ·
                        rfl

theorem cell23_3178953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 6, 3].length) (baseStart_3178953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3178953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3178953 prefixEnd_3178953 := by exact prefixLift 3178953
  have htrace : WordTrace (prefixWord ++ tailWord_3178953) baseStart_3178953 baseEnd_3178953 := by
    simpa [prefixWord, tailWord_3178953, baseEnd_3178953] using wordTrace_append hprefix tailTrace_3178953
  have hstable : (prefixWord ++ tailWord_3178953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178953).length < 2 ^ (prefixWord ++ tailWord_3178953).sum := by decide
  have hdescent : baseEnd_3178953 < baseStart_3178953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179007 : List Nat := [1, 1, 2, 2, 1, 2, 7, 2, 5]
def baseStart_3179007 : Nat := 118140960795 + 3179007 * 2 ^ 59
def prefixEnd_3179007 : Nat := 4983230072969 + 3 ^ 40 * 3179007 * 2
def baseEnd_3179007 : Nat := 181373177223083206021391

theorem tailTrace_3179007 : CollatzResearch.WordTrace tailWord_3179007 prefixEnd_3179007 181373177223083206021391 := by
  unfold tailWord_3179007
  simp only [CollatzResearch.WordTrace]
  refine ⟨115947910794008045015751275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77298607196005363343834183 115947910794008045015751275)
  ·
    refine ⟨173921866191012067523626913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115947910794008045015751275 173921866191012067523626913)
    ·
      refine ⟨130441399643259050642720185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173921866191012067523626913 130441399643259050642720185)
      ·
        refine ⟨97831049732444287982040139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130441399643259050642720185 97831049732444287982040139)
        ·
          refine ⟨146746574598666431973060209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97831049732444287982040139 146746574598666431973060209)
          ·
            refine ⟨110059930948999823979795157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146746574598666431973060209 110059930948999823979795157)
            ·
              refine ⟨2579529631617183374526449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 110059930948999823979795157 2579529631617183374526449)
              ·
                refine ⟨1934647223712887530894837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2579529631617183374526449 1934647223712887530894837)
                ·
                  refine ⟨181373177223083206021391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1934647223712887530894837 181373177223083206021391)
                  ·
                    rfl

theorem cell23_3179007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 2, 5].length) (baseStart_3179007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3179007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3179007 prefixEnd_3179007 := by exact prefixLift 3179007
  have htrace : WordTrace (prefixWord ++ tailWord_3179007) baseStart_3179007 baseEnd_3179007 := by
    simpa [prefixWord, tailWord_3179007, baseEnd_3179007] using wordTrace_append hprefix tailTrace_3179007
  have hstable : (prefixWord ++ tailWord_3179007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179007).length < 2 ^ (prefixWord ++ tailWord_3179007).sum := by decide
  have hdescent : baseEnd_3179007 < baseStart_3179007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179013 : List Nat := [1, 3, 1, 1, 2, 2, 3, 1, 1, 1, 7]
def baseStart_3179013 : Nat := 118140960795 + 3179013 * 2 ^ 59
def prefixEnd_3179013 : Nat := 4983230072969 + 3 ^ 40 * 3179013 * 2
def baseEnd_3179013 : Nat := 1632361675891675830717491

theorem tailTrace_3179013 : CollatzResearch.WordTrace tailWord_3179013 prefixEnd_3179013 1632361675891675830717491 := by
  unfold tailWord_3179013
  simp only [CollatzResearch.WordTrace]
  refine ⟨115948129631986308040469693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77298753087990872026979795 115948129631986308040469693)
  ·
    refine ⟨43480548611994865515176135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115948129631986308040469693 43480548611994865515176135)
    ·
      refine ⟨65220822917992298272764203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43480548611994865515176135 65220822917992298272764203)
      ·
        refine ⟨97831234376988447409146305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65220822917992298272764203 97831234376988447409146305)
        ·
          refine ⟨73373425782741335556859729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97831234376988447409146305 73373425782741335556859729)
          ·
            refine ⟨55030069337056001667644797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73373425782741335556859729 55030069337056001667644797)
            ·
              refine ⟨20636276001396000625366799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55030069337056001667644797 20636276001396000625366799)
              ·
                refine ⟨30954414002094000938050199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20636276001396000625366799 30954414002094000938050199)
                ·
                  refine ⟨46431621003141001407075299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30954414002094000938050199 46431621003141001407075299)
                  ·
                    refine ⟨69647431504711502110612949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46431621003141001407075299 69647431504711502110612949)
                    ·
                      refine ⟨1632361675891675830717491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 69647431504711502110612949 1632361675891675830717491)
                      ·
                        rfl

theorem cell23_3179013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_3179013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3179013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3179013 prefixEnd_3179013 := by exact prefixLift 3179013
  have htrace : WordTrace (prefixWord ++ tailWord_3179013) baseStart_3179013 baseEnd_3179013 := by
    simpa [prefixWord, tailWord_3179013, baseEnd_3179013] using wordTrace_append hprefix tailTrace_3179013
  have hstable : (prefixWord ++ tailWord_3179013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179013).length < 2 ^ (prefixWord ++ tailWord_3179013).sum := by decide
  have hdescent : baseEnd_3179013 < baseStart_3179013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179037 : List Nat := [1, 4, 2, 2, 1, 3, 2, 1, 2, 5]
def baseStart_3179037 : Nat := 118140960795 + 3179037 * 2 ^ 59
def prefixEnd_3179037 : Nat := 4983230072969 + 3 ^ 40 * 3179037 * 2
def baseEnd_3179037 : Nat := 544124666475794578939127

theorem tailTrace_3179037 : CollatzResearch.WordTrace tailWord_3179037 prefixEnd_3179037 544124666475794578939127 := by
  unfold tailWord_3179037
  simp only [CollatzResearch.WordTrace]
  refine ⟨115949004983899360139343365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77299336655932906759562243 115949004983899360139343365)
  ·
    refine ⟨21740438434481130026126881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115949004983899360139343365 21740438434481130026126881)
    ·
      refine ⟨16305328825860847519595161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21740438434481130026126881 16305328825860847519595161)
      ·
        refine ⟨12228996619395635639696371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16305328825860847519595161 12228996619395635639696371)
        ·
          refine ⟨18343494929093453459544557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12228996619395635639696371 18343494929093453459544557)
          ·
            refine ⟨6878810598410045047329209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18343494929093453459544557 6878810598410045047329209)
            ·
              refine ⟨5159107948807533785496907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6878810598410045047329209 5159107948807533785496907)
              ·
                refine ⟨7738661923211300678245361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5159107948807533785496907 7738661923211300678245361)
                ·
                  refine ⟨5803996442408475508684021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7738661923211300678245361 5803996442408475508684021)
                  ·
                    refine ⟨544124666475794578939127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5803996442408475508684021 544124666475794578939127)
                    ·
                      rfl

theorem cell23_3179037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_3179037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3179037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3179037 prefixEnd_3179037 := by exact prefixLift 3179037
  have htrace : WordTrace (prefixWord ++ tailWord_3179037) baseStart_3179037 baseEnd_3179037 := by
    simpa [prefixWord, tailWord_3179037, baseEnd_3179037] using wordTrace_append hprefix tailTrace_3179037
  have hstable : (prefixWord ++ tailWord_3179037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179037).length < 2 ^ (prefixWord ++ tailWord_3179037).sum := by decide
  have hdescent : baseEnd_3179037 < baseStart_3179037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179107 : List Nat := [1, 1, 1, 5, 1, 2, 1, 2, 5, 1, 3]
def baseStart_3179107 : Nat := 118140960795 + 3179107 * 2 ^ 59
def prefixEnd_3179107 : Nat := 4983230072969 + 3 ^ 40 * 3179107 * 2
def baseEnd_3179107 : Nat := 1632409943073198462942059

theorem tailTrace_3179107 : CollatzResearch.WordTrace tailWord_3179107 prefixEnd_3179107 1632409943073198462942059 := by
  unfold tailWord_3179107
  simp only [CollatzResearch.WordTrace]
  refine ⟨115951558093645762094391575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77301038729097174729594383 115951558093645762094391575)
  ·
    refine ⟨173927337140468643141587363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115951558093645762094391575 173927337140468643141587363)
    ·
      refine ⟨260891005710702964712381045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173927337140468643141587363 260891005710702964712381045)
      ·
        refine ⟨24458531785378402941785723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 260891005710702964712381045 24458531785378402941785723)
        ·
          refine ⟨36687797678067604412678585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24458531785378402941785723 36687797678067604412678585)
          ·
            refine ⟨27515848258550703309508939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36687797678067604412678585 27515848258550703309508939)
            ·
              refine ⟨41273772387826054964263409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27515848258550703309508939 41273772387826054964263409)
              ·
                refine ⟨30955329290869541223197557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41273772387826054964263409 30955329290869541223197557)
                ·
                  refine ⟨2902062121019019489674771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30955329290869541223197557 2902062121019019489674771)
                  ·
                    refine ⟨4353093181528529234512157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2902062121019019489674771 4353093181528529234512157)
                    ·
                      refine ⟨1632409943073198462942059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4353093181528529234512157 1632409943073198462942059)
                      ·
                        rfl

theorem cell23_3179107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_3179107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3179107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3179107 prefixEnd_3179107 := by exact prefixLift 3179107
  have htrace : WordTrace (prefixWord ++ tailWord_3179107) baseStart_3179107 baseEnd_3179107 := by
    simpa [prefixWord, tailWord_3179107, baseEnd_3179107] using wordTrace_append hprefix tailTrace_3179107
  have hstable : (prefixWord ++ tailWord_3179107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179107).length < 2 ^ (prefixWord ++ tailWord_3179107).sum := by decide
  have hdescent : baseEnd_3179107 < baseStart_3179107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179164 : List Nat := [2, 2, 3, 2, 2, 1, 2, 3, 1, 1, 4]
def baseStart_3179164 : Nat := 118140960795 + 3179164 * 2 ^ 59
def prefixEnd_3179164 : Nat := 4983230072969 + 3 ^ 40 * 3179164 * 2
def baseEnd_3179164 : Nat := 1632439211470504739929297

theorem tailTrace_3179164 : CollatzResearch.WordTrace tailWord_3179164 prefixEnd_3179164 1632439211470504739929297 := by
  unfold tailWord_3179164
  simp only [CollatzResearch.WordTrace]
  refine ⟨57976818527219630414608273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77302424702959507219477697 57976818527219630414608273)
  ·
    refine ⟨43482613895414722810956205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57976818527219630414608273 43482613895414722810956205)
    ·
      refine ⟨16305980210780521054108577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43482613895414722810956205 16305980210780521054108577)
      ·
        refine ⟨12229485158085390790581433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16305980210780521054108577 12229485158085390790581433)
        ·
          refine ⟨9172113868564043092936075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12229485158085390790581433 9172113868564043092936075)
          ·
            refine ⟨13758170802846064639404113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9172113868564043092936075 13758170802846064639404113)
            ·
              refine ⟨10318628102134548479553085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13758170802846064639404113 10318628102134548479553085)
              ·
                refine ⟨3869485538300455679832407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10318628102134548479553085 3869485538300455679832407)
                ·
                  refine ⟨5804228307450683519748611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3869485538300455679832407 5804228307450683519748611)
                  ·
                    refine ⟨8706342461176025279622917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5804228307450683519748611 8706342461176025279622917)
                    ·
                      refine ⟨1632439211470504739929297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8706342461176025279622917 1632439211470504739929297)
                      ·
                        rfl

theorem cell23_3179164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_3179164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3179164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3179164 prefixEnd_3179164 := by exact prefixLift 3179164
  have htrace : WordTrace (prefixWord ++ tailWord_3179164) baseStart_3179164 baseEnd_3179164 := by
    simpa [prefixWord, tailWord_3179164, baseEnd_3179164] using wordTrace_append hprefix tailTrace_3179164
  have hstable : (prefixWord ++ tailWord_3179164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179164).length < 2 ^ (prefixWord ++ tailWord_3179164).sum := by decide
  have hdescent : baseEnd_3179164 < baseStart_3179164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179175 : List Nat := [1, 1, 6, 3, 2, 1, 1, 1, 3, 1, 3]
def baseStart_3179175 : Nat := 118140960795 + 3179175 * 2 ^ 59
def prefixEnd_3179175 : Nat := 4983230072969 + 3 ^ 40 * 3179175 * 2
def baseEnd_3179175 : Nat := 1632444859757704196891747

theorem tailTrace_3179175 : CollatzResearch.WordTrace tailWord_3179175 prefixEnd_3179175 1632444859757704196891747 := by
  unfold tailWord_3179175
  simp only [CollatzResearch.WordTrace]
  refine ⟨115954038257399409707866979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77302692171599606471911319 115954038257399409707866979)
  ·
    refine ⟨173931057386099114561800469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115954038257399409707866979 173931057386099114561800469)
    ·
      refine ⟨8153018314973395995084397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 173931057386099114561800469 8153018314973395995084397)
      ·
        refine ⟨3057381868115023498156649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8153018314973395995084397 3057381868115023498156649)
        ·
          refine ⟨2293036401086267623617487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3057381868115023498156649 2293036401086267623617487)
          ·
            refine ⟨3439554601629401435426231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2293036401086267623617487 3439554601629401435426231)
            ·
              refine ⟨5159331902444102153139347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3439554601629401435426231 5159331902444102153139347)
              ·
                refine ⟨7738997853666153229709021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5159331902444102153139347 7738997853666153229709021)
                ·
                  refine ⟨2902124195124807461140883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7738997853666153229709021 2902124195124807461140883)
                  ·
                    refine ⟨4353186292687211191711325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2902124195124807461140883 4353186292687211191711325)
                    ·
                      refine ⟨1632444859757704196891747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4353186292687211191711325 1632444859757704196891747)
                      ·
                        rfl

theorem cell23_3179175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_3179175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3179175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3179175 prefixEnd_3179175 := by exact prefixLift 3179175
  have htrace : WordTrace (prefixWord ++ tailWord_3179175) baseStart_3179175 baseEnd_3179175 := by
    simpa [prefixWord, tailWord_3179175, baseEnd_3179175] using wordTrace_append hprefix tailTrace_3179175
  have hstable : (prefixWord ++ tailWord_3179175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179175).length < 2 ^ (prefixWord ++ tailWord_3179175).sum := by decide
  have hdescent : baseEnd_3179175 < baseStart_3179175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179214 : List Nat := [4, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3]
def baseStart_3179214 : Nat := 118140960795 + 3179214 * 2 ^ 59
def prefixEnd_3179214 : Nat := 4983230072969 + 3 ^ 40 * 3179214 * 2
def baseEnd_3179214 : Nat := 1632464885503229544304067

theorem tailTrace_3179214 : CollatzResearch.WordTrace tailWord_3179214 prefixEnd_3179214 1632464885503229544304067 := by
  unfold tailWord_3179214
  simp only [CollatzResearch.WordTrace]
  refine ⟨14494432588032264921067087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77303640469505412912357797 14494432588032264921067087)
  ·
    refine ⟨21741648882048397381600631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14494432588032264921067087 21741648882048397381600631)
    ·
      refine ⟨32612473323072596072400947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21741648882048397381600631 32612473323072596072400947)
      ·
        refine ⟨48918709984608894108601421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32612473323072596072400947 48918709984608894108601421)
        ·
          refine ⟨18344516244228335290725533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48918709984608894108601421 18344516244228335290725533)
          ·
            refine ⟨6879193591585625734022075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18344516244228335290725533 6879193591585625734022075)
            ·
              refine ⟨10318790387378438601033113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6879193591585625734022075 10318790387378438601033113)
              ·
                refine ⟨7739092790533828950774835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10318790387378438601033113 7739092790533828950774835)
                ·
                  refine ⟨11608639185800743426162253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7739092790533828950774835 11608639185800743426162253)
                  ·
                    refine ⟨4353239694675278784810845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11608639185800743426162253 4353239694675278784810845)
                    ·
                      refine ⟨1632464885503229544304067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4353239694675278784810845 1632464885503229544304067)
                      ·
                        rfl

theorem cell23_3179214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3].length) (baseStart_3179214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3179214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3179214 prefixEnd_3179214 := by exact prefixLift 3179214
  have htrace : WordTrace (prefixWord ++ tailWord_3179214) baseStart_3179214 baseEnd_3179214 := by
    simpa [prefixWord, tailWord_3179214, baseEnd_3179214] using wordTrace_append hprefix tailTrace_3179214
  have hstable : (prefixWord ++ tailWord_3179214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179214).length < 2 ^ (prefixWord ++ tailWord_3179214).sum := by decide
  have hdescent : baseEnd_3179214 < baseStart_3179214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179218 : List Nat := [3, 2, 2, 2, 3, 1, 3, 1, 1, 2, 3]
def baseStart_3179218 : Nat := 118140960795 + 3179218 * 2 ^ 59
def prefixEnd_3179218 : Nat := 4983230072969 + 3 ^ 40 * 3179218 * 2
def baseEnd_3179218 : Nat := 1632466939425847528654049

theorem tailTrace_3179218 : CollatzResearch.WordTrace tailWord_3179218 prefixEnd_3179218 1632466939425847528654049 := by
  unfold tailWord_3179218
  simp only [CollatzResearch.WordTrace]
  refine ⟨28988901649060907012920577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77303737730829085367788205 28988901649060907012920577)
  ·
    refine ⟨21741676236795680259690433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28988901649060907012920577 21741676236795680259690433)
    ·
      refine ⟨16306257177596760194767825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21741676236795680259690433 16306257177596760194767825)
      ·
        refine ⟨12229692883197570146075869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16306257177596760194767825 12229692883197570146075869)
        ·
          refine ⟨4586134831199088804778451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12229692883197570146075869 4586134831199088804778451)
          ·
            refine ⟨6879202246798633207167677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4586134831199088804778451 6879202246798633207167677)
            ·
              refine ⟨2579700842549487452687879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6879202246798633207167677 2579700842549487452687879)
              ·
                refine ⟨3869551263824231179031819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2579700842549487452687879 3869551263824231179031819)
                ·
                  refine ⟨5804326895736346768547729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3869551263824231179031819 5804326895736346768547729)
                  ·
                    refine ⟨4353245171802260076410797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5804326895736346768547729 4353245171802260076410797)
                    ·
                      refine ⟨1632466939425847528654049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4353245171802260076410797 1632466939425847528654049)
                      ·
                        rfl

theorem cell23_3179218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_3179218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3179218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3179218 prefixEnd_3179218 := by exact prefixLift 3179218
  have htrace : WordTrace (prefixWord ++ tailWord_3179218) baseStart_3179218 baseEnd_3179218 := by
    simpa [prefixWord, tailWord_3179218, baseEnd_3179218] using wordTrace_append hprefix tailTrace_3179218
  have hstable : (prefixWord ++ tailWord_3179218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179218).length < 2 ^ (prefixWord ++ tailWord_3179218).sum := by decide
  have hdescent : baseEnd_3179218 < baseStart_3179218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179231 : List Nat := [1, 1, 2, 3, 2, 4, 2, 2, 2, 1, 3]
def baseStart_3179231 : Nat := 118140960795 + 3179231 * 2 ^ 59
def prefixEnd_3179231 : Nat := 4983230072969 + 3 ^ 40 * 3179231 * 2
def baseEnd_3179231 : Nat := 1632473614674355977791489

theorem tailTrace_3179231 : CollatzResearch.WordTrace tailWord_3179231 prefixEnd_3179231 1632473614674355977791489 := by
  unfold tailWord_3179231
  simp only [CollatzResearch.WordTrace]
  refine ⟨115956080745196531271905547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77304053830131020847937031 115956080745196531271905547)
  ·
    refine ⟨173934121117794796907858321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115956080745196531271905547 173934121117794796907858321)
    ·
      refine ⟨130450590838346097680893741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173934121117794796907858321 130450590838346097680893741)
      ·
        refine ⟨48918971564379786630335153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130450590838346097680893741 48918971564379786630335153)
        ·
          refine ⟨36689228673284839972751365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48918971564379786630335153 36689228673284839972751365)
          ·
            refine ⟨6879230376240907494890881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36689228673284839972751365 6879230376240907494890881)
            ·
              refine ⟨5159422782180680621168161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6879230376240907494890881 5159422782180680621168161)
              ·
                refine ⟨3869567086635510465876121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5159422782180680621168161 3869567086635510465876121)
                ·
                  refine ⟨2902175314976632849407091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3869567086635510465876121 2902175314976632849407091)
                  ·
                    refine ⟨4353262972464949274110637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2902175314976632849407091 4353262972464949274110637)
                    ·
                      refine ⟨1632473614674355977791489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4353262972464949274110637 1632473614674355977791489)
                      ·
                        rfl

theorem cell23_3179231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 2, 1, 3].length) (baseStart_3179231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3179231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3179231 prefixEnd_3179231 := by exact prefixLift 3179231
  have htrace : WordTrace (prefixWord ++ tailWord_3179231) baseStart_3179231 baseEnd_3179231 := by
    simpa [prefixWord, tailWord_3179231, baseEnd_3179231] using wordTrace_append hprefix tailTrace_3179231
  have hstable : (prefixWord ++ tailWord_3179231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179231).length < 2 ^ (prefixWord ++ tailWord_3179231).sum := by decide
  have hdescent : baseEnd_3179231 < baseStart_3179231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179237 : List Nat := [1, 3, 1, 4, 1, 2, 1, 1, 2, 3, 4]
def baseStart_3179237 : Nat := 118140960795 + 3179237 * 2 ^ 59
def prefixEnd_3179237 : Nat := 4983230072969 + 3 ^ 40 * 3179237 * 2
def baseEnd_3179237 : Nat := 1632476695558282954316461

theorem tailTrace_3179237 : CollatzResearch.WordTrace tailWord_3179237 prefixEnd_3179237 1632476695558282954316461 := by
  unfold tailWord_3179237
  simp only [CollatzResearch.WordTrace]
  refine ⟨115956299583174794296623965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77304199722116529531082643 115956299583174794296623965)
  ·
    refine ⟨43483612343690547861233987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115956299583174794296623965 43483612343690547861233987)
    ·
      refine ⟨65225418515535821791850981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43483612343690547861233987 65225418515535821791850981)
      ·
        refine ⟨12229765971662966585972059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65225418515535821791850981 12229765971662966585972059)
        ·
          refine ⟨18344648957494449878958089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12229765971662966585972059 18344648957494449878958089)
          ·
            refine ⟨13758486718120837409218567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18344648957494449878958089 13758486718120837409218567)
            ·
              refine ⟨20637730077181256113827851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13758486718120837409218567 20637730077181256113827851)
              ·
                refine ⟨30956595115771884170741777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20637730077181256113827851 30956595115771884170741777)
                ·
                  refine ⟨23217446336828913128056333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30956595115771884170741777 23217446336828913128056333)
                  ·
                    refine ⟨8706542376310842423021125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23217446336828913128056333 8706542376310842423021125)
                    ·
                      refine ⟨1632476695558282954316461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8706542376310842423021125 1632476695558282954316461)
                      ·
                        rfl

theorem cell23_3179237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_3179237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3179237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3179237 prefixEnd_3179237 := by exact prefixLift 3179237
  have htrace : WordTrace (prefixWord ++ tailWord_3179237) baseStart_3179237 baseEnd_3179237 := by
    simpa [prefixWord, tailWord_3179237, baseEnd_3179237] using wordTrace_append hprefix tailTrace_3179237
  have hstable : (prefixWord ++ tailWord_3179237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179237).length < 2 ^ (prefixWord ++ tailWord_3179237).sum := by decide
  have hdescent : baseEnd_3179237 < baseStart_3179237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179247 : List Nat := [1, 1, 2, 1, 5, 3, 1, 1, 2, 6]
def baseStart_3179247 : Nat := 118140960795 + 3179247 * 2 ^ 59
def prefixEnd_3179247 : Nat := 4983230072969 + 3 ^ 40 * 3179247 * 2
def baseEnd_3179247 : Nat := 544160610121609305063805

theorem tailTrace_3179247 : CollatzResearch.WordTrace tailWord_3179247 prefixEnd_3179247 544160610121609305063805 := by
  unfold tailWord_3179247
  simp only [CollatzResearch.WordTrace]
  refine ⟨115956664313138566004487995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77304442875425710669658663 115956664313138566004487995)
  ·
    refine ⟨173934996469707849006731993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115956664313138566004487995 173934996469707849006731993)
    ·
      refine ⟨130451247352280886755048995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173934996469707849006731993 130451247352280886755048995)
      ·
        refine ⟨195676871028421330132573493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130451247352280886755048995 195676871028421330132573493)
        ·
          refine ⟨18344706658914499699928765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 195676871028421330132573493 18344706658914499699928765)
          ·
            refine ⟨6879264997092937387473287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18344706658914499699928765 6879264997092937387473287)
            ·
              refine ⟨10318897495639406081209931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6879264997092937387473287 10318897495639406081209931)
              ·
                refine ⟨15478346243459109121814897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10318897495639406081209931 15478346243459109121814897)
                ·
                  refine ⟨11608759682594331841361173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15478346243459109121814897 11608759682594331841361173)
                  ·
                    refine ⟨544160610121609305063805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11608759682594331841361173 544160610121609305063805)
                    ·
                      rfl

theorem cell23_3179247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 6].length) (baseStart_3179247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3179247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3179247 prefixEnd_3179247 := by exact prefixLift 3179247
  have htrace : WordTrace (prefixWord ++ tailWord_3179247) baseStart_3179247 baseEnd_3179247 := by
    simpa [prefixWord, tailWord_3179247, baseEnd_3179247] using wordTrace_append hprefix tailTrace_3179247
  have hstable : (prefixWord ++ tailWord_3179247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179247).length < 2 ^ (prefixWord ++ tailWord_3179247).sum := by decide
  have hdescent : baseEnd_3179247 < baseStart_3179247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179271 : List Nat := [1, 1, 4, 4, 1, 1, 2, 2, 1, 4, 2]
def baseStart_3179271 : Nat := 118140960795 + 3179271 * 2 ^ 59
def prefixEnd_3179271 : Nat := 4983230072969 + 3 ^ 40 * 3179271 * 2
def baseEnd_3179271 : Nat := 1632494153900535821291305

theorem tailTrace_3179271 : CollatzResearch.WordTrace tailWord_3179271 prefixEnd_3179271 1632494153900535821291305 := by
  unfold tailWord_3179271
  simp only [CollatzResearch.WordTrace]
  refine ⟨115957539665051618103361667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77305026443367745402241111 115957539665051618103361667)
  ·
    refine ⟨173936309497577427155042501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115957539665051618103361667 173936309497577427155042501)
    ·
      refine ⟨32613058030795767591570469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173936309497577427155042501 32613058030795767591570469)
      ·
        refine ⟨6114948380774206423419463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32613058030795767591570469 6114948380774206423419463)
        ·
          refine ⟨9172422571161309635129195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6114948380774206423419463 9172422571161309635129195)
          ·
            refine ⟨13758633856741964452693793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9172422571161309635129195 13758633856741964452693793)
            ·
              refine ⟨10318975392556473339520345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13758633856741964452693793 10318975392556473339520345)
              ·
                refine ⟨7739231544417355004640259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10318975392556473339520345 7739231544417355004640259)
                ·
                  refine ⟨11608847316626032506960389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7739231544417355004640259 11608847316626032506960389)
                  ·
                    refine ⟨2176658871867381095055073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11608847316626032506960389 2176658871867381095055073)
                    ·
                      refine ⟨1632494153900535821291305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2176658871867381095055073 1632494153900535821291305)
                      ·
                        rfl

theorem cell23_3179271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_3179271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3179271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3179271 prefixEnd_3179271 := by exact prefixLift 3179271
  have htrace : WordTrace (prefixWord ++ tailWord_3179271) baseStart_3179271 baseEnd_3179271 := by
    simpa [prefixWord, tailWord_3179271, baseEnd_3179271] using wordTrace_append hprefix tailTrace_3179271
  have hstable : (prefixWord ++ tailWord_3179271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179271).length < 2 ^ (prefixWord ++ tailWord_3179271).sum := by decide
  have hdescent : baseEnd_3179271 < baseStart_3179271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179282 : List Nat := [3, 2, 4, 1, 3, 1, 1, 2, 2, 1, 3]
def baseStart_3179282 : Nat := 118140960795 + 3179282 * 2 ^ 59
def prefixEnd_3179282 : Nat := 4983230072969 + 3 ^ 40 * 3179282 * 2
def baseEnd_3179282 : Nat := 1632499802187735278253755

theorem tailTrace_3179282 : CollatzResearch.WordTrace tailWord_3179282 prefixEnd_3179282 1632499802187735278253755 := by
  unfold tailWord_3179282
  simp only [CollatzResearch.WordTrace]
  refine ⟨28989485217002941745503025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77305293912007844654674733 28989485217002941745503025)
  ·
    refine ⟨21742113912752206309127269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28989485217002941745503025 21742113912752206309127269)
    ·
      refine ⟨4076646358641038682961363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21742113912752206309127269 4076646358641038682961363)
      ·
        refine ⟨6114969537961558024442045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4076646358641038682961363 6114969537961558024442045)
        ·
          refine ⟨2293113576735584259165767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6114969537961558024442045 2293113576735584259165767)
          ·
            refine ⟨3439670365103376388748651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2293113576735584259165767 3439670365103376388748651)
            ·
              refine ⟨5159505547655064583122977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3439670365103376388748651 5159505547655064583122977)
              ·
                refine ⟨3869629160741298437342233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5159505547655064583122977 3869629160741298437342233)
                ·
                  refine ⟨2902221870555973828006675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3869629160741298437342233 2902221870555973828006675)
                  ·
                    refine ⟨4353332805833960742010013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2902221870555973828006675 4353332805833960742010013)
                    ·
                      refine ⟨1632499802187735278253755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4353332805833960742010013 1632499802187735278253755)
                      ·
                        rfl

theorem cell23_3179282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_3179282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3179282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3179282 prefixEnd_3179282 := by exact prefixLift 3179282
  have htrace : WordTrace (prefixWord ++ tailWord_3179282) baseStart_3179282 baseEnd_3179282 := by
    simpa [prefixWord, tailWord_3179282, baseEnd_3179282] using wordTrace_append hprefix tailTrace_3179282
  have hstable : (prefixWord ++ tailWord_3179282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179282).length < 2 ^ (prefixWord ++ tailWord_3179282).sum := by decide
  have hdescent : baseEnd_3179282 < baseStart_3179282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179304 : List Nat := [2, 1, 5, 1, 1, 1, 1, 3, 2, 3, 3]
def baseStart_3179304 : Nat := 118140960795 + 3179304 * 2 ^ 59
def prefixEnd_3179304 : Nat := 4983230072969 + 3 ^ 40 * 3179304 * 2
def baseEnd_3179304 : Nat := 1632511098762134192178653

theorem tailTrace_3179304 : CollatzResearch.WordTrace tailWord_3179304 prefixEnd_3179304 1632511098762134192178653 := by
  unfold tailWord_3179304
  simp only [CollatzResearch.WordTrace]
  refine ⟨57979371636966032369656483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77305828849288043159541977 57979371636966032369656483)
  ·
    refine ⟨86969057455449048554484725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57979371636966032369656483 86969057455449048554484725)
    ·
      refine ⟨8153349136448348301982943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86969057455449048554484725 8153349136448348301982943)
      ·
        refine ⟨12230023704672522452974415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8153349136448348301982943 12230023704672522452974415)
        ·
          refine ⟨18345035557008783679461623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12230023704672522452974415 18345035557008783679461623)
          ·
            refine ⟨27517553335513175519192435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18345035557008783679461623 27517553335513175519192435)
            ·
              refine ⟨41276330003269763278788653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27517553335513175519192435 41276330003269763278788653)
              ·
                refine ⟨15478623751226161229545745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41276330003269763278788653 15478623751226161229545745)
                ·
                  refine ⟨11608967813419620922159309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15478623751226161229545745 11608967813419620922159309)
                  ·
                    refine ⟨4353362930032357845809741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11608967813419620922159309 4353362930032357845809741)
                    ·
                      refine ⟨1632511098762134192178653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4353362930032357845809741 1632511098762134192178653)
                      ·
                        rfl

theorem cell23_3179304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_3179304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3179304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3179304 prefixEnd_3179304 := by exact prefixLift 3179304
  have htrace : WordTrace (prefixWord ++ tailWord_3179304) baseStart_3179304 baseEnd_3179304 := by
    simpa [prefixWord, tailWord_3179304, baseEnd_3179304] using wordTrace_append hprefix tailTrace_3179304
  have hstable : (prefixWord ++ tailWord_3179304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179304).length < 2 ^ (prefixWord ++ tailWord_3179304).sum := by decide
  have hdescent : baseEnd_3179304 < baseStart_3179304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179344 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 4, 4, 2]
def baseStart_3179344 : Nat := 118140960795 + 3179344 * 2 ^ 59
def prefixEnd_3179344 : Nat := 4983230072969 + 3 ^ 40 * 3179344 * 2
def baseEnd_3179344 : Nat := 1632531637988314035678469

theorem tailTrace_3179344 : CollatzResearch.WordTrace tailWord_3179344 prefixEnd_3179344 1632531637988314035678469 := by
  unfold tailWord_3179344
  simp only [CollatzResearch.WordTrace]
  refine ⟨57980101096893575785384543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77306801462524767713846057 57980101096893575785384543)
  ·
    refine ⟨86970151645340363678076815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57980101096893575785384543 86970151645340363678076815)
    ·
      refine ⟨130455227468010545517115223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86970151645340363678076815 130455227468010545517115223)
      ·
        refine ⟨195682841202015818275672835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130455227468010545517115223 195682841202015818275672835)
        ·
          refine ⟨293524261803023727413509253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195682841202015818275672835 293524261803023727413509253)
          ·
            refine ⟨55035799088066948890032985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 293524261803023727413509253 55035799088066948890032985)
            ·
              refine ⟨41276849316050211667524739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55035799088066948890032985 41276849316050211667524739)
              ·
                refine ⟨61915273974075317501287109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41276849316050211667524739 61915273974075317501287109)
                ·
                  refine ⟨11609113870139122031491333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61915273974075317501287109 11609113870139122031491333)
                  ·
                    refine ⟨2176708850651085380904625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11609113870139122031491333 2176708850651085380904625)
                    ·
                      refine ⟨1632531637988314035678469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2176708850651085380904625 1632531637988314035678469)
                      ·
                        rfl

theorem cell23_3179344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 4, 4, 2].length) (baseStart_3179344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3179344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3179344 prefixEnd_3179344 := by exact prefixLift 3179344
  have htrace : WordTrace (prefixWord ++ tailWord_3179344) baseStart_3179344 baseEnd_3179344 := by
    simpa [prefixWord, tailWord_3179344, baseEnd_3179344] using wordTrace_append hprefix tailTrace_3179344
  have hstable : (prefixWord ++ tailWord_3179344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179344).length < 2 ^ (prefixWord ++ tailWord_3179344).sum := by decide
  have hdescent : baseEnd_3179344 < baseStart_3179344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179381 : List Nat := [1, 3, 4, 1, 1, 2, 1, 3, 2, 2, 3]
def baseStart_3179381 : Nat := 118140960795 + 3179381 * 2 ^ 59
def prefixEnd_3179381 : Nat := 4983230072969 + 3 ^ 40 * 3179381 * 2
def baseEnd_3179381 : Nat := 1632550636772530390915799

theorem tailTrace_3179381 : CollatzResearch.WordTrace tailWord_3179381 prefixEnd_3179381 1632550636772530390915799 := by
  unfold tailWord_3179381
  simp only [CollatzResearch.WordTrace]
  refine ⟨115961551694653106889865997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77307701129768737926577331 115961551694653106889865997)
  ·
    refine ⟨43485581885494915083699749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115961551694653106889865997 43485581885494915083699749)
    ·
      refine ⟨8153546603530296578193703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43485581885494915083699749 8153546603530296578193703)
      ·
        refine ⟨12230319905295444867290555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8153546603530296578193703 12230319905295444867290555)
        ·
          refine ⟨18345479857943167300935833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12230319905295444867290555 18345479857943167300935833)
          ·
            refine ⟨13759109893457375475701875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18345479857943167300935833 13759109893457375475701875)
            ·
              refine ⟨20638664840186063213552813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13759109893457375475701875 20638664840186063213552813)
              ·
                refine ⟨7739499315069773705082305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20638664840186063213552813 7739499315069773705082305)
                ·
                  refine ⟨5804624486302330278811729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7739499315069773705082305 5804624486302330278811729)
                  ·
                    refine ⟨4353468364726747709108797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5804624486302330278811729 4353468364726747709108797)
                    ·
                      refine ⟨1632550636772530390915799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4353468364726747709108797 1632550636772530390915799)
                      ·
                        rfl

theorem cell23_3179381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_3179381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3179381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3179381 prefixEnd_3179381 := by exact prefixLift 3179381
  have htrace : WordTrace (prefixWord ++ tailWord_3179381) baseStart_3179381 baseEnd_3179381 := by
    simpa [prefixWord, tailWord_3179381, baseEnd_3179381] using wordTrace_append hprefix tailTrace_3179381
  have hstable : (prefixWord ++ tailWord_3179381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179381).length < 2 ^ (prefixWord ++ tailWord_3179381).sum := by decide
  have hdescent : baseEnd_3179381 < baseStart_3179381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179421 : List Nat := [1, 4, 2, 1, 2, 1, 2, 2, 1, 5, 2]
def baseStart_3179421 : Nat := 118140960795 + 3179421 * 2 ^ 59
def prefixEnd_3179421 : Nat := 4983230072969 + 3 ^ 40 * 3179421 * 2
def baseEnd_3179421 : Nat := 1632571175998710234415615

theorem tailTrace_3179421 : CollatzResearch.WordTrace tailWord_3179421 prefixEnd_3179421 1632571175998710234415615 := by
  unfold tailWord_3179421
  simp only [CollatzResearch.WordTrace]
  refine ⟨115963010614508193721322117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77308673743005462480881411 115963010614508193721322117)
  ·
    refine ⟨21743064490220286322747897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115963010614508193721322117 21743064490220286322747897)
    ·
      refine ⟨16307298367665214742060923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21743064490220286322747897 16307298367665214742060923)
      ·
        refine ⟨24460947551497822113091385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16307298367665214742060923 24460947551497822113091385)
        ·
          refine ⟨18345710663623366584818539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24460947551497822113091385 18345710663623366584818539)
          ·
            refine ⟨27518565995435049877227809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18345710663623366584818539 27518565995435049877227809)
            ·
              refine ⟨20638924496576287407920857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27518565995435049877227809 20638924496576287407920857)
              ·
                refine ⟨15479193372432215555940643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20638924496576287407920857 15479193372432215555940643)
                ·
                  refine ⟨23218790058648323333910965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15479193372432215555940643 23218790058648323333910965)
                  ·
                    refine ⟨2176761567998280312554153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23218790058648323333910965 2176761567998280312554153)
                    ·
                      refine ⟨1632571175998710234415615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2176761567998280312554153 1632571175998710234415615)
                      ·
                        rfl

theorem cell23_3179421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_3179421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3179421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3179421 prefixEnd_3179421 := by exact prefixLift 3179421
  have htrace : WordTrace (prefixWord ++ tailWord_3179421) baseStart_3179421 baseEnd_3179421 := by
    simpa [prefixWord, tailWord_3179421, baseEnd_3179421] using wordTrace_append hprefix tailTrace_3179421
  have hstable : (prefixWord ++ tailWord_3179421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179421).length < 2 ^ (prefixWord ++ tailWord_3179421).sum := by decide
  have hdescent : baseEnd_3179421 < baseStart_3179421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179445 : List Nat := [1, 3, 3, 2, 1, 1, 4, 3, 1, 1, 3]
def baseStart_3179445 : Nat := 118140960795 + 3179445 * 2 ^ 59
def prefixEnd_3179445 : Nat := 4983230072969 + 3 ^ 40 * 3179445 * 2
def baseEnd_3179445 : Nat := 1632583499534418140515505

theorem tailTrace_3179445 : CollatzResearch.WordTrace tailWord_3179445 prefixEnd_3179445 1632583499534418140515505 := by
  unfold tailWord_3179445
  simp only [CollatzResearch.WordTrace]
  refine ⟨115963885966421245820195789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77309257310947497213463859 115963885966421245820195789)
  ·
    refine ⟨43486457237407967182573421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115963885966421245820195789 43486457237407967182573421)
    ·
      refine ⟨16307421464027987693465033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43486457237407967182573421 16307421464027987693465033)
      ·
        refine ⟨12230566098020990770098775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16307421464027987693465033 12230566098020990770098775)
        ·
          refine ⟨18345849147031486155148163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12230566098020990770098775 18345849147031486155148163)
          ·
            refine ⟨27518773720547229232722245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18345849147031486155148163 27518773720547229232722245)
            ·
              refine ⟨5159770072602605481135421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27518773720547229232722245 5159770072602605481135421)
              ·
                refine ⟨1934913777225977055425783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5159770072602605481135421 1934913777225977055425783)
                ·
                  refine ⟨2902370665838965583138675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1934913777225977055425783 2902370665838965583138675)
                  ·
                    refine ⟨4353555998758448374708013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2902370665838965583138675 4353555998758448374708013)
                    ·
                      refine ⟨1632583499534418140515505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4353555998758448374708013 1632583499534418140515505)
                      ·
                        rfl

theorem cell23_3179445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_3179445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3179445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3179445 prefixEnd_3179445 := by exact prefixLift 3179445
  have htrace : WordTrace (prefixWord ++ tailWord_3179445) baseStart_3179445 baseEnd_3179445 := by
    simpa [prefixWord, tailWord_3179445, baseEnd_3179445] using wordTrace_append hprefix tailTrace_3179445
  have hstable : (prefixWord ++ tailWord_3179445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179445).length < 2 ^ (prefixWord ++ tailWord_3179445).sum := by decide
  have hdescent : baseEnd_3179445 < baseStart_3179445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179448 : List Nat := [2, 1, 2, 1, 2, 6, 2, 1, 1, 5]
def baseStart_3179448 : Nat := 118140960795 + 3179448 * 2 ^ 59
def prefixEnd_3179448 : Nat := 4983230072969 + 3 ^ 40 * 3179448 * 2
def baseEnd_3179448 : Nat := 544195013325460542925997

theorem tailTrace_3179448 : CollatzResearch.WordTrace tailWord_3179448 prefixEnd_3179448 544195013325460542925997 := by
  unfold tailWord_3179448
  simp only [CollatzResearch.WordTrace]
  refine ⟨57981997692705188666277499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77309330256940251555036665 57981997692705188666277499)
  ·
    refine ⟨86972996539057782999416249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57981997692705188666277499 86972996539057782999416249)
    ·
      refine ⟨65229747404293337249562187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86972996539057782999416249 65229747404293337249562187)
      ·
        refine ⟨97844621106440005874343281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65229747404293337249562187 97844621106440005874343281)
        ·
          refine ⟨73383465829830004405757461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97844621106440005874343281 73383465829830004405757461)
          ·
            refine ⟨3439849960773281456519881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 73383465829830004405757461 3439849960773281456519881)
            ·
              refine ⟨2579887470579961092389911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3439849960773281456519881 2579887470579961092389911)
              ·
                refine ⟨3869831205869941638584867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2579887470579961092389911 3869831205869941638584867)
                ·
                  refine ⟨5804746808804912457877301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3869831205869941638584867 5804746808804912457877301)
                  ·
                    refine ⟨544195013325460542925997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5804746808804912457877301 544195013325460542925997)
                    ·
                      rfl

theorem cell23_3179448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 1, 5].length) (baseStart_3179448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3179448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3179448 prefixEnd_3179448 := by exact prefixLift 3179448
  have htrace : WordTrace (prefixWord ++ tailWord_3179448) baseStart_3179448 baseEnd_3179448 := by
    simpa [prefixWord, tailWord_3179448, baseEnd_3179448] using wordTrace_append hprefix tailTrace_3179448
  have hstable : (prefixWord ++ tailWord_3179448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179448).length < 2 ^ (prefixWord ++ tailWord_3179448).sum := by decide
  have hdescent : baseEnd_3179448 < baseStart_3179448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179478 : List Nat := [5, 2, 1, 1, 2, 1, 3, 1, 1, 6]
def baseStart_3179478 : Nat := 118140960795 + 3179478 * 2 ^ 59
def prefixEnd_3179478 : Nat := 4983230072969 + 3 ^ 40 * 3179478 * 2
def baseEnd_3179478 : Nat := 544200148132005503800951

theorem tailTrace_3179478 : CollatzResearch.WordTrace tailWord_3179478 prefixEnd_3179478 544200148132005503800951 := by
  unfold tailWord_3179478
  simp only [CollatzResearch.WordTrace]
  refine ⟨7247818098456355778509193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77310059716867794970764725 7247818098456355778509193)
  ·
    refine ⟨5435863573842266833881895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7247818098456355778509193 5435863573842266833881895)
    ·
      refine ⟨8153795360763400250822843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5435863573842266833881895 8153795360763400250822843)
      ·
        refine ⟨12230693041145100376234265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8153795360763400250822843 12230693041145100376234265)
        ·
          refine ⟨9173019780858825282175699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12230693041145100376234265 9173019780858825282175699)
          ·
            refine ⟨13759529671288237923263549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9173019780858825282175699 13759529671288237923263549)
            ·
              refine ⟨5159823626733089221223831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13759529671288237923263549 5159823626733089221223831)
              ·
                refine ⟨7739735440099633831835747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5159823626733089221223831 7739735440099633831835747)
                ·
                  refine ⟨11609603160149450747753621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7739735440099633831835747 11609603160149450747753621)
                  ·
                    refine ⟨544200148132005503800951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11609603160149450747753621 544200148132005503800951)
                    ·
                      rfl

theorem cell23_3179478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_3179478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3179478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3179478 prefixEnd_3179478 := by exact prefixLift 3179478
  have htrace : WordTrace (prefixWord ++ tailWord_3179478) baseStart_3179478 baseEnd_3179478 := by
    simpa [prefixWord, tailWord_3179478, baseEnd_3179478] using wordTrace_append hprefix tailTrace_3179478
  have hstable : (prefixWord ++ tailWord_3179478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179478).length < 2 ^ (prefixWord ++ tailWord_3179478).sum := by decide
  have hdescent : baseEnd_3179478 < baseStart_3179478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179481 : List Nat := [1, 2, 1, 2, 5, 1, 3, 1, 1, 2, 4]
def baseStart_3179481 : Nat := 118140960795 + 3179481 * 2 ^ 59
def prefixEnd_3179481 : Nat := 4983230072969 + 3 ^ 40 * 3179481 * 2
def baseEnd_3179481 : Nat := 1632601984837979999665339

theorem tailTrace_3179481 : CollatzResearch.WordTrace tailWord_3179481 prefixEnd_3179481 1632601984837979999665339 := by
  unfold tailWord_3179481
  simp only [CollatzResearch.WordTrace]
  refine ⟨115965198994290823968506297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77310132662860549312337531 115965198994290823968506297)
  ·
    refine ⟨86973899245718117976379723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115965198994290823968506297 86973899245718117976379723)
    ·
      refine ⟨130460848868577176964569585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86973899245718117976379723 130460848868577176964569585)
      ·
        refine ⟨97845636651432882723427189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130460848868577176964569585 97845636651432882723427189)
        ·
          refine ⟨9173028436071832755321299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97845636651432882723427189 9173028436071832755321299)
          ·
            refine ⟨13759542654107749132981949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9173028436071832755321299 13759542654107749132981949)
            ·
              refine ⟨5159828495290405924868231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13759542654107749132981949 5159828495290405924868231)
              ·
                refine ⟨7739742742935608887302347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5159828495290405924868231 7739742742935608887302347)
                ·
                  refine ⟨11609614114403413330953521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7739742742935608887302347 11609614114403413330953521)
                  ·
                    refine ⟨8707210585802559998215141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11609614114403413330953521 8707210585802559998215141)
                    ·
                      refine ⟨1632601984837979999665339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8707210585802559998215141 1632601984837979999665339)
                      ·
                        rfl

theorem cell23_3179481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 2, 4].length) (baseStart_3179481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3179481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3179481 prefixEnd_3179481 := by exact prefixLift 3179481
  have htrace : WordTrace (prefixWord ++ tailWord_3179481) baseStart_3179481 baseEnd_3179481 := by
    simpa [prefixWord, tailWord_3179481, baseEnd_3179481] using wordTrace_append hprefix tailTrace_3179481
  have hstable : (prefixWord ++ tailWord_3179481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179481).length < 2 ^ (prefixWord ++ tailWord_3179481).sum := by decide
  have hdescent : baseEnd_3179481 < baseStart_3179481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179485 : List Nat := [1, 4, 3, 1, 2, 1, 2, 2, 3, 2, 2]
def baseStart_3179485 : Nat := 118140960795 + 3179485 * 2 ^ 59
def prefixEnd_3179485 : Nat := 4983230072969 + 3 ^ 40 * 3179485 * 2
def baseEnd_3179485 : Nat := 1632604038760597984015321

theorem tailTrace_3179485 : CollatzResearch.WordTrace tailWord_3179485 prefixEnd_3179485 1632604038760597984015321 := by
  unfold tailWord_3179485
  simp only [CollatzResearch.WordTrace]
  refine ⟨115965344886276332651651909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77310229924184221767767939 115965344886276332651651909)
  ·
    refine ⟨21743502166176812372184733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115965344886276332651651909 21743502166176812372184733)
    ·
      refine ⟨8153813312316304639569275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21743502166176812372184733 8153813312316304639569275)
      ·
        refine ⟨12230719968474456959353913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8153813312316304639569275 12230719968474456959353913)
        ·
          refine ⟨9173039976355842719515435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12230719968474456959353913 9173039976355842719515435)
          ·
            refine ⟨13759559964533764079273153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9173039976355842719515435 13759559964533764079273153)
            ·
              refine ⟨10319669973400323059454865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13759559964533764079273153 10319669973400323059454865)
              ·
                refine ⟨7739752480050242294591149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10319669973400323059454865 7739752480050242294591149)
                ·
                  refine ⟨2902407180018840860471681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7739752480050242294591149 2902407180018840860471681)
                  ·
                    refine ⟨2176805385014130645353761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2902407180018840860471681 2176805385014130645353761)
                    ·
                      refine ⟨1632604038760597984015321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2176805385014130645353761 1632604038760597984015321)
                      ·
                        rfl

theorem cell23_3179485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_3179485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3179485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3179485 prefixEnd_3179485 := by exact prefixLift 3179485
  have htrace : WordTrace (prefixWord ++ tailWord_3179485) baseStart_3179485 baseEnd_3179485 := by
    simpa [prefixWord, tailWord_3179485, baseEnd_3179485] using wordTrace_append hprefix tailTrace_3179485
  have hstable : (prefixWord ++ tailWord_3179485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179485).length < 2 ^ (prefixWord ++ tailWord_3179485).sum := by decide
  have hdescent : baseEnd_3179485 < baseStart_3179485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179591 : List Nat := [1, 1, 4, 1, 3, 2, 1, 1, 1, 5, 3]
def baseStart_3179591 : Nat := 118140960795 + 3179591 * 2 ^ 59
def prefixEnd_3179591 : Nat := 4983230072969 + 3 ^ 40 * 3179591 * 2
def baseEnd_3179591 : Nat := 1632658467709974569289833

theorem tailTrace_3179591 : CollatzResearch.WordTrace tailWord_3179591 prefixEnd_3179591 1632658467709974569289833 := by
  unfold tailWord_3179591
  simp only [CollatzResearch.WordTrace]
  refine ⟨115969211023892312755010627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77312807349261541836673751 115969211023892312755010627)
  ·
    refine ⟨173953816535838469132515941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115969211023892312755010627 173953816535838469132515941)
    ·
      refine ⟨32616340600469712962346739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173953816535838469132515941 32616340600469712962346739)
      ·
        refine ⟨48924510900704569443520109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32616340600469712962346739 48924510900704569443520109)
        ·
          refine ⟨18346691587764213541320041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48924510900704569443520109 18346691587764213541320041)
          ·
            refine ⟨13760018690823160155990031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18346691587764213541320041 13760018690823160155990031)
            ·
              refine ⟨20640028036234740233985047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13760018690823160155990031 20640028036234740233985047)
              ·
                refine ⟨30960042054352110350977571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20640028036234740233985047 30960042054352110350977571)
                ·
                  refine ⟨46440063081528165526466357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30960042054352110350977571 46440063081528165526466357)
                  ·
                    refine ⟨4353755913893265518106221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46440063081528165526466357 4353755913893265518106221)
                    ·
                      refine ⟨1632658467709974569289833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4353755913893265518106221 1632658467709974569289833)
                      ·
                        rfl

theorem cell23_3179591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 5, 3].length) (baseStart_3179591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3179591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3179591 prefixEnd_3179591 := by exact prefixLift 3179591
  have htrace : WordTrace (prefixWord ++ tailWord_3179591) baseStart_3179591 baseEnd_3179591 := by
    simpa [prefixWord, tailWord_3179591, baseEnd_3179591] using wordTrace_append hprefix tailTrace_3179591
  have hstable : (prefixWord ++ tailWord_3179591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179591).length < 2 ^ (prefixWord ++ tailWord_3179591).sum := by decide
  have hdescent : baseEnd_3179591 < baseStart_3179591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179631 : List Nat := [1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 4]
def baseStart_3179631 : Nat := 118140960795 + 3179631 * 2 ^ 59
def prefixEnd_3179631 : Nat := 4983230072969 + 3 ^ 40 * 3179631 * 2
def baseEnd_3179631 : Nat := 1632679006936154412789649

theorem tailTrace_3179631 : CollatzResearch.WordTrace tailWord_3179631 prefixEnd_3179631 1632679006936154412789649 := by
  unfold tailWord_3179631
  simp only [CollatzResearch.WordTrace]
  refine ⟨115970669943747399586466747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77313779962498266390977831 115970669943747399586466747)
  ·
    refine ⟨173956004915621099379700121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115970669943747399586466747 173956004915621099379700121)
    ·
      refine ⟨130467003686715824534775091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173956004915621099379700121 130467003686715824534775091)
      ·
        refine ⟨195700505530073736802162637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130467003686715824534775091 195700505530073736802162637)
        ·
          refine ⟨73387689573777651300810989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195700505530073736802162637 73387689573777651300810989)
          ·
            refine ⟨27520383590166619237804121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73387689573777651300810989 27520383590166619237804121)
            ·
              refine ⟨20640287692624964428353091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27520383590166619237804121 20640287692624964428353091)
              ·
                refine ⟨30960431538937446642529637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20640287692624964428353091 30960431538937446642529637)
                ·
                  refine ⟨5805080913550771245474307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30960431538937446642529637 5805080913550771245474307)
                  ·
                    refine ⟨8707621370326156868211461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5805080913550771245474307 8707621370326156868211461)
                    ·
                      refine ⟨1632679006936154412789649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8707621370326156868211461 1632679006936154412789649)
                      ·
                        rfl

theorem cell23_3179631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 4].length) (baseStart_3179631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3179631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3179631 prefixEnd_3179631 := by exact prefixLift 3179631
  have htrace : WordTrace (prefixWord ++ tailWord_3179631) baseStart_3179631 baseEnd_3179631 := by
    simpa [prefixWord, tailWord_3179631, baseEnd_3179631] using wordTrace_append hprefix tailTrace_3179631
  have hstable : (prefixWord ++ tailWord_3179631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179631).length < 2 ^ (prefixWord ++ tailWord_3179631).sum := by decide
  have hdescent : baseEnd_3179631 < baseStart_3179631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179648 : List Nat := [2, 1, 1, 2, 1, 3, 4, 1, 2, 4, 2]
def baseStart_3179648 : Nat := 118140960795 + 3179648 * 2 ^ 59
def prefixEnd_3179648 : Nat := 4983230072969 + 3 ^ 40 * 3179648 * 2
def baseEnd_3179648 : Nat := 1632687736107280846277071

theorem tailTrace_3179648 : CollatzResearch.WordTrace tailWord_3179648 prefixEnd_3179648 1632687736107280846277071 := by
  unfold tailWord_3179648
  simp only [CollatzResearch.WordTrace]
  refine ⟨57985644992342905744917799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77314193323123874326557065 57985644992342905744917799)
  ·
    refine ⟨86978467488514358617376699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57985644992342905744917799 86978467488514358617376699)
    ·
      refine ⟨130467701232771537926065049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86978467488514358617376699 130467701232771537926065049)
      ·
        refine ⟨97850775924578653444548787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130467701232771537926065049 97850775924578653444548787)
        ·
          refine ⟨146776163886867980166823181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97850775924578653444548787 146776163886867980166823181)
          ·
            refine ⟨55041061457575492562558693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146776163886867980166823181 55041061457575492562558693)
            ·
              refine ⟨10320199023295404855479755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55041061457575492562558693 10320199023295404855479755)
              ·
                refine ⟨15480298534943107283219633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10320199023295404855479755 15480298534943107283219633)
                ·
                  refine ⟨11610223901207330462414725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15480298534943107283219633 11610223901207330462414725)
                  ·
                    refine ⟨2176916981476374461702761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11610223901207330462414725 2176916981476374461702761)
                    ·
                      refine ⟨1632687736107280846277071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2176916981476374461702761 1632687736107280846277071)
                      ·
                        rfl

theorem cell23_3179648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 2, 4, 2].length) (baseStart_3179648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3179648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3179648 prefixEnd_3179648 := by exact prefixLift 3179648
  have htrace : WordTrace (prefixWord ++ tailWord_3179648) baseStart_3179648 baseEnd_3179648 := by
    simpa [prefixWord, tailWord_3179648, baseEnd_3179648] using wordTrace_append hprefix tailTrace_3179648
  have hstable : (prefixWord ++ tailWord_3179648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179648).length < 2 ^ (prefixWord ++ tailWord_3179648).sum := by decide
  have hdescent : baseEnd_3179648 < baseStart_3179648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179651 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 3, 4, 3]
def baseStart_3179651 : Nat := 118140960795 + 3179651 * 2 ^ 59
def prefixEnd_3179651 : Nat := 4983230072969 + 3 ^ 40 * 3179651 * 2
def baseEnd_3179651 : Nat := 1632689276549244334539557

theorem tailTrace_3179651 : CollatzResearch.WordTrace tailWord_3179651 prefixEnd_3179651 1632689276549244334539557 := by
  unfold tailWord_3179651
  simp only [CollatzResearch.WordTrace]
  refine ⟨115971399403674943002194807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77314266269116628668129871 115971399403674943002194807)
  ·
    refine ⟨173957099105512414503292211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115971399403674943002194807 173957099105512414503292211)
    ·
      refine ⟨260935648658268621754938317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173957099105512414503292211 260935648658268621754938317)
      ·
        refine ⟨97850868246850733158101869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260935648658268621754938317 97850868246850733158101869)
        ·
          refine ⟨36694075592569024934288201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97850868246850733158101869 36694075592569024934288201)
          ·
            refine ⟨27520556694426768700716151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36694075592569024934288201 27520556694426768700716151)
            ·
              refine ⟨41280835041640153051074227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27520556694426768700716151 41280835041640153051074227)
              ·
                refine ⟨61921252562460229576611341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41280835041640153051074227 61921252562460229576611341)
                ·
                  refine ⟨23220469710922586091229253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61921252562460229576611341 23220469710922586091229253)
                  ·
                    refine ⟨4353838070797984892105485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23220469710922586091229253 4353838070797984892105485)
                    ·
                      refine ⟨1632689276549244334539557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4353838070797984892105485 1632689276549244334539557)
                      ·
                        rfl

theorem cell23_3179651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 4, 3].length) (baseStart_3179651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3179651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3179651 prefixEnd_3179651 := by exact prefixLift 3179651
  have htrace : WordTrace (prefixWord ++ tailWord_3179651) baseStart_3179651 baseEnd_3179651 := by
    simpa [prefixWord, tailWord_3179651, baseEnd_3179651] using wordTrace_append hprefix tailTrace_3179651
  have hstable : (prefixWord ++ tailWord_3179651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179651).length < 2 ^ (prefixWord ++ tailWord_3179651).sum := by decide
  have hdescent : baseEnd_3179651 < baseStart_3179651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179658 : List Nat := [3, 1, 2, 3, 1, 1, 1, 4, 3, 4]
def baseStart_3179658 : Nat := 118140960795 + 3179658 * 2 ^ 59
def prefixEnd_3179658 : Nat := 4983230072969 + 3 ^ 40 * 3179658 * 2
def baseEnd_3179658 : Nat := 544230956971275269050675

theorem tailTrace_3179658 : CollatzResearch.WordTrace tailWord_3179658 prefixEnd_3179658 544230956971275269050675 := by
  unfold tailWord_3179658
  simp only [CollatzResearch.WordTrace]
  refine ⟨28992913678662395799424907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77314436476433055465133085 28992913678662395799424907)
  ·
    refine ⟨43489370517993593699137361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28992913678662395799424907 43489370517993593699137361)
    ·
      refine ⟨32617027888495195274353021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43489370517993593699137361 32617027888495195274353021)
      ·
        refine ⟨12231385458185698227882383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32617027888495195274353021 12231385458185698227882383)
        ·
          refine ⟨18347078187278547341823575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12231385458185698227882383 18347078187278547341823575)
          ·
            refine ⟨27520617280917821012735363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18347078187278547341823575 27520617280917821012735363)
            ·
              refine ⟨41280925921376731519103045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27520617280917821012735363 41280925921376731519103045)
              ·
                refine ⟨7740173610258137159831821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41280925921376731519103045 7740173610258137159831821)
                ·
                  refine ⟨2902565103846801434936933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7740173610258137159831821 2902565103846801434936933)
                  ·
                    refine ⟨544230956971275269050675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2902565103846801434936933 544230956971275269050675)
                    ·
                      rfl

theorem cell23_3179658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 3, 4].length) (baseStart_3179658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3179658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3179658 prefixEnd_3179658 := by exact prefixLift 3179658
  have htrace : WordTrace (prefixWord ++ tailWord_3179658) baseStart_3179658 baseEnd_3179658 := by
    simpa [prefixWord, tailWord_3179658, baseEnd_3179658] using wordTrace_append hprefix tailTrace_3179658
  have hstable : (prefixWord ++ tailWord_3179658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179658).length < 2 ^ (prefixWord ++ tailWord_3179658).sum := by decide
  have hdescent : baseEnd_3179658 < baseStart_3179658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179671 : List Nat := [1, 1, 3, 3, 3, 1, 1, 2, 8]
def baseStart_3179671 : Nat := 118140960795 + 3179671 * 2 ^ 59
def prefixEnd_3179671 : Nat := 4983230072969 + 3 ^ 40 * 3179671 * 2
def baseEnd_3179671 : Nat := 181411060684703806254385

theorem tailTrace_3179671 : CollatzResearch.WordTrace tailWord_3179671 prefixEnd_3179671 181411060684703806254385 := by
  unfold tailWord_3179671
  simp only [CollatzResearch.WordTrace]
  refine ⟨115972128863602486417922867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77314752575734990945281911 115972128863602486417922867)
  ·
    refine ⟨173958193295403729626884301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115972128863602486417922867 173958193295403729626884301)
    ·
      refine ⟨65234322485776398610081613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173958193295403729626884301 65234322485776398610081613)
      ·
        refine ⟨24462870932166149478780605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65234322485776398610081613 24462870932166149478780605)
        ·
          refine ⟨9173576599562306054542727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24462870932166149478780605 9173576599562306054542727)
          ·
            refine ⟨13760364899343459081814091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9173576599562306054542727 13760364899343459081814091)
            ·
              refine ⟨20640547349015188622721137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13760364899343459081814091 20640547349015188622721137)
              ·
                refine ⟨15480410511761391467040853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20640547349015188622721137 15480410511761391467040853)
                ·
                  refine ⟨181411060684703806254385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15480410511761391467040853 181411060684703806254385)
                  ·
                    rfl

theorem cell23_3179671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 8].length) (baseStart_3179671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3179671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3179671 prefixEnd_3179671 := by exact prefixLift 3179671
  have htrace : WordTrace (prefixWord ++ tailWord_3179671) baseStart_3179671 baseEnd_3179671 := by
    simpa [prefixWord, tailWord_3179671, baseEnd_3179671] using wordTrace_append hprefix tailTrace_3179671
  have hstable : (prefixWord ++ tailWord_3179671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179671).length < 2 ^ (prefixWord ++ tailWord_3179671).sum := by decide
  have hdescent : baseEnd_3179671 < baseStart_3179671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179705 : List Nat := [1, 2, 1, 4, 1, 5, 2, 1, 6]
def baseStart_3179705 : Nat := 118140960795 + 3179705 * 2 ^ 59
def prefixEnd_3179705 : Nat := 4983230072969 + 3 ^ 40 * 3179705 * 2
def baseEnd_3179705 : Nat := 181413000500509680362701

theorem tailTrace_3179705 : CollatzResearch.WordTrace tailWord_3179705 prefixEnd_3179705 181413000500509680362701 := by
  unfold tailWord_3179705
  simp only [CollatzResearch.WordTrace]
  refine ⟨115973368945479310224660569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77315579296986206816440379 115973368945479310224660569)
  ·
    refine ⟨86980026709109482668495427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115973368945479310224660569 86980026709109482668495427)
    ·
      refine ⟨130470040063664224002743141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86980026709109482668495427 130470040063664224002743141)
      ·
        refine ⟨24463132511937042000514339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130470040063664224002743141 24463132511937042000514339)
        ·
          refine ⟨36694698767905563000771509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24463132511937042000514339 36694698767905563000771509)
          ·
            refine ⟨3440128009491146531322329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36694698767905563000771509 3440128009491146531322329)
            ·
              refine ⟨2580096007118359898491747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3440128009491146531322329 2580096007118359898491747)
              ·
                refine ⟨3870144010677539847737621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2580096007118359898491747 3870144010677539847737621)
                ·
                  refine ⟨181413000500509680362701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3870144010677539847737621 181413000500509680362701)
                  ·
                    rfl

theorem cell23_3179705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 6].length) (baseStart_3179705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3179705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3179705 prefixEnd_3179705 := by exact prefixLift 3179705
  have htrace : WordTrace (prefixWord ++ tailWord_3179705) baseStart_3179705 baseEnd_3179705 := by
    simpa [prefixWord, tailWord_3179705, baseEnd_3179705] using wordTrace_append hprefix tailTrace_3179705
  have hstable : (prefixWord ++ tailWord_3179705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179705).length < 2 ^ (prefixWord ++ tailWord_3179705).sum := by decide
  have hdescent : baseEnd_3179705 < baseStart_3179705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179731 : List Nat := [1, 1, 1, 2, 1, 1, 1, 8, 1, 6]
def baseStart_3179731 : Nat := 118140960795 + 3179731 * 2 ^ 59
def prefixEnd_3179731 : Nat := 4983230072969 + 3 ^ 40 * 3179731 * 2
def baseEnd_3179731 : Nat := 544243451667201340513063

theorem tailTrace_3179731 : CollatzResearch.WordTrace tailWord_3179731 prefixEnd_3179731 544243451667201340513063 := by
  unfold tailWord_3179731
  simp only [CollatzResearch.WordTrace]
  refine ⟨115974317243385116665107047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77316211495590077776738031 115974317243385116665107047)
  ·
    refine ⟨173961475865077674997660571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115974317243385116665107047 173961475865077674997660571)
    ·
      refine ⟨260942213797616512496490857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173961475865077674997660571 260942213797616512496490857)
      ·
        refine ⟨195706660348212384372368143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260942213797616512496490857 195706660348212384372368143)
        ·
          refine ⟨293559990522318576558552215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195706660348212384372368143 293559990522318576558552215)
          ·
            refine ⟨440339985783477864837828323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293559990522318576558552215 440339985783477864837828323)
            ·
              refine ⟨660509978675216797256742485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440339985783477864837828323 660509978675216797256742485)
              ·
                refine ⟨7740351312600196842852451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 660509978675216797256742485 7740351312600196842852451)
                ·
                  refine ⟨11610526968900295264278677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7740351312600196842852451 11610526968900295264278677)
                  ·
                    refine ⟨544243451667201340513063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11610526968900295264278677 544243451667201340513063)
                    ·
                      rfl

theorem cell23_3179731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 6].length) (baseStart_3179731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3179731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3179731 prefixEnd_3179731 := by exact prefixLift 3179731
  have htrace : WordTrace (prefixWord ++ tailWord_3179731) baseStart_3179731 baseEnd_3179731 := by
    simpa [prefixWord, tailWord_3179731, baseEnd_3179731] using wordTrace_append hprefix tailTrace_3179731
  have hstable : (prefixWord ++ tailWord_3179731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179731).length < 2 ^ (prefixWord ++ tailWord_3179731).sum := by decide
  have hdescent : baseEnd_3179731 < baseStart_3179731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179748 : List Nat := [2, 3, 1, 1, 1, 2, 2, 3, 4, 4]
def baseStart_3179748 : Nat := 118140960795 + 3179748 * 2 ^ 59
def prefixEnd_3179748 : Nat := 4983230072969 + 3 ^ 40 * 3179748 * 2
def baseEnd_3179748 : Nat := 544246361390910151675537

theorem tailTrace_3179748 : CollatzResearch.WordTrace tailWord_3179748 prefixEnd_3179748 544246361390910151675537 := by
  unfold tailWord_3179748
  simp only [CollatzResearch.WordTrace]
  refine ⟨57987468642161764284237949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77316624856215685712317265 57987468642161764284237949)
  ·
    refine ⟨21745300740810661606589231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57987468642161764284237949 21745300740810661606589231)
    ·
      refine ⟨32617951111215992409883847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21745300740810661606589231 32617951111215992409883847)
      ·
        refine ⟨48926926666823988614825771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32617951111215992409883847 48926926666823988614825771)
        ·
          refine ⟨73390390000235982922238657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48926926666823988614825771 73390390000235982922238657)
          ·
            refine ⟨55042792500176987191678993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73390390000235982922238657 55042792500176987191678993)
            ·
              refine ⟨41282094375132740393759245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55042792500176987191678993 41282094375132740393759245)
              ·
                refine ⟨15480785390674777647659717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41282094375132740393759245 15480785390674777647659717)
                ·
                  refine ⟨2902647260751520808936197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15480785390674777647659717 2902647260751520808936197)
                  ·
                    refine ⟨544246361390910151675537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2902647260751520808936197 544246361390910151675537)
                    ·
                      rfl

theorem cell23_3179748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 4, 4].length) (baseStart_3179748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3179748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3179748 prefixEnd_3179748 := by exact prefixLift 3179748
  have htrace : WordTrace (prefixWord ++ tailWord_3179748) baseStart_3179748 baseEnd_3179748 := by
    simpa [prefixWord, tailWord_3179748, baseEnd_3179748] using wordTrace_append hprefix tailTrace_3179748
  have hstable : (prefixWord ++ tailWord_3179748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179748).length < 2 ^ (prefixWord ++ tailWord_3179748).sum := by decide
  have hdescent : baseEnd_3179748 < baseStart_3179748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179749 : List Nat := [1, 3, 1, 4, 3, 1, 1, 4, 1, 1, 3]
def baseStart_3179749 : Nat := 118140960795 + 3179749 * 2 ^ 59
def prefixEnd_3179749 : Nat := 4983230072969 + 3 ^ 40 * 3179749 * 2
def baseEnd_3179749 : Nat := 1632739597653384951114107

theorem tailTrace_3179749 : CollatzResearch.WordTrace tailWord_3179749 prefixEnd_3179749 1632739597653384951114107 := by
  unfold tailWord_3179749
  simp only [CollatzResearch.WordTrace]
  refine ⟨115974973757319905739262301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77316649171546603826174867 115974973757319905739262301)
  ·
    refine ⟨43490615158994964652223363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115974973757319905739262301 43490615158994964652223363)
    ·
      refine ⟨65235922738492446978335045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43490615158994964652223363 65235922738492446978335045)
      ·
        refine ⟨12231735513467333808437821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65235922738492446978335045 12231735513467333808437821)
        ·
          refine ⟨4586900817550250178164183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12231735513467333808437821 4586900817550250178164183)
          ·
            refine ⟨6880351226325375267246275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4586900817550250178164183 6880351226325375267246275)
            ·
              refine ⟨10320526839488062900869413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6880351226325375267246275 10320526839488062900869413)
              ·
                refine ⟨1935098782404011793913015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10320526839488062900869413 1935098782404011793913015)
                ·
                  refine ⟨2902648173606017690869523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1935098782404011793913015 2902648173606017690869523)
                  ·
                    refine ⟨4353972260409026536304285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2902648173606017690869523 4353972260409026536304285)
                    ·
                      refine ⟨1632739597653384951114107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4353972260409026536304285 1632739597653384951114107)
                      ·
                        rfl

theorem cell23_3179749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_3179749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3179749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3179749 prefixEnd_3179749 := by exact prefixLift 3179749
  have htrace : WordTrace (prefixWord ++ tailWord_3179749) baseStart_3179749 baseEnd_3179749 := by
    simpa [prefixWord, tailWord_3179749, baseEnd_3179749] using wordTrace_append hprefix tailTrace_3179749
  have hstable : (prefixWord ++ tailWord_3179749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179749).length < 2 ^ (prefixWord ++ tailWord_3179749).sum := by decide
  have hdescent : baseEnd_3179749 < baseStart_3179749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179758 : List Nat := [4, 1, 2, 1, 1, 1, 2, 4, 1, 1, 5]
def baseStart_3179758 : Nat := 118140960795 + 3179758 * 2 ^ 59
def prefixEnd_3179758 : Nat := 4983230072969 + 3 ^ 40 * 3179758 * 2
def baseEnd_3179758 : Nat := 1632744218979275415901565

theorem tailTrace_3179758 : CollatzResearch.WordTrace tailWord_3179758 prefixEnd_3179758 1632744218979275415901565 := by
  unfold tailWord_3179758
  simp only [CollatzResearch.WordTrace]
  refine ⟨14496912751785912534542491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77316868009524866850893285 14496912751785912534542491)
  ·
    refine ⟨21745369127678868801813737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14496912751785912534542491 21745369127678868801813737)
    ·
      refine ⟨16309026845759151601360303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21745369127678868801813737 16309026845759151601360303)
      ·
        refine ⟨24463540268638727402040455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16309026845759151601360303 24463540268638727402040455)
        ·
          refine ⟨36695310402958091103060683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24463540268638727402040455 36695310402958091103060683)
          ·
            refine ⟨55042965604437136654591025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36695310402958091103060683 55042965604437136654591025)
            ·
              refine ⟨41282224203327852490943269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55042965604437136654591025 41282224203327852490943269)
              ·
                refine ⟨7740417038123972342051863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41282224203327852490943269 7740417038123972342051863)
                ·
                  refine ⟨11610625557185958513077795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7740417038123972342051863 11610625557185958513077795)
                  ·
                    refine ⟨17415938335778937769616693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11610625557185958513077795 17415938335778937769616693)
                    ·
                      refine ⟨1632744218979275415901565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17415938335778937769616693 1632744218979275415901565)
                      ·
                        rfl

theorem cell23_3179758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_3179758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3179758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3179758 prefixEnd_3179758 := by exact prefixLift 3179758
  have htrace : WordTrace (prefixWord ++ tailWord_3179758) baseStart_3179758 baseEnd_3179758 := by
    simpa [prefixWord, tailWord_3179758, baseEnd_3179758] using wordTrace_append hprefix tailTrace_3179758
  have hstable : (prefixWord ++ tailWord_3179758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179758).length < 2 ^ (prefixWord ++ tailWord_3179758).sum := by decide
  have hdescent : baseEnd_3179758 < baseStart_3179758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179845 : List Nat := [1, 3, 1, 1, 1, 2, 1, 6, 1, 4, 2]
def baseStart_3179845 : Nat := 118140960795 + 3179845 * 2 ^ 59
def prefixEnd_3179845 : Nat := 4983230072969 + 3 ^ 40 * 3179845 * 2
def baseEnd_3179845 : Nat := 1632788891796216575513665

theorem tailTrace_3179845 : CollatzResearch.WordTrace tailWord_3179845 prefixEnd_3179845 1632788891796216575513665 := by
  unfold tailWord_3179845
  simp only [CollatzResearch.WordTrace]
  refine ⟨115978475164972114134756989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77318983443314742756504659 115978475164972114134756989)
  ·
    refine ⟨43491928186864542800533871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115978475164972114134756989 43491928186864542800533871)
    ·
      refine ⟨65237892280296814200800807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43491928186864542800533871 65237892280296814200800807)
      ·
        refine ⟨97856838420445221301201211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65237892280296814200800807 97856838420445221301201211)
        ·
          refine ⟨146785257630667831951801817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97856838420445221301201211 146785257630667831951801817)
          ·
            refine ⟨110088943223000873963851363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146785257630667831951801817 110088943223000873963851363)
            ·
              refine ⟨165133414834501310945777045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110088943223000873963851363 165133414834501310945777045)
              ·
                refine ⟨7740628820367248950583299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 165133414834501310945777045 7740628820367248950583299)
                ·
                  refine ⟨11610943230550873425874949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7740628820367248950583299 11610943230550873425874949)
                  ·
                    refine ⟨2177051855728288767351553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11610943230550873425874949 2177051855728288767351553)
                    ·
                      refine ⟨1632788891796216575513665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2177051855728288767351553 1632788891796216575513665)
                      ·
                        rfl

theorem cell23_3179845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 4, 2].length) (baseStart_3179845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3179845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3179845 prefixEnd_3179845 := by exact prefixLift 3179845
  have htrace : WordTrace (prefixWord ++ tailWord_3179845) baseStart_3179845 baseEnd_3179845 := by
    simpa [prefixWord, tailWord_3179845, baseEnd_3179845] using wordTrace_append hprefix tailTrace_3179845
  have hstable : (prefixWord ++ tailWord_3179845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179845).length < 2 ^ (prefixWord ++ tailWord_3179845).sum := by decide
  have hdescent : baseEnd_3179845 < baseStart_3179845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179848 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 1, 6, 3]
def baseStart_3179848 : Nat := 118140960795 + 3179848 * 2 ^ 59
def prefixEnd_3179848 : Nat := 4983230072969 + 3 ^ 40 * 3179848 * 2
def baseEnd_3179848 : Nat := 1632790432238180063776151

theorem tailTrace_3179848 : CollatzResearch.WordTrace tailWord_3179848 prefixEnd_3179848 1632790432238180063776151 := by
  unfold tailWord_3179848
  simp only [CollatzResearch.WordTrace]
  refine ⟨57989292291980622823558099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77319056389307497098077465 57989292291980622823558099)
  ·
    refine ⟨86983938437970934235337149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57989292291980622823558099 86983938437970934235337149)
    ·
      refine ⟨32618976914239100338251431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86983938437970934235337149 32618976914239100338251431)
      ·
        refine ⟨48928465371358650507377147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32618976914239100338251431 48928465371358650507377147)
        ·
          refine ⟨73392698057037975761065721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48928465371358650507377147 73392698057037975761065721)
          ·
            refine ⟨55044523542778481820799291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73392698057037975761065721 55044523542778481820799291)
            ·
              refine ⟨82566785314167722731198937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55044523542778481820799291 82566785314167722731198937)
              ·
                refine ⟨61925088985625792048399203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82566785314167722731198937 61925088985625792048399203)
                ·
                  refine ⟨92887633478438688072598805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61925088985625792048399203 92887633478438688072598805)
                  ·
                    refine ⟨4354107819301813503403069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 92887633478438688072598805 4354107819301813503403069)
                    ·
                      refine ⟨1632790432238180063776151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4354107819301813503403069 1632790432238180063776151)
                      ·
                        rfl

theorem cell23_3179848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 1, 6, 3].length) (baseStart_3179848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3179848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3179848 prefixEnd_3179848 := by exact prefixLift 3179848
  have htrace : WordTrace (prefixWord ++ tailWord_3179848) baseStart_3179848 baseEnd_3179848 := by
    simpa [prefixWord, tailWord_3179848, baseEnd_3179848] using wordTrace_append hprefix tailTrace_3179848
  have hstable : (prefixWord ++ tailWord_3179848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179848).length < 2 ^ (prefixWord ++ tailWord_3179848).sum := by decide
  have hdescent : baseEnd_3179848 < baseStart_3179848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179898 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 6, 5]
def baseStart_3179898 : Nat := 118140960795 + 3179898 * 2 ^ 59
def prefixEnd_3179898 : Nat := 4983230072969 + 3 ^ 40 * 3179898 * 2
def baseEnd_3179898 : Nat := 544272035423634956050307

theorem tailTrace_3179898 : CollatzResearch.WordTrace tailWord_3179898 prefixEnd_3179898 544272035423634956050307 := by
  unfold tailWord_3179898
  simp only [CollatzResearch.WordTrace]
  refine ⟨28995102058445026046609087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77320272155853402790957565 28995102058445026046609087)
  ·
    refine ⟨43492653087667539069913631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28995102058445026046609087 43492653087667539069913631)
    ·
      refine ⟨65238979631501308604870447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43492653087667539069913631 65238979631501308604870447)
      ·
        refine ⟨97858469447251962907305671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65238979631501308604870447 97858469447251962907305671)
        ·
          refine ⟨146787704170877944360958507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97858469447251962907305671 146787704170877944360958507)
          ·
            refine ⟨220181556256316916541437761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146787704170877944360958507 220181556256316916541437761)
            ·
              refine ⟨165136167192237687406078321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220181556256316916541437761 165136167192237687406078321)
              ·
                refine ⟨123852125394178265554558741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165136167192237687406078321 123852125394178265554558741)
                ·
                  refine ⟨5805568377852106197869941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 123852125394178265554558741 5805568377852106197869941)
                  ·
                    refine ⟨544272035423634956050307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5805568377852106197869941 544272035423634956050307)
                    ·
                      rfl

theorem cell23_3179898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 6, 5].length) (baseStart_3179898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3179898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3179898 prefixEnd_3179898 := by exact prefixLift 3179898
  have htrace : WordTrace (prefixWord ++ tailWord_3179898) baseStart_3179898 baseEnd_3179898 := by
    simpa [prefixWord, tailWord_3179898, baseEnd_3179898] using wordTrace_append hprefix tailTrace_3179898
  have hstable : (prefixWord ++ tailWord_3179898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179898).length < 2 ^ (prefixWord ++ tailWord_3179898).sum := by decide
  have hdescent : baseEnd_3179898 < baseStart_3179898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179949 : List Nat := [1, 5, 2, 2, 1, 3, 1, 1, 2, 5]
def baseStart_3179949 : Nat := 118140960795 + 3179949 * 2 ^ 59
def prefixEnd_3179949 : Nat := 4983230072969 + 3 ^ 40 * 3179949 * 2
def baseEnd_3179949 : Nat := 544280764594761389537729

theorem tailTrace_3179949 : CollatzResearch.WordTrace tailWord_3179949 prefixEnd_3179949 544280764594761389537729 := by
  unfold tailWord_3179949
  simp only [CollatzResearch.WordTrace]
  refine ⟨115982268356595339896542901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77321512237730226597695267 115982268356595339896542901)
  ·
    refine ⟨10873337658430813115300897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115982268356595339896542901 10873337658430813115300897)
    ·
      refine ⟨8155003243823109836475673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10873337658430813115300897 8155003243823109836475673)
      ·
        refine ⟨6116252432867332377356755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8155003243823109836475673 6116252432867332377356755)
        ·
          refine ⟨9174378649300998566035133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6116252432867332377356755 9174378649300998566035133)
          ·
            refine ⟨3440391993487874462263175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9174378649300998566035133 3440391993487874462263175)
            ·
              refine ⟨5160587990231811693394763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3440391993487874462263175 5160587990231811693394763)
              ·
                refine ⟨7740881985347717540092145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5160587990231811693394763 7740881985347717540092145)
                ·
                  refine ⟨5805661489010788155069109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7740881985347717540092145 5805661489010788155069109)
                  ·
                    refine ⟨544280764594761389537729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5805661489010788155069109 544280764594761389537729)
                    ·
                      rfl

theorem cell23_3179949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_3179949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3179949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3179949 prefixEnd_3179949 := by exact prefixLift 3179949
  have htrace : WordTrace (prefixWord ++ tailWord_3179949) baseStart_3179949 baseEnd_3179949 := by
    simpa [prefixWord, tailWord_3179949, baseEnd_3179949] using wordTrace_append hprefix tailTrace_3179949
  have hstable : (prefixWord ++ tailWord_3179949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179949).length < 2 ^ (prefixWord ++ tailWord_3179949).sum := by decide
  have hdescent : baseEnd_3179949 < baseStart_3179949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180013 : List Nat := [1, 5, 1, 3, 2, 2, 1, 3, 1, 4]
def baseStart_3180013 : Nat := 118140960795 + 3180013 * 2 ^ 59
def prefixEnd_3180013 : Nat := 4983230072969 + 3 ^ 40 * 3180013 * 2
def baseEnd_3180013 : Nat := 544291718848723972737631

theorem tailTrace_3180013 : CollatzResearch.WordTrace tailWord_3180013 prefixEnd_3180013 544291718848723972737631 := by
  unfold tailWord_3180013
  simp only [CollatzResearch.WordTrace]
  refine ⟨115984602628363478826872693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77323068418908985884581795 115984602628363478826872693)
  ·
    refine ⟨10873556496409076140019315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115984602628363478826872693 10873556496409076140019315)
    ·
      refine ⟨16310334744613614210028973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10873556496409076140019315 16310334744613614210028973)
      ·
        refine ⟨6116375529230105328760865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16310334744613614210028973 6116375529230105328760865)
        ·
          refine ⟨4587281646922578996570649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6116375529230105328760865 4587281646922578996570649)
          ·
            refine ⟨3440461235191934247427987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4587281646922578996570649 3440461235191934247427987)
            ·
              refine ⟨5160691852787901371141981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3440461235191934247427987 5160691852787901371141981)
              ·
                refine ⟨1935259444795463014178243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5160691852787901371141981 1935259444795463014178243)
                ·
                  refine ⟨2902889167193194521267365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1935259444795463014178243 2902889167193194521267365)
                  ·
                    refine ⟨544291718848723972737631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2902889167193194521267365 544291718848723972737631)
                    ·
                      rfl

theorem cell23_3180013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_3180013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180013 prefixEnd_3180013 := by exact prefixLift 3180013
  have htrace : WordTrace (prefixWord ++ tailWord_3180013) baseStart_3180013 baseEnd_3180013 := by
    simpa [prefixWord, tailWord_3180013, baseEnd_3180013] using wordTrace_append hprefix tailTrace_3180013
  have hstable : (prefixWord ++ tailWord_3180013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180013).length < 2 ^ (prefixWord ++ tailWord_3180013).sum := by decide
  have hdescent : baseEnd_3180013 < baseStart_3180013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180019 : List Nat := [1, 1, 1, 2, 2, 2, 2, 7, 1, 1, 3]
def baseStart_3180019 : Nat := 118140960795 + 3180019 * 2 ^ 59
def prefixEnd_3180019 : Nat := 4983230072969 + 3 ^ 40 * 3180019 * 2
def baseEnd_3180019 : Nat := 1632878237430098894737865

theorem tailTrace_3180019 : CollatzResearch.WordTrace tailWord_3180019 prefixEnd_3180019 1632878237430098894737865 := by
  unfold tailWord_3180019
  simp only [CollatzResearch.WordTrace]
  refine ⟨115984821466341741851591111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77323214310894494567727407 115984821466341741851591111)
  ·
    refine ⟨173977232199512612777386667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115984821466341741851591111 173977232199512612777386667)
    ·
      refine ⟨260965848299268919166080001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173977232199512612777386667 260965848299268919166080001)
      ·
        refine ⟨195724386224451689374560001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260965848299268919166080001 195724386224451689374560001)
        ·
          refine ⟨146793289668338767030920001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195724386224451689374560001 146793289668338767030920001)
          ·
            refine ⟨110094967251254075273190001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146793289668338767030920001 110094967251254075273190001)
            ·
              refine ⟨82571225438440556454892501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110094967251254075273190001 82571225438440556454892501)
              ·
                refine ⟨1935263096213450541911543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 82571225438440556454892501 1935263096213450541911543)
                ·
                  refine ⟨2902894644320175812867315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1935263096213450541911543 2902894644320175812867315)
                  ·
                    refine ⟨4354341966480263719300973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2902894644320175812867315 4354341966480263719300973)
                    ·
                      refine ⟨1632878237430098894737865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4354341966480263719300973 1632878237430098894737865)
                      ·
                        rfl

theorem cell23_3180019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7, 1, 1, 3].length) (baseStart_3180019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180019 prefixEnd_3180019 := by exact prefixLift 3180019
  have htrace : WordTrace (prefixWord ++ tailWord_3180019) baseStart_3180019 baseEnd_3180019 := by
    simpa [prefixWord, tailWord_3180019, baseEnd_3180019] using wordTrace_append hprefix tailTrace_3180019
  have hstable : (prefixWord ++ tailWord_3180019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180019).length < 2 ^ (prefixWord ++ tailWord_3180019).sum := by decide
  have hdescent : baseEnd_3180019 < baseStart_3180019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180025 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 5, 1, 4]
def baseStart_3180025 : Nat := 118140960795 + 3180025 * 2 ^ 59
def prefixEnd_3180025 : Nat := 4983230072969 + 3 ^ 40 * 3180025 * 2
def baseEnd_3180025 : Nat := 1632881318314025871262837

theorem tailTrace_3180025 : CollatzResearch.WordTrace tailWord_3180025 prefixEnd_3180025 1632881318314025871262837 := by
  unfold tailWord_3180025
  simp only [CollatzResearch.WordTrace]
  refine ⟨115985040304320004876309529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77323360202880003250873019 115985040304320004876309529)
  ·
    refine ⟨86988780228240003657232147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115985040304320004876309529 86988780228240003657232147)
    ·
      refine ⟨130483170342360005485848221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86988780228240003657232147 130483170342360005485848221)
      ·
        refine ⟨48931188878385002057193083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130483170342360005485848221 48931188878385002057193083)
        ·
          refine ⟨73396783317577503085789625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48931188878385002057193083 73396783317577503085789625)
          ·
            refine ⟨55047587488183127314342219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73396783317577503085789625 55047587488183127314342219)
            ·
              refine ⟨82571381232274690971513329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55047587488183127314342219 82571381232274690971513329)
              ·
                refine ⟨61928535924206018228634997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82571381232274690971513329 61928535924206018228634997)
                ·
                  refine ⟨5805800242894314208934531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61928535924206018228634997 5805800242894314208934531)
                  ·
                    refine ⟨8708700364341471313401797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5805800242894314208934531 8708700364341471313401797)
                    ·
                      refine ⟨1632881318314025871262837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8708700364341471313401797 1632881318314025871262837)
                      ·
                        rfl

theorem cell23_3180025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_3180025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180025 prefixEnd_3180025 := by exact prefixLift 3180025
  have htrace : WordTrace (prefixWord ++ tailWord_3180025) baseStart_3180025 baseEnd_3180025 := by
    simpa [prefixWord, tailWord_3180025, baseEnd_3180025] using wordTrace_append hprefix tailTrace_3180025
  have hstable : (prefixWord ++ tailWord_3180025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180025).length < 2 ^ (prefixWord ++ tailWord_3180025).sum := by decide
  have hdescent : baseEnd_3180025 < baseStart_3180025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180029 : List Nat := [1, 4, 1, 1, 1, 5, 1, 2, 2, 3, 2]
def baseStart_3180029 : Nat := 118140960795 + 3180029 * 2 ^ 59
def prefixEnd_3180029 : Nat := 4983230072969 + 3 ^ 40 * 3180029 * 2
def baseEnd_3180029 : Nat := 1632883372236643855612819

theorem tailTrace_3180029 : CollatzResearch.WordTrace tailWord_3180029 prefixEnd_3180029 1632883372236643855612819 := by
  unfold tailWord_3180029
  simp only [CollatzResearch.WordTrace]
  refine ⟨115985186196305513559455141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77323457464203675706303427 115985186196305513559455141)
  ·
    refine ⟨21747222411807283792397839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115985186196305513559455141 21747222411807283792397839)
    ·
      refine ⟨32620833617710925688596759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21747222411807283792397839 32620833617710925688596759)
      ·
        refine ⟨48931250426566388532895139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32620833617710925688596759 48931250426566388532895139)
        ·
          refine ⟨73396875639849582799342709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48931250426566388532895139 73396875639849582799342709)
          ·
            refine ⟨6880957091235898387438379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73396875639849582799342709 6880957091235898387438379)
            ·
              refine ⟨10321435636853847581157569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6880957091235898387438379 10321435636853847581157569)
              ·
                refine ⟨7741076727640385685868177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10321435636853847581157569 7741076727640385685868177)
                ·
                  refine ⟨5805807545730289264401133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7741076727640385685868177 5805807545730289264401133)
                  ·
                    refine ⟨2177177829648858474150425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5805807545730289264401133 2177177829648858474150425)
                    ·
                      refine ⟨1632883372236643855612819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2177177829648858474150425 1632883372236643855612819)
                      ·
                        rfl

theorem cell23_3180029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 3, 2].length) (baseStart_3180029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180029 prefixEnd_3180029 := by exact prefixLift 3180029
  have htrace : WordTrace (prefixWord ++ tailWord_3180029) baseStart_3180029 baseEnd_3180029 := by
    simpa [prefixWord, tailWord_3180029, baseEnd_3180029] using wordTrace_append hprefix tailTrace_3180029
  have hstable : (prefixWord ++ tailWord_3180029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180029).length < 2 ^ (prefixWord ++ tailWord_3180029).sum := by decide
  have hdescent : baseEnd_3180029 < baseStart_3180029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180030 : List Nat := [4, 2, 2, 3, 1, 1, 3, 2, 1, 4]
def baseStart_3180030 : Nat := 118140960795 + 3180030 * 2 ^ 59
def prefixEnd_3180030 : Nat := 4983230072969 + 3 ^ 40 * 3180030 * 2
def baseEnd_3180030 : Nat := 544294628572432783900105

theorem tailTrace_3180030 : CollatzResearch.WordTrace tailWord_3180030 prefixEnd_3180030 544294628572432783900105 := by
  unfold tailWord_3180030
  simp only [CollatzResearch.WordTrace]
  refine ⟨14498152833662736341280193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77323481779534593820161029 14498152833662736341280193)
  ·
    refine ⟨10873614625247052255960145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14498152833662736341280193 10873614625247052255960145)
    ·
      refine ⟨8155210968935289191970109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10873614625247052255960145 8155210968935289191970109)
      ·
        refine ⟨3058204113350733446988791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8155210968935289191970109 3058204113350733446988791)
        ·
          refine ⟨4587306170026100170483187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3058204113350733446988791 4587306170026100170483187)
          ·
            refine ⟨6880959255039150255724781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4587306170026100170483187 6880959255039150255724781)
            ·
              refine ⟨2580359720639681345896793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6880959255039150255724781 2580359720639681345896793)
              ·
                refine ⟨1935269790479761009422595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2580359720639681345896793 1935269790479761009422595)
                ·
                  refine ⟨2902904685719641514133893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1935269790479761009422595 2902904685719641514133893)
                  ·
                    refine ⟨544294628572432783900105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2902904685719641514133893 544294628572432783900105)
                    ·
                      rfl

theorem cell23_3180030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_3180030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180030 prefixEnd_3180030 := by exact prefixLift 3180030
  have htrace : WordTrace (prefixWord ++ tailWord_3180030) baseStart_3180030 baseEnd_3180030 := by
    simpa [prefixWord, tailWord_3180030, baseEnd_3180030] using wordTrace_append hprefix tailTrace_3180030
  have hstable : (prefixWord ++ tailWord_3180030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180030).length < 2 ^ (prefixWord ++ tailWord_3180030).sum := by decide
  have hdescent : baseEnd_3180030 < baseStart_3180030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180056 : List Nat := [2, 1, 2, 3, 5, 1, 1, 2, 1, 5]
def baseStart_3180056 : Nat := 118140960795 + 3180056 * 2 ^ 59
def prefixEnd_3180056 : Nat := 4983230072969 + 3 ^ 40 * 3180056 * 2
def baseEnd_3180056 : Nat := 544299078738105083325065

theorem tailTrace_3180056 : CollatzResearch.WordTrace tailWord_3180056 prefixEnd_3180056 544299078738105083325065 := by
  unfold tailWord_3180056
  simp only [CollatzResearch.WordTrace]
  refine ⟨57993085483603848585344011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77324113978138464780458681 57993085483603848585344011)
  ·
    refine ⟨86989628225405772878016017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57993085483603848585344011 86989628225405772878016017)
    ·
      refine ⟨65242221169054329658512013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86989628225405772878016017 65242221169054329658512013)
      ·
        refine ⟨24465832938395373621942005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65242221169054329658512013 24465832938395373621942005)
        ·
          refine ⟨2293671837974566277057063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24465832938395373621942005 2293671837974566277057063)
          ·
            refine ⟨3440507756961849415585595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2293671837974566277057063 3440507756961849415585595)
            ·
              refine ⟨5160761635442774123378393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3440507756961849415585595 5160761635442774123378393)
              ·
                refine ⟨3870571226582080592533795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5160761635442774123378393 3870571226582080592533795)
                ·
                  refine ⟨5805856839873120888800693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3870571226582080592533795 5805856839873120888800693)
                  ·
                    refine ⟨544299078738105083325065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5805856839873120888800693 544299078738105083325065)
                    ·
                      rfl

theorem cell23_3180056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 1, 5].length) (baseStart_3180056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180056 prefixEnd_3180056 := by exact prefixLift 3180056
  have htrace : WordTrace (prefixWord ++ tailWord_3180056) baseStart_3180056 baseEnd_3180056 := by
    simpa [prefixWord, tailWord_3180056, baseEnd_3180056] using wordTrace_append hprefix tailTrace_3180056
  have hstable : (prefixWord ++ tailWord_3180056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180056).length < 2 ^ (prefixWord ++ tailWord_3180056).sum := by decide
  have hdescent : baseEnd_3180056 < baseStart_3180056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180065 : List Nat := [1, 2, 3, 2, 2, 2, 2, 9]
def baseStart_3180065 : Nat := 118140960795 + 3180065 * 2 ^ 59
def prefixEnd_3180065 : Nat := 4983230072969 + 3 ^ 40 * 3180065 * 2
def baseEnd_3180065 : Nat := 60477846575563174620839

theorem tailTrace_3180065 : CollatzResearch.WordTrace tailWord_3180065 prefixEnd_3180065 60477846575563174620839 := by
  unfold tailWord_3180065
  simp only [CollatzResearch.WordTrace]
  refine ⟨115986499224175091707765649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77324332816116727805177099 115986499224175091707765649)
  ·
    refine ⟨86989874418131318780824237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115986499224175091707765649 86989874418131318780824237)
    ·
      refine ⟨32621202906799244542809089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86989874418131318780824237 32621202906799244542809089)
      ·
        refine ⟨24465902180099433407106817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32621202906799244542809089 24465902180099433407106817)
        ·
          refine ⟨18349426635074575055330113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24465902180099433407106817 18349426635074575055330113)
          ·
            refine ⟨13762069976305931291497585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18349426635074575055330113 13762069976305931291497585)
            ·
              refine ⟨10321552482229448468623189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13762069976305931291497585 10321552482229448468623189)
              ·
                refine ⟨60477846575563174620839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10321552482229448468623189 60477846575563174620839)
                ·
                  rfl

theorem cell23_3180065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 9].length) (baseStart_3180065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180065 prefixEnd_3180065 := by exact prefixLift 3180065
  have htrace : WordTrace (prefixWord ++ tailWord_3180065) baseStart_3180065 baseEnd_3180065 := by
    simpa [prefixWord, tailWord_3180065, baseEnd_3180065] using wordTrace_append hprefix tailTrace_3180065
  have hstable : (prefixWord ++ tailWord_3180065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180065).length < 2 ^ (prefixWord ++ tailWord_3180065).sum := by decide
  have hdescent : baseEnd_3180065 < baseStart_3180065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180095 : List Nat := [1, 1, 2, 2, 3, 3, 1, 1, 2, 7]
def baseStart_3180095 : Nat := 118140960795 + 3180095 * 2 ^ 59
def prefixEnd_3180095 : Nat := 4983230072969 + 3 ^ 40 * 3180095 * 2
def baseEnd_3180095 : Nat := 544305753986613532462505

theorem tailTrace_3180095 : CollatzResearch.WordTrace tailWord_3180095 prefixEnd_3180095 544305753986613532462505 := by
  unfold tailWord_3180095
  simp only [CollatzResearch.WordTrace]
  refine ⟨115987593414066406831357739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77325062276044271220905159 115987593414066406831357739)
  ·
    refine ⟨173981390121099610247036609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115987593414066406831357739 173981390121099610247036609)
    ·
      refine ⟨130486042590824707685277457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173981390121099610247036609 130486042590824707685277457)
      ·
        refine ⟨97864531943118530763958093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130486042590824707685277457 97864531943118530763958093)
        ·
          refine ⟨36699199478669449036484285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97864531943118530763958093 36699199478669449036484285)
          ·
            refine ⟨13762199804501043388681607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36699199478669449036484285 13762199804501043388681607)
            ·
              refine ⟨20643299706751565083022411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13762199804501043388681607 20643299706751565083022411)
              ·
                refine ⟨30964949560127347624533617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20643299706751565083022411 30964949560127347624533617)
                ·
                  refine ⟨23223712170095510718400213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30964949560127347624533617 23223712170095510718400213)
                  ·
                    refine ⟨544305753986613532462505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23223712170095510718400213 544305753986613532462505)
                    ·
                      rfl

theorem cell23_3180095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 7].length) (baseStart_3180095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180095 prefixEnd_3180095 := by exact prefixLift 3180095
  have htrace : WordTrace (prefixWord ++ tailWord_3180095) baseStart_3180095 baseEnd_3180095 := by
    simpa [prefixWord, tailWord_3180095, baseEnd_3180095] using wordTrace_append hprefix tailTrace_3180095
  have hstable : (prefixWord ++ tailWord_3180095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180095).length < 2 ^ (prefixWord ++ tailWord_3180095).sum := by decide
  have hdescent : baseEnd_3180095 < baseStart_3180095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180119 : List Nat := [1, 1, 3, 2, 2, 3, 2, 1, 3, 3, 2]
def baseStart_3180119 : Nat := 118140960795 + 3180119 * 2 ^ 59
def prefixEnd_3180119 : Nat := 4983230072969 + 3 ^ 40 * 3180119 * 2
def baseEnd_3180119 : Nat := 1632929585495548503487405

theorem tailTrace_3180119 : CollatzResearch.WordTrace tailWord_3180119 prefixEnd_3180119 1632929585495548503487405 := by
  unfold tailWord_3180119
  simp only [CollatzResearch.WordTrace]
  refine ⟨115988468765979458930231411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77325645843986305953487607 115988468765979458930231411)
  ·
    refine ⟨173982703148969188395347117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115988468765979458930231411 173982703148969188395347117)
    ·
      refine ⟨65243513680863445648255169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173982703148969188395347117 65243513680863445648255169)
      ·
        refine ⟨48932635260647584236191377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65243513680863445648255169 48932635260647584236191377)
        ·
          refine ⟨36699476445485688177143533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48932635260647584236191377 36699476445485688177143533)
          ·
            refine ⟨13762303667057133066428825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36699476445485688177143533 13762303667057133066428825)
            ·
              refine ⟨10321727750292849799821619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13762303667057133066428825 10321727750292849799821619)
              ·
                refine ⟨15482591625439274699732429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10321727750292849799821619 15482591625439274699732429)
                ·
                  refine ⟨5805971859539728012399661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15482591625439274699732429 5805971859539728012399661)
                  ·
                    refine ⟨2177239447327398004649873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5805971859539728012399661 2177239447327398004649873)
                    ·
                      refine ⟨1632929585495548503487405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2177239447327398004649873 1632929585495548503487405)
                      ·
                        rfl

theorem cell23_3180119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 3, 2].length) (baseStart_3180119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180119 prefixEnd_3180119 := by exact prefixLift 3180119
  have htrace : WordTrace (prefixWord ++ tailWord_3180119) baseStart_3180119 baseEnd_3180119 := by
    simpa [prefixWord, tailWord_3180119, baseEnd_3180119] using wordTrace_append hprefix tailTrace_3180119
  have hstable : (prefixWord ++ tailWord_3180119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180119).length < 2 ^ (prefixWord ++ tailWord_3180119).sum := by decide
  have hdescent : baseEnd_3180119 < baseStart_3180119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180236 : List Nat := [2, 2, 1, 5, 2, 1, 2, 1, 2, 5]
def baseStart_3180236 : Nat := 118140960795 + 3180236 * 2 ^ 59
def prefixEnd_3180236 : Nat := 4983230072969 + 3 ^ 40 * 3180236 * 2
def baseEnd_3180236 : Nat := 544329887577374848574789

theorem tailTrace_3180236 : CollatzResearch.WordTrace tailWord_3180236 prefixEnd_3180236 544329887577374848574789 := by
  unfold tailWord_3180236
  simp only [CollatzResearch.WordTrace]
  refine ⟨57996368053277793956120281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77328490737703725274827041 57996368053277793956120281)
  ·
    refine ⟨43497276039958345467090211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57996368053277793956120281 43497276039958345467090211)
    ·
      refine ⟨65245914059937518200635317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43497276039958345467090211 65245914059937518200635317)
      ·
        refine ⟨6116804443119142331309561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65245914059937518200635317 6116804443119142331309561)
        ·
          refine ⟨4587603332339356748482171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6116804443119142331309561 4587603332339356748482171)
          ·
            refine ⟨6881404998509035122723257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4587603332339356748482171 6881404998509035122723257)
            ·
              refine ⟨5161053748881776342042443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6881404998509035122723257 5161053748881776342042443)
              ·
                refine ⟨7741580623322664513063665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5161053748881776342042443 7741580623322664513063665)
                ·
                  refine ⟨5806185467491998384797749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7741580623322664513063665 5806185467491998384797749)
                  ·
                    refine ⟨544329887577374848574789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5806185467491998384797749 544329887577374848574789)
                    ·
                      rfl

theorem cell23_3180236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 2, 5].length) (baseStart_3180236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180236 prefixEnd_3180236 := by exact prefixLift 3180236
  have htrace : WordTrace (prefixWord ++ tailWord_3180236) baseStart_3180236 baseEnd_3180236 := by
    simpa [prefixWord, tailWord_3180236, baseEnd_3180236] using wordTrace_append hprefix tailTrace_3180236
  have hstable : (prefixWord ++ tailWord_3180236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180236).length < 2 ^ (prefixWord ++ tailWord_3180236).sum := by decide
  have hdescent : baseEnd_3180236 < baseStart_3180236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180316 : List Nat := [2, 2, 3, 1, 1, 2, 2, 1, 4, 3, 2]
def baseStart_3180316 : Nat := 118140960795 + 3180316 * 2 ^ 59
def prefixEnd_3180316 : Nat := 4983230072969 + 3 ^ 40 * 3180316 * 2
def baseEnd_3180316 : Nat := 1633030741184484232723999

theorem tailTrace_3180316 : CollatzResearch.WordTrace tailWord_3180316 prefixEnd_3180316 1633030741184484232723999 := by
  unfold tailWord_3180316
  simp only [CollatzResearch.WordTrace]
  refine ⟨57997826973132880787576401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77330435964177174383435201 57997826973132880787576401)
  ·
    refine ⟨43498370229849660590682301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57997826973132880787576401 43498370229849660590682301)
    ·
      refine ⟨16311888836193622721505863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43498370229849660590682301 16311888836193622721505863)
      ·
        refine ⟨24467833254290434082258795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16311888836193622721505863 24467833254290434082258795)
        ·
          refine ⟨36701749881435651123388193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24467833254290434082258795 36701749881435651123388193)
          ·
            refine ⟨27526312411076738342541145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36701749881435651123388193 27526312411076738342541145)
            ·
              refine ⟨20644734308307553756905859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27526312411076738342541145 20644734308307553756905859)
              ·
                refine ⟨30967101462461330635358789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20644734308307553756905859 30967101462461330635358789)
                ·
                  refine ⟨5806331524211499494129773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30967101462461330635358789 5806331524211499494129773)
                  ·
                    refine ⟨2177374321579312310298665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5806331524211499494129773 2177374321579312310298665)
                    ·
                      refine ⟨1633030741184484232723999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2177374321579312310298665 1633030741184484232723999)
                      ·
                        rfl

theorem cell23_3180316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_3180316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180316 prefixEnd_3180316 := by exact prefixLift 3180316
  have htrace : WordTrace (prefixWord ++ tailWord_3180316) baseStart_3180316 baseEnd_3180316 := by
    simpa [prefixWord, tailWord_3180316, baseEnd_3180316] using wordTrace_append hprefix tailTrace_3180316
  have hstable : (prefixWord ++ tailWord_3180316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180316).length < 2 ^ (prefixWord ++ tailWord_3180316).sum := by decide
  have hdescent : baseEnd_3180316 < baseStart_3180316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180323 : List Nat := [1, 1, 1, 4, 2, 1, 4, 4, 1, 1, 3]
def baseStart_3180323 : Nat := 118140960795 + 3180323 * 2 ^ 59
def prefixEnd_3180323 : Nat := 4983230072969 + 3 ^ 40 * 3180323 * 2
def baseEnd_3180323 : Nat := 1633034335549065705336467

theorem tailTrace_3180323 : CollatzResearch.WordTrace tailWord_3180323 prefixEnd_3180323 1633034335549065705336467 := by
  unfold tailWord_3180323
  simp only [CollatzResearch.WordTrace]
  refine ⟨115995909257240401770657623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77330606171493601180438415 115995909257240401770657623)
  ·
    refine ⟨173993863885860602655986435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115995909257240401770657623 173993863885860602655986435)
    ·
      refine ⟨260990795828790903983979653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173993863885860602655986435 260990795828790903983979653)
      ·
        refine ⟨48935774217898294496996185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 260990795828790903983979653 48935774217898294496996185)
        ·
          refine ⟨36701830663423720872747139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48935774217898294496996185 36701830663423720872747139)
          ·
            refine ⟨55052745995135581309120709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36701830663423720872747139 55052745995135581309120709)
            ·
              refine ⟨10322389874087921495460133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55052745995135581309120709 10322389874087921495460133)
              ·
                refine ⟨1935448101391485280398775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10322389874087921495460133 1935448101391485280398775)
                ·
                  refine ⟨2903172152087227920598163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1935448101391485280398775 2903172152087227920598163)
                  ·
                    refine ⟨4354758228130841880897245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2903172152087227920598163 4354758228130841880897245)
                    ·
                      refine ⟨1633034335549065705336467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4354758228130841880897245 1633034335549065705336467)
                      ·
                        rfl

theorem cell23_3180323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 4, 1, 1, 3].length) (baseStart_3180323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180323 prefixEnd_3180323 := by exact prefixLift 3180323
  have htrace : WordTrace (prefixWord ++ tailWord_3180323) baseStart_3180323 baseEnd_3180323 := by
    simpa [prefixWord, tailWord_3180323, baseEnd_3180323] using wordTrace_append hprefix tailTrace_3180323
  have hstable : (prefixWord ++ tailWord_3180323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180323).length < 2 ^ (prefixWord ++ tailWord_3180323).sum := by decide
  have hdescent : baseEnd_3180323 < baseStart_3180323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180329 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 4, 6, 2]
def baseStart_3180329 : Nat := 118140960795 + 3180329 * 2 ^ 59
def prefixEnd_3180329 : Nat := 4983230072969 + 3 ^ 40 * 3180329 * 2
def baseEnd_3180329 : Nat := 1633037416432992681861439

theorem tailTrace_3180329 : CollatzResearch.WordTrace tailWord_3180329 prefixEnd_3180329 1633037416432992681861439 := by
  unfold tailWord_3180329
  simp only [CollatzResearch.WordTrace]
  refine ⟨115996128095218664795376041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77330752063479109863584027 115996128095218664795376041)
  ·
    refine ⟨86997096071413998596532031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115996128095218664795376041 86997096071413998596532031)
    ·
      refine ⟨130495644107120997894798047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86997096071413998596532031 130495644107120997894798047)
      ·
        refine ⟨195743466160681496842197071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130495644107120997894798047 195743466160681496842197071)
        ·
          refine ⟨293615199241022245263295607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195743466160681496842197071 293615199241022245263295607)
          ·
            refine ⟨440422798861533367894943411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293615199241022245263295607 440422798861533367894943411)
            ·
              refine ⟨660634198292300051842415117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440422798861533367894943411 660634198292300051842415117)
              ·
                refine ⟨247737824359612519440905669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 660634198292300051842415117 247737824359612519440905669)
                ·
                  refine ⟨46450842067427347395169813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 247737824359612519440905669 46450842067427347395169813)
                  ·
                    refine ⟨2177383221910656909148585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 46450842067427347395169813 2177383221910656909148585)
                    ·
                      refine ⟨1633037416432992681861439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2177383221910656909148585 1633037416432992681861439)
                      ·
                        rfl

theorem cell23_3180329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 6, 2].length) (baseStart_3180329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180329 prefixEnd_3180329 := by exact prefixLift 3180329
  have htrace : WordTrace (prefixWord ++ tailWord_3180329) baseStart_3180329 baseEnd_3180329 := by
    simpa [prefixWord, tailWord_3180329, baseEnd_3180329] using wordTrace_append hprefix tailTrace_3180329
  have hstable : (prefixWord ++ tailWord_3180329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180329).length < 2 ^ (prefixWord ++ tailWord_3180329).sum := by decide
  have hdescent : baseEnd_3180329 < baseStart_3180329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180346 : List Nat := [3, 1, 1, 1, 5, 1, 1, 4, 1, 1, 4]
def baseStart_3180346 : Nat := 118140960795 + 3180346 * 2 ^ 59
def prefixEnd_3180346 : Nat := 4983230072969 + 3 ^ 40 * 3180346 * 2
def baseEnd_3180346 : Nat := 1633046145604119115348861

theorem tailTrace_3180346 : CollatzResearch.WordTrace tailWord_3180346 prefixEnd_3180346 1633046145604119115348861 := by
  unfold tailWord_3180346
  simp only [CollatzResearch.WordTrace]
  refine ⟨28999187034039269174686223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77331165424104717799163261 28999187034039269174686223)
  ·
    refine ⟨43498780551058903762029335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28999187034039269174686223 43498780551058903762029335)
    ·
      refine ⟨65248170826588355643044003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43498780551058903762029335 65248170826588355643044003)
      ·
        refine ⟨97872256239882533464566005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65248170826588355643044003 97872256239882533464566005)
        ·
          refine ⟨9175524022488987512303063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97872256239882533464566005 9175524022488987512303063)
          ·
            refine ⟨13763286033733481268454595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9175524022488987512303063 13763286033733481268454595)
            ·
              refine ⟨20644929050600221902681893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13763286033733481268454595 20644929050600221902681893)
              ·
                refine ⟨3870924196987541606752855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20644929050600221902681893 3870924196987541606752855)
                ·
                  refine ⟨5806386295481312410129283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3870924196987541606752855 5806386295481312410129283)
                  ·
                    refine ⟨8709579443221968615193925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5806386295481312410129283 8709579443221968615193925)
                    ·
                      refine ⟨1633046145604119115348861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8709579443221968615193925 1633046145604119115348861)
                      ·
                        rfl

theorem cell23_3180346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 1, 1, 4].length) (baseStart_3180346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180346 prefixEnd_3180346 := by exact prefixLift 3180346
  have htrace : WordTrace (prefixWord ++ tailWord_3180346) baseStart_3180346 baseEnd_3180346 := by
    simpa [prefixWord, tailWord_3180346, baseEnd_3180346] using wordTrace_append hprefix tailTrace_3180346
  have hstable : (prefixWord ++ tailWord_3180346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180346).length < 2 ^ (prefixWord ++ tailWord_3180346).sum := by decide
  have hdescent : baseEnd_3180346 < baseStart_3180346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180359 : List Nat := [1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 4]
def baseStart_3180359 : Nat := 118140960795 + 3180359 * 2 ^ 59
def prefixEnd_3180359 : Nat := 4983230072969 + 3 ^ 40 * 3180359 * 2
def baseEnd_3180359 : Nat := 1633052820852627564486301

theorem tailTrace_3180359 : CollatzResearch.WordTrace tailWord_3180359 prefixEnd_3180359 1633052820852627564486301 := by
  unfold tailWord_3180359
  simp only [CollatzResearch.WordTrace]
  refine ⟨115997222285109979918968131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77331481523406653279312087 115997222285109979918968131)
  ·
    refine ⟨173995833427664969878452197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115997222285109979918968131 173995833427664969878452197)
    ·
      refine ⟨32624218767687181852209787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173995833427664969878452197 32624218767687181852209787)
      ·
        refine ⟨48936328151530772778314681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32624218767687181852209787 48936328151530772778314681)
        ·
          refine ⟨36702246113648079583736011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48936328151530772778314681 36702246113648079583736011)
          ·
            refine ⟨55053369170472119375604017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36702246113648079583736011 55053369170472119375604017)
            ·
              refine ⟨41290026877854089531703013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55053369170472119375604017 41290026877854089531703013)
              ·
                refine ⟨7741880039597641787194315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41290026877854089531703013 7741880039597641787194315)
                ·
                  refine ⟨11612820059396462680791473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7741880039597641787194315 11612820059396462680791473)
                  ·
                    refine ⟨8709615044547347010593605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11612820059396462680791473 8709615044547347010593605)
                    ·
                      refine ⟨1633052820852627564486301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8709615044547347010593605 1633052820852627564486301)
                      ·
                        rfl

theorem cell23_3180359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_3180359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180359 prefixEnd_3180359 := by exact prefixLift 3180359
  have htrace : WordTrace (prefixWord ++ tailWord_3180359) baseStart_3180359 baseEnd_3180359 := by
    simpa [prefixWord, tailWord_3180359, baseEnd_3180359] using wordTrace_append hprefix tailTrace_3180359
  have hstable : (prefixWord ++ tailWord_3180359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180359).length < 2 ^ (prefixWord ++ tailWord_3180359).sum := by decide
  have hdescent : baseEnd_3180359 < baseStart_3180359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180369 : List Nat := [1, 2, 2, 1, 5, 3, 9]
def baseStart_3180369 : Nat := 118140960795 + 3180369 * 2 ^ 59
def prefixEnd_3180369 : Nat := 4983230072969 + 3 ^ 40 * 3180369 * 2
def baseEnd_3180369 : Nat := 20161209329125586732855

theorem tailTrace_3180369 : CollatzResearch.WordTrace tailWord_3180369 prefixEnd_3180369 20161209329125586732855 := by
  unfold tailWord_3180369
  simp only [CollatzResearch.WordTrace]
  refine ⟨115997587015073751626832161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77331724676715834417888107 115997587015073751626832161)
  ·
    refine ⟨86998190261305313720124121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115997587015073751626832161 86998190261305313720124121)
    ·
      refine ⟨65248642695978985290093091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86998190261305313720124121 65248642695978985290093091)
      ·
        refine ⟨97872964043968477935139637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65248642695978985290093091 97872964043968477935139637)
        ·
          refine ⟨9175590379122044806419341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97872964043968477935139637 9175590379122044806419341)
          ·
            refine ⟨3440846392170766802407253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9175590379122044806419341 3440846392170766802407253)
            ·
              refine ⟨20161209329125586732855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3440846392170766802407253 20161209329125586732855)
              ·
                rfl

theorem cell23_3180369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 9].length) (baseStart_3180369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180369 prefixEnd_3180369 := by exact prefixLift 3180369
  have htrace : WordTrace (prefixWord ++ tailWord_3180369) baseStart_3180369 baseEnd_3180369 := by
    simpa [prefixWord, tailWord_3180369, baseEnd_3180369] using wordTrace_append hprefix tailTrace_3180369
  have hstable : (prefixWord ++ tailWord_3180369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180369).length < 2 ^ (prefixWord ++ tailWord_3180369).sum := by decide
  have hdescent : baseEnd_3180369 < baseStart_3180369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180386 : List Nat := [3, 3, 2, 1, 2, 2, 2, 8]
def baseStart_3180386 : Nat := 118140960795 + 3180386 * 2 ^ 59
def prefixEnd_3180386 : Nat := 4983230072969 + 3 ^ 40 * 3180386 * 2
def baseEnd_3180386 : Nat := 60483951290011072549951

theorem tailTrace_3180386 : CollatzResearch.WordTrace tailWord_3180386 prefixEnd_3180386 60483951290011072549951 := by
  unfold tailWord_3180386
  simp only [CollatzResearch.WordTrace]
  refine ⟨28999551764003040882550253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77332138037341442353467341 28999551764003040882550253)
  ·
    refine ⟨10874831911501140330956345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28999551764003040882550253 10874831911501140330956345)
    ·
      refine ⟨8156123933625855248217259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10874831911501140330956345 8156123933625855248217259)
      ·
        refine ⟨12234185900438782872325889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8156123933625855248217259 12234185900438782872325889)
        ·
          refine ⟨9175639425329087154244417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12234185900438782872325889 9175639425329087154244417)
          ·
            refine ⟨6881729568996815365683313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9175639425329087154244417 6881729568996815365683313)
            ·
              refine ⟨5161297176747611524262485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6881729568996815365683313 5161297176747611524262485)
              ·
                refine ⟨60483951290011072549951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5161297176747611524262485 60483951290011072549951)
                ·
                  rfl

theorem cell23_3180386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 8].length) (baseStart_3180386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180386 prefixEnd_3180386 := by exact prefixLift 3180386
  have htrace : WordTrace (prefixWord ++ tailWord_3180386) baseStart_3180386 baseEnd_3180386 := by
    simpa [prefixWord, tailWord_3180386, baseEnd_3180386] using wordTrace_append hprefix tailTrace_3180386
  have hstable : (prefixWord ++ tailWord_3180386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180386).length < 2 ^ (prefixWord ++ tailWord_3180386).sum := by decide
  have hdescent : baseEnd_3180386 < baseStart_3180386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180417 : List Nat := [1, 2, 4, 4, 1, 1, 3, 1, 1, 2, 3]
def baseStart_3180417 : Nat := 118140960795 + 3180417 * 2 ^ 59
def prefixEnd_3180417 : Nat := 4983230072969 + 3 ^ 40 * 3180417 * 2
def baseEnd_3180417 : Nat := 1633082602730588337561035

theorem tailTrace_3180417 : CollatzResearch.WordTrace tailWord_3180417 prefixEnd_3180417 1633082602730588337561035 := by
  unfold tailWord_3180417
  simp only [CollatzResearch.WordTrace]
  refine ⟨115999337718899855824579505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77332891812599903883053003 115999337718899855824579505)
  ·
    refine ⟨86999503289174891868434629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115999337718899855824579505 86999503289174891868434629)
    ·
      refine ⟨16312406866720292225331493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86999503289174891868434629 16312406866720292225331493)
      ·
        refine ⟨3058576287510054792249655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16312406866720292225331493 3058576287510054792249655)
        ·
          refine ⟨4587864431265082188374483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3058576287510054792249655 4587864431265082188374483)
          ·
            refine ⟨6881796646897623282561725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4587864431265082188374483 6881796646897623282561725)
            ·
              refine ⟨2580673742586608730960647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6881796646897623282561725 2580673742586608730960647)
              ·
                refine ⟨3871010613879913096440971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2580673742586608730960647 3871010613879913096440971)
                ·
                  refine ⟨5806515920819869644661457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3871010613879913096440971 5806515920819869644661457)
                  ·
                    refine ⟨4354886940614902233496093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5806515920819869644661457 4354886940614902233496093)
                    ·
                      refine ⟨1633082602730588337561035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4354886940614902233496093 1633082602730588337561035)
                      ·
                        rfl

theorem cell23_3180417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_3180417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180417 prefixEnd_3180417 := by exact prefixLift 3180417
  have htrace : WordTrace (prefixWord ++ tailWord_3180417) baseStart_3180417 baseEnd_3180417 := by
    simpa [prefixWord, tailWord_3180417, baseEnd_3180417] using wordTrace_append hprefix tailTrace_3180417
  have hstable : (prefixWord ++ tailWord_3180417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180417).length < 2 ^ (prefixWord ++ tailWord_3180417).sum := by decide
  have hdescent : baseEnd_3180417 < baseStart_3180417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180436 : List Nat := [2, 4, 2, 1, 1, 2, 1, 1, 2, 3, 4]
def baseStart_3180436 : Nat := 118140960795 + 3180436 * 2 ^ 59
def prefixEnd_3180436 : Nat := 4983230072969 + 3 ^ 40 * 3180436 * 2
def baseEnd_3180436 : Nat := 1633092358863023763223447

theorem tailTrace_3180436 : CollatzResearch.WordTrace tailWord_3180436 prefixEnd_3180436 1633092358863023763223447 := by
  unfold tailWord_3180436
  simp only [CollatzResearch.WordTrace]
  refine ⟨58000015352915511034760581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77333353803887348046347441 58000015352915511034760581)
  ·
    refine ⟨10875002878671658319017609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58000015352915511034760581 10875002878671658319017609)
    ·
      refine ⟨8156252159003743739263207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10875002878671658319017609 8156252159003743739263207)
      ·
        refine ⟨12234378238505615608894811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8156252159003743739263207 12234378238505615608894811)
        ·
          refine ⟨18351567357758423413342217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12234378238505615608894811 18351567357758423413342217)
          ·
            refine ⟨13763675518318817560006663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18351567357758423413342217 13763675518318817560006663)
            ·
              refine ⟨20645513277478226340009995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13763675518318817560006663 20645513277478226340009995)
              ·
                refine ⟨30968269916217339510014993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20645513277478226340009995 30968269916217339510014993)
                ·
                  refine ⟨23226202437163004632511245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30968269916217339510014993 23226202437163004632511245)
                  ·
                    refine ⟨8709825913936126737191717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23226202437163004632511245 8709825913936126737191717)
                    ·
                      refine ⟨1633092358863023763223447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8709825913936126737191717 1633092358863023763223447)
                      ·
                        rfl

theorem cell23_3180436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_3180436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180436 prefixEnd_3180436 := by exact prefixLift 3180436
  have htrace : WordTrace (prefixWord ++ tailWord_3180436) baseStart_3180436 baseEnd_3180436 := by
    simpa [prefixWord, tailWord_3180436, baseEnd_3180436] using wordTrace_append hprefix tailTrace_3180436
  have hstable : (prefixWord ++ tailWord_3180436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180436).length < 2 ^ (prefixWord ++ tailWord_3180436).sum := by decide
  have hdescent : baseEnd_3180436 < baseStart_3180436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180496 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 1, 7, 2]
def baseStart_3180496 : Nat := 118140960795 + 3180496 * 2 ^ 59
def prefixEnd_3180496 : Nat := 4983230072969 + 3 ^ 40 * 3180496 * 2
def baseEnd_3180496 : Nat := 1633123167702293528473171

theorem tailTrace_3180496 : CollatzResearch.WordTrace tailWord_3180496 prefixEnd_3180496 1633123167702293528473171 := by
  unfold tailWord_3180496
  simp only [CollatzResearch.WordTrace]
  refine ⟨58001109542806826158352671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77334812723742434877803561 58001109542806826158352671)
  ·
    refine ⟨87001664314210239237529007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58001109542806826158352671 87001664314210239237529007)
    ·
      refine ⟨130502496471315358856293511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87001664314210239237529007 130502496471315358856293511)
      ·
        refine ⟨195753744706973038284440267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130502496471315358856293511 195753744706973038284440267)
        ·
          refine ⟨293630617060459557426660401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195753744706973038284440267 293630617060459557426660401)
          ·
            refine ⟨220222962795344668069995301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293630617060459557426660401 220222962795344668069995301)
            ·
              refine ⟨41291805524127125263124119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 220222962795344668069995301 41291805524127125263124119)
              ·
                refine ⟨61937708286190687894686179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41291805524127125263124119 61937708286190687894686179)
                ·
                  refine ⟨92906562429286031842029269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61937708286190687894686179 92906562429286031842029269)
                  ·
                    refine ⟨2177497556936391371297561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 92906562429286031842029269 2177497556936391371297561)
                    ·
                      refine ⟨1633123167702293528473171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2177497556936391371297561 1633123167702293528473171)
                      ·
                        rfl

theorem cell23_3180496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 1, 7, 2].length) (baseStart_3180496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180496 prefixEnd_3180496 := by exact prefixLift 3180496
  have htrace : WordTrace (prefixWord ++ tailWord_3180496) baseStart_3180496 baseEnd_3180496 := by
    simpa [prefixWord, tailWord_3180496, baseEnd_3180496] using wordTrace_append hprefix tailTrace_3180496
  have hstable : (prefixWord ++ tailWord_3180496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180496).length < 2 ^ (prefixWord ++ tailWord_3180496).sum := by decide
  have hdescent : baseEnd_3180496 < baseStart_3180496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180536 : List Nat := [2, 1, 2, 1, 1, 3, 2, 2, 5, 4]
def baseStart_3180536 : Nat := 118140960795 + 3180536 * 2 ^ 59
def prefixEnd_3180536 : Nat := 4983230072969 + 3 ^ 40 * 3180536 * 2
def baseEnd_3180536 : Nat := 544381235642824457324329

theorem tailTrace_3180536 : CollatzResearch.WordTrace tailWord_3180536 prefixEnd_3180536 544381235642824457324329 := by
  unfold tailWord_3180536
  simp only [CollatzResearch.WordTrace]
  refine ⟨58001839002734369574080731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77335785336979159432107641 58001839002734369574080731)
  ·
    refine ⟨87002758504101554361121097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58001839002734369574080731 87002758504101554361121097)
    ·
      refine ⟨65252068878076165770840823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87002758504101554361121097 65252068878076165770840823)
      ·
        refine ⟨97878103317114248656261235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65252068878076165770840823 97878103317114248656261235)
        ·
          refine ⟨146817154975671372984391853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97878103317114248656261235 146817154975671372984391853)
          ·
            refine ⟨55056433115876764869146945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146817154975671372984391853 55056433115876764869146945)
            ·
              refine ⟨41292324836907573651860209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55056433115876764869146945 41292324836907573651860209)
              ·
                refine ⟨30969243627680680238895157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41292324836907573651860209 30969243627680680238895157)
                ·
                  refine ⟨2903366590095063772396421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30969243627680680238895157 2903366590095063772396421)
                  ·
                    refine ⟨544381235642824457324329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2903366590095063772396421 544381235642824457324329)
                    ·
                      rfl

theorem cell23_3180536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 5, 4].length) (baseStart_3180536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180536 prefixEnd_3180536 := by exact prefixLift 3180536
  have htrace : WordTrace (prefixWord ++ tailWord_3180536) baseStart_3180536 baseEnd_3180536 := by
    simpa [prefixWord, tailWord_3180536, baseEnd_3180536] using wordTrace_append hprefix tailTrace_3180536
  have hstable : (prefixWord ++ tailWord_3180536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180536).length < 2 ^ (prefixWord ++ tailWord_3180536).sum := by decide
  have hdescent : baseEnd_3180536 < baseStart_3180536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180539 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 6]
def baseStart_3180539 : Nat := 118140960795 + 3180539 * 2 ^ 59
def prefixEnd_3180539 : Nat := 4983230072969 + 3 ^ 40 * 3180539 * 2
def baseEnd_3180539 : Nat := 1633145247370436860235473

theorem tailTrace_3180539 : CollatzResearch.WordTrace tailWord_3180539 prefixEnd_3180539 1633145247370436860235473 := by
  unfold tailWord_3180539
  simp only [CollatzResearch.WordTrace]
  refine ⟨116003787424457870660520671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77335858282971913773680447 116003787424457870660520671)
  ·
    refine ⟨174005681136686805990781007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116003787424457870660520671 174005681136686805990781007)
    ·
      refine ⟨261008521705030208986171511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174005681136686805990781007 261008521705030208986171511)
      ·
        refine ⟨391512782557545313479257267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261008521705030208986171511 391512782557545313479257267)
        ·
          refine ⟨587269173836317970218885901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391512782557545313479257267 587269173836317970218885901)
          ·
            refine ⟨220225940188619238832082213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 587269173836317970218885901 220225940188619238832082213)
            ·
              refine ⟨41292363785366107281015415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 220225940188619238832082213 41292363785366107281015415)
              ·
                refine ⟨61938545678049160921523123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41292363785366107281015415 61938545678049160921523123)
                ·
                  refine ⟨92907818517073741382284685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61938545678049160921523123 92907818517073741382284685)
                  ·
                    refine ⟨34840431943902653018356757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92907818517073741382284685 34840431943902653018356757)
                    ·
                      refine ⟨1633145247370436860235473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34840431943902653018356757 1633145247370436860235473)
                      ·
                        rfl

theorem cell23_3180539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 6].length) (baseStart_3180539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180539 prefixEnd_3180539 := by exact prefixLift 3180539
  have htrace : WordTrace (prefixWord ++ tailWord_3180539) baseStart_3180539 baseEnd_3180539 := by
    simpa [prefixWord, tailWord_3180539, baseEnd_3180539] using wordTrace_append hprefix tailTrace_3180539
  have hstable : (prefixWord ++ tailWord_3180539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180539).length < 2 ^ (prefixWord ++ tailWord_3180539).sum := by decide
  have hdescent : baseEnd_3180539 < baseStart_3180539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180633 : List Nat := [1, 2, 1, 2, 2, 1, 4, 4, 1, 1, 4]
def baseStart_3180633 : Nat := 118140960795 + 3180633 * 2 ^ 59
def prefixEnd_3180633 : Nat := 4983230072969 + 3 ^ 40 * 3180633 * 2
def baseEnd_3180633 : Nat := 1633193514551959492460041

theorem tailTrace_3180633 : CollatzResearch.WordTrace tailWord_3180633 prefixEnd_3180633 1633193514551959492460041 := by
  unfold tailWord_3180633
  simp only [CollatzResearch.WordTrace]
  refine ⟨116007215886117324714442553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77338143924078216476295035 116007215886117324714442553)
  ·
    refine ⟨87005411914587993535831915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116007215886117324714442553 87005411914587993535831915)
    ·
      refine ⟨130508117871881990303747873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87005411914587993535831915 130508117871881990303747873)
      ·
        refine ⟨97881088403911492727810905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130508117871881990303747873 97881088403911492727810905)
        ·
          refine ⟨73410816302933619545858179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97881088403911492727810905 73410816302933619545858179)
          ·
            refine ⟨110116224454400429318787269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73410816302933619545858179 110116224454400429318787269)
            ·
              refine ⟨20646792085200080497272613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110116224454400429318787269 20646792085200080497272613)
              ·
                refine ⟨3871273515975015093238615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20646792085200080497272613 3871273515975015093238615)
                ·
                  refine ⟨5806910273962522639857923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3871273515975015093238615 5806910273962522639857923)
                  ·
                    refine ⟨8710365410943783959786885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5806910273962522639857923 8710365410943783959786885)
                    ·
                      refine ⟨1633193514551959492460041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8710365410943783959786885 1633193514551959492460041)
                      ·
                        rfl

theorem cell23_3180633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 1, 4].length) (baseStart_3180633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180633 prefixEnd_3180633 := by exact prefixLift 3180633
  have htrace : WordTrace (prefixWord ++ tailWord_3180633) baseStart_3180633 baseEnd_3180633 := by
    simpa [prefixWord, tailWord_3180633, baseEnd_3180633] using wordTrace_append hprefix tailTrace_3180633
  have hstable : (prefixWord ++ tailWord_3180633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180633).length < 2 ^ (prefixWord ++ tailWord_3180633).sum := by decide
  have hdescent : baseEnd_3180633 < baseStart_3180633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180637 : List Nat := [1, 4, 4, 1, 1, 2, 1, 1, 1, 5, 2]
def baseStart_3180637 : Nat := 118140960795 + 3180637 * 2 ^ 59
def prefixEnd_3180637 : Nat := 4983230072969 + 3 ^ 40 * 3180637 * 2
def baseEnd_3180637 : Nat := 1633195568474577476810023

theorem tailTrace_3180637 : CollatzResearch.WordTrace tailWord_3180637 prefixEnd_3180637 1633195568474577476810023 := by
  unfold tailWord_3180637
  simp only [CollatzResearch.WordTrace]
  refine ⟨116007361778102833397588165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77338241185401888931725443 116007361778102833397588165)
  ·
    refine ⟨21751380333394281262047781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116007361778102833397588165 21751380333394281262047781)
    ·
      refine ⟨4078383812511427736633959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21751380333394281262047781 4078383812511427736633959)
      ·
        refine ⟨6117575718767141604950939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4078383812511427736633959 6117575718767141604950939)
        ·
          refine ⟨9176363578150712407426409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6117575718767141604950939 9176363578150712407426409)
          ·
            refine ⟨6882272683613034305569807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9176363578150712407426409 6882272683613034305569807)
            ·
              refine ⟨10323409025419551458354711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6882272683613034305569807 10323409025419551458354711)
              ·
                refine ⟨15485113538129327187532067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10323409025419551458354711 15485113538129327187532067)
                ·
                  refine ⟨23227670307193990781298101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15485113538129327187532067 23227670307193990781298101)
                  ·
                    refine ⟨2177594091299436635746697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23227670307193990781298101 2177594091299436635746697)
                    ·
                      refine ⟨1633195568474577476810023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2177594091299436635746697 1633195568474577476810023)
                      ·
                        rfl

theorem cell23_3180637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_3180637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180637 prefixEnd_3180637 := by exact prefixLift 3180637
  have htrace : WordTrace (prefixWord ++ tailWord_3180637) baseStart_3180637 baseEnd_3180637 := by
    simpa [prefixWord, tailWord_3180637, baseEnd_3180637] using wordTrace_append hprefix tailTrace_3180637
  have hstable : (prefixWord ++ tailWord_3180637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180637).length < 2 ^ (prefixWord ++ tailWord_3180637).sum := by decide
  have hdescent : baseEnd_3180637 < baseStart_3180637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180653 : List Nat := [1, 5, 1, 1, 2, 1, 2, 3, 1, 1, 5]
def baseStart_3180653 : Nat := 118140960795 + 3180653 * 2 ^ 59
def prefixEnd_3180653 : Nat := 4983230072969 + 3 ^ 40 * 3180653 * 2
def baseEnd_3180653 : Nat := 1633203784165049414209949

theorem tailTrace_3180653 : CollatzResearch.WordTrace tailWord_3180653 prefixEnd_3180653 1633203784165049414209949 := by
  unfold tailWord_3180653
  simp only [CollatzResearch.WordTrace]
  refine ⟨116007945346044868130170613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77338630230696578753447075 116007945346044868130170613)
  ·
    refine ⟨10875744876191706387203495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116007945346044868130170613 10875744876191706387203495)
    ·
      refine ⟨16313617314287559580805243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10875744876191706387203495 16313617314287559580805243)
      ·
        refine ⟨24470425971431339371207865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16313617314287559580805243 24470425971431339371207865)
        ·
          refine ⟨18352819478573504528405899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24470425971431339371207865 18352819478573504528405899)
          ·
            refine ⟨27529229217860256792608849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18352819478573504528405899 27529229217860256792608849)
            ·
              refine ⟨20646921913395192594456637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27529229217860256792608849 20646921913395192594456637)
              ·
                refine ⟨7742595717523197222921239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20646921913395192594456637 7742595717523197222921239)
                ·
                  refine ⟨11613893576284795834381859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7742595717523197222921239 11613893576284795834381859)
                  ·
                    refine ⟨17420840364427193751572789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11613893576284795834381859 17420840364427193751572789)
                    ·
                      refine ⟨1633203784165049414209949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17420840364427193751572789 1633203784165049414209949)
                      ·
                        rfl

theorem cell23_3180653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_3180653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180653 prefixEnd_3180653 := by exact prefixLift 3180653
  have htrace : WordTrace (prefixWord ++ tailWord_3180653) baseStart_3180653 baseEnd_3180653 := by
    simpa [prefixWord, tailWord_3180653, baseEnd_3180653] using wordTrace_append hprefix tailTrace_3180653
  have hstable : (prefixWord ++ tailWord_3180653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180653).length < 2 ^ (prefixWord ++ tailWord_3180653).sum := by decide
  have hdescent : baseEnd_3180653 < baseStart_3180653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180656 : List Nat := [2, 1, 1, 1, 5, 3, 10]
def baseStart_3180656 : Nat := 118140960795 + 3180656 * 2 ^ 59
def prefixEnd_3180656 : Nat := 4983230072969 + 3 ^ 40 * 3180656 * 2
def baseEnd_3180656 : Nat := 20163028698852011141635

theorem tailTrace_3180656 : CollatzResearch.WordTrace tailWord_3180656 prefixEnd_3180656 20163028698852011141635 := by
  unfold tailWord_3180656
  simp only [CollatzResearch.WordTrace]
  refine ⟨58004027382516999821264911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77338703176689333095019881 58004027382516999821264911)
  ·
    refine ⟨87006041073775499731897367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58004027382516999821264911 87006041073775499731897367)
    ·
      refine ⟨130509061610663249597846051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87006041073775499731897367 130509061610663249597846051)
      ·
        refine ⟨195763592415994874396769077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130509061610663249597846051 195763592415994874396769077)
        ·
          refine ⟨18352836788999519474697101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 195763592415994874396769077 18352836788999519474697101)
          ·
            refine ⟨6882313795874819803011413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18352836788999519474697101 6882313795874819803011413)
            ·
              refine ⟨20163028698852011141635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6882313795874819803011413 20163028698852011141635)
              ·
                rfl

theorem cell23_3180656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 10].length) (baseStart_3180656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180656 prefixEnd_3180656 := by exact prefixLift 3180656
  have htrace : WordTrace (prefixWord ++ tailWord_3180656) baseStart_3180656 baseEnd_3180656 := by
    simpa [prefixWord, tailWord_3180656, baseEnd_3180656] using wordTrace_append hprefix tailTrace_3180656
  have hstable : (prefixWord ++ tailWord_3180656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180656).length < 2 ^ (prefixWord ++ tailWord_3180656).sum := by decide
  have hdescent : baseEnd_3180656 < baseStart_3180656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180677 : List Nat := [1, 3, 1, 1, 5, 2, 3, 1, 2, 4]
def baseStart_3180677 : Nat := 118140960795 + 3180677 * 2 ^ 59
def prefixEnd_3180677 : Nat := 4983230072969 + 3 ^ 40 * 3180677 * 2
def baseEnd_3180677 : Nat := 544405369233585773436613

theorem tailTrace_3180677 : CollatzResearch.WordTrace tailWord_3180677 prefixEnd_3180677 544405369233585773436613 := by
  unfold tailWord_3180677
  simp only [CollatzResearch.WordTrace]
  refine ⟨116008820697957920229044285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77339213798638613486029523 116008820697957920229044285)
  ·
    refine ⟨43503307761734220085891607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116008820697957920229044285 43503307761734220085891607)
    ·
      refine ⟨65254961642601330128837411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43503307761734220085891607 65254961642601330128837411)
      ·
        refine ⟨97882442463901995193256117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65254961642601330128837411 97882442463901995193256117)
        ·
          refine ⟨9176478980990812049367761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97882442463901995193256117 9176478980990812049367761)
          ·
            refine ⟨6882359235743109037025821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9176478980990812049367761 6882359235743109037025821)
            ·
              refine ⟨2580884713403665888884683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6882359235743109037025821 2580884713403665888884683)
              ·
                refine ⟨3871327070105498833327025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2580884713403665888884683 3871327070105498833327025)
                ·
                  refine ⟨2903495302579124124995269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3871327070105498833327025 2903495302579124124995269)
                  ·
                    refine ⟨544405369233585773436613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2903495302579124124995269 544405369233585773436613)
                    ·
                      rfl

theorem cell23_3180677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 2, 4].length) (baseStart_3180677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180677 prefixEnd_3180677 := by exact prefixLift 3180677
  have htrace : WordTrace (prefixWord ++ tailWord_3180677) baseStart_3180677 baseEnd_3180677 := by
    simpa [prefixWord, tailWord_3180677, baseEnd_3180677] using wordTrace_append hprefix tailTrace_3180677
  have hstable : (prefixWord ++ tailWord_3180677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180677).length < 2 ^ (prefixWord ++ tailWord_3180677).sum := by decide
  have hdescent : baseEnd_3180677 < baseStart_3180677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180680 : List Nat := [2, 1, 3, 4, 1, 1, 3, 1, 1, 2, 4]
def baseStart_3180680 : Nat := 118140960795 + 3180680 * 2 ^ 59
def prefixEnd_3180680 : Nat := 4983230072969 + 3 ^ 40 * 3180680 * 2
def baseEnd_3180680 : Nat := 1633217648142720808572325

theorem tailTrace_3180680 : CollatzResearch.WordTrace tailWord_3180680 prefixEnd_3180680 1633217648142720808572325 := by
  unfold tailWord_3180680
  simp only [CollatzResearch.WordTrace]
  refine ⟨58004465058473525870701747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77339286744631367827602329 58004465058473525870701747)
  ·
    refine ⟨87006697587710288806052621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58004465058473525870701747 87006697587710288806052621)
    ·
      refine ⟨32627511595391358302269733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87006697587710288806052621 32627511595391358302269733)
      ·
        refine ⟨6117658424135879681675575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32627511595391358302269733 6117658424135879681675575)
        ·
          refine ⟨9176487636203819522513363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6117658424135879681675575 9176487636203819522513363)
          ·
            refine ⟨13764731454305729283770045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9176487636203819522513363 13764731454305729283770045)
            ·
              refine ⟨5161774295364648481413767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13764731454305729283770045 5161774295364648481413767)
              ·
                refine ⟨7742661443046972722120651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5161774295364648481413767 7742661443046972722120651)
                ·
                  refine ⟨11613992164570459083180977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7742661443046972722120651 11613992164570459083180977)
                  ·
                    refine ⟨8710494123427844312385733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11613992164570459083180977 8710494123427844312385733)
                    ·
                      refine ⟨1633217648142720808572325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8710494123427844312385733 1633217648142720808572325)
                      ·
                        rfl

theorem cell23_3180680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_3180680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180680 prefixEnd_3180680 := by exact prefixLift 3180680
  have htrace : WordTrace (prefixWord ++ tailWord_3180680) baseStart_3180680 baseEnd_3180680 := by
    simpa [prefixWord, tailWord_3180680, baseEnd_3180680] using wordTrace_append hprefix tailTrace_3180680
  have hstable : (prefixWord ++ tailWord_3180680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180680).length < 2 ^ (prefixWord ++ tailWord_3180680).sum := by decide
  have hdescent : baseEnd_3180680 < baseStart_3180680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180700 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 6, 1, 3]
def baseStart_3180700 : Nat := 118140960795 + 3180700 * 2 ^ 59
def prefixEnd_3180700 : Nat := 4983230072969 + 3 ^ 40 * 3180700 * 2
def baseEnd_3180700 : Nat := 1633227917755810730322233

theorem tailTrace_3180700 : CollatzResearch.WordTrace tailWord_3180700 prefixEnd_3180700 1633227917755810730322233 := by
  unfold tailWord_3180700
  simp only [CollatzResearch.WordTrace]
  refine ⟨58004829788437297578565777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77339773051249730104754369 58004829788437297578565777)
  ·
    refine ⟨43503622341327973183924333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58004829788437297578565777 43503622341327973183924333)
    ·
      refine ⟨16313858377997989943971625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43503622341327973183924333 16313858377997989943971625)
      ·
        refine ⟨12235393783498492457978719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16313858377997989943971625 12235393783498492457978719)
        ·
          refine ⟨18353090675247738686968079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12235393783498492457978719 18353090675247738686968079)
          ·
            refine ⟨27529636012871608030452119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18353090675247738686968079 27529636012871608030452119)
            ·
              refine ⟨41294454019307412045678179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27529636012871608030452119 41294454019307412045678179)
              ·
                refine ⟨61941681028961118068517269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41294454019307412045678179 61941681028961118068517269)
                ·
                  refine ⟨2903516298232552409461747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 61941681028961118068517269 2903516298232552409461747)
                  ·
                    refine ⟨4355274447348828614192621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2903516298232552409461747 4355274447348828614192621)
                    ·
                      refine ⟨1633227917755810730322233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4355274447348828614192621 1633227917755810730322233)
                      ·
                        rfl

theorem cell23_3180700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_3180700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180700 prefixEnd_3180700 := by exact prefixLift 3180700
  have htrace : WordTrace (prefixWord ++ tailWord_3180700) baseStart_3180700 baseEnd_3180700 := by
    simpa [prefixWord, tailWord_3180700, baseEnd_3180700] using wordTrace_append hprefix tailTrace_3180700
  have hstable : (prefixWord ++ tailWord_3180700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180700).length < 2 ^ (prefixWord ++ tailWord_3180700).sum := by decide
  have hdescent : baseEnd_3180700 < baseStart_3180700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180701 : List Nat := [1, 4, 2, 1, 1, 5, 1, 3, 1, 2, 2]
def baseStart_3180701 : Nat := 118140960795 + 3180701 * 2 ^ 59
def prefixEnd_3180701 : Nat := 4983230072969 + 3 ^ 40 * 3180701 * 2
def baseEnd_3180701 : Nat := 1633228431236465226409729

theorem tailTrace_3180701 : CollatzResearch.WordTrace tailWord_3180701 prefixEnd_3180701 1633228431236465226409729 := by
  unfold tailWord_3180701
  simp only [CollatzResearch.WordTrace]
  refine ⟨116009696049870972327917957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77339797366580648218611971 116009696049870972327917957)
  ·
    refine ⟨21751818009350807311484617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116009696049870972327917957 21751818009350807311484617)
    ·
      refine ⟨16313863507013105483613463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21751818009350807311484617 16313863507013105483613463)
      ·
        refine ⟨24470795260519658225420195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16313863507013105483613463 24470795260519658225420195)
        ·
          refine ⟨36706192890779487338130293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24470795260519658225420195 36706192890779487338130293)
          ·
            refine ⟨3441205583510576937949715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36706192890779487338130293 3441205583510576937949715)
            ·
              refine ⟨5161808375265865406924573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3441205583510576937949715 5161808375265865406924573)
              ·
                refine ⟨1935678140724699527596715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5161808375265865406924573 1935678140724699527596715)
                ·
                  refine ⟨2903517211087049291395073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1935678140724699527596715 2903517211087049291395073)
                  ·
                    refine ⟨2177637908315286968546305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2903517211087049291395073 2177637908315286968546305)
                    ·
                      refine ⟨1633228431236465226409729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2177637908315286968546305 1633228431236465226409729)
                      ·
                        rfl

theorem cell23_3180701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 3, 1, 2, 2].length) (baseStart_3180701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180701 prefixEnd_3180701 := by exact prefixLift 3180701
  have htrace : WordTrace (prefixWord ++ tailWord_3180701) baseStart_3180701 baseEnd_3180701 := by
    simpa [prefixWord, tailWord_3180701, baseEnd_3180701] using wordTrace_append hprefix tailTrace_3180701
  have hstable : (prefixWord ++ tailWord_3180701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180701).length < 2 ^ (prefixWord ++ tailWord_3180701).sum := by decide
  have hdescent : baseEnd_3180701 < baseStart_3180701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180717 : List Nat := [1, 5, 2, 1, 2, 1, 2, 1, 4, 1, 3]
def baseStart_3180717 : Nat := 118140960795 + 3180717 * 2 ^ 59
def prefixEnd_3180717 : Nat := 4983230072969 + 3 ^ 40 * 3180717 * 2
def baseEnd_3180717 : Nat := 1633236646926937163809655

theorem tailTrace_3180717 : CollatzResearch.WordTrace tailWord_3180717 prefixEnd_3180717 1633236646926937163809655 := by
  unfold tailWord_3180717
  simp only [CollatzResearch.WordTrace]
  refine ⟨116010279617813007060500405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77340186411875338040333603 116010279617813007060500405)
  ·
    refine ⟨10875963714169969411921913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116010279617813007060500405 10875963714169969411921913)
    ·
      refine ⟨8156972785627477058941435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10875963714169969411921913 8156972785627477058941435)
      ·
        refine ⟨12235459178441215588412153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8156972785627477058941435 12235459178441215588412153)
        ·
          refine ⟨9176594383830911691309115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12235459178441215588412153 9176594383830911691309115)
          ·
            refine ⟨13764891575746367536963673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9176594383830911691309115 13764891575746367536963673)
            ·
              refine ⟨10323668681809775652722755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13764891575746367536963673 10323668681809775652722755)
              ·
                refine ⟨15485503022714663479084133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10323668681809775652722755 15485503022714663479084133)
                ·
                  refine ⟨2903531816758999402328275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15485503022714663479084133 2903531816758999402328275)
                  ·
                    refine ⟨4355297725138499103492413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2903531816758999402328275 4355297725138499103492413)
                    ·
                      refine ⟨1633236646926937163809655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4355297725138499103492413 1633236646926937163809655)
                      ·
                        rfl

theorem cell23_3180717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_3180717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180717 prefixEnd_3180717 := by exact prefixLift 3180717
  have htrace : WordTrace (prefixWord ++ tailWord_3180717) baseStart_3180717 baseEnd_3180717 := by
    simpa [prefixWord, tailWord_3180717, baseEnd_3180717] using wordTrace_append hprefix tailTrace_3180717
  have hstable : (prefixWord ++ tailWord_3180717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180717).length < 2 ^ (prefixWord ++ tailWord_3180717).sum := by decide
  have hdescent : baseEnd_3180717 < baseStart_3180717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180718 : List Nat := [4, 1, 4, 2, 1, 2, 1, 1, 3, 2, 2]
def baseStart_3180718 : Nat := 118140960795 + 3180718 * 2 ^ 59
def prefixEnd_3180718 : Nat := 4983230072969 + 3 ^ 40 * 3180718 * 2
def baseEnd_3180718 : Nat := 1633237160407591659897151

theorem tailTrace_3180718 : CollatzResearch.WordTrace tailWord_3180718 prefixEnd_3180718 1633237160407591659897151 := by
  unfold tailWord_3180718
  simp only [CollatzResearch.WordTrace]
  refine ⟨14501289511351173028910851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77340210727206256154191205 14501289511351173028910851)
  ·
    refine ⟨21751934267026759543366277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14501289511351173028910851 21751934267026759543366277)
    ·
      refine ⟨4078487675067517414381177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21751934267026759543366277 4078487675067517414381177)
      ·
        refine ⟨3058865756300638060785883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4078487675067517414381177 3058865756300638060785883)
        ·
          refine ⟨4588298634450957091178825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3058865756300638060785883 4588298634450957091178825)
          ·
            refine ⟨3441223975838217818384119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4588298634450957091178825 3441223975838217818384119)
            ·
              refine ⟨5161835963757326727576179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3441223975838217818384119 5161835963757326727576179)
              ·
                refine ⟨7742753945635990091364269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5161835963757326727576179 7742753945635990091364269)
                ·
                  refine ⟨2903532729613496284261601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7742753945635990091364269 2903532729613496284261601)
                  ·
                    refine ⟨2177649547210122213196201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2903532729613496284261601 2177649547210122213196201)
                    ·
                      refine ⟨1633237160407591659897151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2177649547210122213196201 1633237160407591659897151)
                      ·
                        rfl

theorem cell23_3180718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_3180718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180718 prefixEnd_3180718 := by exact prefixLift 3180718
  have htrace : WordTrace (prefixWord ++ tailWord_3180718) baseStart_3180718 baseEnd_3180718 := by
    simpa [prefixWord, tailWord_3180718, baseEnd_3180718] using wordTrace_append hprefix tailTrace_3180718
  have hstable : (prefixWord ++ tailWord_3180718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180718).length < 2 ^ (prefixWord ++ tailWord_3180718).sum := by decide
  have hdescent : baseEnd_3180718 < baseStart_3180718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
