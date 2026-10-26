import V185TrunkScan23Chunk0661

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3913918 : List Nat := [4, 2, 1, 1, 4, 2, 1, 1, 2, 5]
def baseStart_3913918 : Nat := 118140960795 + 3913918 * 2 ^ 59
def prefixEnd_3913918 : Nat := 4983230072969 + 3 ^ 40 * 3913918 * 2
def baseEnd_3913918 : Nat := 669907058761374337175075

theorem tailTrace_3913918 : CollatzResearch.WordTrace tailWord_3913918 prefixEnd_3913918 669907058761374337175075 := by
  unfold tailWord_3913918
  simp only [CollatzResearch.WordTrace]
  refine ⟨17844039629318875602745801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95168211356367336547977605 17844039629318875602745801)
  ·
    refine ⟨13383029721989156702059351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17844039629318875602745801 13383029721989156702059351)
    ·
      refine ⟨20074544582983735053089027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13383029721989156702059351 20074544582983735053089027)
      ·
        refine ⟨30111816874475602579633541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20074544582983735053089027 30111816874475602579633541)
        ·
          refine ⟨5645965663964175483681289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30111816874475602579633541 5645965663964175483681289)
          ·
            refine ⟨4234474247973131612760967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5645965663964175483681289 4234474247973131612760967)
            ·
              refine ⟨6351711371959697419141451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4234474247973131612760967 6351711371959697419141451)
              ·
                refine ⟨9527567057939546128712177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6351711371959697419141451 9527567057939546128712177)
                ·
                  refine ⟨7145675293454659596534133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9527567057939546128712177 7145675293454659596534133)
                  ·
                    refine ⟨669907058761374337175075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7145675293454659596534133 669907058761374337175075)
                    ·
                      rfl

theorem cell23_3913918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_3913918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913918 prefixEnd_3913918 := by exact prefixLift 3913918
  have htrace : WordTrace (prefixWord ++ tailWord_3913918) baseStart_3913918 baseEnd_3913918 := by
    simpa [prefixWord, tailWord_3913918, baseEnd_3913918] using wordTrace_append hprefix tailTrace_3913918
  have hstable : (prefixWord ++ tailWord_3913918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913918).length < 2 ^ (prefixWord ++ tailWord_3913918).sum := by decide
  have hdescent : baseEnd_3913918 < baseStart_3913918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913934 : List Nat := [4, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6]
def baseStart_3913934 : Nat := 118140960795 + 3913934 * 2 ^ 59
def prefixEnd_3913934 : Nat := 4983230072969 + 3 ^ 40 * 3913934 * 2
def baseEnd_3913934 : Nat := 2009729391974594948925151

theorem tailTrace_3913934 : CollatzResearch.WordTrace tailWord_3913934 prefixEnd_3913934 2009729391974594948925151 := by
  unfold tailWord_3913934
  simp only [CollatzResearch.WordTrace]
  refine ⟨17844112575311629944318607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95168600401662026369699237 17844112575311629944318607)
  ·
    refine ⟨26766168862967444916477911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17844112575311629944318607 26766168862967444916477911)
    ·
      refine ⟨40149253294451167374716867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26766168862967444916477911 40149253294451167374716867)
      ·
        refine ⟨60223879941676751062075301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40149253294451167374716867 60223879941676751062075301)
        ·
          refine ⟨11291977489064390824139119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60223879941676751062075301 11291977489064390824139119)
          ·
            refine ⟨16937966233596586236208679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11291977489064390824139119 16937966233596586236208679)
            ·
              refine ⟨25406949350394879354313019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16937966233596586236208679 25406949350394879354313019)
              ·
                refine ⟨38110424025592319031469529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25406949350394879354313019 38110424025592319031469529)
                ·
                  refine ⟨28582818019194239273602147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38110424025592319031469529 28582818019194239273602147)
                  ·
                    refine ⟨42874227028791358910403221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28582818019194239273602147 42874227028791358910403221)
                    ·
                      refine ⟨2009729391974594948925151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42874227028791358910403221 2009729391974594948925151)
                      ·
                        rfl

theorem cell23_3913934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_3913934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913934 prefixEnd_3913934 := by exact prefixLift 3913934
  have htrace : WordTrace (prefixWord ++ tailWord_3913934) baseStart_3913934 baseEnd_3913934 := by
    simpa [prefixWord, tailWord_3913934, baseEnd_3913934] using wordTrace_append hprefix tailTrace_3913934
  have hstable : (prefixWord ++ tailWord_3913934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913934).length < 2 ^ (prefixWord ++ tailWord_3913934).sum := by decide
  have hdescent : baseEnd_3913934 < baseStart_3913934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913944 : List Nat := [2, 1, 2, 2, 4, 2, 1, 1, 8]
def baseStart_3913944 : Nat := 118140960795 + 3913944 * 2 ^ 59
def prefixEnd_3913944 : Nat := 4983230072969 + 3 ^ 40 * 3913944 * 2
def baseEnd_3913944 : Nat := 223303836309015545533345

theorem tailTrace_3913944 : CollatzResearch.WordTrace tailWord_3913944 prefixEnd_3913944 223303836309015545533345 := by
  unfold tailWord_3913944
  simp only [CollatzResearch.WordTrace]
  refine ⟨71376632666228405631206443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95168843554971207508275257 71376632666228405631206443)
  ·
    refine ⟨107064948999342608446809665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71376632666228405631206443 107064948999342608446809665)
    ·
      refine ⟨80298711749506956335107249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107064948999342608446809665 80298711749506956335107249)
      ·
        refine ⟨60224033812130217251330437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80298711749506956335107249 60224033812130217251330437)
        ·
          refine ⟨11292006339774415734624457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60224033812130217251330437 11292006339774415734624457)
          ·
            refine ⟨8469004754830811800968343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11292006339774415734624457 8469004754830811800968343)
            ·
              refine ⟨12703507132246217701452515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8469004754830811800968343 12703507132246217701452515)
              ·
                refine ⟨19055260698369326552178773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12703507132246217701452515 19055260698369326552178773)
                ·
                  refine ⟨223303836309015545533345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19055260698369326552178773 223303836309015545533345)
                  ·
                    rfl

theorem cell23_3913944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 8].length) (baseStart_3913944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913944 prefixEnd_3913944 := by exact prefixLift 3913944
  have htrace : WordTrace (prefixWord ++ tailWord_3913944) baseStart_3913944 baseEnd_3913944 := by
    simpa [prefixWord, tailWord_3913944, baseEnd_3913944] using wordTrace_append hprefix tailTrace_3913944
  have hstable : (prefixWord ++ tailWord_3913944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913944).length < 2 ^ (prefixWord ++ tailWord_3913944).sum := by decide
  have hdescent : baseEnd_3913944 < baseStart_3913944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913947 : List Nat := [1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 6]
def baseStart_3913947 : Nat := 118140960795 + 3913947 * 2 ^ 59
def prefixEnd_3913947 : Nat := 4983230072969 + 3 ^ 40 * 3913947 * 2
def baseEnd_3913947 : Nat := 2009736067223103398062591

theorem tailTrace_3913947 : CollatzResearch.WordTrace tailWord_3913947 prefixEnd_3913947 2009736067223103398062591 := by
  unfold tailWord_3913947
  simp only [CollatzResearch.WordTrace]
  refine ⟨142753374751445942774772095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95168916500963961849848063 142753374751445942774772095)
  ·
    refine ⟨214130062127168914162158143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142753374751445942774772095 214130062127168914162158143)
    ·
      refine ⟨321195093190753371243237215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214130062127168914162158143 321195093190753371243237215)
      ·
        refine ⟨481792639786130056864855823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321195093190753371243237215 481792639786130056864855823)
        ·
          refine ⟨722688959679195085297283735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481792639786130056864855823 722688959679195085297283735)
          ·
            refine ⟨1084033439518792627945925603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722688959679195085297283735 1084033439518792627945925603)
            ·
              refine ⟨1626050159278188941918888405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1084033439518792627945925603 1626050159278188941918888405)
              ·
                refine ⟨38110550608082553326223947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1626050159278188941918888405 38110550608082553326223947)
                ·
                  refine ⟨57165825912123829989335921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38110550608082553326223947 57165825912123829989335921)
                  ·
                    refine ⟨42874369434092872492001941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57165825912123829989335921 42874369434092872492001941)
                    ·
                      refine ⟨2009736067223103398062591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42874369434092872492001941 2009736067223103398062591)
                      ·
                        rfl

theorem cell23_3913947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 6].length) (baseStart_3913947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913947 prefixEnd_3913947 := by exact prefixLift 3913947
  have htrace : WordTrace (prefixWord ++ tailWord_3913947) baseStart_3913947 baseEnd_3913947 := by
    simpa [prefixWord, tailWord_3913947, baseEnd_3913947] using wordTrace_append hprefix tailTrace_3913947
  have hstable : (prefixWord ++ tailWord_3913947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913947).length < 2 ^ (prefixWord ++ tailWord_3913947).sum := by decide
  have hdescent : baseEnd_3913947 < baseStart_3913947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913971 : List Nat := [1, 1, 1, 2, 2, 4, 1, 4, 3, 1, 3]
def baseStart_3913971 : Nat := 118140960795 + 3913971 * 2 ^ 59
def prefixEnd_3913971 : Nat := 4983230072969 + 3 ^ 40 * 3913971 * 2
def baseEnd_3913971 : Nat := 2009748390758811304162481

theorem tailTrace_3913971 : CollatzResearch.WordTrace tailWord_3913971 prefixEnd_3913971 2009748390758811304162481 := by
  unfold tailWord_3913971
  simp only [CollatzResearch.WordTrace]
  refine ⟨142754250103358994873645767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95169500068905996582430511 142754250103358994873645767)
  ·
    refine ⟨214131375155038492310468651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142754250103358994873645767 214131375155038492310468651)
    ·
      refine ⟨321197062732557738465702977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214131375155038492310468651 321197062732557738465702977)
      ·
        refine ⟨240897797049418303849277233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321197062732557738465702977 240897797049418303849277233)
        ·
          refine ⟨180673347787063727886957925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240897797049418303849277233 180673347787063727886957925)
          ·
            refine ⟨33876252710074448978804611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180673347787063727886957925 33876252710074448978804611)
            ·
              refine ⟨50814379065111673468206917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33876252710074448978804611 50814379065111673468206917)
              ·
                refine ⟨9527696074708438775288797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50814379065111673468206917 9527696074708438775288797)
                ·
                  refine ⟨3572886028015664540733299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9527696074708438775288797 3572886028015664540733299)
                  ·
                    refine ⟨5359329042023496811099949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3572886028015664540733299 5359329042023496811099949)
                    ·
                      refine ⟨2009748390758811304162481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5359329042023496811099949 2009748390758811304162481)
                      ·
                        rfl

theorem cell23_3913971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 3, 1, 3].length) (baseStart_3913971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913971 prefixEnd_3913971 := by exact prefixLift 3913971
  have htrace : WordTrace (prefixWord ++ tailWord_3913971) baseStart_3913971 baseEnd_3913971 := by
    simpa [prefixWord, tailWord_3913971, baseEnd_3913971] using wordTrace_append hprefix tailTrace_3913971
  have hstable : (prefixWord ++ tailWord_3913971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913971).length < 2 ^ (prefixWord ++ tailWord_3913971).sum := by decide
  have hdescent : baseEnd_3913971 < baseStart_3913971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913981 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 6, 3, 2]
def baseStart_3913981 : Nat := 118140960795 + 3913981 * 2 ^ 59
def prefixEnd_3913981 : Nat := 4983230072969 + 3 ^ 40 * 3913981 * 2
def baseEnd_3913981 : Nat := 2009753525565356265037435

theorem tailTrace_3913981 : CollatzResearch.WordTrace tailWord_3913981 prefixEnd_3913981 2009753525565356265037435 := by
  unfold tailWord_3913981
  simp only [CollatzResearch.WordTrace]
  refine ⟨142754614833322766581509797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95169743222215177721006531 142754614833322766581509797)
  ·
    refine ⟨26766490281248018734033087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142754614833322766581509797 26766490281248018734033087)
    ·
      refine ⟨40149735421872028101049631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26766490281248018734033087 40149735421872028101049631)
      ·
        refine ⟨60224603132808042151574447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40149735421872028101049631 60224603132808042151574447)
        ·
          refine ⟨90336904699212063227361671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60224603132808042151574447 90336904699212063227361671)
          ·
            refine ⟨135505357048818094841042507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90336904699212063227361671 135505357048818094841042507)
            ·
              refine ⟨203258035573227142261563761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135505357048818094841042507 203258035573227142261563761)
              ·
                refine ⟨152443526679920356696172821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203258035573227142261563761 152443526679920356696172821)
                ·
                  refine ⟨7145790313121266720133101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 152443526679920356696172821 7145790313121266720133101)
                  ·
                    refine ⟨2679671367420475020049913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7145790313121266720133101 2679671367420475020049913)
                    ·
                      refine ⟨2009753525565356265037435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2679671367420475020049913 2009753525565356265037435)
                      ·
                        rfl

theorem cell23_3913981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 3, 2].length) (baseStart_3913981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913981 prefixEnd_3913981 := by exact prefixLift 3913981
  have htrace : WordTrace (prefixWord ++ tailWord_3913981) baseStart_3913981 baseEnd_3913981 := by
    simpa [prefixWord, tailWord_3913981, baseEnd_3913981] using wordTrace_append hprefix tailTrace_3913981
  have hstable : (prefixWord ++ tailWord_3913981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913981).length < 2 ^ (prefixWord ++ tailWord_3913981).sum := by decide
  have hdescent : baseEnd_3913981 < baseStart_3913981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913998 : List Nat := [4, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2]
def baseStart_3913998 : Nat := 118140960795 + 3913998 * 2 ^ 59
def prefixEnd_3913998 : Nat := 4983230072969 + 3 ^ 40 * 3913998 * 2
def baseEnd_3913998 : Nat := 2009762254736482698524857

theorem tailTrace_3913998 : CollatzResearch.WordTrace tailWord_3913998 prefixEnd_3913998 2009762254736482698524857 := by
  unfold tailWord_3913998
  simp only [CollatzResearch.WordTrace]
  refine ⟨17844404359282647310609831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95170156582840785656585765 17844404359282647310609831)
  ·
    refine ⟨26766606538923970965914747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17844404359282647310609831 26766606538923970965914747)
    ·
      refine ⟨40149909808385956448872121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26766606538923970965914747 40149909808385956448872121)
      ·
        refine ⟨30112432356289467336654091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40149909808385956448872121 30112432356289467336654091)
        ·
          refine ⟨45168648534434201004981137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30112432356289467336654091 45168648534434201004981137)
          ·
            refine ⟨33876486400825650753735853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45168648534434201004981137 33876486400825650753735853)
            ·
              refine ⟨12703682400309619032650945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33876486400825650753735853 12703682400309619032650945)
              ·
                refine ⟨9527761800232214274488209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12703682400309619032650945 9527761800232214274488209)
                ·
                  refine ⟨7145821350174160705866157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9527761800232214274488209 7145821350174160705866157)
                  ·
                    refine ⟨2679683006315310264699809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7145821350174160705866157 2679683006315310264699809)
                    ·
                      refine ⟨2009762254736482698524857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2679683006315310264699809 2009762254736482698524857)
                      ·
                        rfl

theorem cell23_3913998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_3913998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913998 prefixEnd_3913998 := by exact prefixLift 3913998
  have htrace : WordTrace (prefixWord ++ tailWord_3913998) baseStart_3913998 baseEnd_3913998 := by
    simpa [prefixWord, tailWord_3913998, baseEnd_3913998] using wordTrace_append hprefix tailTrace_3913998
  have hstable : (prefixWord ++ tailWord_3913998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913998).length < 2 ^ (prefixWord ++ tailWord_3913998).sum := by decide
  have hdescent : baseEnd_3913998 < baseStart_3913998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914028 : List Nat := [2, 2, 1, 1, 1, 3, 2, 4, 3, 2, 2]
def baseStart_3914028 : Nat := 118140960795 + 3914028 * 2 ^ 59
def prefixEnd_3914028 : Nat := 4983230072969 + 3 ^ 40 * 3914028 * 2
def baseEnd_3914028 : Nat := 2009777659156117581149719

theorem tailTrace_3914028 : CollatzResearch.WordTrace tailWord_3914028 prefixEnd_3914028 2009777659156117581149719 := by
  unfold tailWord_3914028
  simp only [CollatzResearch.WordTrace]
  refine ⟨71378164532076246804235369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95170886042768329072313825 71378164532076246804235369)
  ·
    refine ⟨53533623399057185103176527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71378164532076246804235369 53533623399057185103176527)
    ·
      refine ⟨80300435098585777654764791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53533623399057185103176527 80300435098585777654764791)
      ·
        refine ⟨120450652647878666482147187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80300435098585777654764791 120450652647878666482147187)
        ·
          refine ⟨180675978971817999723220781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120450652647878666482147187 180675978971817999723220781)
          ·
            refine ⟨67753492114431749896207793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180675978971817999723220781 67753492114431749896207793)
            ·
              refine ⟨50815119085823812422155845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67753492114431749896207793 50815119085823812422155845)
              ·
                refine ⟨9527834828591964829154221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50815119085823812422155845 9527834828591964829154221)
                ·
                  refine ⟨3572938060721986810932833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9527834828591964829154221 3572938060721986810932833)
                  ·
                    refine ⟨2679703545541490108199625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3572938060721986810932833 2679703545541490108199625)
                    ·
                      refine ⟨2009777659156117581149719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2679703545541490108199625 2009777659156117581149719)
                      ·
                        rfl

theorem cell23_3914028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 2, 2].length) (baseStart_3914028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914028 prefixEnd_3914028 := by exact prefixLift 3914028
  have htrace : WordTrace (prefixWord ++ tailWord_3914028) baseStart_3914028 baseEnd_3914028 := by
    simpa [prefixWord, tailWord_3914028, baseEnd_3914028] using wordTrace_append hprefix tailTrace_3914028
  have hstable : (prefixWord ++ tailWord_3914028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914028).length < 2 ^ (prefixWord ++ tailWord_3914028).sum := by decide
  have hdescent : baseEnd_3914028 < baseStart_3914028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914041 : List Nat := [1, 2, 1, 6, 1, 1, 1, 1, 3, 2, 4]
def baseStart_3914041 : Nat := 118140960795 + 3914041 * 2 ^ 59
def prefixEnd_3914041 : Nat := 4983230072969 + 3 ^ 40 * 3914041 * 2
def baseEnd_3914041 : Nat := 2009784334404626030287159

theorem tailTrace_3914041 : CollatzResearch.WordTrace tailWord_3914041 prefixEnd_3914041 2009784334404626030287159 := by
  unfold tailWord_3914041
  simp only [CollatzResearch.WordTrace]
  refine ⟨142756803213105396828693977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95171202142070264552462651 142756803213105396828693977)
  ·
    refine ⟨107067602409829047621520483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142756803213105396828693977 107067602409829047621520483)
    ·
      refine ⟨160601403614743571432280725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107067602409829047621520483 160601403614743571432280725)
      ·
        refine ⟨7528190794441104910888159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 160601403614743571432280725 7528190794441104910888159)
        ·
          refine ⟨11292286191661657366332239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7528190794441104910888159 11292286191661657366332239)
          ·
            refine ⟨16938429287492486049498359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11292286191661657366332239 16938429287492486049498359)
            ·
              refine ⟨25407643931238729074247539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16938429287492486049498359 25407643931238729074247539)
              ·
                refine ⟨38111465896858093611371309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25407643931238729074247539 38111465896858093611371309)
                ·
                  refine ⟨14291799711321785104264241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38111465896858093611371309 14291799711321785104264241)
                  ·
                    refine ⟨10718849783491338828198181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14291799711321785104264241 10718849783491338828198181)
                    ·
                      refine ⟨2009784334404626030287159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10718849783491338828198181 2009784334404626030287159)
                      ·
                        rfl

theorem cell23_3914041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_3914041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914041 prefixEnd_3914041 := by exact prefixLift 3914041
  have htrace : WordTrace (prefixWord ++ tailWord_3914041) baseStart_3914041 baseEnd_3914041 := by
    simpa [prefixWord, tailWord_3914041, baseEnd_3914041] using wordTrace_append hprefix tailTrace_3914041
  have hstable : (prefixWord ++ tailWord_3914041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914041).length < 2 ^ (prefixWord ++ tailWord_3914041).sum := by decide
  have hdescent : baseEnd_3914041 < baseStart_3914041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914064 : List Nat := [2, 1, 1, 1, 1, 6, 1, 1, 2, 7]
def baseStart_3914064 : Nat := 118140960795 + 3914064 * 2 ^ 59
def prefixEnd_3914064 : Nat := 4983230072969 + 3 ^ 40 * 3914064 * 2
def baseEnd_3914064 : Nat := 669932048153226480099851

theorem tailTrace_3914064 : CollatzResearch.WordTrace tailWord_3914064 prefixEnd_3914064 669932048153226480099851 := by
  unfold tailWord_3914064
  simp only [CollatzResearch.WordTrace]
  refine ⟨71378821046011035878390623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95171761394681381171187497 71378821046011035878390623)
  ·
    refine ⟨107068231569016553817585935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71378821046011035878390623 107068231569016553817585935)
    ·
      refine ⟨160602347353524830726378903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107068231569016553817585935 160602347353524830726378903)
      ·
        refine ⟨240903521030287246089568355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160602347353524830726378903 240903521030287246089568355)
        ·
          refine ⟨361355281545430869134352533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240903521030287246089568355 361355281545430869134352533)
          ·
            refine ⟨16938528822442071990672775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 361355281545430869134352533 16938528822442071990672775)
            ·
              refine ⟨25407793233663107986009163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16938528822442071990672775 25407793233663107986009163)
              ·
                refine ⟨38111689850494661979013745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25407793233663107986009163 38111689850494661979013745)
                ·
                  refine ⟨28583767387870996484260309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38111689850494661979013745 28583767387870996484260309)
                  ·
                    refine ⟨669932048153226480099851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28583767387870996484260309 669932048153226480099851)
                    ·
                      rfl

theorem cell23_3914064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 2, 7].length) (baseStart_3914064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914064 prefixEnd_3914064 := by exact prefixLift 3914064
  have htrace : WordTrace (prefixWord ++ tailWord_3914064) baseStart_3914064 baseEnd_3914064 := by
    simpa [prefixWord, tailWord_3914064, baseEnd_3914064] using wordTrace_append hprefix tailTrace_3914064
  have hstable : (prefixWord ++ tailWord_3914064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914064).length < 2 ^ (prefixWord ++ tailWord_3914064).sum := by decide
  have hdescent : baseEnd_3914064 < baseStart_3914064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914074 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 1, 4, 5]
def baseStart_3914074 : Nat := 118140960795 + 3914074 * 2 ^ 59
def prefixEnd_3914074 : Nat := 4983230072969 + 3 ^ 40 * 3914074 * 2
def baseEnd_3914074 : Nat := 2009801279266224401174507

theorem tailTrace_3914074 : CollatzResearch.WordTrace tailWord_3914074 prefixEnd_3914074 2009801279266224401174507 := by
  unfold tailWord_3914074
  simp only [CollatzResearch.WordTrace]
  refine ⟨35689501705496460866161319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95172004547990562309763517 35689501705496460866161319)
  ·
    refine ⟨53534252558244691299241979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35689501705496460866161319 53534252558244691299241979)
    ·
      refine ⟨80301378837367036948862969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53534252558244691299241979 80301378837367036948862969)
      ·
        refine ⟨60226034128025277711647227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80301378837367036948862969 60226034128025277711647227)
        ·
          refine ⟨90339051192037916567470841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60226034128025277711647227 90339051192037916567470841)
          ·
            refine ⟨67754288394028437425603131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90339051192037916567470841 67754288394028437425603131)
            ·
              refine ⟨101631432591042656138404697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67754288394028437425603131 101631432591042656138404697)
              ·
                refine ⟨76223574443281992103803523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101631432591042656138404697 76223574443281992103803523)
                ·
                  refine ⟨114335361664922988155705285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76223574443281992103803523 114335361664922988155705285)
                  ·
                    refine ⟨21437880312173060279194741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114335361664922988155705285 21437880312173060279194741)
                    ·
                      refine ⟨2009801279266224401174507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21437880312173060279194741 2009801279266224401174507)
                      ·
                        rfl

theorem cell23_3914074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_3914074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914074 prefixEnd_3914074 := by exact prefixLift 3914074
  have htrace : WordTrace (prefixWord ++ tailWord_3914074) baseStart_3914074 baseEnd_3914074 := by
    simpa [prefixWord, tailWord_3914074, baseEnd_3914074] using wordTrace_append hprefix tailTrace_3914074
  have hstable : (prefixWord ++ tailWord_3914074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914074).length < 2 ^ (prefixWord ++ tailWord_3914074).sum := by decide
  have hdescent : baseEnd_3914074 < baseStart_3914074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914135 : List Nat := [1, 1, 3, 3, 1, 1, 2, 5, 2, 2, 2]
def baseStart_3914135 : Nat := 118140960795 + 3914135 * 2 ^ 59
def prefixEnd_3914135 : Nat := 4983230072969 + 3 ^ 40 * 3914135 * 2
def baseEnd_3914135 : Nat := 2009832601586148662511727

theorem tailTrace_3914135 : CollatzResearch.WordTrace tailWord_3914135 prefixEnd_3914135 2009832601586148662511727 := by
  unfold tailWord_3914135
  simp only [CollatzResearch.WordTrace]
  refine ⟨142760231674764850882615859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95173487783176567255077239 142760231674764850882615859)
  ·
    refine ⟨214140347512147276323923789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142760231674764850882615859 214140347512147276323923789)
    ·
      refine ⟨80302630317055228621471421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214140347512147276323923789 80302630317055228621471421)
      ·
        refine ⟨30113486368895710733051783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80302630317055228621471421 30113486368895710733051783)
        ·
          refine ⟨45170229553343566099577675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30113486368895710733051783 45170229553343566099577675)
          ·
            refine ⟨67755344330015349149366513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45170229553343566099577675 67755344330015349149366513)
            ·
              refine ⟨50816508247511511862024885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67755344330015349149366513 50816508247511511862024885)
              ·
                refine ⟨4764047648204204237064833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50816508247511511862024885 4764047648204204237064833)
                ·
                  refine ⟨3573035736153153177798625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4764047648204204237064833 3573035736153153177798625)
                  ·
                    refine ⟨2679776802114864883348969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3573035736153153177798625 2679776802114864883348969)
                    ·
                      refine ⟨2009832601586148662511727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2679776802114864883348969 2009832601586148662511727)
                      ·
                        rfl

theorem cell23_3914135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_3914135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914135 prefixEnd_3914135 := by exact prefixLift 3914135
  have htrace : WordTrace (prefixWord ++ tailWord_3914135) baseStart_3914135 baseEnd_3914135 := by
    simpa [prefixWord, tailWord_3914135, baseEnd_3914135] using wordTrace_append hprefix tailTrace_3914135
  have hstable : (prefixWord ++ tailWord_3914135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914135).length < 2 ^ (prefixWord ++ tailWord_3914135).sum := by decide
  have hdescent : baseEnd_3914135 < baseStart_3914135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914152 : List Nat := [2, 1, 6, 1, 1, 1, 1, 2, 4, 2, 2]
def baseStart_3914152 : Nat := 118140960795 + 3914152 * 2 ^ 59
def prefixEnd_3914152 : Nat := 4983230072969 + 3 ^ 40 * 3914152 * 2
def baseEnd_3914152 : Nat := 2009841330757275095999149

theorem tailTrace_3914152 : CollatzResearch.WordTrace tailWord_3914152 prefixEnd_3914152 2009841330757275095999149 := by
  unfold tailWord_3914152
  simp only [CollatzResearch.WordTrace]
  refine ⟨71380425857851631392992355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95173901143802175190656473 71380425857851631392992355)
  ·
    refine ⟨107070638786777447089488533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71380425857851631392992355 107070638786777447089488533)
    ·
      refine ⟨5018936193130192832319775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 107070638786777447089488533 5018936193130192832319775)
      ·
        refine ⟨7528404289695289248479663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5018936193130192832319775 7528404289695289248479663)
        ·
          refine ⟨11292606434542933872719495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7528404289695289248479663 11292606434542933872719495)
          ·
            refine ⟨16938909651814400809079243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11292606434542933872719495 16938909651814400809079243)
            ·
              refine ⟨25408364477721601213618865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16938909651814400809079243 25408364477721601213618865)
              ·
                refine ⟨19056273358291200910214149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25408364477721601213618865 19056273358291200910214149)
                ·
                  refine ⟨3573051254679600170665153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19056273358291200910214149 3573051254679600170665153)
                  ·
                    refine ⟨2679788441009700127998865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3573051254679600170665153 2679788441009700127998865)
                    ·
                      refine ⟨2009841330757275095999149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2679788441009700127998865 2009841330757275095999149)
                      ·
                        rfl

theorem cell23_3914152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_3914152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914152 prefixEnd_3914152 := by exact prefixLift 3914152
  have htrace : WordTrace (prefixWord ++ tailWord_3914152) baseStart_3914152 baseEnd_3914152 := by
    simpa [prefixWord, tailWord_3914152, baseEnd_3914152] using wordTrace_append hprefix tailTrace_3914152
  have hstable : (prefixWord ++ tailWord_3914152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914152).length < 2 ^ (prefixWord ++ tailWord_3914152).sum := by decide
  have hdescent : baseEnd_3914152 < baseStart_3914152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914191 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 4]
def baseStart_3914191 : Nat := 118140960795 + 3914191 * 2 ^ 59
def prefixEnd_3914191 : Nat := 4983230072969 + 3 ^ 40 * 3914191 * 2
def baseEnd_3914191 : Nat := 2009861356502800443411469

theorem tailTrace_3914191 : CollatzResearch.WordTrace tailWord_3914191 prefixEnd_3914191 2009861356502800443411469 := by
  unfold tailWord_3914191
  simp only [CollatzResearch.WordTrace]
  refine ⟨142762274162561972446654427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95174849441707981631102951 142762274162561972446654427)
  ·
    refine ⟨214143411243842958669981641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142762274162561972446654427 214143411243842958669981641)
    ·
      refine ⟨160607558432882219002486231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214143411243842958669981641 160607558432882219002486231)
      ·
        refine ⟨240911337649323328503729347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160607558432882219002486231 240911337649323328503729347)
        ·
          refine ⟨361367006473984992755594021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240911337649323328503729347 361367006473984992755594021)
          ·
            refine ⟨67756313713872186141673879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 361367006473984992755594021 67756313713872186141673879)
            ·
              refine ⟨101634470570808279212510819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67756313713872186141673879 101634470570808279212510819)
              ·
                refine ⟨152451705856212418818766229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101634470570808279212510819 152451705856212418818766229)
                ·
                  refine ⟨7146173712009957132129667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 152451705856212418818766229 7146173712009957132129667)
                  ·
                    refine ⟨10719260568014935698194501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7146173712009957132129667 10719260568014935698194501)
                    ·
                      refine ⟨2009861356502800443411469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10719260568014935698194501 2009861356502800443411469)
                      ·
                        rfl

theorem cell23_3914191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 4].length) (baseStart_3914191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914191 prefixEnd_3914191 := by exact prefixLift 3914191
  have htrace : WordTrace (prefixWord ++ tailWord_3914191) baseStart_3914191 baseEnd_3914191 := by
    simpa [prefixWord, tailWord_3914191, baseEnd_3914191] using wordTrace_append hprefix tailTrace_3914191
  have hstable : (prefixWord ++ tailWord_3914191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914191).length < 2 ^ (prefixWord ++ tailWord_3914191).sum := by decide
  have hdescent : baseEnd_3914191 < baseStart_3914191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914198 : List Nat := [5, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7]
def baseStart_3914198 : Nat := 118140960795 + 3914198 * 2 ^ 59
def prefixEnd_3914198 : Nat := 4983230072969 + 3 ^ 40 * 3914198 * 2
def baseEnd_3914198 : Nat := 2009864950867381916023937

theorem tailTrace_3914198 : CollatzResearch.WordTrace tailWord_3914198 prefixEnd_3914198 2009864950867381916023937 := by
  unfold tailWord_3914198
  simp only [CollatzResearch.WordTrace]
  refine ⟨8922658092096038290134953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95175019649024408428106165 8922658092096038290134953)
  ·
    refine ⟨6691993569072028717601215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8922658092096038290134953 6691993569072028717601215)
    ·
      refine ⟨10037990353608043076401823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6691993569072028717601215 10037990353608043076401823)
      ·
        refine ⟨15056985530412064614602735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10037990353608043076401823 15056985530412064614602735)
        ·
          refine ⟨22585478295618096921904103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15056985530412064614602735 22585478295618096921904103)
          ·
            refine ⟨33878217443427145382856155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22585478295618096921904103 33878217443427145382856155)
            ·
              refine ⟨50817326165140718074284233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33878217443427145382856155 50817326165140718074284233)
              ·
                refine ⟨38112994623855538555713175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50817326165140718074284233 38112994623855538555713175)
                ·
                  refine ⟨57169491935783307833569763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38112994623855538555713175 57169491935783307833569763)
                  ·
                    refine ⟨85754237903674961750354645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57169491935783307833569763 85754237903674961750354645)
                    ·
                      refine ⟨2009864950867381916023937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 85754237903674961750354645 2009864950867381916023937)
                      ·
                        rfl

theorem cell23_3914198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_3914198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914198 prefixEnd_3914198 := by exact prefixLift 3914198
  have htrace : WordTrace (prefixWord ++ tailWord_3914198) baseStart_3914198 baseEnd_3914198 := by
    simpa [prefixWord, tailWord_3914198, baseEnd_3914198] using wordTrace_append hprefix tailTrace_3914198
  have hstable : (prefixWord ++ tailWord_3914198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914198).length < 2 ^ (prefixWord ++ tailWord_3914198).sum := by decide
  have hdescent : baseEnd_3914198 < baseStart_3914198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914208 : List Nat := [2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 4]
def baseStart_3914208 : Nat := 118140960795 + 3914208 * 2 ^ 59
def prefixEnd_3914208 : Nat := 4983230072969 + 3 ^ 40 * 3914208 * 2
def baseEnd_3914208 : Nat := 2009870085673926876898891

theorem tailTrace_3914208 : CollatzResearch.WordTrace tailWord_3914208 prefixEnd_3914208 2009870085673926876898891 := by
  unfold tailWord_3914208
  simp only [CollatzResearch.WordTrace]
  refine ⟨71381447101750192175011639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95175262802333589566682185 71381447101750192175011639)
  ·
    refine ⟨107072170652625288262517459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71381447101750192175011639 107072170652625288262517459)
    ·
      refine ⟨160608255978937932393776189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107072170652625288262517459 160608255978937932393776189)
      ·
        refine ⟨60228095992101724647666071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160608255978937932393776189 60228095992101724647666071)
        ·
          refine ⟨90342143988152586971499107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60228095992101724647666071 90342143988152586971499107)
          ·
            refine ⟨135513215982228880457248661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90342143988152586971499107 135513215982228880457248661)
            ·
              refine ⟨6352181999166978771433531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 135513215982228880457248661 6352181999166978771433531)
              ·
                refine ⟨9528272998750468157150297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6352181999166978771433531 9528272998750468157150297)
                ·
                  refine ⟨7146204749062851117862723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9528272998750468157150297 7146204749062851117862723)
                  ·
                    refine ⟨10719307123594276676794085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7146204749062851117862723 10719307123594276676794085)
                    ·
                      refine ⟨2009870085673926876898891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10719307123594276676794085 2009870085673926876898891)
                      ·
                        rfl

theorem cell23_3914208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 4].length) (baseStart_3914208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914208 prefixEnd_3914208 := by exact prefixLift 3914208
  have htrace : WordTrace (prefixWord ++ tailWord_3914208) baseStart_3914208 baseEnd_3914208 := by
    simpa [prefixWord, tailWord_3914208, baseEnd_3914208] using wordTrace_append hprefix tailTrace_3914208
  have hstable : (prefixWord ++ tailWord_3914208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914208).length < 2 ^ (prefixWord ++ tailWord_3914208).sum := by decide
  have hdescent : baseEnd_3914208 < baseStart_3914208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914271 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 5]
def baseStart_3914271 : Nat := 118140960795 + 3914271 * 2 ^ 59
def prefixEnd_3914271 : Nat := 4983230072969 + 3 ^ 40 * 3914271 * 2
def baseEnd_3914271 : Nat := 2009902434955160130411101

theorem tailTrace_3914271 : CollatzResearch.WordTrace tailWord_3914271 prefixEnd_3914271 2009902434955160130411101 := by
  unfold tailWord_3914271
  simp only [CollatzResearch.WordTrace]
  refine ⟨142765192002272146109566667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95176794668181430739711111 142765192002272146109566667)
  ·
    refine ⟨214147788003408219164350001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142765192002272146109566667 214147788003408219164350001)
    ·
      refine ⟨160610841002556164373262501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214147788003408219164350001 160610841002556164373262501)
      ·
        refine ⟨30114532687979280819986719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160610841002556164373262501 30114532687979280819986719)
        ·
          refine ⟨45171799031968921229980079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30114532687979280819986719 45171799031968921229980079)
          ·
            refine ⟨67757698547953381844970119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45171799031968921229980079 67757698547953381844970119)
            ·
              refine ⟨101636547821930072767455179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67757698547953381844970119 101636547821930072767455179)
              ·
                refine ⟨152454821732895109151182769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101636547821930072767455179 152454821732895109151182769)
                ·
                  refine ⟨114341116299671331863387077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152454821732895109151182769 114341116299671331863387077)
                  ·
                    refine ⟨21438959306188374724385077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114341116299671331863387077 21438959306188374724385077)
                    ·
                      refine ⟨2009902434955160130411101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21438959306188374724385077 2009902434955160130411101)
                      ·
                        rfl

theorem cell23_3914271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_3914271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914271 prefixEnd_3914271 := by exact prefixLift 3914271
  have htrace : WordTrace (prefixWord ++ tailWord_3914271) baseStart_3914271 baseEnd_3914271 := by
    simpa [prefixWord, tailWord_3914271, baseEnd_3914271] using wordTrace_append hprefix tailTrace_3914271
  have hstable : (prefixWord ++ tailWord_3914271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914271).length < 2 ^ (prefixWord ++ tailWord_3914271).sum := by decide
  have hdescent : baseEnd_3914271 < baseStart_3914271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914328 : List Nat := [2, 1, 2, 2, 1, 2, 2, 4, 1, 2, 4]
def baseStart_3914328 : Nat := 118140960795 + 3914328 * 2 ^ 59
def prefixEnd_3914328 : Nat := 4983230072969 + 3 ^ 40 * 3914328 * 2
def baseEnd_3914328 : Nat := 2009931703352466407398339

theorem tailTrace_3914328 : CollatzResearch.WordTrace tailWord_3914328 prefixEnd_3914328 2009931703352466407398339 := by
  unfold tailWord_3914328
  simp only [CollatzResearch.WordTrace]
  refine ⟨71383635481532822422195819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95178180642043763229594425 71383635481532822422195819)
  ·
    refine ⟨107075453222299233633293729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71383635481532822422195819 107075453222299233633293729)
    ·
      refine ⟨80306589916724425224970297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107075453222299233633293729 80306589916724425224970297)
      ·
        refine ⟨60229942437543318918727723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80306589916724425224970297 60229942437543318918727723)
        ·
          refine ⟨90344913656314978378091585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60229942437543318918727723 90344913656314978378091585)
          ·
            refine ⟨67758685242236233783568689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90344913656314978378091585 67758685242236233783568689)
            ·
              refine ⟨50819013931677175337676517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67758685242236233783568689 50819013931677175337676517)
              ·
                refine ⟨9528565112189470375814347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50819013931677175337676517 9528565112189470375814347)
                ·
                  refine ⟨14292847668284205563721521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9528565112189470375814347 14292847668284205563721521)
                  ·
                    refine ⟨10719635751213154172791141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14292847668284205563721521 10719635751213154172791141)
                    ·
                      refine ⟨2009931703352466407398339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10719635751213154172791141 2009931703352466407398339)
                      ·
                        rfl

theorem cell23_3914328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_3914328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914328 prefixEnd_3914328 := by exact prefixLift 3914328
  have htrace : WordTrace (prefixWord ++ tailWord_3914328) baseStart_3914328 baseEnd_3914328 := by
    simpa [prefixWord, tailWord_3914328, baseEnd_3914328] using wordTrace_append hprefix tailTrace_3914328
  have hstable : (prefixWord ++ tailWord_3914328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914328).length < 2 ^ (prefixWord ++ tailWord_3914328).sum := by decide
  have hdescent : baseEnd_3914328 < baseStart_3914328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914349 : List Nat := [1, 5, 1, 1, 3, 1, 3, 1, 3, 2, 2]
def baseStart_3914349 : Nat := 118140960795 + 3914349 * 2 ^ 59
def prefixEnd_3914349 : Nat := 4983230072969 + 3 ^ 40 * 3914349 * 2
def baseEnd_3914349 : Nat := 2009942486446210825235743

theorem tailTrace_3914349 : CollatzResearch.WordTrace tailWord_3914349 prefixEnd_3914349 2009942486446210825235743 := by
  unfold tailWord_3914349
  simp only [CollatzResearch.WordTrace]
  refine ⟨142768036895989565430906101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95178691263993043620604067 142768036895989565430906101)
  ·
    refine ⟨13384503458999021759147447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142768036895989565430906101 13384503458999021759147447)
    ·
      refine ⟨20076755188498532638721171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13384503458999021759147447 20076755188498532638721171)
      ·
        refine ⟨30115132782747798958081757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20076755188498532638721171 30115132782747798958081757)
        ·
          refine ⟨11293174793530424609280659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30115132782747798958081757 11293174793530424609280659)
          ·
            refine ⟨16939762190295636913920989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11293174793530424609280659 16939762190295636913920989)
            ·
              refine ⟨6352410821360863842720371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16939762190295636913920989 6352410821360863842720371)
              ·
                refine ⟨9528616232041295764080557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6352410821360863842720371 9528616232041295764080557)
                ·
                  refine ⟨3573231087015485911530209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9528616232041295764080557 3573231087015485911530209)
                  ·
                    refine ⟨2679923315261614433647657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3573231087015485911530209 2679923315261614433647657)
                    ·
                      refine ⟨2009942486446210825235743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2679923315261614433647657 2009942486446210825235743)
                      ·
                        rfl

theorem cell23_3914349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_3914349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914349 prefixEnd_3914349 := by exact prefixLift 3914349
  have htrace : WordTrace (prefixWord ++ tailWord_3914349) baseStart_3914349 baseEnd_3914349 := by
    simpa [prefixWord, tailWord_3914349, baseEnd_3914349] using wordTrace_append hprefix tailTrace_3914349
  have hstable : (prefixWord ++ tailWord_3914349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914349).length < 2 ^ (prefixWord ++ tailWord_3914349).sum := by decide
  have hdescent : baseEnd_3914349 < baseStart_3914349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914400 : List Nat := [2, 1, 1, 4, 5, 1, 2, 2, 1, 2, 2]
def baseStart_3914400 : Nat := 118140960795 + 3914400 * 2 ^ 59
def prefixEnd_3914400 : Nat := 4983230072969 + 3 ^ 40 * 3914400 * 2
def baseEnd_3914400 : Nat := 2009968673959590125698009

theorem tailTrace_3914400 : CollatzResearch.WordTrace tailWord_3914400 prefixEnd_3914400 2009968673959590125698009 := by
  unfold tailWord_3914400
  simp only [CollatzResearch.WordTrace]
  refine ⟨71384948509402400570506327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95179931345869867427341769 71384948509402400570506327)
  ·
    refine ⟨107077422764103600855759491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71384948509402400570506327 107077422764103600855759491)
    ·
      refine ⟨160616134146155401283639237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107077422764103600855759491 160616134146155401283639237)
      ·
        refine ⟨30115525152404137740682357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160616134146155401283639237 30115525152404137740682357)
        ·
          refine ⟨2823330483037887913188971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30115525152404137740682357 2823330483037887913188971)
          ·
            refine ⟨4234995724556831869783457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2823330483037887913188971 4234995724556831869783457)
            ·
              refine ⟨3176246793417623902337593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4234995724556831869783457 3176246793417623902337593)
              ·
                refine ⟨2382185095063217926753195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3176246793417623902337593 2382185095063217926753195)
                ·
                  refine ⟨3573277642594826890129793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2382185095063217926753195 3573277642594826890129793)
                  ·
                    refine ⟨2679958231946120167597345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3573277642594826890129793 2679958231946120167597345)
                    ·
                      refine ⟨2009968673959590125698009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2679958231946120167597345 2009968673959590125698009)
                      ·
                        rfl

theorem cell23_3914400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 2, 1, 2, 2].length) (baseStart_3914400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914400 prefixEnd_3914400 := by exact prefixLift 3914400
  have htrace : WordTrace (prefixWord ++ tailWord_3914400) baseStart_3914400 baseEnd_3914400 := by
    simpa [prefixWord, tailWord_3914400, baseEnd_3914400] using wordTrace_append hprefix tailTrace_3914400
  have hstable : (prefixWord ++ tailWord_3914400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914400).length < 2 ^ (prefixWord ++ tailWord_3914400).sum := by decide
  have hdescent : baseEnd_3914400 < baseStart_3914400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914405 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 5, 4, 2]
def baseStart_3914405 : Nat := 118140960795 + 3914405 * 2 ^ 59
def prefixEnd_3914405 : Nat := 4983230072969 + 3 ^ 40 * 3914405 * 2
def baseEnd_3914405 : Nat := 2009971241362862606135485

theorem tailTrace_3914405 : CollatzResearch.WordTrace tailWord_3914405 prefixEnd_3914405 2009971241362862606135485 := by
  unfold tailWord_3914405
  simp only [CollatzResearch.WordTrace]
  refine ⟨142770079383786686994944669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95180052922524457996629779 142770079383786686994944669)
  ·
    refine ⟨53538779768920007623104251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142770079383786686994944669 53538779768920007623104251)
    ·
      refine ⟨80308169653380011434656377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53538779768920007623104251 80308169653380011434656377)
      ·
        refine ⟨60231127240035008575992283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80308169653380011434656377 60231127240035008575992283)
        ·
          refine ⟨90346690860052512863988425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60231127240035008575992283 90346690860052512863988425)
          ·
            refine ⟨67760018145039384647991319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90346690860052512863988425 67760018145039384647991319)
            ·
              refine ⟨101640027217559076971986979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67760018145039384647991319 101640027217559076971986979)
              ·
                refine ⟨152460040826338615457980469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101640027217559076971986979 152460040826338615457980469)
                ·
                  refine ⟨14293128827469245199185669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 152460040826338615457980469 14293128827469245199185669)
                  ·
                    refine ⟨2679961655150483474847313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14293128827469245199185669 2679961655150483474847313)
                    ·
                      refine ⟨2009971241362862606135485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2679961655150483474847313 2009971241362862606135485)
                      ·
                        rfl

theorem cell23_3914405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 4, 2].length) (baseStart_3914405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914405 prefixEnd_3914405 := by exact prefixLift 3914405
  have htrace : WordTrace (prefixWord ++ tailWord_3914405) baseStart_3914405 baseEnd_3914405 := by
    simpa [prefixWord, tailWord_3914405, baseEnd_3914405] using wordTrace_append hprefix tailTrace_3914405
  have hstable : (prefixWord ++ tailWord_3914405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914405).length < 2 ^ (prefixWord ++ tailWord_3914405).sum := by decide
  have hdescent : baseEnd_3914405 < baseStart_3914405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914455 : List Nat := [1, 1, 3, 2, 1, 4, 1, 2, 2, 3, 3]
def baseStart_3914455 : Nat := 118140960795 + 3914455 * 2 ^ 59
def prefixEnd_3914455 : Nat := 4983230072969 + 3 ^ 40 * 3914455 * 2
def baseEnd_3914455 : Nat := 2009996915395587410510255

theorem tailTrace_3914455 : CollatzResearch.WordTrace tailWord_3914455 prefixEnd_3914455 2009996915395587410510255 := by
  unfold tailWord_3914455
  simp only [CollatzResearch.WordTrace]
  refine ⟨142771903033605545534264819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95181268689070363689509879 142771903033605545534264819)
  ·
    refine ⟨214157854550408318301397229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142771903033605545534264819 214157854550408318301397229)
    ·
      refine ⟨80309195456403119363023961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214157854550408318301397229 80309195456403119363023961)
      ·
        refine ⟨60231896592302339522267971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80309195456403119363023961 60231896592302339522267971)
        ·
          refine ⟨90347844888453509283401957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60231896592302339522267971 90347844888453509283401957)
          ·
            refine ⟨16940220916585032990637867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90347844888453509283401957 16940220916585032990637867)
            ·
              refine ⟨25410331374877549485956801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16940220916585032990637867 25410331374877549485956801)
              ·
                refine ⟨19057748531158162114467601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25410331374877549485956801 19057748531158162114467601)
                ·
                  refine ⟨14293311398368621585850701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19057748531158162114467601 14293311398368621585850701)
                  ·
                    refine ⟨5359991774388233094694013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14293311398368621585850701 5359991774388233094694013)
                    ·
                      refine ⟨2009996915395587410510255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5359991774388233094694013 2009996915395587410510255)
                      ·
                        rfl

theorem cell23_3914455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 3, 3].length) (baseStart_3914455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914455 prefixEnd_3914455 := by exact prefixLift 3914455
  have htrace : WordTrace (prefixWord ++ tailWord_3914455) baseStart_3914455 baseEnd_3914455 := by
    simpa [prefixWord, tailWord_3914455, baseEnd_3914455] using wordTrace_append hprefix tailTrace_3914455
  have hstable : (prefixWord ++ tailWord_3914455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914455).length < 2 ^ (prefixWord ++ tailWord_3914455).sum := by decide
  have hdescent : baseEnd_3914455 < baseStart_3914455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914456 : List Nat := [2, 1, 2, 2, 3, 4, 1, 2, 2, 2, 2]
def baseStart_3914456 : Nat := 118140960795 + 3914456 * 2 ^ 59
def prefixEnd_3914456 : Nat := 4983230072969 + 3 ^ 40 * 3914456 * 2
def baseEnd_3914456 : Nat := 2009997428876241906597751

theorem tailTrace_3914456 : CollatzResearch.WordTrace tailWord_3914456 prefixEnd_3914456 2009997428876241906597751 := by
  unfold tailWord_3914456
  simp only [CollatzResearch.WordTrace]
  refine ⟨71385969753300961352525611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95181293004401281803367481 71385969753300961352525611)
  ·
    refine ⟨107078954629951442028788417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71385969753300961352525611 107078954629951442028788417)
    ·
      refine ⟨80309215972463581521591313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107078954629951442028788417 80309215972463581521591313)
      ·
        refine ⟨60231911979347686141193485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80309215972463581521591313 60231911979347686141193485)
        ·
          refine ⟨22586966992255382302947557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60231911979347686141193485 22586966992255382302947557)
          ·
            refine ⟨4235056311047884181802667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22586966992255382302947557 4235056311047884181802667)
            ·
              refine ⟨6352584466571826272704001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4235056311047884181802667 6352584466571826272704001)
              ·
                refine ⟨4764438349928869704528001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6352584466571826272704001 4764438349928869704528001)
                ·
                  refine ⟨3573328762446652278396001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4764438349928869704528001 3573328762446652278396001)
                  ·
                    refine ⟨2679996571834989208797001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3573328762446652278396001 2679996571834989208797001)
                    ·
                      refine ⟨2009997428876241906597751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2679996571834989208797001 2009997428876241906597751)
                      ·
                        rfl

theorem cell23_3914456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 2, 2, 2].length) (baseStart_3914456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914456 prefixEnd_3914456 := by exact prefixLift 3914456
  have htrace : WordTrace (prefixWord ++ tailWord_3914456) baseStart_3914456 baseEnd_3914456 := by
    simpa [prefixWord, tailWord_3914456, baseEnd_3914456] using wordTrace_append hprefix tailTrace_3914456
  have hstable : (prefixWord ++ tailWord_3914456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914456).length < 2 ^ (prefixWord ++ tailWord_3914456).sum := by decide
  have hdescent : baseEnd_3914456 < baseStart_3914456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914488 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 2, 8]
def baseStart_3914488 : Nat := 118140960795 + 3914488 * 2 ^ 59
def prefixEnd_3914488 : Nat := 4983230072969 + 3 ^ 40 * 3914488 * 2
def baseEnd_3914488 : Nat := 670004620085728593799201

theorem tailTrace_3914488 : CollatzResearch.WordTrace tailWord_3914488 prefixEnd_3914488 670004620085728593799201 := by
  unfold tailWord_3914488
  simp only [CollatzResearch.WordTrace]
  refine ⟨71386553321242996085108059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95182071094990661446810745 71386553321242996085108059)
  ·
    refine ⟨107079829981864494127662089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71386553321242996085108059 107079829981864494127662089)
    ·
      refine ⟨80309872486398370595746567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107079829981864494127662089 80309872486398370595746567)
      ·
        refine ⟨120464808729597555893619851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80309872486398370595746567 120464808729597555893619851)
        ·
          refine ⟨180697213094396333840429777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120464808729597555893619851 180697213094396333840429777)
          ·
            refine ⟨135522909820797250380322333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180697213094396333840429777 135522909820797250380322333)
            ·
              refine ⟨50821091182798968892620875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135522909820797250380322333 50821091182798968892620875)
              ·
                refine ⟨76231636774198453338931313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50821091182798968892620875 76231636774198453338931313)
                ·
                  refine ⟨57173727580648840004198485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76231636774198453338931313 57173727580648840004198485)
                  ·
                    refine ⟨670004620085728593799201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57173727580648840004198485 670004620085728593799201)
                    ·
                      rfl

theorem cell23_3914488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 2, 8].length) (baseStart_3914488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914488 prefixEnd_3914488 := by exact prefixLift 3914488
  have htrace : WordTrace (prefixWord ++ tailWord_3914488) baseStart_3914488 baseEnd_3914488 := by
    simpa [prefixWord, tailWord_3914488, baseEnd_3914488] using wordTrace_append hprefix tailTrace_3914488
  have hstable : (prefixWord ++ tailWord_3914488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914488).length < 2 ^ (prefixWord ++ tailWord_3914488).sum := by decide
  have hdescent : baseEnd_3914488 < baseStart_3914488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914495 : List Nat := [1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 4]
def baseStart_3914495 : Nat := 118140960795 + 3914495 * 2 ^ 59
def prefixEnd_3914495 : Nat := 4983230072969 + 3 ^ 40 * 3914495 * 2
def baseEnd_3914495 : Nat := 2010017454621767254010071

theorem tailTrace_3914495 : CollatzResearch.WordTrace tailWord_3914495 prefixEnd_3914495 2010017454621767254010071 := by
  unfold tailWord_3914495
  simp only [CollatzResearch.WordTrace]
  refine ⟨142773361953460632365720939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95182241302307088243813959 142773361953460632365720939)
  ·
    refine ⟨214160042930190948548581409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142773361953460632365720939 214160042930190948548581409)
    ·
      refine ⟨160620032197643211411436057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214160042930190948548581409 160620032197643211411436057)
      ·
        refine ⟨120465024148232408558577043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160620032197643211411436057 120465024148232408558577043)
        ·
          refine ⟨180697536222348612837865565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120465024148232408558577043 180697536222348612837865565)
          ·
            refine ⟨67761576083380729814199587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180697536222348612837865565 67761576083380729814199587)
            ·
              refine ⟨101642364125071094721299381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67761576083380729814199587 101642364125071094721299381)
              ·
                refine ⟨9528971636725415130121817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101642364125071094721299381 9528971636725415130121817)
                ·
                  refine ⟨7146728727544061347591363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9528971636725415130121817 7146728727544061347591363)
                  ·
                    refine ⟨10720093091316092021387045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7146728727544061347591363 10720093091316092021387045)
                    ·
                      refine ⟨2010017454621767254010071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10720093091316092021387045 2010017454621767254010071)
                      ·
                        rfl

theorem cell23_3914495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 4].length) (baseStart_3914495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914495 prefixEnd_3914495 := by exact prefixLift 3914495
  have htrace : WordTrace (prefixWord ++ tailWord_3914495) baseStart_3914495 baseEnd_3914495 := by
    simpa [prefixWord, tailWord_3914495, baseEnd_3914495] using wordTrace_append hprefix tailTrace_3914495
  have hstable : (prefixWord ++ tailWord_3914495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914495).length < 2 ^ (prefixWord ++ tailWord_3914495).sum := by decide
  have hdescent : baseEnd_3914495 < baseStart_3914495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914505 : List Nat := [1, 2, 1, 1, 3, 2, 2, 2, 5, 4]
def baseStart_3914505 : Nat := 118140960795 + 3914505 * 2 ^ 59
def prefixEnd_3914505 : Nat := 4983230072969 + 3 ^ 40 * 3914505 * 2
def baseEnd_3914505 : Nat := 670007529809437404961675

theorem tailTrace_3914505 : CollatzResearch.WordTrace tailWord_3914505 prefixEnd_3914505 670007529809437404961675 := by
  unfold tailWord_3914505
  simp only [CollatzResearch.WordTrace]
  refine ⟨142773726683424404073584969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95182484455616269382389979 142773726683424404073584969)
  ·
    refine ⟨107080295012568303055188727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142773726683424404073584969 107080295012568303055188727)
    ·
      refine ⟨160620442518852454582783091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107080295012568303055188727 160620442518852454582783091)
      ·
        refine ⟨240930663778278681874174637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160620442518852454582783091 240930663778278681874174637)
        ·
          refine ⟨90348998916854505702815489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240930663778278681874174637 90348998916854505702815489)
          ·
            refine ⟨67761749187640879277111617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90348998916854505702815489 67761749187640879277111617)
            ·
              refine ⟨50821311890730659457833713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67761749187640879277111617 50821311890730659457833713)
              ·
                refine ⟨38115983918047994593375285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50821311890730659457833713 38115983918047994593375285)
                ·
                  refine ⟨3573373492316999493128933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38115983918047994593375285 3573373492316999493128933)
                  ·
                    refine ⟨670007529809437404961675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3573373492316999493128933 670007529809437404961675)
                    ·
                      rfl

theorem cell23_3914505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 5, 4].length) (baseStart_3914505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914505 prefixEnd_3914505 := by exact prefixLift 3914505
  have htrace : WordTrace (prefixWord ++ tailWord_3914505) baseStart_3914505 baseEnd_3914505 := by
    simpa [prefixWord, tailWord_3914505, baseEnd_3914505] using wordTrace_append hprefix tailTrace_3914505
  have hstable : (prefixWord ++ tailWord_3914505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914505).length < 2 ^ (prefixWord ++ tailWord_3914505).sum := by decide
  have hdescent : baseEnd_3914505 < baseStart_3914505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914549 : List Nat := [1, 3, 3, 1, 3, 2, 2, 1, 2, 2, 3]
def baseStart_3914549 : Nat := 118140960795 + 3914549 * 2 ^ 59
def prefixEnd_3914549 : Nat := 4983230072969 + 3 ^ 40 * 3914549 * 2
def baseEnd_3914549 : Nat := 2010045182577110042734823

theorem tailTrace_3914549 : CollatzResearch.WordTrace tailWord_3914549 prefixEnd_3914549 2010045182577110042734823 := by
  unfold tailWord_3914549
  simp only [CollatzResearch.WordTrace]
  refine ⟨142775331495264999588186701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95183554330176666392124467 142775331495264999588186701)
  ·
    refine ⟨53540749310724374845570013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142775331495264999588186701 53540749310724374845570013)
    ·
      refine ⟨20077780991521640567088755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53540749310724374845570013 20077780991521640567088755)
      ·
        refine ⟨30116671487282460850633133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20077780991521640567088755 30116671487282460850633133)
        ·
          refine ⟨11293751807730922818987425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30116671487282460850633133 11293751807730922818987425)
          ·
            refine ⟨8470313855798192114240569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11293751807730922818987425 8470313855798192114240569)
            ·
              refine ⟨6352735391848644085680427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8470313855798192114240569 6352735391848644085680427)
              ·
                refine ⟨9529103087772966128520641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6352735391848644085680427 9529103087772966128520641)
                ·
                  refine ⟨7146827315829724596390481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9529103087772966128520641 7146827315829724596390481)
                  ·
                    refine ⟨5360120486872293447292861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7146827315829724596390481 5360120486872293447292861)
                    ·
                      refine ⟨2010045182577110042734823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5360120486872293447292861 2010045182577110042734823)
                      ·
                        rfl

theorem cell23_3914549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_3914549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914549 prefixEnd_3914549 := by exact prefixLift 3914549
  have htrace : WordTrace (prefixWord ++ tailWord_3914549) baseStart_3914549 baseEnd_3914549 := by
    simpa [prefixWord, tailWord_3914549, baseEnd_3914549] using wordTrace_append hprefix tailTrace_3914549
  have hstable : (prefixWord ++ tailWord_3914549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914549).length < 2 ^ (prefixWord ++ tailWord_3914549).sum := by decide
  have hdescent : baseEnd_3914549 < baseStart_3914549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914573 : List Nat := [1, 6, 1, 2, 2, 1, 1, 4, 1, 4]
def baseStart_3914573 : Nat := 118140960795 + 3914573 * 2 ^ 59
def prefixEnd_3914573 : Nat := 4983230072969 + 3 ^ 40 * 3914573 * 2
def baseEnd_3914573 : Nat := 670019168704272649611571

theorem tailTrace_3914573 : CollatzResearch.WordTrace tailWord_3914573 prefixEnd_3914573 670019168704272649611571 := by
  unfold tailWord_3914573
  simp only [CollatzResearch.WordTrace]
  refine ⟨142776206847178051687060373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95184137898118701124706915 142776206847178051687060373)
  ·
    refine ⟨6692634695961471172830955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 142776206847178051687060373 6692634695961471172830955)
    ·
      refine ⟨10038952043942206759246433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6692634695961471172830955 10038952043942206759246433)
      ·
        refine ⟨7529214032956655069434825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10038952043942206759246433 7529214032956655069434825)
        ·
          refine ⟨5646910524717491302076119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7529214032956655069434825 5646910524717491302076119)
          ·
            refine ⟨8470365787076236953114179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5646910524717491302076119 8470365787076236953114179)
            ·
              refine ⟨12705548680614355429671269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8470365787076236953114179 12705548680614355429671269)
              ·
                refine ⟨2382290377615191643063363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12705548680614355429671269 2382290377615191643063363)
                ·
                  refine ⟨3573435566422787464595045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2382290377615191643063363 3573435566422787464595045)
                  ·
                    refine ⟨670019168704272649611571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3573435566422787464595045 670019168704272649611571)
                    ·
                      rfl

theorem cell23_3914573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_3914573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914573 prefixEnd_3914573 := by exact prefixLift 3914573
  have htrace : WordTrace (prefixWord ++ tailWord_3914573) baseStart_3914573 baseEnd_3914573 := by
    simpa [prefixWord, tailWord_3914573, baseEnd_3914573] using wordTrace_append hprefix tailTrace_3914573
  have hstable : (prefixWord ++ tailWord_3914573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914573).length < 2 ^ (prefixWord ++ tailWord_3914573).sum := by decide
  have hdescent : baseEnd_3914573 < baseStart_3914573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914606 : List Nat := [4, 1, 2, 3, 2, 1, 1, 1, 1, 5, 2]
def baseStart_3914606 : Nat := 118140960795 + 3914606 * 2 ^ 59
def prefixEnd_3914606 : Nat := 4983230072969 + 3 ^ 40 * 3914606 * 2
def baseEnd_3914606 : Nat := 2010074450974416319722061

theorem tailTrace_3914606 : CollatzResearch.WordTrace tailWord_3914606 prefixEnd_3914606 2010074450974416319722061 := by
  unfold tailWord_3914606
  simp only [CollatzResearch.WordTrace]
  refine ⟨17847176307007312290376459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95184940304038998882007781 17847176307007312290376459)
  ·
    refine ⟨26770764460510968435564689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17847176307007312290376459 26770764460510968435564689)
    ·
      refine ⟨20078073345383226326673517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26770764460510968435564689 20078073345383226326673517)
      ·
        refine ⟨7529277504518709872502569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20078073345383226326673517 7529277504518709872502569)
        ·
          refine ⟨5646958128389032404376927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7529277504518709872502569 5646958128389032404376927)
          ·
            refine ⟨8470437192583548606565391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5646958128389032404376927 8470437192583548606565391)
            ·
              refine ⟨12705655788875322909848087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8470437192583548606565391 12705655788875322909848087)
              ·
                refine ⟨19058483683312984364772131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12705655788875322909848087 19058483683312984364772131)
                ·
                  refine ⟨28587725524969476547158197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19058483683312984364772131 28587725524969476547158197)
                  ·
                    refine ⟨2680099267965888426296081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28587725524969476547158197 2680099267965888426296081)
                    ·
                      refine ⟨2010074450974416319722061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2680099267965888426296081 2010074450974416319722061)
                      ·
                        rfl

theorem cell23_3914606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_3914606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914606 prefixEnd_3914606 := by exact prefixLift 3914606
  have htrace : WordTrace (prefixWord ++ tailWord_3914606) baseStart_3914606 baseEnd_3914606 := by
    simpa [prefixWord, tailWord_3914606, baseEnd_3914606] using wordTrace_append hprefix tailTrace_3914606
  have hstable : (prefixWord ++ tailWord_3914606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914606).length < 2 ^ (prefixWord ++ tailWord_3914606).sum := by decide
  have hdescent : baseEnd_3914606 < baseStart_3914606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914613 : List Nat := [1, 3, 4, 1, 1, 3, 2, 3, 1, 1, 3]
def baseStart_3914613 : Nat := 118140960795 + 3914613 * 2 ^ 59
def prefixEnd_3914613 : Nat := 4983230072969 + 3 ^ 40 * 3914613 * 2
def baseEnd_3914613 : Nat := 2010078045338997792334529

theorem tailTrace_3914613 : CollatzResearch.WordTrace tailWord_3914613 prefixEnd_3914613 2010078045338997792334529 := by
  unfold tailWord_3914613
  simp only [CollatzResearch.WordTrace]
  refine ⟨142777665767033138518516493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95185110511355425679010995 142777665767033138518516493)
  ·
    refine ⟨53541624662637426944443685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142777665767033138518516493 53541624662637426944443685)
    ·
      refine ⟨10039054624244517552083191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53541624662637426944443685 10039054624244517552083191)
      ·
        refine ⟨15058581936366776328124787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10039054624244517552083191 15058581936366776328124787)
        ·
          refine ⟨22587872904550164492187181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15058581936366776328124787 22587872904550164492187181)
          ·
            refine ⟨8470452339206311684570193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22587872904550164492187181 8470452339206311684570193)
            ·
              refine ⟨6352839254404733763427645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8470452339206311684570193 6352839254404733763427645)
              ·
                refine ⟨2382314720401775161285367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6352839254404733763427645 2382314720401775161285367)
                ·
                  refine ⟨3573472080602662741928051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2382314720401775161285367 3573472080602662741928051)
                  ·
                    refine ⟨5360208120903994112892077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3573472080602662741928051 5360208120903994112892077)
                    ·
                      refine ⟨2010078045338997792334529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5360208120903994112892077 2010078045338997792334529)
                      ·
                        rfl

theorem cell23_3914613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_3914613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914613 prefixEnd_3914613 := by exact prefixLift 3914613
  have htrace : WordTrace (prefixWord ++ tailWord_3914613) baseStart_3914613 baseEnd_3914613 := by
    simpa [prefixWord, tailWord_3914613, baseEnd_3914613] using wordTrace_append hprefix tailTrace_3914613
  have hstable : (prefixWord ++ tailWord_3914613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914613).length < 2 ^ (prefixWord ++ tailWord_3914613).sum := by decide
  have hdescent : baseEnd_3914613 < baseStart_3914613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914619 : List Nat := [1, 1, 1, 1, 1, 5, 6, 1, 1, 1, 4]
def baseStart_3914619 : Nat := 118140960795 + 3914619 * 2 ^ 59
def prefixEnd_3914619 : Nat := 4983230072969 + 3 ^ 40 * 3914619 * 2
def baseEnd_3914619 : Nat := 2010081126222924768859501

theorem tailTrace_3914619 : CollatzResearch.WordTrace tailWord_3914619 prefixEnd_3914619 2010081126222924768859501 := by
  unfold tailWord_3914619
  simp only [CollatzResearch.WordTrace]
  refine ⟨142777884605011401543234911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95185256403340934362156607 142777884605011401543234911)
  ·
    refine ⟨214166826907517102314852367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142777884605011401543234911 214166826907517102314852367)
    ·
      refine ⟨321250240361275653472278551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214166826907517102314852367 321250240361275653472278551)
      ·
        refine ⟨481875360541913480208417827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321250240361275653472278551 481875360541913480208417827)
        ·
          refine ⟨722813040812870220312626741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481875360541913480208417827 722813040812870220312626741)
          ·
            refine ⟨67763722576206583154308757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 722813040812870220312626741 67763722576206583154308757)
            ·
              refine ⟨3176424495759683585358223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 67763722576206583154308757 3176424495759683585358223)
              ·
                refine ⟨4764636743639525378037335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3176424495759683585358223 4764636743639525378037335)
                ·
                  refine ⟨7146955115459288067056003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4764636743639525378037335 7146955115459288067056003)
                  ·
                    refine ⟨10720432673188932100584005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7146955115459288067056003 10720432673188932100584005)
                    ·
                      refine ⟨2010081126222924768859501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10720432673188932100584005 2010081126222924768859501)
                      ·
                        rfl

theorem cell23_3914619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 1, 1, 4].length) (baseStart_3914619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914619 prefixEnd_3914619 := by exact prefixLift 3914619
  have htrace : WordTrace (prefixWord ++ tailWord_3914619) baseStart_3914619 baseEnd_3914619 := by
    simpa [prefixWord, tailWord_3914619, baseEnd_3914619] using wordTrace_append hprefix tailTrace_3914619
  have hstable : (prefixWord ++ tailWord_3914619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914619).length < 2 ^ (prefixWord ++ tailWord_3914619).sum := by decide
  have hdescent : baseEnd_3914619 < baseStart_3914619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914629 : List Nat := [1, 3, 1, 1, 3, 3, 3, 2, 2, 4]
def baseStart_3914629 : Nat := 118140960795 + 3914629 * 2 ^ 59
def prefixEnd_3914629 : Nat := 4983230072969 + 3 ^ 40 * 3914629 * 2
def baseEnd_3914629 : Nat := 670028753676489909911485

theorem tailTrace_3914629 : CollatzResearch.WordTrace tailWord_3914629 prefixEnd_3914629 670028753676489909911485 := by
  unfold tailWord_3914629
  simp only [CollatzResearch.WordTrace]
  refine ⟨142778249334975173251098941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95185499556650115500732627 142778249334975173251098941)
  ·
    refine ⟨53541843500615689969162103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142778249334975173251098941 53541843500615689969162103)
    ·
      refine ⟨80312765250923534953743155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53541843500615689969162103 80312765250923534953743155)
      ·
        refine ⟨120469147876385302430614733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80312765250923534953743155 120469147876385302430614733)
        ·
          refine ⟨45175930453644488411480525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120469147876385302430614733 45175930453644488411480525)
          ·
            refine ⟨16940973920116683154305197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45175930453644488411480525 16940973920116683154305197)
            ·
              refine ⟨6352865220043756182864449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16940973920116683154305197 6352865220043756182864449)
              ·
                refine ⟨4764648915032817137148337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6352865220043756182864449 4764648915032817137148337)
                ·
                  refine ⟨3573486686274612852861253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4764648915032817137148337 3573486686274612852861253)
                  ·
                    refine ⟨670028753676489909911485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3573486686274612852861253 670028753676489909911485)
                    ·
                      rfl

theorem cell23_3914629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 2, 4].length) (baseStart_3914629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914629 prefixEnd_3914629 := by exact prefixLift 3914629
  have htrace : WordTrace (prefixWord ++ tailWord_3914629) baseStart_3914629 baseEnd_3914629 := by
    simpa [prefixWord, tailWord_3914629, baseEnd_3914629] using wordTrace_append hprefix tailTrace_3914629
  have hstable : (prefixWord ++ tailWord_3914629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914629).length < 2 ^ (prefixWord ++ tailWord_3914629).sum := by decide
  have hdescent : baseEnd_3914629 < baseStart_3914629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914665 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 1, 4, 5]
def baseStart_3914665 : Nat := 118140960795 + 3914665 * 2 ^ 59
def prefixEnd_3914665 : Nat := 4983230072969 + 3 ^ 40 * 3914665 * 2
def baseEnd_3914665 : Nat := 2010104746333031588884289

theorem tailTrace_3914665 : CollatzResearch.WordTrace tailWord_3914665 prefixEnd_3914665 2010104746333031588884289 := by
  unfold tailWord_3914665
  simp only [CollatzResearch.WordTrace]
  refine ⟨142779562362844751399409449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95186374908563167599606299 142779562362844751399409449)
  ·
    refine ⟨107084671772133563549557087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142779562362844751399409449 107084671772133563549557087)
    ·
      refine ⟨160627007658200345324335631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107084671772133563549557087 160627007658200345324335631)
      ·
        refine ⟨240940511487300517986503447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160627007658200345324335631 240940511487300517986503447)
        ·
          refine ⟨361410767230950776979755171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240940511487300517986503447 361410767230950776979755171)
          ·
            refine ⟨542116150846426165469632757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361410767230950776979755171 542116150846426165469632757)
            ·
              refine ⟨50823389141852453012778071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 542116150846426165469632757 50823389141852453012778071)
              ·
                refine ⟨76235083712778679519167107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50823389141852453012778071 76235083712778679519167107)
                ·
                  refine ⟨114352625569168019278750661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76235083712778679519167107 114352625569168019278750661)
                  ·
                    refine ⟨21441117294219003614765749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114352625569168019278750661 21441117294219003614765749)
                    ·
                      refine ⟨2010104746333031588884289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21441117294219003614765749 2010104746333031588884289)
                      ·
                        rfl

theorem cell23_3914665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 4, 5].length) (baseStart_3914665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914665 prefixEnd_3914665 := by exact prefixLift 3914665
  have htrace : WordTrace (prefixWord ++ tailWord_3914665) baseStart_3914665 baseEnd_3914665 := by
    simpa [prefixWord, tailWord_3914665, baseEnd_3914665] using wordTrace_append hprefix tailTrace_3914665
  have hstable : (prefixWord ++ tailWord_3914665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914665).length < 2 ^ (prefixWord ++ tailWord_3914665).sum := by decide
  have hdescent : baseEnd_3914665 < baseStart_3914665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914686 : List Nat := [4, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3]
def baseStart_3914686 : Nat := 118140960795 + 3914686 * 2 ^ 59
def prefixEnd_3914686 : Nat := 4983230072969 + 3 ^ 40 * 3914686 * 2
def baseEnd_3914686 : Nat := 2010115529426776006721693

theorem tailTrace_3914686 : CollatzResearch.WordTrace tailWord_3914686 prefixEnd_3914686 2010115529426776006721693 := by
  unfold tailWord_3914686
  simp only [CollatzResearch.WordTrace]
  refine ⟨17847541036971083998240489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95186885530512447990615941 17847541036971083998240489)
  ·
    refine ⟨13385655777728312998680367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17847541036971083998240489 13385655777728312998680367)
    ·
      refine ⟨20078483666592469498020551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13385655777728312998680367 20078483666592469498020551)
      ·
        refine ⟨30117725499888704247030827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20078483666592469498020551 30117725499888704247030827)
        ·
          refine ⟨45176588249833056370546241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30117725499888704247030827 45176588249833056370546241)
          ·
            refine ⟨33882441187374792277909681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45176588249833056370546241 33882441187374792277909681)
            ·
              refine ⟨25411830890531094208432261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33882441187374792277909681 25411830890531094208432261)
              ·
                refine ⟨4764718291974580164081049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25411830890531094208432261 4764718291974580164081049)
                ·
                  refine ⟨3573538718980935123060787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4764718291974580164081049 3573538718980935123060787)
                  ·
                    refine ⟨5360308078471402684591181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3573538718980935123060787 5360308078471402684591181)
                    ·
                      refine ⟨2010115529426776006721693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5360308078471402684591181 2010115529426776006721693)
                      ·
                        rfl

theorem cell23_3914686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_3914686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914686 prefixEnd_3914686 := by exact prefixLift 3914686
  have htrace : WordTrace (prefixWord ++ tailWord_3914686) baseStart_3914686 baseEnd_3914686 := by
    simpa [prefixWord, tailWord_3914686, baseEnd_3914686] using wordTrace_append hprefix tailTrace_3914686
  have hstable : (prefixWord ++ tailWord_3914686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914686).length < 2 ^ (prefixWord ++ tailWord_3914686).sum := by decide
  have hdescent : baseEnd_3914686 < baseStart_3914686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914703 : List Nat := [1, 1, 2, 1, 1, 8, 2, 1, 2, 1, 3]
def baseStart_3914703 : Nat := 118140960795 + 3914703 * 2 ^ 59
def prefixEnd_3914703 : Nat := 4983230072969 + 3 ^ 40 * 3914703 * 2
def baseEnd_3914703 : Nat := 2010124258597902440209115

theorem tailTrace_3914703 : CollatzResearch.WordTrace tailWord_3914703 prefixEnd_3914703 2010124258597902440209115 := by
  unfold tailWord_3914703
  simp only [CollatzResearch.WordTrace]
  refine ⟨142780948336707083889292763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95187298891138055926195175 142780948336707083889292763)
  ·
    refine ⟨214171422505060625833939145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142780948336707083889292763 214171422505060625833939145)
    ·
      refine ⟨160628566878795469375454359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214171422505060625833939145 160628566878795469375454359)
      ·
        refine ⟨240942850318193204063181539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160628566878795469375454359 240942850318193204063181539)
        ·
          refine ⟨361414275477289806094772309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240942850318193204063181539 361414275477289806094772309)
          ·
            refine ⟨4235323540749489915173113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 361414275477289806094772309 4235323540749489915173113)
            ·
              refine ⟨3176492655562117436379835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4235323540749489915173113 3176492655562117436379835)
              ·
                refine ⟨4764738983343176154569753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3176492655562117436379835 4764738983343176154569753)
                ·
                  refine ⟨3573554237507382115927315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4764738983343176154569753 3573554237507382115927315)
                  ·
                    refine ⟨5360331356261073173890973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3573554237507382115927315 5360331356261073173890973)
                    ·
                      refine ⟨2010124258597902440209115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5360331356261073173890973 2010124258597902440209115)
                      ·
                        rfl

theorem cell23_3914703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 2, 1, 3].length) (baseStart_3914703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914703 prefixEnd_3914703 := by exact prefixLift 3914703
  have htrace : WordTrace (prefixWord ++ tailWord_3914703) baseStart_3914703 baseEnd_3914703 := by
    simpa [prefixWord, tailWord_3914703, baseEnd_3914703] using wordTrace_append hprefix tailTrace_3914703
  have hstable : (prefixWord ++ tailWord_3914703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914703).length < 2 ^ (prefixWord ++ tailWord_3914703).sum := by decide
  have hdescent : baseEnd_3914703 < baseStart_3914703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914712 : List Nat := [2, 1, 2, 2, 2, 3, 1, 2, 2, 1, 5]
def baseStart_3914712 : Nat := 118140960795 + 3914712 * 2 ^ 59
def prefixEnd_3914712 : Nat := 4983230072969 + 3 ^ 40 * 3914712 * 2
def baseEnd_3914712 : Nat := 2010128879923792904996573

theorem tailTrace_3914712 : CollatzResearch.WordTrace tailWord_3914712 prefixEnd_3914712 2010128879923792904996573 := by
  unfold tailWord_3914712
  simp only [CollatzResearch.WordTrace]
  refine ⟨71390638296837239213185195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95187517729116318950913593 71390638296837239213185195)
  ·
    refine ⟨107085957445255858819777793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71390638296837239213185195 107085957445255858819777793)
    ·
      refine ⟨80314468083941894114833345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107085957445255858819777793 80314468083941894114833345)
      ·
        refine ⟨60235851062956420586125009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80314468083941894114833345 60235851062956420586125009)
        ·
          refine ⟨45176888297217315439593757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60235851062956420586125009 45176888297217315439593757)
          ·
            refine ⟨16941333111456493289847659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45176888297217315439593757 16941333111456493289847659)
            ·
              refine ⟨25411999667184739934771489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16941333111456493289847659 25411999667184739934771489)
              ·
                refine ⟨19058999750388554951078617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25411999667184739934771489 19058999750388554951078617)
                ·
                  refine ⟨14294249812791416213308963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19058999750388554951078617 14294249812791416213308963)
                  ·
                    refine ⟨21441374719187124319963445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14294249812791416213308963 21441374719187124319963445)
                    ·
                      refine ⟨2010128879923792904996573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21441374719187124319963445 2010128879923792904996573)
                      ·
                        rfl

theorem cell23_3914712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_3914712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914712 prefixEnd_3914712 := by exact prefixLift 3914712
  have htrace : WordTrace (prefixWord ++ tailWord_3914712) baseStart_3914712 baseEnd_3914712 := by
    simpa [prefixWord, tailWord_3914712, baseEnd_3914712] using wordTrace_append hprefix tailTrace_3914712
  have hstable : (prefixWord ++ tailWord_3914712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914712).length < 2 ^ (prefixWord ++ tailWord_3914712).sum := by decide
  have hdescent : baseEnd_3914712 < baseStart_3914712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914713 : List Nat := [1, 2, 1, 2, 5, 3, 1, 2, 1, 3, 2]
def baseStart_3914713 : Nat := 118140960795 + 3914713 * 2 ^ 59
def prefixEnd_3914713 : Nat := 4983230072969 + 3 ^ 40 * 3914713 * 2
def baseEnd_3914713 : Nat := 2010129393404447401084069

theorem tailTrace_3914713 : CollatzResearch.WordTrace tailWord_3914713 prefixEnd_3914713 2010129393404447401084069 := by
  unfold tailWord_3914713
  simp only [CollatzResearch.WordTrace]
  refine ⟨142781313066670855597156793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95187542044447237064771195 142781313066670855597156793)
  ·
    refine ⟨107085984800003141697867595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142781313066670855597156793 107085984800003141697867595)
    ·
      refine ⟨160628977200004712546801393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107085984800003141697867595 160628977200004712546801393)
      ·
        refine ⟨120471732900003534410101045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160628977200004712546801393 120471732900003534410101045)
        ·
          refine ⟨11294224959375331350946973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120471732900003534410101045 11294224959375331350946973)
          ·
            refine ⟨4235334359765749256605115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11294224959375331350946973 4235334359765749256605115)
            ·
              refine ⟨6353001539648623884907673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4235334359765749256605115 6353001539648623884907673)
              ·
                refine ⟨4764751154736467913680755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6353001539648623884907673 4764751154736467913680755)
                ·
                  refine ⟨7147126732104701870521133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4764751154736467913680755 7147126732104701870521133)
                  ·
                    refine ⟨2680172524539263201445425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7147126732104701870521133 2680172524539263201445425)
                    ·
                      refine ⟨2010129393404447401084069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2680172524539263201445425 2010129393404447401084069)
                      ·
                        rfl

theorem cell23_3914713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 3, 2].length) (baseStart_3914713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914713 prefixEnd_3914713 := by exact prefixLift 3914713
  have htrace : WordTrace (prefixWord ++ tailWord_3914713) baseStart_3914713 baseEnd_3914713 := by
    simpa [prefixWord, tailWord_3914713, baseEnd_3914713] using wordTrace_append hprefix tailTrace_3914713
  have hstable : (prefixWord ++ tailWord_3914713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914713).length < 2 ^ (prefixWord ++ tailWord_3914713).sum := by decide
  have hdescent : baseEnd_3914713 < baseStart_3914713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914759 : List Nat := [1, 1, 4, 3, 1, 1, 3, 1, 2, 3, 3]
def baseStart_3914759 : Nat := 118140960795 + 3914759 * 2 ^ 59
def prefixEnd_3914759 : Nat := 4983230072969 + 3 ^ 40 * 3914759 * 2
def baseEnd_3914759 : Nat := 2010153013514554221108857

theorem tailTrace_3914759 : CollatzResearch.WordTrace tailWord_3914759 prefixEnd_3914759 2010153013514554221108857 := by
  unfold tailWord_3914759
  simp only [CollatzResearch.WordTrace]
  refine ⟨142782990824504205453331331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95188660549669470302220887 142782990824504205453331331)
  ·
    refine ⟨214174486236756308179996997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142782990824504205453331331 214174486236756308179996997)
    ·
      refine ⟨40157716169391807783749437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214174486236756308179996997 40157716169391807783749437)
      ·
        refine ⟨15059143563521927918906039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40157716169391807783749437 15059143563521927918906039)
        ·
          refine ⟨22588715345282891878359059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15059143563521927918906039 22588715345282891878359059)
          ·
            refine ⟨33883073017924337817538589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22588715345282891878359059 33883073017924337817538589)
            ·
              refine ⟨12706152381721626681576971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33883073017924337817538589 12706152381721626681576971)
              ·
                refine ⟨19059228572582440022365457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12706152381721626681576971 19059228572582440022365457)
                ·
                  refine ⟨14294421429436830016774093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19059228572582440022365457 14294421429436830016774093)
                  ·
                    refine ⟨5360408036038811256290285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14294421429436830016774093 5360408036038811256290285)
                    ·
                      refine ⟨2010153013514554221108857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5360408036038811256290285 2010153013514554221108857)
                      ·
                        rfl

theorem cell23_3914759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_3914759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914759 prefixEnd_3914759 := by exact prefixLift 3914759
  have htrace : WordTrace (prefixWord ++ tailWord_3914759) baseStart_3914759 baseEnd_3914759 := by
    simpa [prefixWord, tailWord_3914759, baseEnd_3914759] using wordTrace_append hprefix tailTrace_3914759
  have hstable : (prefixWord ++ tailWord_3914759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914759).length < 2 ^ (prefixWord ++ tailWord_3914759).sum := by decide
  have hdescent : baseEnd_3914759 < baseStart_3914759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914842 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 1, 1, 8]
def baseStart_3914842 : Nat := 118140960795 + 3914842 * 2 ^ 59
def prefixEnd_3914842 : Nat := 4983230072969 + 3 ^ 40 * 3914842 * 2
def baseEnd_3914842 : Nat := 2010195632408877396370975

theorem tailTrace_3914842 : CollatzResearch.WordTrace tailWord_3914842 prefixEnd_3914842 2010195632408877396370975 := by
  unfold tailWord_3914842
  simp only [CollatzResearch.WordTrace]
  refine ⟨35696504520800877657150695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95190678722135673752401853 35696504520800877657150695)
  ·
    refine ⟨53544756781201316485726043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35696504520800877657150695 53544756781201316485726043)
    ·
      refine ⟨80317135171801974728589065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53544756781201316485726043 80317135171801974728589065)
      ·
        refine ⟨60237851378851481046441799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80317135171801974728589065 60237851378851481046441799)
        ·
          refine ⟨90356777068277221569662699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60237851378851481046441799 90356777068277221569662699)
          ·
            refine ⟨135535165602415832354494049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90356777068277221569662699 135535165602415832354494049)
            ·
              refine ⟨101651374201811874265870537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135535165602415832354494049 101651374201811874265870537)
              ·
                refine ⟨76238530651358905699402903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101651374201811874265870537 76238530651358905699402903)
                ·
                  refine ⟨114357795977038358549104355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76238530651358905699402903 114357795977038358549104355)
                  ·
                    refine ⟨171536693965557537823656533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114357795977038358549104355 171536693965557537823656533)
                    ·
                      refine ⟨2010195632408877396370975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 171536693965557537823656533 2010195632408877396370975)
                      ·
                        rfl

theorem cell23_3914842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_3914842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914842 prefixEnd_3914842 := by exact prefixLift 3914842
  have htrace : WordTrace (prefixWord ++ tailWord_3914842) baseStart_3914842 baseEnd_3914842 := by
    simpa [prefixWord, tailWord_3914842, baseEnd_3914842] using wordTrace_append hprefix tailTrace_3914842
  have hstable : (prefixWord ++ tailWord_3914842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914842).length < 2 ^ (prefixWord ++ tailWord_3914842).sum := by decide
  have hdescent : baseEnd_3914842 < baseStart_3914842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914859 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 2, 9, 2]
def baseStart_3914859 : Nat := 118140960795 + 3914859 * 2 ^ 59
def prefixEnd_3914859 : Nat := 4983230072969 + 3 ^ 40 * 3914859 * 2
def baseEnd_3914859 : Nat := 2010204361580003829858397

theorem tailTrace_3914859 : CollatzResearch.WordTrace tailWord_3914859 prefixEnd_3914859 2010204361580003829858397 := by
  unfold tailWord_3914859
  simp only [CollatzResearch.WordTrace]
  refine ⟨142786638124141922531971631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95191092082761281687981087 142786638124141922531971631)
  ·
    refine ⟨214179957186212883797957447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142786638124141922531971631 214179957186212883797957447)
    ·
      refine ⟨321269935779319325696936171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214179957186212883797957447 321269935779319325696936171)
      ·
        refine ⟨481904903668978988545404257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321269935779319325696936171 481904903668978988545404257)
        ·
          refine ⟨361428677751734241409053193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 481904903668978988545404257 361428677751734241409053193)
          ·
            refine ⟨271071508313800681056789895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361428677751734241409053193 271071508313800681056789895)
            ·
              refine ⟨406607262470701021585184843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271071508313800681056789895 406607262470701021585184843)
              ·
                refine ⟨609910893706051532377777265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 406607262470701021585184843 609910893706051532377777265)
                ·
                  refine ⟨457433170279538649283332949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 609910893706051532377777265 457433170279538649283332949)
                  ·
                    refine ⟨2680272482106671773144529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 457433170279538649283332949 2680272482106671773144529)
                    ·
                      refine ⟨2010204361580003829858397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2680272482106671773144529 2010204361580003829858397)
                      ·
                        rfl

theorem cell23_3914859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 9, 2].length) (baseStart_3914859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914859 prefixEnd_3914859 := by exact prefixLift 3914859
  have htrace : WordTrace (prefixWord ++ tailWord_3914859) baseStart_3914859 baseEnd_3914859 := by
    simpa [prefixWord, tailWord_3914859, baseEnd_3914859] using wordTrace_append hprefix tailTrace_3914859
  have hstable : (prefixWord ++ tailWord_3914859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914859).length < 2 ^ (prefixWord ++ tailWord_3914859).sum := by decide
  have hdescent : baseEnd_3914859 < baseStart_3914859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914873 : List Nat := [1, 2, 1, 3, 5, 2, 2, 1, 6]
def baseStart_3914873 : Nat := 118140960795 + 3914873 * 2 ^ 59
def prefixEnd_3914873 : Nat := 4983230072969 + 3 ^ 40 * 3914873 * 2
def baseEnd_3914873 : Nat := 223356838923240752787037

theorem tailTrace_3914873 : CollatzResearch.WordTrace tailWord_3914873 prefixEnd_3914873 223356838923240752787037 := by
  unfold tailWord_3914873
  simp only [CollatzResearch.WordTrace]
  refine ⟨142787148746091202922981273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95191432497394135281987515 142787148746091202922981273)
  ·
    refine ⟨107090361559568402192235955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142787148746091202922981273 107090361559568402192235955)
    ·
      refine ⟨160635542339352603288353933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107090361559568402192235955 160635542339352603288353933)
      ·
        refine ⟨60238328377257226233132725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160635542339352603288353933 60238328377257226233132725)
        ·
          refine ⟨5647343285367864959356193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60238328377257226233132725 5647343285367864959356193)
          ·
            refine ⟨4235507464025898719517145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5647343285367864959356193 4235507464025898719517145)
            ·
              refine ⟨3176630598019424039637859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4235507464025898719517145 3176630598019424039637859)
              ·
                refine ⟨4764945897029136059456789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3176630598019424039637859 4764945897029136059456789)
                ·
                  refine ⟨223356838923240752787037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4764945897029136059456789 223356838923240752787037)
                  ·
                    rfl

theorem cell23_3914873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 6].length) (baseStart_3914873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914873 prefixEnd_3914873 := by exact prefixLift 3914873
  have htrace : WordTrace (prefixWord ++ tailWord_3914873) baseStart_3914873 baseEnd_3914873 := by
    simpa [prefixWord, tailWord_3914873, baseEnd_3914873] using wordTrace_append hprefix tailTrace_3914873
  have hstable : (prefixWord ++ tailWord_3914873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914873).length < 2 ^ (prefixWord ++ tailWord_3914873).sum := by decide
  have hdescent : baseEnd_3914873 < baseStart_3914873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914876 : List Nat := [2, 2, 2, 1, 1, 3, 1, 2, 4, 3, 2]
def baseStart_3914876 : Nat := 118140960795 + 3914876 * 2 ^ 59
def prefixEnd_3914876 : Nat := 4983230072969 + 3 ^ 40 * 3914876 * 2
def baseEnd_3914876 : Nat := 2010213090751130263345819

theorem tailTrace_3914876 : CollatzResearch.WordTrace tailWord_3914876 prefixEnd_3914876 2010213090751130263345819 := by
  unfold tailWord_3914876
  simp only [CollatzResearch.WordTrace]
  refine ⟨71393629082540167217670241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95191505443386889623560321 71393629082540167217670241)
  ·
    refine ⟨53545221811905125413252681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71393629082540167217670241 53545221811905125413252681)
    ·
      refine ⟨40158916358928844059939511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53545221811905125413252681 40158916358928844059939511)
      ·
        refine ⟨60238374538393266089909267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40158916358928844059939511 60238374538393266089909267)
        ·
          refine ⟨90357561807589899134863901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60238374538393266089909267 90357561807589899134863901)
          ·
            refine ⟨33884085677846212175573963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90357561807589899134863901 33884085677846212175573963)
            ·
              refine ⟨50826128516769318263360945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33884085677846212175573963 50826128516769318263360945)
              ·
                refine ⟨38119596387576988697520709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50826128516769318263360945 38119596387576988697520709)
                ·
                  refine ⟨7147424322670685380785133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38119596387576988697520709 7147424322670685380785133)
                  ·
                    refine ⟨2680284121001507017794425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7147424322670685380785133 2680284121001507017794425)
                    ·
                      refine ⟨2010213090751130263345819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2680284121001507017794425 2010213090751130263345819)
                      ·
                        rfl

theorem cell23_3914876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 4, 3, 2].length) (baseStart_3914876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914876 prefixEnd_3914876 := by exact prefixLift 3914876
  have htrace : WordTrace (prefixWord ++ tailWord_3914876) baseStart_3914876 baseEnd_3914876 := by
    simpa [prefixWord, tailWord_3914876, baseEnd_3914876] using wordTrace_append hprefix tailTrace_3914876
  have hstable : (prefixWord ++ tailWord_3914876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914876).length < 2 ^ (prefixWord ++ tailWord_3914876).sum := by decide
  have hdescent : baseEnd_3914876 < baseStart_3914876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914899 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 6, 4]
def baseStart_3914899 : Nat := 118140960795 + 3914899 * 2 ^ 59
def prefixEnd_3914899 : Nat := 4983230072969 + 3 ^ 40 * 3914899 * 2
def baseEnd_3914899 : Nat := 670074966935394557786071

theorem tailTrace_3914899 : CollatzResearch.WordTrace tailWord_3914899 prefixEnd_3914899 670074966935394557786071 := by
  unfold tailWord_3914899
  simp only [CollatzResearch.WordTrace]
  refine ⟨142788097043997009363427751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95192064695998006242285167 142788097043997009363427751)
  ·
    refine ⟨214182145565995514045141627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142788097043997009363427751 214182145565995514045141627)
    ·
      refine ⟨321273218348993271067712441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214182145565995514045141627 321273218348993271067712441)
      ·
        refine ⟨240954913761744953300784331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321273218348993271067712441 240954913761744953300784331)
        ·
          refine ⟨361432370642617429951176497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240954913761744953300784331 361432370642617429951176497)
          ·
            refine ⟨271074277981963072463382373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361432370642617429951176497 271074277981963072463382373)
            ·
              refine ⟨50826427121618076086884195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 271074277981963072463382373 50826427121618076086884195)
              ·
                refine ⟨76239640682427114130326293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50826427121618076086884195 76239640682427114130326293)
                ·
                  refine ⟨3573733156988770974859045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 76239640682427114130326293 3573733156988770974859045)
                  ·
                    refine ⟨670074966935394557786071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3573733156988770974859045 670074966935394557786071)
                    ·
                      rfl

theorem cell23_3914899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 6, 4].length) (baseStart_3914899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914899 prefixEnd_3914899 := by exact prefixLift 3914899
  have htrace : WordTrace (prefixWord ++ tailWord_3914899) baseStart_3914899 baseEnd_3914899 := by
    simpa [prefixWord, tailWord_3914899, baseEnd_3914899] using wordTrace_append hprefix tailTrace_3914899
  have hstable : (prefixWord ++ tailWord_3914899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914899).length < 2 ^ (prefixWord ++ tailWord_3914899).sum := by decide
  have hdescent : baseEnd_3914899 < baseStart_3914899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914903 : List Nat := [1, 1, 3, 3, 3, 2, 3, 1, 1, 5]
def baseStart_3914903 : Nat := 118140960795 + 3914903 * 2 ^ 59
def prefixEnd_3914903 : Nat := 4983230072969 + 3 ^ 40 * 3914903 * 2
def baseEnd_3914903 : Nat := 670075651576267219236065

theorem tailTrace_3914903 : CollatzResearch.WordTrace tailWord_3914903 prefixEnd_3914903 670075651576267219236065 := by
  unfold tailWord_3914903
  simp only [CollatzResearch.WordTrace]
  refine ⟨142788242935982518046573363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95192161957321678697715575 142788242935982518046573363)
  ·
    refine ⟨214182364403973777069860045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142788242935982518046573363 214182364403973777069860045)
    ·
      refine ⟨80318386651490166401197517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214182364403973777069860045 80318386651490166401197517)
      ·
        refine ⟨30119394994308812400449069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80318386651490166401197517 30119394994308812400449069)
        ·
          refine ⟨11294773122865804650168401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30119394994308812400449069 11294773122865804650168401)
          ·
            refine ⟨8471079842149353487626301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11294773122865804650168401 8471079842149353487626301)
            ·
              refine ⟨3176654940806007557859863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8471079842149353487626301 3176654940806007557859863)
              ·
                refine ⟨4764982411209011336789795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3176654940806007557859863 4764982411209011336789795)
                ·
                  refine ⟨7147473616813517005184693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4764982411209011336789795 7147473616813517005184693)
                  ·
                    refine ⟨670075651576267219236065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7147473616813517005184693 670075651576267219236065)
                    ·
                      rfl

theorem cell23_3914903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 1, 5].length) (baseStart_3914903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914903 prefixEnd_3914903 := by exact prefixLift 3914903
  have htrace : WordTrace (prefixWord ++ tailWord_3914903) baseStart_3914903 baseEnd_3914903 := by
    simpa [prefixWord, tailWord_3914903, baseEnd_3914903] using wordTrace_append hprefix tailTrace_3914903
  have hstable : (prefixWord ++ tailWord_3914903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914903).length < 2 ^ (prefixWord ++ tailWord_3914903).sum := by decide
  have hdescent : baseEnd_3914903 < baseStart_3914903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914910 : List Nat := [4, 3, 1, 1, 2, 1, 2, 2, 2, 3, 2]
def baseStart_3914910 : Nat := 118140960795 + 3914910 * 2 ^ 59
def prefixEnd_3914910 : Nat := 4983230072969 + 3 ^ 40 * 3914910 * 2
def baseEnd_3914910 : Nat := 2010230549093383130320663

theorem tailTrace_3914910 : CollatzResearch.WordTrace tailWord_3914910 prefixEnd_3914910 2010230549093383130320663 := by
  unfold tailWord_3914910
  simp only [CollatzResearch.WordTrace]
  refine ⟨17848562280869644780259773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95192332164638105494718789 17848562280869644780259773)
  ·
    refine ⟨6693210855326116792597415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17848562280869644780259773 6693210855326116792597415)
    ·
      refine ⟨10039816282989175188896123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6693210855326116792597415 10039816282989175188896123)
      ·
        refine ⟨15059724424483762783344185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10039816282989175188896123 15059724424483762783344185)
        ·
          refine ⟨11294793318362822087508139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15059724424483762783344185 11294793318362822087508139)
          ·
            refine ⟨16942189977544233131262209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11294793318362822087508139 16942189977544233131262209)
            ·
              refine ⟨12706642483158174848446657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16942189977544233131262209 12706642483158174848446657)
              ·
                refine ⟨9529981862368631136334993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12706642483158174848446657 9529981862368631136334993)
                ·
                  refine ⟨7147486396776473352251245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9529981862368631136334993 7147486396776473352251245)
                  ·
                    refine ⟨2680307398791177507094217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7147486396776473352251245 2680307398791177507094217)
                    ·
                      refine ⟨2010230549093383130320663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2680307398791177507094217 2010230549093383130320663)
                      ·
                        rfl

theorem cell23_3914910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_3914910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914910 prefixEnd_3914910 := by exact prefixLift 3914910
  have htrace : WordTrace (prefixWord ++ tailWord_3914910) baseStart_3914910 baseEnd_3914910 := by
    simpa [prefixWord, tailWord_3914910, baseEnd_3914910] using wordTrace_append hprefix tailTrace_3914910
  have hstable : (prefixWord ++ tailWord_3914910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914910).length < 2 ^ (prefixWord ++ tailWord_3914910).sum := by decide
  have hdescent : baseEnd_3914910 < baseStart_3914910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914917 : List Nat := [1, 3, 1, 2, 1, 6, 2, 2, 1, 1, 3]
def baseStart_3914917 : Nat := 118140960795 + 3914917 * 2 ^ 59
def prefixEnd_3914917 : Nat := 4983230072969 + 3 ^ 40 * 3914917 * 2
def baseEnd_3914917 : Nat := 2010234143457964602933131

theorem tailTrace_3914917 : CollatzResearch.WordTrace tailWord_3914917 prefixEnd_3914917 2010234143457964602933131 := by
  unfold tailWord_3914917
  simp only [CollatzResearch.WordTrace]
  refine ⟨142788753557931798437583005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95192502371954532291722003 142788753557931798437583005)
  ·
    refine ⟨53545782584224424414093627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142788753557931798437583005 53545782584224424414093627)
    ·
      refine ⟨80318673876336636621140441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53545782584224424414093627 80318673876336636621140441)
      ·
        refine ⟨60239005407252477465855331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80318673876336636621140441 60239005407252477465855331)
        ·
          refine ⟨90358508110878716198782997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60239005407252477465855331 90358508110878716198782997)
          ·
            refine ⟨4235555067697439821817953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 90358508110878716198782997 4235555067697439821817953)
            ·
              refine ⟨3176666300773079866363465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4235555067697439821817953 3176666300773079866363465)
              ·
                refine ⟨2382499725579809899772599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3176666300773079866363465 2382499725579809899772599)
                ·
                  refine ⟨3573749588369714849658899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2382499725579809899772599 3573749588369714849658899)
                  ·
                    refine ⟨5360624382554572274488349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3573749588369714849658899 5360624382554572274488349)
                    ·
                      refine ⟨2010234143457964602933131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5360624382554572274488349 2010234143457964602933131)
                      ·
                        rfl

theorem cell23_3914917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 2, 1, 1, 3].length) (baseStart_3914917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914917 prefixEnd_3914917 := by exact prefixLift 3914917
  have htrace : WordTrace (prefixWord ++ tailWord_3914917) baseStart_3914917 baseEnd_3914917 := by
    simpa [prefixWord, tailWord_3914917, baseEnd_3914917] using wordTrace_append hprefix tailTrace_3914917
  have hstable : (prefixWord ++ tailWord_3914917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914917).length < 2 ^ (prefixWord ++ tailWord_3914917).sum := by decide
  have hdescent : baseEnd_3914917 < baseStart_3914917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914940 : List Nat := [2, 2, 2, 3, 2, 2, 1, 2, 3, 2, 2]
def baseStart_3914940 : Nat := 118140960795 + 3914940 * 2 ^ 59
def prefixEnd_3914940 : Nat := 4983230072969 + 3 ^ 40 * 3914940 * 2
def baseEnd_3914940 : Nat := 2010245953513018012945525

theorem tailTrace_3914940 : CollatzResearch.WordTrace tailWord_3914940 prefixEnd_3914940 2010245953513018012945525 := by
  unfold tailWord_3914940
  simp only [CollatzResearch.WordTrace]
  refine ⟨71394796218424236682835137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95193061624565648910446849 71394796218424236682835137)
  ·
    refine ⟨53546097163818177512126353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71394796218424236682835137 53546097163818177512126353)
    ·
      refine ⟨40159572872863633134094765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53546097163818177512126353 40159572872863633134094765)
      ·
        refine ⟨15059839827323862425285537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40159572872863633134094765 15059839827323862425285537)
        ·
          refine ⟨11294879870492896818964153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15059839827323862425285537 11294879870492896818964153)
          ·
            refine ⟨8471159902869672614223115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11294879870492896818964153 8471159902869672614223115)
            ·
              refine ⟨12706739854304508921334673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8471159902869672614223115 12706739854304508921334673)
              ·
                refine ⟨9530054890728381691001005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12706739854304508921334673 9530054890728381691001005)
                ·
                  refine ⟨3573770584023143134125377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9530054890728381691001005 3573770584023143134125377)
                  ·
                    refine ⟨2680327938017357350594033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3573770584023143134125377 2680327938017357350594033)
                    ·
                      refine ⟨2010245953513018012945525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2680327938017357350594033 2010245953513018012945525)
                      ·
                        rfl

theorem cell23_3914940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_3914940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914940 prefixEnd_3914940 := by exact prefixLift 3914940
  have htrace : WordTrace (prefixWord ++ tailWord_3914940) baseStart_3914940 baseEnd_3914940 := by
    simpa [prefixWord, tailWord_3914940, baseEnd_3914940] using wordTrace_append hprefix tailTrace_3914940
  have hstable : (prefixWord ++ tailWord_3914940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914940).length < 2 ^ (prefixWord ++ tailWord_3914940).sum := by decide
  have hdescent : baseEnd_3914940 < baseStart_3914940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914957 : List Nat := [1, 6, 2, 2, 1, 1, 1, 3, 1, 1, 4]
def baseStart_3914957 : Nat := 118140960795 + 3914957 * 2 ^ 59
def prefixEnd_3914957 : Nat := 4983230072969 + 3 ^ 40 * 3914957 * 2
def baseEnd_3914957 : Nat := 2010254682684144446432947

theorem tailTrace_3914957 : CollatzResearch.WordTrace tailWord_3914957 prefixEnd_3914957 2010254682684144446432947 := by
  unfold tailWord_3914957
  simp only [CollatzResearch.WordTrace]
  refine ⟨142790212477786885269039125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95193474985191256846026083 142790212477786885269039125)
  ·
    refine ⟨6693291209896260246986209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 142790212477786885269039125 6693291209896260246986209)
    ·
      refine ⟨5019968407422195185239657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6693291209896260246986209 5019968407422195185239657)
      ·
        refine ⟨3764976305566646388929743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5019968407422195185239657 3764976305566646388929743)
        ·
          refine ⟨5647464458349969583394615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3764976305566646388929743 5647464458349969583394615)
          ·
            refine ⟨8471196687524954375091923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5647464458349969583394615 8471196687524954375091923)
            ·
              refine ⟨12706795031287431562637885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8471196687524954375091923 12706795031287431562637885)
              ·
                refine ⟨4765048136732786835989207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12706795031287431562637885 4765048136732786835989207)
                ·
                  refine ⟨7147572205099180253983811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4765048136732786835989207 7147572205099180253983811)
                  ·
                    refine ⟨10721358307648770380975717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7147572205099180253983811 10721358307648770380975717)
                    ·
                      refine ⟨2010254682684144446432947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10721358307648770380975717 2010254682684144446432947)
                      ·
                        rfl

theorem cell23_3914957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_3914957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914957 prefixEnd_3914957 := by exact prefixLift 3914957
  have htrace : WordTrace (prefixWord ++ tailWord_3914957) baseStart_3914957 baseEnd_3914957 := by
    simpa [prefixWord, tailWord_3914957, baseEnd_3914957] using wordTrace_append hprefix tailTrace_3914957
  have hstable : (prefixWord ++ tailWord_3914957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914957).length < 2 ^ (prefixWord ++ tailWord_3914957).sum := by decide
  have hdescent : baseEnd_3914957 < baseStart_3914957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914999 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 5]
def baseStart_3914999 : Nat := 118140960795 + 3914999 * 2 ^ 59
def prefixEnd_3914999 : Nat := 4983230072969 + 3 ^ 40 * 3914999 * 2
def baseEnd_3914999 : Nat := 2010276248871633282107753

theorem tailTrace_3914999 : CollatzResearch.WordTrace tailWord_3914999 prefixEnd_3914999 2010276248871633282107753 := by
  unfold tailWord_3914999
  simp only [CollatzResearch.WordTrace]
  refine ⟨142791744343634726442068051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95194496229089817628045367 142791744343634726442068051)
  ·
    refine ⟨214187616515452089663102077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142791744343634726442068051 214187616515452089663102077)
    ·
      refine ⟨80320356193294533623663279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214187616515452089663102077 80320356193294533623663279)
      ·
        refine ⟨120480534289941800435494919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80320356193294533623663279 120480534289941800435494919)
        ·
          refine ⟨180720801434912700653242379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120480534289941800435494919 180720801434912700653242379)
          ·
            refine ⟨271081202152369050979863569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180720801434912700653242379 271081202152369050979863569)
            ·
              refine ⟨203310901614276788234897677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271081202152369050979863569 203310901614276788234897677)
              ·
                refine ⟨76241588105353795588086629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203310901614276788234897677 76241588105353795588086629)
                ·
                  refine ⟨14295297769753836672766243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76241588105353795588086629 14295297769753836672766243)
                  ·
                    refine ⟨21442946654630755009149365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14295297769753836672766243 21442946654630755009149365)
                    ·
                      refine ⟨2010276248871633282107753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21442946654630755009149365 2010276248871633282107753)
                      ·
                        rfl

theorem cell23_3914999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 5].length) (baseStart_3914999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3914999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3914999 prefixEnd_3914999 := by exact prefixLift 3914999
  have htrace : WordTrace (prefixWord ++ tailWord_3914999) baseStart_3914999 baseEnd_3914999 := by
    simpa [prefixWord, tailWord_3914999, baseEnd_3914999] using wordTrace_append hprefix tailTrace_3914999
  have hstable : (prefixWord ++ tailWord_3914999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914999).length < 2 ^ (prefixWord ++ tailWord_3914999).sum := by decide
  have hdescent : baseEnd_3914999 < baseStart_3914999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915013 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 6, 2, 2]
def baseStart_3915013 : Nat := 118140960795 + 3915013 * 2 ^ 59
def prefixEnd_3915013 : Nat := 4983230072969 + 3 ^ 40 * 3915013 * 2
def baseEnd_3915013 : Nat := 2010283437600796227332689

theorem tailTrace_3915013 : CollatzResearch.WordTrace tailWord_3915013 prefixEnd_3915013 2010283437600796227332689 := by
  unfold tailWord_3915013
  simp only [CollatzResearch.WordTrace]
  refine ⟨142792254965584006833077693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95194836643722671222051795 142792254965584006833077693)
  ·
    refine ⟨53547095612094002562404135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142792254965584006833077693 53547095612094002562404135)
    ·
      refine ⟨80320643418141003843606203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53547095612094002562404135 80320643418141003843606203)
      ·
        refine ⟨120480965127211505765409305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80320643418141003843606203 120480965127211505765409305)
        ·
          refine ⟨90360723845408629324056979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120480965127211505765409305 90360723845408629324056979)
          ·
            refine ⟨135541085768112943986085469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90360723845408629324056979 135541085768112943986085469)
            ·
              refine ⟨50827907163042353994782051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135541085768112943986085469 50827907163042353994782051)
              ·
                refine ⟨76241860744563530992173077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50827907163042353994782051 76241860744563530992173077)
                ·
                  refine ⟨3573837222401415515258113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 76241860744563530992173077 3573837222401415515258113)
                  ·
                    refine ⟨2680377916801061636443585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3573837222401415515258113 2680377916801061636443585)
                    ·
                      refine ⟨2010283437600796227332689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2680377916801061636443585 2010283437600796227332689)
                      ·
                        rfl

theorem cell23_3915013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 6, 2, 2].length) (baseStart_3915013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915013 prefixEnd_3915013 := by exact prefixLift 3915013
  have htrace : WordTrace (prefixWord ++ tailWord_3915013) baseStart_3915013 baseEnd_3915013 := by
    simpa [prefixWord, tailWord_3915013, baseEnd_3915013] using wordTrace_append hprefix tailTrace_3915013
  have hstable : (prefixWord ++ tailWord_3915013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915013).length < 2 ^ (prefixWord ++ tailWord_3915013).sum := by decide
  have hdescent : baseEnd_3915013 < baseStart_3915013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915029 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 1, 1, 9]
def baseStart_3915029 : Nat := 118140960795 + 3915029 * 2 ^ 59
def prefixEnd_3915029 : Nat := 4983230072969 + 3 ^ 40 * 3915029 * 2
def baseEnd_3915029 : Nat := 2010291653291268164732615

theorem tailTrace_3915029 : CollatzResearch.WordTrace tailWord_3915029 prefixEnd_3915029 2010291653291268164732615 := by
  unfold tailWord_3915029
  simp only [CollatzResearch.WordTrace]
  refine ⟨142792838533526041565660141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95195225689017361043773427 142792838533526041565660141)
  ·
    refine ⟨53547314450072265587122553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142792838533526041565660141 53547314450072265587122553)
    ·
      refine ⟨40160485837554199190341915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53547314450072265587122553 40160485837554199190341915)
      ·
        refine ⟨60240728756331298785512873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40160485837554199190341915 60240728756331298785512873)
        ·
          refine ⟨45180546567248474089134655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60240728756331298785512873 45180546567248474089134655)
          ·
            refine ⟨67770819850872711133701983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45180546567248474089134655 67770819850872711133701983)
            ·
              refine ⟨101656229776309066700552975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67770819850872711133701983 101656229776309066700552975)
              ·
                refine ⟨152484344664463600050829463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101656229776309066700552975 152484344664463600050829463)
                ·
                  refine ⟨228726516996695400076244195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152484344664463600050829463 228726516996695400076244195)
                  ·
                    refine ⟨343089775495043100114366293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 228726516996695400076244195 343089775495043100114366293)
                    ·
                      refine ⟨2010291653291268164732615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 343089775495043100114366293 2010291653291268164732615)
                      ·
                        rfl

theorem cell23_3915029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_3915029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915029 prefixEnd_3915029 := by exact prefixLift 3915029
  have htrace : WordTrace (prefixWord ++ tailWord_3915029) baseStart_3915029 baseEnd_3915029 := by
    simpa [prefixWord, tailWord_3915029, baseEnd_3915029] using wordTrace_append hprefix tailTrace_3915029
  have hstable : (prefixWord ++ tailWord_3915029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915029).length < 2 ^ (prefixWord ++ tailWord_3915029).sum := by decide
  have hdescent : baseEnd_3915029 < baseStart_3915029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915036 : List Nat := [2, 2, 3, 1, 1, 1, 5, 1, 7]
def baseStart_3915036 : Nat := 118140960795 + 3915036 * 2 ^ 59
def prefixEnd_3915036 : Nat := 4983230072969 + 3 ^ 40 * 3915036 * 2
def baseEnd_3915036 : Nat := 223366138628427737482787

theorem tailTrace_3915036 : CollatzResearch.WordTrace tailWord_3915036 prefixEnd_3915036 223366138628427737482787 := by
  unfold tailWord_3915036
  simp only [CollatzResearch.WordTrace]
  refine ⟨71396546922250340880582481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95195395896333787840776641 71396546922250340880582481)
  ·
    refine ⟨53547410191687755660436861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71396546922250340880582481 53547410191687755660436861)
    ·
      refine ⟨20080278821882908372663823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53547410191687755660436861 20080278821882908372663823)
      ·
        refine ⟨30120418232824362558995735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20080278821882908372663823 30120418232824362558995735)
        ·
          refine ⟨45180627349236543838493603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30120418232824362558995735 45180627349236543838493603)
          ·
            refine ⟨67770941023854815757740405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45180627349236543838493603 67770941023854815757740405)
            ·
              refine ⟨6353525720986388977288163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67770941023854815757740405 6353525720986388977288163)
              ·
                refine ⟨9530288581479583465932245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6353525720986388977288163 9530288581479583465932245)
                ·
                  refine ⟨223366138628427737482787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9530288581479583465932245 223366138628427737482787)
                  ·
                    rfl

theorem cell23_3915036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 7].length) (baseStart_3915036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915036 prefixEnd_3915036 := by exact prefixLift 3915036
  have htrace : WordTrace (prefixWord ++ tailWord_3915036) baseStart_3915036 baseEnd_3915036 := by
    simpa [prefixWord, tailWord_3915036, baseEnd_3915036] using wordTrace_append hprefix tailTrace_3915036
  have hstable : (prefixWord ++ tailWord_3915036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915036).length < 2 ^ (prefixWord ++ tailWord_3915036).sum := by decide
  have hdescent : baseEnd_3915036 < baseStart_3915036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915094 : List Nat := [5, 2, 3, 1, 1, 1, 1, 1, 2, 2, 4]
def baseStart_3915094 : Nat := 118140960795 + 3915094 * 2 ^ 59
def prefixEnd_3915094 : Nat := 4983230072969 + 3 ^ 40 * 3915094 * 2
def baseEnd_3915094 : Nat := 2010325029533810410419817

theorem tailTrace_3915094 : CollatzResearch.WordTrace tailWord_3915094 prefixEnd_3915094 2010325029533810410419817 := by
  unfold tailWord_3915094
  simp only [CollatzResearch.WordTrace]
  refine ⟨8924700579893159854173521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95196806185527038444517557 8924700579893159854173521)
  ·
    refine ⟨6693525434919869890630141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8924700579893159854173521 6693525434919869890630141)
    ·
      refine ⟨2510072038094951208986303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6693525434919869890630141 2510072038094951208986303)
      ·
        refine ⟨3765108057142426813479455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2510072038094951208986303 3765108057142426813479455)
        ·
          refine ⟨5647662085713640220219183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3765108057142426813479455 5647662085713640220219183)
          ·
            refine ⟨8471493128570460330328775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5647662085713640220219183 8471493128570460330328775)
            ·
              refine ⟨12707239692855690495493163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8471493128570460330328775 12707239692855690495493163)
              ·
                refine ⟨19060859539283535743239745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12707239692855690495493163 19060859539283535743239745)
                ·
                  refine ⟨14295644654462651807429809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19060859539283535743239745 14295644654462651807429809)
                  ·
                    refine ⟨10721733490846988855572357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14295644654462651807429809 10721733490846988855572357)
                    ·
                      refine ⟨2010325029533810410419817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10721733490846988855572357 2010325029533810410419817)
                      ·
                        rfl

theorem cell23_3915094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_3915094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915094 prefixEnd_3915094 := by exact prefixLift 3915094
  have htrace : WordTrace (prefixWord ++ tailWord_3915094) baseStart_3915094 baseEnd_3915094 := by
    simpa [prefixWord, tailWord_3915094, baseEnd_3915094] using wordTrace_append hprefix tailTrace_3915094
  have hstable : (prefixWord ++ tailWord_3915094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915094).length < 2 ^ (prefixWord ++ tailWord_3915094).sum := by decide
  have hdescent : baseEnd_3915094 < baseStart_3915094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915136 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 3]
def baseStart_3915136 : Nat := 118140960795 + 3915136 * 2 ^ 59
def prefixEnd_3915136 : Nat := 4983230072969 + 3 ^ 40 * 3915136 * 2
def baseEnd_3915136 : Nat := 2010346595721299246094623

theorem tailTrace_3915136 : CollatzResearch.WordTrace tailWord_3915136 prefixEnd_3915136 2010346595721299246094623 := by
  unfold tailWord_3915136
  simp only [CollatzResearch.WordTrace]
  refine ⟨71398370572069199419902631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95197827429425599226536841 71398370572069199419902631)
  ·
    refine ⟨107097555858103799129853947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71398370572069199419902631 107097555858103799129853947)
    ·
      refine ⟨160646333787155698694780921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107097555858103799129853947 160646333787155698694780921)
      ·
        refine ⟨120484750340366774021085691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160646333787155698694780921 120484750340366774021085691)
        ·
          refine ⟨180727125510550161031628537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120484750340366774021085691 180727125510550161031628537)
          ·
            refine ⟨135545344132912620773721403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180727125510550161031628537 135545344132912620773721403)
            ·
              refine ⟨203318016199368931160582105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135545344132912620773721403 203318016199368931160582105)
              ·
                refine ⟨152488512149526698370436579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203318016199368931160582105 152488512149526698370436579)
                ·
                  refine ⟨228732768224290047555654869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152488512149526698370436579 228732768224290047555654869)
                  ·
                    refine ⟨5360924255256797989585661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 228732768224290047555654869 5360924255256797989585661)
                    ·
                      refine ⟨2010346595721299246094623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5360924255256797989585661 2010346595721299246094623)
                      ·
                        rfl

theorem cell23_3915136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 3].length) (baseStart_3915136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915136 prefixEnd_3915136 := by exact prefixLift 3915136
  have htrace : WordTrace (prefixWord ++ tailWord_3915136) baseStart_3915136 baseEnd_3915136 := by
    simpa [prefixWord, tailWord_3915136, baseEnd_3915136] using wordTrace_append hprefix tailTrace_3915136
  have hstable : (prefixWord ++ tailWord_3915136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915136).length < 2 ^ (prefixWord ++ tailWord_3915136).sum := by decide
  have hdescent : baseEnd_3915136 < baseStart_3915136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915143 : List Nat := [1, 1, 4, 2, 2, 2, 3, 2, 6]
def baseStart_3915143 : Nat := 118140960795 + 3915143 * 2 ^ 59
def prefixEnd_3915143 : Nat := 4983230072969 + 3 ^ 40 * 3915143 * 2
def baseEnd_3915143 : Nat := 223372243342875635411899

theorem tailTrace_3915143 : CollatzResearch.WordTrace tailWord_3915143 prefixEnd_3915143 223372243342875635411899 := by
  unfold tailWord_3915143
  simp only [CollatzResearch.WordTrace]
  refine ⟨142796996455113039035310083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95197997636742026023540055 142796996455113039035310083)
  ·
    refine ⟨214195494682669558552965125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142796996455113039035310083 214195494682669558552965125)
    ·
      refine ⟨40161655253000542228680961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214195494682669558552965125 40161655253000542228680961)
      ·
        refine ⟨30121241439750406671510721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40161655253000542228680961 30121241439750406671510721)
        ·
          refine ⟨22590931079812805003633041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30121241439750406671510721 22590931079812805003633041)
          ·
            refine ⟨16943198309859603752724781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22590931079812805003633041 16943198309859603752724781)
            ·
              refine ⟨6353699366197351407271793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16943198309859603752724781 6353699366197351407271793)
              ·
                refine ⟨4765274524648013555453845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6353699366197351407271793 4765274524648013555453845)
                ·
                  refine ⟨223372243342875635411899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4765274524648013555453845 223372243342875635411899)
                  ·
                    rfl

theorem cell23_3915143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 6].length) (baseStart_3915143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915143 prefixEnd_3915143 := by exact prefixLift 3915143
  have htrace : WordTrace (prefixWord ++ tailWord_3915143) baseStart_3915143 baseEnd_3915143 := by
    simpa [prefixWord, tailWord_3915143, baseEnd_3915143] using wordTrace_append hprefix tailTrace_3915143
  have hstable : (prefixWord ++ tailWord_3915143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915143).length < 2 ^ (prefixWord ++ tailWord_3915143).sum := by decide
  have hdescent : baseEnd_3915143 < baseStart_3915143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915153 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 7, 1, 3]
def baseStart_3915153 : Nat := 118140960795 + 3915153 * 2 ^ 59
def prefixEnd_3915153 : Nat := 4983230072969 + 3 ^ 40 * 3915153 * 2
def baseEnd_3915153 : Nat := 2010355324892425679582045

theorem tailTrace_3915153 : CollatzResearch.WordTrace tailWord_3915153 prefixEnd_3915153 2010355324892425679582045 := by
  unfold tailWord_3915153
  simp only [CollatzResearch.WordTrace]
  refine ⟨142797361185076810743174113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95198240790051207162116075 142797361185076810743174113)
  ·
    refine ⟨107098020888807608057380585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142797361185076810743174113 107098020888807608057380585)
    ·
      refine ⟨80323515666605706043035439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107098020888807608057380585 80323515666605706043035439)
      ·
        refine ⟨120485273499908559064553159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80323515666605706043035439 120485273499908559064553159)
        ·
          refine ⟨180727910249862838596829739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120485273499908559064553159 180727910249862838596829739)
          ·
            refine ⟨271091865374794257895244609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180727910249862838596829739 271091865374794257895244609)
            ·
              refine ⟨203318899031095693421433457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271091865374794257895244609 203318899031095693421433457)
              ·
                refine ⟨152489174273321770066075093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203318899031095693421433457 152489174273321770066075093)
                ·
                  refine ⟨3573965022030978985923635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 152489174273321770066075093 3573965022030978985923635)
                  ·
                    refine ⟨5360947533046468478885453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3573965022030978985923635 5360947533046468478885453)
                    ·
                      refine ⟨2010355324892425679582045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5360947533046468478885453 2010355324892425679582045)
                      ·
                        rfl

theorem cell23_3915153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 7, 1, 3].length) (baseStart_3915153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915153 prefixEnd_3915153 := by exact prefixLift 3915153
  have htrace : WordTrace (prefixWord ++ tailWord_3915153) baseStart_3915153 baseEnd_3915153 := by
    simpa [prefixWord, tailWord_3915153, baseEnd_3915153] using wordTrace_append hprefix tailTrace_3915153
  have hstable : (prefixWord ++ tailWord_3915153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915153).length < 2 ^ (prefixWord ++ tailWord_3915153).sum := by decide
  have hdescent : baseEnd_3915153 < baseStart_3915153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915203 : List Nat := [1, 1, 1, 3, 1, 1, 6, 1, 4, 4]
def baseStart_3915203 : Nat := 118140960795 + 3915203 * 2 ^ 59
def prefixEnd_3915203 : Nat := 4983230072969 + 3 ^ 40 * 3915203 * 2
def baseEnd_3915203 : Nat := 670126999641716827985605

theorem tailTrace_3915203 : CollatzResearch.WordTrace tailWord_3915203 prefixEnd_3915203 670126999641716827985605 := by
  unfold tailWord_3915203
  simp only [CollatzResearch.WordTrace]
  refine ⟨142799184834895669282494263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95199456556597112854996175 142799184834895669282494263)
  ·
    refine ⟨214198777252343503923741395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142799184834895669282494263 214198777252343503923741395)
    ·
      refine ⟨321298165878515255885612093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214198777252343503923741395 321298165878515255885612093)
      ·
        refine ⟨120486812204443220957104535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321298165878515255885612093 120486812204443220957104535)
        ·
          refine ⟨180730218306664831435656803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120486812204443220957104535 180730218306664831435656803)
          ·
            refine ⟨271095327459997247153485205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180730218306664831435656803 271095327459997247153485205)
            ·
              refine ⟨12707593474687370960319619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 271095327459997247153485205 12707593474687370960319619)
              ·
                refine ⟨19061390212031056440479429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12707593474687370960319619 19061390212031056440479429)
                ·
                  refine ⟨3574010664755823082589893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19061390212031056440479429 3574010664755823082589893)
                  ·
                    refine ⟨670126999641716827985605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3574010664755823082589893 670126999641716827985605)
                    ·
                      rfl

theorem cell23_3915203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 4, 4].length) (baseStart_3915203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915203 prefixEnd_3915203 := by exact prefixLift 3915203
  have htrace : WordTrace (prefixWord ++ tailWord_3915203) baseStart_3915203 baseEnd_3915203 := by
    simpa [prefixWord, tailWord_3915203, baseEnd_3915203] using wordTrace_append hprefix tailTrace_3915203
  have hstable : (prefixWord ++ tailWord_3915203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915203).length < 2 ^ (prefixWord ++ tailWord_3915203).sum := by decide
  have hdescent : baseEnd_3915203 < baseStart_3915203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915204 : List Nat := [2, 3, 3, 2, 1, 3, 1, 1, 3, 1, 3]
def baseStart_3915204 : Nat := 118140960795 + 3915204 * 2 ^ 59
def prefixEnd_3915204 : Nat := 4983230072969 + 3 ^ 40 * 3915204 * 2
def baseEnd_3915204 : Nat := 2010381512405804980044311

theorem tailTrace_3915204 : CollatzResearch.WordTrace tailWord_3915204 prefixEnd_3915204 2010381512405804980044311 := by
  unfold tailWord_3915204
  simp only [CollatzResearch.WordTrace]
  refine ⟨71399610653946023226640333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95199480871928030968853777 71399610653946023226640333)
  ·
    refine ⟨26774853995229758709990125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71399610653946023226640333 26774853995229758709990125)
    ·
      refine ⟨10040570248211159516246297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26774853995229758709990125 10040570248211159516246297)
      ·
        refine ⟨7530427686158369637184723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10040570248211159516246297 7530427686158369637184723)
        ·
          refine ⟨11295641529237554455777085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7530427686158369637184723 11295641529237554455777085)
          ·
            refine ⟨4235865573464082920916407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11295641529237554455777085 4235865573464082920916407)
            ·
              refine ⟨6353798360196124381374611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4235865573464082920916407 6353798360196124381374611)
              ·
                refine ⟨9530697540294186572061917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6353798360196124381374611 9530697540294186572061917)
                ·
                  refine ⟨3574011577610319964523219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9530697540294186572061917 3574011577610319964523219)
                  ·
                    refine ⟨5361017366415479946784829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3574011577610319964523219 5361017366415479946784829)
                    ·
                      refine ⟨2010381512405804980044311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5361017366415479946784829 2010381512405804980044311)
                      ·
                        rfl

theorem cell23_3915204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_3915204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915204 prefixEnd_3915204 := by exact prefixLift 3915204
  have htrace : WordTrace (prefixWord ++ tailWord_3915204) baseStart_3915204 baseEnd_3915204 := by
    simpa [prefixWord, tailWord_3915204, baseEnd_3915204] using wordTrace_append hprefix tailTrace_3915204
  have hstable : (prefixWord ++ tailWord_3915204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915204).length < 2 ^ (prefixWord ++ tailWord_3915204).sum := by decide
  have hdescent : baseEnd_3915204 < baseStart_3915204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915260 : List Nat := [2, 2, 2, 1, 2, 1, 2, 3, 4, 1, 3]
def baseStart_3915260 : Nat := 118140960795 + 3915260 * 2 ^ 59
def prefixEnd_3915260 : Nat := 4983230072969 + 3 ^ 40 * 3915260 * 2
def baseEnd_3915260 : Nat := 2010410267322456760944053

theorem tailTrace_3915260 : CollatzResearch.WordTrace tailWord_3915260 prefixEnd_3915260 2010410267322456760944053 := by
  unfold tailWord_3915260
  simp only [CollatzResearch.WordTrace]
  refine ⟨71400631897844584008659617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95200842530459445344879489 71400631897844584008659617)
  ·
    refine ⟨53550473923383438006494713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71400631897844584008659617 53550473923383438006494713)
    ·
      refine ⟨40162855442537578504871035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53550473923383438006494713 40162855442537578504871035)
      ·
        refine ⟨60244283163806367757306553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40162855442537578504871035 60244283163806367757306553)
        ·
          refine ⟨45183212372854775817979915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60244283163806367757306553 45183212372854775817979915)
          ·
            refine ⟨67774818559282163726969873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45183212372854775817979915 67774818559282163726969873)
            ·
              refine ⟨50831113919461622795227405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67774818559282163726969873 50831113919461622795227405)
              ·
                refine ⟨19061667719798108548210277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50831113919461622795227405 19061667719798108548210277)
                ·
                  refine ⟨3574062697462145352789427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19061667719798108548210277 3574062697462145352789427)
                  ·
                    refine ⟨5361094046193218029184141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3574062697462145352789427 5361094046193218029184141)
                    ·
                      refine ⟨2010410267322456760944053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5361094046193218029184141 2010410267322456760944053)
                      ·
                        rfl

theorem cell23_3915260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 4, 1, 3].length) (baseStart_3915260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915260 prefixEnd_3915260 := by exact prefixLift 3915260
  have htrace : WordTrace (prefixWord ++ tailWord_3915260) baseStart_3915260 baseEnd_3915260 := by
    simpa [prefixWord, tailWord_3915260, baseEnd_3915260] using wordTrace_append hprefix tailTrace_3915260
  have hstable : (prefixWord ++ tailWord_3915260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915260).length < 2 ^ (prefixWord ++ tailWord_3915260).sum := by decide
  have hdescent : baseEnd_3915260 < baseStart_3915260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915261 : List Nat := [1, 4, 1, 1, 1, 4, 4, 2, 1, 2, 2]
def baseStart_3915261 : Nat := 118140960795 + 3915261 * 2 ^ 59
def prefixEnd_3915261 : Nat := 4983230072969 + 3 ^ 40 * 3915261 * 2
def baseEnd_3915261 : Nat := 2010410780803111257031549

theorem tailTrace_3915261 : CollatzResearch.WordTrace tailWord_3915261 prefixEnd_3915261 2010410780803111257031549 := by
  unfold tailWord_3915261
  simp only [CollatzResearch.WordTrace]
  refine ⟨142801300268685545188105637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95200866845790363458737091 142801300268685545188105637)
  ·
    refine ⟨26775243800378539722769807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142801300268685545188105637 26775243800378539722769807)
    ·
      refine ⟨40162865700567809584154711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26775243800378539722769807 40162865700567809584154711)
      ·
        refine ⟨60244298550851714376232067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40162865700567809584154711 60244298550851714376232067)
        ·
          refine ⟨90366447826277571564348101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60244298550851714376232067 90366447826277571564348101)
          ·
            refine ⟨16943708967427044668315269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90366447826277571564348101 16943708967427044668315269)
            ·
              refine ⟨3176945431392570875309113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16943708967427044668315269 3176945431392570875309113)
              ·
                refine ⟨2382709073544428156481835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3176945431392570875309113 2382709073544428156481835)
                ·
                  refine ⟨3574063610316642234722753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2382709073544428156481835 3574063610316642234722753)
                  ·
                    refine ⟨2680547707737481676042065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3574063610316642234722753 2680547707737481676042065)
                    ·
                      refine ⟨2010410780803111257031549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2680547707737481676042065 2010410780803111257031549)
                      ·
                        rfl

theorem cell23_3915261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 2, 1, 2, 2].length) (baseStart_3915261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915261 prefixEnd_3915261 := by exact prefixLift 3915261
  have htrace : WordTrace (prefixWord ++ tailWord_3915261) baseStart_3915261 baseEnd_3915261 := by
    simpa [prefixWord, tailWord_3915261, baseEnd_3915261] using wordTrace_append hprefix tailTrace_3915261
  have hstable : (prefixWord ++ tailWord_3915261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915261).length < 2 ^ (prefixWord ++ tailWord_3915261).sum := by decide
  have hdescent : baseEnd_3915261 < baseStart_3915261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915293 : List Nat := [1, 4, 2, 2, 1, 1, 1, 2, 1, 8]
def baseStart_3915293 : Nat := 118140960795 + 3915293 * 2 ^ 59
def prefixEnd_3915293 : Nat := 4983230072969 + 3 ^ 40 * 3915293 * 2
def baseEnd_3915293 : Nat := 670142404061351710610467

theorem tailTrace_3915293 : CollatzResearch.WordTrace tailWord_3915293 prefixEnd_3915293 670142404061351710610467 := by
  unfold tailWord_3915293
  simp only [CollatzResearch.WordTrace]
  refine ⟨142802467404569614653270533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95201644936379743102180355 142802467404569614653270533)
  ·
    refine ⟨26775462638356802747488225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142802467404569614653270533 26775462638356802747488225)
    ·
      refine ⟨20081596978767602060616169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26775462638356802747488225 20081596978767602060616169)
      ·
        refine ⟨15061197734075701545462127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20081596978767602060616169 15061197734075701545462127)
        ·
          refine ⟨22591796601113552318193191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15061197734075701545462127 22591796601113552318193191)
          ·
            refine ⟨33887694901670328477289787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22591796601113552318193191 33887694901670328477289787)
            ·
              refine ⟨50831542352505492715934681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33887694901670328477289787 50831542352505492715934681)
              ·
                refine ⟨38123656764379119536951011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50831542352505492715934681 38123656764379119536951011)
                ·
                  refine ⟨57185485146568679305426517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38123656764379119536951011 57185485146568679305426517)
                  ·
                    refine ⟨670142404061351710610467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57185485146568679305426517 670142404061351710610467)
                    ·
                      rfl

theorem cell23_3915293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_3915293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915293 prefixEnd_3915293 := by exact prefixLift 3915293
  have htrace : WordTrace (prefixWord ++ tailWord_3915293) baseStart_3915293 baseEnd_3915293 := by
    simpa [prefixWord, tailWord_3915293, baseEnd_3915293] using wordTrace_append hprefix tailTrace_3915293
  have hstable : (prefixWord ++ tailWord_3915293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915293).length < 2 ^ (prefixWord ++ tailWord_3915293).sum := by decide
  have hdescent : baseEnd_3915293 < baseStart_3915293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915310 : List Nat := [4, 1, 3, 1, 2, 1, 1, 2, 2, 6]
def baseStart_3915310 : Nat := 118140960795 + 3915310 * 2 ^ 59
def prefixEnd_3915310 : Nat := 4983230072969 + 3 ^ 40 * 3915310 * 2
def baseEnd_3915310 : Nat := 670145313785060521772941

theorem tailTrace_3915310 : CollatzResearch.WordTrace tailWord_3915310 prefixEnd_3915310 670145313785060521772941 := by
  unfold tailWord_3915310
  simp only [CollatzResearch.WordTrace]
  refine ⟨17850385930688503319579923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95202058297005351037759589 17850385930688503319579923)
  ·
    refine ⟨26775578896032754979369885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17850385930688503319579923 26775578896032754979369885)
    ·
      refine ⟨10040842086012283117263707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26775578896032754979369885 10040842086012283117263707)
      ·
        refine ⟨15061263129018424675895561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10040842086012283117263707 15061263129018424675895561)
        ·
          refine ⟨11295947346763818506921671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15061263129018424675895561 11295947346763818506921671)
          ·
            refine ⟨16943921020145727760382507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11295947346763818506921671 16943921020145727760382507)
            ·
              refine ⟨25415881530218591640573761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16943921020145727760382507 25415881530218591640573761)
              ·
                refine ⟨19061911147663943730430321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25415881530218591640573761 19061911147663943730430321)
                ·
                  refine ⟨14296433360747957797822741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19061911147663943730430321 14296433360747957797822741)
                  ·
                    refine ⟨670145313785060521772941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14296433360747957797822741 670145313785060521772941)
                    ·
                      rfl

theorem cell23_3915310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_3915310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915310 prefixEnd_3915310 := by exact prefixLift 3915310
  have htrace : WordTrace (prefixWord ++ tailWord_3915310) baseStart_3915310 baseEnd_3915310 := by
    simpa [prefixWord, tailWord_3915310, baseEnd_3915310] using wordTrace_append hprefix tailTrace_3915310
  have hstable : (prefixWord ++ tailWord_3915310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915310).length < 2 ^ (prefixWord ++ tailWord_3915310).sum := by decide
  have hdescent : baseEnd_3915310 < baseStart_3915310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915353 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 6, 5]
def baseStart_3915353 : Nat := 118140960795 + 3915353 * 2 ^ 59
def prefixEnd_3915353 : Nat := 4983230072969 + 3 ^ 40 * 3915353 * 2
def baseEnd_3915353 : Nat := 670152673674441632360375

theorem tailTrace_3915353 : CollatzResearch.WordTrace tailWord_3915353 prefixEnd_3915353 670152673674441632360375 := by
  unfold tailWord_3915353
  simp only [CollatzResearch.WordTrace]
  refine ⟨142804655784352244900454713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95203103856234829933636475 142804655784352244900454713)
  ·
    refine ⟨107103491838264183675341035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142804655784352244900454713 107103491838264183675341035)
    ·
      refine ⟨160655237757396275513011553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107103491838264183675341035 160655237757396275513011553)
      ·
        refine ⟨120491428318047206634758665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160655237757396275513011553 120491428318047206634758665)
        ·
          refine ⟨90368571238535404976068999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120491428318047206634758665 90368571238535404976068999)
          ·
            refine ⟨135552856857803107464103499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90368571238535404976068999 135552856857803107464103499)
            ·
              refine ⟨203329285286704661196155249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135552856857803107464103499 203329285286704661196155249)
              ·
                refine ⟨152496963965028495897116437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203329285286704661196155249 152496963965028495897116437)
                ·
                  refine ⟨7148295185860710745177333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 152496963965028495897116437 7148295185860710745177333)
                  ·
                    refine ⟨670152673674441632360375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7148295185860710745177333 670152673674441632360375)
                    ·
                      rfl

theorem cell23_3915353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 5].length) (baseStart_3915353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915353 prefixEnd_3915353 := by exact prefixLift 3915353
  have htrace : WordTrace (prefixWord ++ tailWord_3915353) baseStart_3915353 baseEnd_3915353 := by
    simpa [prefixWord, tailWord_3915353, baseEnd_3915353] using wordTrace_append hprefix tailTrace_3915353
  have hstable : (prefixWord ++ tailWord_3915353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915353).length < 2 ^ (prefixWord ++ tailWord_3915353).sum := by decide
  have hdescent : baseEnd_3915353 < baseStart_3915353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915360 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 1, 7, 2]
def baseStart_3915360 : Nat := 118140960795 + 3915360 * 2 ^ 59
def prefixEnd_3915360 : Nat := 4983230072969 + 3 ^ 40 * 3915360 * 2
def baseEnd_3915360 : Nat := 2010461615387906369693593

theorem tailTrace_3915360 : CollatzResearch.WordTrace tailWord_3915360 prefixEnd_3915360 2010461615387906369693593 := by
  unfold tailWord_3915360
  simp only [CollatzResearch.WordTrace]
  refine ⟨71402455547663442547979767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95203274063551256730639689 71402455547663442547979767)
  ·
    refine ⟨107103683321495163821969651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71402455547663442547979767 107103683321495163821969651)
    ·
      refine ⟨160655524982242745732954477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107103683321495163821969651 160655524982242745732954477)
      ·
        refine ⟨60245821868341029649857929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160655524982242745732954477 60245821868341029649857929)
        ·
          refine ⟨45184366401255772237393447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60245821868341029649857929 45184366401255772237393447)
          ·
            refine ⟨67776549601883658356090171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45184366401255772237393447 67776549601883658356090171)
            ·
              refine ⟨101664824402825487534135257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67776549601883658356090171 101664824402825487534135257)
              ·
                refine ⟨76248618302119115650601443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101664824402825487534135257 76248618302119115650601443)
                ·
                  refine ⟨114372927453178673475902165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76248618302119115650601443 114372927453178673475902165)
                  ·
                    refine ⟨2680615487183875159591457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 114372927453178673475902165 2680615487183875159591457)
                    ·
                      refine ⟨2010461615387906369693593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2680615487183875159591457 2010461615387906369693593)
                      ·
                        rfl

theorem cell23_3915360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 1, 7, 2].length) (baseStart_3915360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915360 prefixEnd_3915360 := by exact prefixLift 3915360
  have htrace : WordTrace (prefixWord ++ tailWord_3915360) baseStart_3915360 baseEnd_3915360 := by
    simpa [prefixWord, tailWord_3915360, baseEnd_3915360] using wordTrace_append hprefix tailTrace_3915360
  have hstable : (prefixWord ++ tailWord_3915360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915360).length < 2 ^ (prefixWord ++ tailWord_3915360).sum := by decide
  have hdescent : baseEnd_3915360 < baseStart_3915360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915370 : List Nat := [3, 1, 3, 2, 1, 2, 1, 1, 4, 5]
def baseStart_3915370 : Nat := 118140960795 + 3915370 * 2 ^ 59
def prefixEnd_3915370 : Nat := 4983230072969 + 3 ^ 40 * 3915370 * 2
def baseEnd_3915370 : Nat := 670155583398150443522849

theorem tailTrace_3915370 : CollatzResearch.WordTrace tailWord_3915370 prefixEnd_3915370 670155583398150443522849 := by
  unfold tailWord_3915370
  simp only [CollatzResearch.WordTrace]
  refine ⟨35701318956322664200955891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95203517216860437869215709 35701318956322664200955891)
  ·
    refine ⟨53551978434483996301433837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35701318956322664200955891 53551978434483996301433837)
    ·
      refine ⟨20081991912931498613037689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53551978434483996301433837 20081991912931498613037689)
      ·
        refine ⟨15061493934698623959778267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20081991912931498613037689 15061493934698623959778267)
        ·
          refine ⟨22592240902047935939667401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15061493934698623959778267 22592240902047935939667401)
          ·
            refine ⟨16944180676535951954750551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22592240902047935939667401 16944180676535951954750551)
            ·
              refine ⟨25416271014803927932125827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16944180676535951954750551 25416271014803927932125827)
              ·
                refine ⟨38124406522205891898188741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25416271014803927932125827 38124406522205891898188741)
                ·
                  refine ⟨7148326222913604730910389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38124406522205891898188741 7148326222913604730910389)
                  ·
                    refine ⟨670155583398150443522849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7148326222913604730910389 670155583398150443522849)
                    ·
                      rfl

theorem cell23_3915370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_3915370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915370 prefixEnd_3915370 := by exact prefixLift 3915370
  have htrace : WordTrace (prefixWord ++ tailWord_3915370) baseStart_3915370 baseEnd_3915370 := by
    simpa [prefixWord, tailWord_3915370, baseEnd_3915370] using wordTrace_append hprefix tailTrace_3915370
  have hstable : (prefixWord ++ tailWord_3915370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915370).length < 2 ^ (prefixWord ++ tailWord_3915370).sum := by decide
  have hdescent : baseEnd_3915370 < baseStart_3915370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915374 : List Nat := [4, 1, 2, 2, 4, 1, 1, 1, 7]
def baseStart_3915374 : Nat := 118140960795 + 3915374 * 2 ^ 59
def prefixEnd_3915374 : Nat := 4983230072969 + 3 ^ 40 * 3915374 * 2
def baseEnd_3915374 : Nat := 223385422679674368324281

theorem tailTrace_3915374 : CollatzResearch.WordTrace tailWord_3915374 prefixEnd_3915374 223385422679674368324281 := by
  unfold tailWord_3915374
  simp only [CollatzResearch.WordTrace]
  refine ⟨17850677714659520685871147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95203614478184110324646117 17850677714659520685871147)
  ·
    refine ⟨26776016571989281028806721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17850677714659520685871147 26776016571989281028806721)
    ·
      refine ⟨20082012428991960771605041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26776016571989281028806721 20082012428991960771605041)
      ·
        refine ⟨15061509321743970578703781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20082012428991960771605041 15061509321743970578703781)
        ·
          refine ⟨2824032997826994483506959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15061509321743970578703781 2824032997826994483506959)
          ·
            refine ⟨4236049496740491725260439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2824032997826994483506959 4236049496740491725260439)
            ·
              refine ⟨6354074245110737587890659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4236049496740491725260439 6354074245110737587890659)
              ·
                refine ⟨9531111367666106381835989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6354074245110737587890659 9531111367666106381835989)
                ·
                  refine ⟨223385422679674368324281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9531111367666106381835989 223385422679674368324281)
                  ·
                    rfl

theorem cell23_3915374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 7].length) (baseStart_3915374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915374 prefixEnd_3915374 := by exact prefixLift 3915374
  have htrace : WordTrace (prefixWord ++ tailWord_3915374) baseStart_3915374 baseEnd_3915374 := by
    simpa [prefixWord, tailWord_3915374, baseEnd_3915374] using wordTrace_append hprefix tailTrace_3915374
  have hstable : (prefixWord ++ tailWord_3915374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915374).length < 2 ^ (prefixWord ++ tailWord_3915374).sum := by decide
  have hdescent : baseEnd_3915374 < baseStart_3915374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915413 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 10]
def baseStart_3915413 : Nat := 118140960795 + 3915413 * 2 ^ 59
def prefixEnd_3915413 : Nat := 4983230072969 + 3 ^ 40 * 3915413 * 2
def baseEnd_3915413 : Nat := 223387647762510518036761

theorem tailTrace_3915413 : CollatzResearch.WordTrace tailWord_3915413 prefixEnd_3915413 223387647762510518036761 := by
  unfold tailWord_3915413
  simp only [CollatzResearch.WordTrace]
  refine ⟨142806844164134875147638893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95204562776089916765092595 142806844164134875147638893)
  ·
    refine ⟨53552566561550578180364585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142806844164134875147638893 53552566561550578180364585)
    ·
      refine ⟨40164424921162933635273439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53552566561550578180364585 40164424921162933635273439)
      ·
        refine ⟨60246637381744400452910159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40164424921162933635273439 60246637381744400452910159)
        ·
          refine ⟨90369956072616600679365239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60246637381744400452910159 90369956072616600679365239)
          ·
            refine ⟨135554934108924901019047859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90369956072616600679365239 135554934108924901019047859)
            ·
              refine ⟨203332401163387351528571789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135554934108924901019047859 203332401163387351528571789)
              ·
                refine ⟨76249650436270256823214421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203332401163387351528571789 76249650436270256823214421)
                ·
                  refine ⟨223387647762510518036761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 76249650436270256823214421 223387647762510518036761)
                  ·
                    rfl

theorem cell23_3915413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 10].length) (baseStart_3915413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915413 prefixEnd_3915413 := by exact prefixLift 3915413
  have htrace : WordTrace (prefixWord ++ tailWord_3915413) baseStart_3915413 baseEnd_3915413 := by
    simpa [prefixWord, tailWord_3915413, baseEnd_3915413] using wordTrace_append hprefix tailTrace_3915413
  have hstable : (prefixWord ++ tailWord_3915413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915413).length < 2 ^ (prefixWord ++ tailWord_3915413).sum := by decide
  have hdescent : baseEnd_3915413 < baseStart_3915413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915491 : List Nat := [1, 1, 1, 7, 2, 1, 2, 1, 3, 1, 3]
def baseStart_3915491 : Nat := 118140960795 + 3915491 * 2 ^ 59
def prefixEnd_3915491 : Nat := 4983230072969 + 3 ^ 40 * 3915491 * 2
def baseEnd_3915491 : Nat := 2010528881353645357155491

theorem tailTrace_3915491 : CollatzResearch.WordTrace tailWord_3915491 prefixEnd_3915491 2010528881353645357155491 := by
  unfold tailWord_3915491
  simp only [CollatzResearch.WordTrace]
  refine ⟨142809689057852294468978327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95206459371901529645985551 142809689057852294468978327)
  ·
    refine ⟨214214533586778441703467491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142809689057852294468978327 214214533586778441703467491)
    ·
      refine ⟨321321800380167662555201237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214214533586778441703467491 321321800380167662555201237)
      ·
        refine ⟨7530979696410179591137529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 321321800380167662555201237 7530979696410179591137529)
        ·
          refine ⟨5648234772307634693353147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7530979696410179591137529 5648234772307634693353147)
          ·
            refine ⟨8472352158461452040029721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5648234772307634693353147 8472352158461452040029721)
            ·
              refine ⟨6354264118846089030022291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8472352158461452040029721 6354264118846089030022291)
              ·
                refine ⟨9531396178269133545033437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6354264118846089030022291 9531396178269133545033437)
                ·
                  refine ⟨3574273566850925079387539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9531396178269133545033437 3574273566850925079387539)
                  ·
                    refine ⟨5361410350276387619081309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3574273566850925079387539 5361410350276387619081309)
                    ·
                      refine ⟨2010528881353645357155491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5361410350276387619081309 2010528881353645357155491)
                      ·
                        rfl

theorem cell23_3915491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_3915491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915491 prefixEnd_3915491 := by exact prefixLift 3915491
  have htrace : WordTrace (prefixWord ++ tailWord_3915491) baseStart_3915491 baseEnd_3915491 := by
    simpa [prefixWord, tailWord_3915491, baseEnd_3915491] using wordTrace_append hprefix tailTrace_3915491
  have hstable : (prefixWord ++ tailWord_3915491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915491).length < 2 ^ (prefixWord ++ tailWord_3915491).sum := by decide
  have hdescent : baseEnd_3915491 < baseStart_3915491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915500 : List Nat := [2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 5]
def baseStart_3915500 : Nat := 118140960795 + 3915500 * 2 ^ 59
def prefixEnd_3915500 : Nat := 4983230072969 + 3 ^ 40 * 3915500 * 2
def baseEnd_3915500 : Nat := 2010533502679535821942949

theorem tailTrace_3915500 : CollatzResearch.WordTrace tailWord_3915500 prefixEnd_3915500 2010533502679535821942949 := by
  unfold tailWord_3915500
  simp only [CollatzResearch.WordTrace]
  refine ⟨71405008657409844503027977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95206678209879792670703969 71405008657409844503027977)
  ·
    refine ⟨53553756493057383377270983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71405008657409844503027977 53553756493057383377270983)
    ·
      refine ⟨80330634739586075065906475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53553756493057383377270983 80330634739586075065906475)
      ·
        refine ⟨120495952109379112598859713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80330634739586075065906475 120495952109379112598859713)
        ·
          refine ⟨90371964082034334449144785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120495952109379112598859713 90371964082034334449144785)
          ·
            refine ⟨67778973061525750836858589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90371964082034334449144785 67778973061525750836858589)
            ·
              refine ⟨25417114898072156563821971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67778973061525750836858589 25417114898072156563821971)
              ·
                refine ⟨38125672347108234845732957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25417114898072156563821971 38125672347108234845732957)
                ·
                  refine ⟨14297127130165588067149859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38125672347108234845732957 14297127130165588067149859)
                  ·
                    refine ⟨21445690695248382100724789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14297127130165588067149859 21445690695248382100724789)
                    ·
                      refine ⟨2010533502679535821942949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21445690695248382100724789 2010533502679535821942949)
                      ·
                        rfl

theorem cell23_3915500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 5].length) (baseStart_3915500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915500 prefixEnd_3915500 := by exact prefixLift 3915500
  have htrace : WordTrace (prefixWord ++ tailWord_3915500) baseStart_3915500 baseEnd_3915500 := by
    simpa [prefixWord, tailWord_3915500, baseEnd_3915500] using wordTrace_append hprefix tailTrace_3915500
  have hstable : (prefixWord ++ tailWord_3915500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915500).length < 2 ^ (prefixWord ++ tailWord_3915500).sum := by decide
  have hdescent : baseEnd_3915500 < baseStart_3915500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915507 : List Nat := [1, 1, 1, 2, 2, 3, 2, 5, 2, 4]
def baseStart_3915507 : Nat := 118140960795 + 3915507 * 2 ^ 59
def prefixEnd_3915507 : Nat := 4983230072969 + 3 ^ 40 * 3915507 * 2
def baseEnd_3915507 : Nat := 670179032348039098185139

theorem tailTrace_3915507 : CollatzResearch.WordTrace tailWord_3915507 prefixEnd_3915507 670179032348039098185139 := by
  unfold tailWord_3915507
  simp only [CollatzResearch.WordTrace]
  refine ⟨142810272625794329201560775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95206848417196219467707183 142810272625794329201560775)
  ·
    refine ⟨214215408938691493802341163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142810272625794329201560775 214215408938691493802341163)
    ·
      refine ⟨321323113408037240703511745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214215408938691493802341163 321323113408037240703511745)
      ·
        refine ⟨240992335056027930527633809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321323113408037240703511745 240992335056027930527633809)
        ·
          refine ⟨180744251292020947895725357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240992335056027930527633809 180744251292020947895725357)
          ·
            refine ⟨67779094234507855460897009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180744251292020947895725357 67779094234507855460897009)
            ·
              refine ⟨50834320675880891595672757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67779094234507855460897009 50834320675880891595672757)
              ·
                refine ⟨4765717563363833587094321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50834320675880891595672757 4765717563363833587094321)
                ·
                  refine ⟨3574288172522875190320741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4765717563363833587094321 3574288172522875190320741)
                  ·
                    refine ⟨670179032348039098185139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3574288172522875190320741 670179032348039098185139)
                    ·
                      rfl

theorem cell23_3915507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 2, 4].length) (baseStart_3915507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915507 prefixEnd_3915507 := by exact prefixLift 3915507
  have htrace : WordTrace (prefixWord ++ tailWord_3915507) baseStart_3915507 baseEnd_3915507 := by
    simpa [prefixWord, tailWord_3915507, baseEnd_3915507] using wordTrace_append hprefix tailTrace_3915507
  have hstable : (prefixWord ++ tailWord_3915507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915507).length < 2 ^ (prefixWord ++ tailWord_3915507).sum := by decide
  have hdescent : baseEnd_3915507 < baseStart_3915507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915508 : List Nat := [2, 6, 1, 1, 1, 1, 2, 2, 3, 1, 3]
def baseStart_3915508 : Nat := 118140960795 + 3915508 * 2 ^ 59
def prefixEnd_3915508 : Nat := 4983230072969 + 3 ^ 40 * 3915508 * 2
def baseEnd_3915508 : Nat := 2010537610524771790642913

theorem tailTrace_3915508 : CollatzResearch.WordTrace tailWord_3915508 prefixEnd_3915508 2010537610524771790642913 := by
  unfold tailWord_3915508
  simp only [CollatzResearch.WordTrace]
  refine ⟨71405154549395353186173589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95206872732527137581564785 71405154549395353186173589)
  ·
    refine ⟨3347116619502907180601887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 71405154549395353186173589 3347116619502907180601887)
    ·
      refine ⟨5020674929254360770902831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3347116619502907180601887 5020674929254360770902831)
      ·
        refine ⟨7531012393881541156354247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5020674929254360770902831 7531012393881541156354247)
        ·
          refine ⟨11296518590822311734531371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7531012393881541156354247 11296518590822311734531371)
          ·
            refine ⟨16944777886233467601797057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11296518590822311734531371 16944777886233467601797057)
            ·
              refine ⟨12708583414675100701347793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16944777886233467601797057 12708583414675100701347793)
              ·
                refine ⟨9531437561006325526010845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12708583414675100701347793 9531437561006325526010845)
                ·
                  refine ⟨3574289085377372072254067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9531437561006325526010845 3574289085377372072254067)
                  ·
                    refine ⟨5361433628066058108381101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3574289085377372072254067 5361433628066058108381101)
                    ·
                      refine ⟨2010537610524771790642913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5361433628066058108381101 2010537610524771790642913)
                      ·
                        rfl

theorem cell23_3915508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_3915508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915508 prefixEnd_3915508 := by exact prefixLift 3915508
  have htrace : WordTrace (prefixWord ++ tailWord_3915508) baseStart_3915508 baseEnd_3915508 := by
    simpa [prefixWord, tailWord_3915508, baseEnd_3915508] using wordTrace_append hprefix tailTrace_3915508
  have hstable : (prefixWord ++ tailWord_3915508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915508).length < 2 ^ (prefixWord ++ tailWord_3915508).sum := by decide
  have hdescent : baseEnd_3915508 < baseStart_3915508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915534 : List Nat := [4, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3]
def baseStart_3915534 : Nat := 118140960795 + 3915534 * 2 ^ 59
def prefixEnd_3915534 : Nat := 4983230072969 + 3 ^ 40 * 3915534 * 2
def baseEnd_3915534 : Nat := 2010550961021788688917793

theorem tailTrace_3915534 : CollatzResearch.WordTrace tailWord_3915534 prefixEnd_3915534 2010550961021788688917793 := by
  unfold tailWord_3915534
  simp only [CollatzResearch.WordTrace]
  refine ⟨17851407174587064101599207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95207504931131008541862437 17851407174587064101599207)
  ·
    refine ⟨26777110761880596152398811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17851407174587064101599207 26777110761880596152398811)
    ·
      refine ⟨40165666142820894228598217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26777110761880596152398811 40165666142820894228598217)
      ·
        refine ⟨30124249607115670671448663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40165666142820894228598217 30124249607115670671448663)
        ·
          refine ⟨45186374410673506007172995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30124249607115670671448663 45186374410673506007172995)
          ·
            refine ⟨67779561616010259010759493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45186374410673506007172995 67779561616010259010759493)
            ·
              refine ⟨12708667803001923564517405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67779561616010259010759493 12708667803001923564517405)
              ·
                refine ⟨4765750426125721336694027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12708667803001923564517405 4765750426125721336694027)
                ·
                  refine ⟨7148625639188582005041041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4765750426125721336694027 7148625639188582005041041)
                  ·
                    refine ⟨5361469229391436503780781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7148625639188582005041041 5361469229391436503780781)
                    ·
                      refine ⟨2010550961021788688917793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5361469229391436503780781 2010550961021788688917793)
                      ·
                        rfl

theorem cell23_3915534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_3915534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915534 prefixEnd_3915534 := by exact prefixLift 3915534
  have htrace : WordTrace (prefixWord ++ tailWord_3915534) baseStart_3915534 baseEnd_3915534 := by
    simpa [prefixWord, tailWord_3915534, baseEnd_3915534] using wordTrace_append hprefix tailTrace_3915534
  have hstable : (prefixWord ++ tailWord_3915534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915534).length < 2 ^ (prefixWord ++ tailWord_3915534).sum := by decide
  have hdescent : baseEnd_3915534 < baseStart_3915534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915600 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 6]
def baseStart_3915600 : Nat := 118140960795 + 3915600 * 2 ^ 59
def prefixEnd_3915600 : Nat := 4983230072969 + 3 ^ 40 * 3915600 * 2
def baseEnd_3915600 : Nat := 2010584850744985430692489

theorem tailTrace_3915600 : CollatzResearch.WordTrace tailWord_3915600 prefixEnd_3915600 2010584850744985430692489 := by
  unfold tailWord_3915600
  simp only [CollatzResearch.WordTrace]
  refine ⟨71406832307228703042348127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95209109742971604056464169 71406832307228703042348127)
  ·
    refine ⟨107110248460843054563522191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71406832307228703042348127 107110248460843054563522191)
    ·
      refine ⟨160665372691264581845283287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107110248460843054563522191 160665372691264581845283287)
      ·
        refine ⟨240998059036896872767924931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160665372691264581845283287 240998059036896872767924931)
        ·
          refine ⟨361497088555345309151887397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240998059036896872767924931 361497088555345309151887397)
          ·
            refine ⟨67780704104127245465978887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 361497088555345309151887397 67780704104127245465978887)
            ·
              refine ⟨101671056156190868198968331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67780704104127245465978887 101671056156190868198968331)
              ·
                refine ⟨152506584234286302298452497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101671056156190868198968331 152506584234286302298452497)
                ·
                  refine ⟨114379938175714726723839373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152506584234286302298452497 114379938175714726723839373)
                  ·
                    refine ⟨42892476815893022521439765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 114379938175714726723839373 42892476815893022521439765)
                    ·
                      refine ⟨2010584850744985430692489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42892476815893022521439765 2010584850744985430692489)
                      ·
                        rfl

theorem cell23_3915600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 6].length) (baseStart_3915600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915600 prefixEnd_3915600 := by exact prefixLift 3915600
  have htrace : WordTrace (prefixWord ++ tailWord_3915600) baseStart_3915600 baseEnd_3915600 := by
    simpa [prefixWord, tailWord_3915600, baseEnd_3915600] using wordTrace_append hprefix tailTrace_3915600
  have hstable : (prefixWord ++ tailWord_3915600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915600).length < 2 ^ (prefixWord ++ tailWord_3915600).sum := by decide
  have hdescent : baseEnd_3915600 < baseStart_3915600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915617 : List Nat := [1, 2, 3, 1, 1, 1, 5, 1, 2, 2, 4]
def baseStart_3915617 : Nat := 118140960795 + 3915617 * 2 ^ 59
def prefixEnd_3915617 : Nat := 4983230072969 + 3 ^ 40 * 3915617 * 2
def baseEnd_3915617 : Nat := 2010593579916111864179911

theorem tailTrace_3915617 : CollatzResearch.WordTrace tailWord_3915617 prefixEnd_3915617 2010593579916111864179911 := by
  unfold tailWord_3915617
  simp only [CollatzResearch.WordTrace]
  refine ⟨142814284655395817988065105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95209523103597211992043403 142814284655395817988065105)
  ·
    refine ⟨107110713491546863491048829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142814284655395817988065105 107110713491546863491048829)
    ·
      refine ⟨40166517559330073809143311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107110713491546863491048829 40166517559330073809143311)
      ·
        refine ⟨60249776338995110713714967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40166517559330073809143311 60249776338995110713714967)
        ·
          refine ⟨90374664508492666070572451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60249776338995110713714967 90374664508492666070572451)
          ·
            refine ⟨135561996762738999105858677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90374664508492666070572451 135561996762738999105858677)
            ·
              refine ⟨12708937196506781166174251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135561996762738999105858677 12708937196506781166174251)
              ·
                refine ⟨19063405794760171749261377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12708937196506781166174251 19063405794760171749261377)
                ·
                  refine ⟨14297554346070128811946033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19063405794760171749261377 14297554346070128811946033)
                  ·
                    refine ⟨10723165759552596608959525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14297554346070128811946033 10723165759552596608959525)
                    ·
                      refine ⟨2010593579916111864179911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10723165759552596608959525 2010593579916111864179911)
                      ·
                        rfl

theorem cell23_3915617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_3915617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915617 prefixEnd_3915617 := by exact prefixLift 3915617
  have htrace : WordTrace (prefixWord ++ tailWord_3915617) baseStart_3915617 baseEnd_3915617 := by
    simpa [prefixWord, tailWord_3915617, baseEnd_3915617] using wordTrace_append hprefix tailTrace_3915617
  have hstable : (prefixWord ++ tailWord_3915617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915617).length < 2 ^ (prefixWord ++ tailWord_3915617).sum := by decide
  have hdescent : baseEnd_3915617 < baseStart_3915617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915655 : List Nat := [1, 1, 4, 2, 4, 2, 1, 2, 2, 2, 2]
def baseStart_3915655 : Nat := 118140960795 + 3915655 * 2 ^ 59
def prefixEnd_3915655 : Nat := 4983230072969 + 3 ^ 40 * 3915655 * 2
def baseEnd_3915655 : Nat := 2010613092180982715504737

theorem tailTrace_3915655 : CollatzResearch.WordTrace tailWord_3915655 prefixEnd_3915655 2010613092180982715504737 := by
  unfold tailWord_3915655
  simp only [CollatzResearch.WordTrace]
  refine ⟨142815670629258150477948419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95210447086172100318632279 142815670629258150477948419)
  ·
    refine ⟨214223505943887225716922629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142815670629258150477948419 214223505943887225716922629)
    ·
      refine ⟨40166907364478854821922993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214223505943887225716922629 40166907364478854821922993)
      ·
        refine ⟨30125180523359141116442245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40166907364478854821922993 30125180523359141116442245)
        ·
          refine ⟨5648471348129838959332921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30125180523359141116442245 5648471348129838959332921)
          ·
            refine ⟨4236353511097379219499691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5648471348129838959332921 4236353511097379219499691)
            ·
              refine ⟨6354530266646068829249537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4236353511097379219499691 6354530266646068829249537)
              ·
                refine ⟨4765897699984551621937153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6354530266646068829249537 4765897699984551621937153)
                ·
                  refine ⟨3574423274988413716452865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4765897699984551621937153 3574423274988413716452865)
                  ·
                    refine ⟨2680817456241310287339649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3574423274988413716452865 2680817456241310287339649)
                    ·
                      refine ⟨2010613092180982715504737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2680817456241310287339649 2010613092180982715504737)
                      ·
                        rfl

theorem cell23_3915655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_3915655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915655 prefixEnd_3915655 := by exact prefixLift 3915655
  have htrace : WordTrace (prefixWord ++ tailWord_3915655) baseStart_3915655 baseEnd_3915655 := by
    simpa [prefixWord, tailWord_3915655, baseEnd_3915655] using wordTrace_append hprefix tailTrace_3915655
  have hstable : (prefixWord ++ tailWord_3915655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915655).length < 2 ^ (prefixWord ++ tailWord_3915655).sum := by decide
  have hdescent : baseEnd_3915655 < baseStart_3915655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915657 : List Nat := [1, 2, 1, 1, 5, 1, 2, 1, 4, 5]
def baseStart_3915657 : Nat := 118140960795 + 3915657 * 2 ^ 59
def prefixEnd_3915657 : Nat := 4983230072969 + 3 ^ 40 * 3915657 * 2
def baseEnd_3915657 : Nat := 670204706380763902559909

theorem tailTrace_3915657 : CollatzResearch.WordTrace tailWord_3915657 prefixEnd_3915657 670204706380763902559909 := by
  unfold tailWord_3915657
  simp only [CollatzResearch.WordTrace]
  refine ⟨142815743575250904819521225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95210495716833936546347483 142815743575250904819521225)
  ·
    refine ⟨107111807681438178614640919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142815743575250904819521225 107111807681438178614640919)
    ·
      refine ⟨160667711522157267921961379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107111807681438178614640919 160667711522157267921961379)
      ·
        refine ⟨241001567283235901882942069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160667711522157267921961379 241001567283235901882942069)
        ·
          refine ⟨22593896932803365801525819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 241001567283235901882942069 22593896932803365801525819)
          ·
            refine ⟨33890845399205048702288729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22593896932803365801525819 33890845399205048702288729)
            ·
              refine ⟨25418134049403786526716547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33890845399205048702288729 25418134049403786526716547)
              ·
                refine ⟨38127201074105679790074821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25418134049403786526716547 38127201074105679790074821)
                ·
                  refine ⟨7148850201394814960639029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38127201074105679790074821 7148850201394814960639029)
                  ·
                    refine ⟨670204706380763902559909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7148850201394814960639029 670204706380763902559909)
                    ·
                      rfl

theorem cell23_3915657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 5].length) (baseStart_3915657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915657 prefixEnd_3915657 := by exact prefixLift 3915657
  have htrace : WordTrace (prefixWord ++ tailWord_3915657) baseStart_3915657 baseEnd_3915657 := by
    simpa [prefixWord, tailWord_3915657, baseEnd_3915657] using wordTrace_append hprefix tailTrace_3915657
  have hstable : (prefixWord ++ tailWord_3915657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915657).length < 2 ^ (prefixWord ++ tailWord_3915657).sum := by decide
  have hdescent : baseEnd_3915657 < baseStart_3915657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915672 : List Nat := [2, 1, 2, 6, 1, 1, 3, 1, 2, 2, 2]
def baseStart_3915672 : Nat := 118140960795 + 3915672 * 2 ^ 59
def prefixEnd_3915672 : Nat := 4983230072969 + 3 ^ 40 * 3915672 * 2
def baseEnd_3915672 : Nat := 2010621821352109148992159

theorem tailTrace_3915672 : CollatzResearch.WordTrace tailWord_3915672 prefixEnd_3915672 2010621821352109148992159 := by
  unfold tailWord_3915672
  simp only [CollatzResearch.WordTrace]
  refine ⟨71408145335098281190658635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95210860446797708254211513 71408145335098281190658635)
  ·
    refine ⟨107112218002647421785987953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71408145335098281190658635 107112218002647421785987953)
    ·
      refine ⟨80334163501985566339490965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107112218002647421785987953 80334163501985566339490965)
      ·
        refine ⟨3765663914155573422163639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 80334163501985566339490965 3765663914155573422163639)
        ·
          refine ⟨5648495871233360133245459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3765663914155573422163639 5648495871233360133245459)
          ·
            refine ⟨8472743806850040199868189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5648495871233360133245459 8472743806850040199868189)
            ·
              refine ⟨3177278927568765074950571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8472743806850040199868189 3177278927568765074950571)
              ·
                refine ⟨4765918391353147612425857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3177278927568765074950571 4765918391353147612425857)
                ·
                  refine ⟨3574438793514860709319393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4765918391353147612425857 3574438793514860709319393)
                  ·
                    refine ⟨2680829095136145531989545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3574438793514860709319393 2680829095136145531989545)
                    ·
                      refine ⟨2010621821352109148992159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2680829095136145531989545 2010621821352109148992159)
                      ·
                        rfl

theorem cell23_3915672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_3915672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915672 prefixEnd_3915672 := by exact prefixLift 3915672
  have htrace : WordTrace (prefixWord ++ tailWord_3915672) baseStart_3915672 baseEnd_3915672 := by
    simpa [prefixWord, tailWord_3915672, baseEnd_3915672] using wordTrace_append hprefix tailTrace_3915672
  have hstable : (prefixWord ++ tailWord_3915672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915672).length < 2 ^ (prefixWord ++ tailWord_3915672).sum := by decide
  have hdescent : baseEnd_3915672 < baseStart_3915672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915771 : List Nat := [1, 1, 1, 1, 1, 3, 6, 2, 2, 3, 2]
def baseStart_3915771 : Nat := 118140960795 + 3915771 * 2 ^ 59
def prefixEnd_3915771 : Nat := 4983230072969 + 3 ^ 40 * 3915771 * 2
def baseEnd_3915771 : Nat := 2010672655936904261654203

theorem tailTrace_3915771 : CollatzResearch.WordTrace tailWord_3915771 prefixEnd_3915771 2010672655936904261654203 := by
  unfold tailWord_3915771
  simp only [CollatzResearch.WordTrace]
  refine ⟨142819901496837902289171167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95213267664558601526114111 142819901496837902289171167)
  ·
    refine ⟨214229852245256853433756751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142819901496837902289171167 214229852245256853433756751)
    ·
      refine ⟨321344778367885280150635127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214229852245256853433756751 321344778367885280150635127)
      ·
        refine ⟨482017167551827920225952691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321344778367885280150635127 482017167551827920225952691)
        ·
          refine ⟨723025751327741880338929037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482017167551827920225952691 723025751327741880338929037)
          ·
            refine ⟨271134656747903205127098389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 723025751327741880338929037 271134656747903205127098389)
            ·
              refine ⟨12709437035057962740332737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 271134656747903205127098389 12709437035057962740332737)
              ·
                refine ⟨9532077776293472055249553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12709437035057962740332737 9532077776293472055249553)
                ·
                  refine ⟨7149058332220104041437165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9532077776293472055249553 7149058332220104041437165)
                  ·
                    refine ⟨2680896874582539015538937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7149058332220104041437165 2680896874582539015538937)
                    ·
                      refine ⟨2010672655936904261654203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2680896874582539015538937 2010672655936904261654203)
                      ·
                        rfl

theorem cell23_3915771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 3, 2].length) (baseStart_3915771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915771 prefixEnd_3915771 := by exact prefixLift 3915771
  have htrace : WordTrace (prefixWord ++ tailWord_3915771) baseStart_3915771 baseEnd_3915771 := by
    simpa [prefixWord, tailWord_3915771, baseEnd_3915771] using wordTrace_append hprefix tailTrace_3915771
  have hstable : (prefixWord ++ tailWord_3915771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915771).length < 2 ^ (prefixWord ++ tailWord_3915771).sum := by decide
  have hdescent : baseEnd_3915771 < baseStart_3915771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915784 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 5, 1, 4]
def baseStart_3915784 : Nat := 118140960795 + 3915784 * 2 ^ 59
def prefixEnd_3915784 : Nat := 4983230072969 + 3 ^ 40 * 3915784 * 2
def baseEnd_3915784 : Nat := 2010679331185412710791643

theorem tailTrace_3915784 : CollatzResearch.WordTrace tailWord_3915784 prefixEnd_3915784 2010679331185412710791643 := by
  unfold tailWord_3915784
  simp only [CollatzResearch.WordTrace]
  refine ⟨71410187822895402754697203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95213583763860537006262937 71410187822895402754697203)
  ·
    refine ⟨107115281734343104132045805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71410187822895402754697203 107115281734343104132045805)
    ·
      refine ⟨40168230650378664049517177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107115281734343104132045805 40168230650378664049517177)
      ·
        refine ⟨30126172987783998037137883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40168230650378664049517177 30126172987783998037137883)
        ·
          refine ⟨45189259481675997055706825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30126172987783998037137883 45189259481675997055706825)
          ·
            refine ⟨33891944611256997791780119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45189259481675997055706825 33891944611256997791780119)
            ·
              refine ⟨50837916916885496687670179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33891944611256997791780119 50837916916885496687670179)
              ·
                refine ⟨76256875375328245031505269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50837916916885496687670179 76256875375328245031505269)
                ·
                  refine ⟨7149082066437022971703619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76256875375328245031505269 7149082066437022971703619)
                  ·
                    refine ⟨10723623099655534457555429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7149082066437022971703619 10723623099655534457555429)
                    ·
                      refine ⟨2010679331185412710791643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10723623099655534457555429 2010679331185412710791643)
                      ·
                        rfl

theorem cell23_3915784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_3915784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915784 prefixEnd_3915784 := by exact prefixLift 3915784
  have htrace : WordTrace (prefixWord ++ tailWord_3915784) baseStart_3915784 baseEnd_3915784 := by
    simpa [prefixWord, tailWord_3915784, baseEnd_3915784] using wordTrace_append hprefix tailTrace_3915784
  have hstable : (prefixWord ++ tailWord_3915784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915784).length < 2 ^ (prefixWord ++ tailWord_3915784).sum := by decide
  have hdescent : baseEnd_3915784 < baseStart_3915784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915805 : List Nat := [1, 4, 2, 2, 2, 3, 1, 1, 2, 3, 2]
def baseStart_3915805 : Nat := 118140960795 + 3915805 * 2 ^ 59
def prefixEnd_3915805 : Nat := 4983230072969 + 3 ^ 40 * 3915805 * 2
def baseEnd_3915805 : Nat := 2010690114279157128629047

theorem tailTrace_3915805 : CollatzResearch.WordTrace tailWord_3915805 prefixEnd_3915805 2010690114279157128629047 := by
  unfold tailWord_3915805
  simp only [CollatzResearch.WordTrace]
  refine ⟨142821141578714726095908869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95214094385809817397272579 142821141578714726095908869)
  ·
    refine ⟨26778964046009011142982913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142821141578714726095908869 26778964046009011142982913)
    ·
      refine ⟨20084223034506758357237185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26778964046009011142982913 20084223034506758357237185)
      ·
        refine ⟨15063167275880068767927889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20084223034506758357237185 15063167275880068767927889)
        ·
          refine ⟨11297375456910051575945917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15063167275880068767927889 11297375456910051575945917)
          ·
            refine ⟨4236515796341269340979719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11297375456910051575945917 4236515796341269340979719)
            ·
              refine ⟨6354773694511904011469579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4236515796341269340979719 6354773694511904011469579)
              ·
                refine ⟨9532160541767856017204369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6354773694511904011469579 9532160541767856017204369)
                ·
                  refine ⟨7149120406325892012903277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9532160541767856017204369 7149120406325892012903277)
                  ·
                    refine ⟨2680920152372209504838729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7149120406325892012903277 2680920152372209504838729)
                    ·
                      refine ⟨2010690114279157128629047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2680920152372209504838729 2010690114279157128629047)
                      ·
                        rfl

theorem cell23_3915805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_3915805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915805 prefixEnd_3915805 := by exact prefixLift 3915805
  have htrace : WordTrace (prefixWord ++ tailWord_3915805) baseStart_3915805 baseEnd_3915805 := by
    simpa [prefixWord, tailWord_3915805, baseEnd_3915805] using wordTrace_append hprefix tailTrace_3915805
  have hstable : (prefixWord ++ tailWord_3915805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915805).length < 2 ^ (prefixWord ++ tailWord_3915805).sum := by decide
  have hdescent : baseEnd_3915805 < baseStart_3915805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915812 : List Nat := [2, 3, 1, 4, 2, 1, 2, 3, 1, 1, 3]
def baseStart_3915812 : Nat := 118140960795 + 3915812 * 2 ^ 59
def prefixEnd_3915812 : Nat := 4983230072969 + 3 ^ 40 * 3915812 * 2
def baseEnd_3915812 : Nat := 2010693708643738601241515

theorem tailTrace_3915812 : CollatzResearch.WordTrace tailWord_3915812 prefixEnd_3915812 2010693708643738601241515 := by
  unfold tailWord_3915812
  simp only [CollatzResearch.WordTrace]
  refine ⟨71410698444844683145706845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95214264593126244194275793 71410698444844683145706845)
  ·
    refine ⟨26779011916816756179640067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71410698444844683145706845 26779011916816756179640067)
    ·
      refine ⟨40168517875225134269460101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26779011916816756179640067 40168517875225134269460101)
      ·
        refine ⟨7531597101604712675523769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40168517875225134269460101 7531597101604712675523769)
        ·
          refine ⟨5648697826203534506642827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7531597101604712675523769 5648697826203534506642827)
          ·
            refine ⟨8473046739305301759964241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5648697826203534506642827 8473046739305301759964241)
            ·
              refine ⟨6354785054478976319973181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8473046739305301759964241 6354785054478976319973181)
              ·
                refine ⟨2383044395429616119989943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6354785054478976319973181 2383044395429616119989943)
                ·
                  refine ⟨3574566593144424179984915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2383044395429616119989943 3574566593144424179984915)
                  ·
                    refine ⟨5361849889716636269977373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3574566593144424179984915 5361849889716636269977373)
                    ·
                      refine ⟨2010693708643738601241515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5361849889716636269977373 2010693708643738601241515)
                      ·
                        rfl

theorem cell23_3915812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_3915812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915812 prefixEnd_3915812 := by exact prefixLift 3915812
  have htrace : WordTrace (prefixWord ++ tailWord_3915812) baseStart_3915812 baseEnd_3915812 := by
    simpa [prefixWord, tailWord_3915812, baseEnd_3915812] using wordTrace_append hprefix tailTrace_3915812
  have hstable : (prefixWord ++ tailWord_3915812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915812).length < 2 ^ (prefixWord ++ tailWord_3915812).sum := by decide
  have hdescent : baseEnd_3915812 < baseStart_3915812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915817 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 3, 4, 7]
def baseStart_3915817 : Nat := 118140960795 + 3915817 * 2 ^ 59
def prefixEnd_3915817 : Nat := 4983230072969 + 3 ^ 40 * 3915817 * 2
def baseEnd_3915817 : Nat := 2010696276047011081678991

theorem tailTrace_3915817 : CollatzResearch.WordTrace tailWord_3915817 prefixEnd_3915817 2010696276047011081678991 := by
  unfold tailWord_3915817
  simp only [CollatzResearch.WordTrace]
  refine ⟨142821579254671252145345705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95214386169780834763563803 142821579254671252145345705)
  ·
    refine ⟨107116184441003439109009279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142821579254671252145345705 107116184441003439109009279)
    ·
      refine ⟨160674276661505158663513919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107116184441003439109009279 160674276661505158663513919)
      ·
        refine ⟨241011414992257737995270879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160674276661505158663513919 241011414992257737995270879)
        ·
          refine ⟨361517122488386606992906319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241011414992257737995270879 361517122488386606992906319)
          ·
            refine ⟨542275683732579910489359479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361517122488386606992906319 542275683732579910489359479)
            ·
              refine ⟨813413525598869865734039219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 542275683732579910489359479 813413525598869865734039219)
              ·
                refine ⟨1220120288398304798601058829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 813413525598869865734039219 1220120288398304798601058829)
                ·
                  refine ⟨457545108149364299475397061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1220120288398304798601058829 457545108149364299475397061)
                  ·
                    refine ⟨85789707778005806151636949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 457545108149364299475397061 85789707778005806151636949)
                    ·
                      refine ⟨2010696276047011081678991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 85789707778005806151636949 2010696276047011081678991)
                      ·
                        rfl

theorem cell23_3915817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 4, 7].length) (baseStart_3915817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915817 prefixEnd_3915817 := by exact prefixLift 3915817
  have htrace : WordTrace (prefixWord ++ tailWord_3915817) baseStart_3915817 baseEnd_3915817 := by
    simpa [prefixWord, tailWord_3915817, baseEnd_3915817] using wordTrace_append hprefix tailTrace_3915817
  have hstable : (prefixWord ++ tailWord_3915817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915817).length < 2 ^ (prefixWord ++ tailWord_3915817).sum := by decide
  have hdescent : baseEnd_3915817 < baseStart_3915817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915818 : List Nat := [3, 1, 4, 1, 2, 2, 1, 3, 1, 1, 4]
def baseStart_3915818 : Nat := 118140960795 + 3915818 * 2 ^ 59
def prefixEnd_3915818 : Nat := 4983230072969 + 3 ^ 40 * 3915818 * 2
def baseEnd_3915818 : Nat := 2010696789527665577766487

theorem tailTrace_3915818 : CollatzResearch.WordTrace tailWord_3915818 prefixEnd_3915818 2010696789527665577766487 := by
  unfold tailWord_3915818
  simp only [CollatzResearch.WordTrace]
  refine ⟨35705403931916907329033027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95214410485111752877421405 35705403931916907329033027)
  ·
    refine ⟨53558105897875360993549541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35705403931916907329033027 53558105897875360993549541)
    ·
      refine ⟨10042144855851630186290539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53558105897875360993549541 10042144855851630186290539)
      ·
        refine ⟨15063217283777445279435809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10042144855851630186290539 15063217283777445279435809)
        ·
          refine ⟨11297412962833083959576857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15063217283777445279435809 11297412962833083959576857)
          ·
            refine ⟨8473059722124812969682643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11297412962833083959576857 8473059722124812969682643)
            ·
              refine ⟨12709589583187219454523965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8473059722124812969682643 12709589583187219454523965)
              ·
                refine ⟨4766096093695207295446487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12709589583187219454523965 4766096093695207295446487)
                ·
                  refine ⟨7149144140542810943169731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4766096093695207295446487 7149144140542810943169731)
                  ·
                    refine ⟨10723716210814216414754597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7149144140542810943169731 10723716210814216414754597)
                    ·
                      refine ⟨2010696789527665577766487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10723716210814216414754597 2010696789527665577766487)
                      ·
                        rfl

theorem cell23_3915818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_3915818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915818 prefixEnd_3915818 := by exact prefixLift 3915818
  have htrace : WordTrace (prefixWord ++ tailWord_3915818) baseStart_3915818 baseEnd_3915818 := by
    simpa [prefixWord, tailWord_3915818, baseEnd_3915818] using wordTrace_append hprefix tailTrace_3915818
  have hstable : (prefixWord ++ tailWord_3915818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915818).length < 2 ^ (prefixWord ++ tailWord_3915818).sum := by decide
  have hdescent : baseEnd_3915818 < baseStart_3915818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915838 : List Nat := [4, 2, 1, 3, 2, 1, 1, 2, 1, 1, 5]
def baseStart_3915838 : Nat := 118140960795 + 3915838 * 2 ^ 59
def prefixEnd_3915838 : Nat := 4983230072969 + 3 ^ 40 * 3915838 * 2
def baseEnd_3915838 : Nat := 2010707059140755499516395

theorem tailTrace_3915838 : CollatzResearch.WordTrace tailWord_3915838 prefixEnd_3915838 2010707059140755499516395 := by
  unfold tailWord_3915838
  simp only [CollatzResearch.WordTrace]
  refine ⟨17852793148449396591482521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95214896791730115154573445 17852793148449396591482521)
  ·
    refine ⟨13389594861337047443611891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17852793148449396591482521 13389594861337047443611891)
    ·
      refine ⟨20084392292005571165417837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13389594861337047443611891 20084392292005571165417837)
      ·
        refine ⟨7531647109502089187031689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20084392292005571165417837 7531647109502089187031689)
        ·
          refine ⟨5648735332126566890273767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7531647109502089187031689 5648735332126566890273767)
          ·
            refine ⟨8473102998189850335410651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5648735332126566890273767 8473102998189850335410651)
            ·
              refine ⟨12709654497284775503115977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8473102998189850335410651 12709654497284775503115977)
              ·
                refine ⟨9532240872963581627336983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12709654497284775503115977 9532240872963581627336983)
                ·
                  refine ⟨14298361309445372441005475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9532240872963581627336983 14298361309445372441005475)
                  ·
                    refine ⟨21447541964168058661508213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14298361309445372441005475 21447541964168058661508213)
                    ·
                      refine ⟨2010707059140755499516395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21447541964168058661508213 2010707059140755499516395)
                      ·
                        rfl

theorem cell23_3915838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_3915838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915838 prefixEnd_3915838 := by exact prefixLift 3915838
  have htrace : WordTrace (prefixWord ++ tailWord_3915838) baseStart_3915838 baseEnd_3915838 := by
    simpa [prefixWord, tailWord_3915838, baseEnd_3915838] using wordTrace_append hprefix tailTrace_3915838
  have hstable : (prefixWord ++ tailWord_3915838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915838).length < 2 ^ (prefixWord ++ tailWord_3915838).sum := by decide
  have hdescent : baseEnd_3915838 < baseStart_3915838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915858 : List Nat := [3, 2, 2, 1, 4, 2, 2, 7]
def baseStart_3915858 : Nat := 118140960795 + 3915858 * 2 ^ 59
def prefixEnd_3915858 : Nat := 4983230072969 + 3 ^ 40 * 3915858 * 2
def baseEnd_3915858 : Nat := 74471012176068348935789

theorem tailTrace_3915858 : CollatzResearch.WordTrace tailWord_3915858 prefixEnd_3915858 74471012176068348935789 := by
  unfold tailWord_3915858
  simp only [CollatzResearch.WordTrace]
  refine ⟨35705768661880679036897057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95215383098348477431725485 35705768661880679036897057)
  ·
    refine ⟨26779326496410509277672793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35705768661880679036897057 26779326496410509277672793)
    ·
      refine ⟨20084494872307881958254595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26779326496410509277672793 20084494872307881958254595)
      ·
        refine ⟨30126742308461822937381893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20084494872307881958254595 30126742308461822937381893)
        ·
          refine ⟨5648764182836591800759105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30126742308461822937381893 5648764182836591800759105)
          ·
            refine ⟨4236573137127443850569329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5648764182836591800759105 4236573137127443850569329)
            ·
              refine ⟨3177429852845582887926997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4236573137127443850569329 3177429852845582887926997)
              ·
                refine ⟨74471012176068348935789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3177429852845582887926997 74471012176068348935789)
                ·
                  rfl

theorem cell23_3915858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 7].length) (baseStart_3915858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915858 prefixEnd_3915858 := by exact prefixLift 3915858
  have htrace : WordTrace (prefixWord ++ tailWord_3915858) baseStart_3915858 baseEnd_3915858 := by
    simpa [prefixWord, tailWord_3915858, baseEnd_3915858] using wordTrace_append hprefix tailTrace_3915858
  have hstable : (prefixWord ++ tailWord_3915858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915858).length < 2 ^ (prefixWord ++ tailWord_3915858).sum := by decide
  have hdescent : baseEnd_3915858 < baseStart_3915858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915864 : List Nat := [2, 1, 2, 2, 1, 4, 1, 1, 2, 2, 5]
def baseStart_3915864 : Nat := 118140960795 + 3915864 * 2 ^ 59
def prefixEnd_3915864 : Nat := 4983230072969 + 3 ^ 40 * 3915864 * 2
def baseEnd_3915864 : Nat := 2010720409637772397791275

theorem tailTrace_3915864 : CollatzResearch.WordTrace tailWord_3915864 prefixEnd_3915864 2010720409637772397791275 := by
  unfold tailWord_3915864
  simp only [CollatzResearch.WordTrace]
  refine ⟨71411646742750489586153323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95215528990333986114871097 71411646742750489586153323)
  ·
    refine ⟨107117470114125734379229985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71411646742750489586153323 107117470114125734379229985)
    ·
      refine ⟨80338102585594300784422489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107117470114125734379229985 80338102585594300784422489)
      ·
        refine ⟨60253576939195725588316867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80338102585594300784422489 60253576939195725588316867)
        ·
          refine ⟨90380365408793588382475301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60253576939195725588316867 90380365408793588382475301)
          ·
            refine ⟨16946318514148797821714119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90380365408793588382475301 16946318514148797821714119)
            ·
              refine ⟨25419477771223196732571179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16946318514148797821714119 25419477771223196732571179)
              ·
                refine ⟨38129216656834795098856769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25419477771223196732571179 38129216656834795098856769)
                ·
                  refine ⟨28596912492626096324142577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38129216656834795098856769 28596912492626096324142577)
                  ·
                    refine ⟨21447684369469572243106933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28596912492626096324142577 21447684369469572243106933)
                    ·
                      refine ⟨2010720409637772397791275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21447684369469572243106933 2010720409637772397791275)
                      ·
                        rfl

theorem cell23_3915864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_3915864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915864 prefixEnd_3915864 := by exact prefixLift 3915864
  have htrace : WordTrace (prefixWord ++ tailWord_3915864) baseStart_3915864 baseEnd_3915864 := by
    simpa [prefixWord, tailWord_3915864, baseEnd_3915864] using wordTrace_append hprefix tailTrace_3915864
  have hstable : (prefixWord ++ tailWord_3915864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915864).length < 2 ^ (prefixWord ++ tailWord_3915864).sum := by decide
  have hdescent : baseEnd_3915864 < baseStart_3915864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915868 : List Nat := [2, 2, 4, 1, 1, 2, 1, 2, 4, 1, 3]
def baseStart_3915868 : Nat := 118140960795 + 3915868 * 2 ^ 59
def prefixEnd_3915868 : Nat := 4983230072969 + 3 ^ 40 * 3915868 * 2
def baseEnd_3915868 : Nat := 2010722463560390382141257

theorem tailTrace_3915868 : CollatzResearch.WordTrace tailWord_3915868 prefixEnd_3915868 2010722463560390382141257 := by
  unfold tailWord_3915868
  simp only [CollatzResearch.WordTrace]
  refine ⟨71411719688743243927726129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95215626251657658570301505 71411719688743243927726129)
  ·
    refine ⟨53558789766557432945794597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71411719688743243927726129 53558789766557432945794597)
    ·
      refine ⟨10042273081229518677336487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53558789766557432945794597 10042273081229518677336487)
      ·
        refine ⟨15063409621844278016004731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10042273081229518677336487 15063409621844278016004731)
        ·
          refine ⟨22595114432766417024007097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15063409621844278016004731 22595114432766417024007097)
          ·
            refine ⟨16946335824574812768005323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22595114432766417024007097 16946335824574812768005323)
            ·
              refine ⟨25419503736862219152007985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16946335824574812768005323 25419503736862219152007985)
              ·
                refine ⟨19064627802646664364005989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25419503736862219152007985 19064627802646664364005989)
                ·
                  refine ⟨3574617712996249568251123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19064627802646664364005989 3574617712996249568251123)
                  ·
                    refine ⟨5361926569494374352376685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3574617712996249568251123 5361926569494374352376685)
                    ·
                      refine ⟨2010722463560390382141257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5361926569494374352376685 2010722463560390382141257)
                      ·
                        rfl

theorem cell23_3915868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_3915868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915868 prefixEnd_3915868 := by exact prefixLift 3915868
  have htrace : WordTrace (prefixWord ++ tailWord_3915868) baseStart_3915868 baseEnd_3915868 := by
    simpa [prefixWord, tailWord_3915868, baseEnd_3915868] using wordTrace_append hprefix tailTrace_3915868
  have hstable : (prefixWord ++ tailWord_3915868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915868).length < 2 ^ (prefixWord ++ tailWord_3915868).sum := by decide
  have hdescent : baseEnd_3915868 < baseStart_3915868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915869 : List Nat := [1, 4, 4, 1, 1, 1, 3, 3, 1, 2, 2]
def baseStart_3915869 : Nat := 118140960795 + 3915869 * 2 ^ 59
def prefixEnd_3915869 : Nat := 4983230072969 + 3 ^ 40 * 3915869 * 2
def baseEnd_3915869 : Nat := 2010722977041044878228753

theorem tailTrace_3915869 : CollatzResearch.WordTrace tailWord_3915869 prefixEnd_3915869 2010722977041044878228753 := by
  unfold tailWord_3915869
  simp only [CollatzResearch.WordTrace]
  refine ⟨142823475850482865026238661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95215650566988576684159107 142823475850482865026238661)
  ·
    refine ⟨26779401721965537192419749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142823475850482865026238661 26779401721965537192419749)
    ·
      refine ⟨5021137822868538223578703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26779401721965537192419749 5021137822868538223578703)
      ·
        refine ⟨7531706734302807335368055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5021137822868538223578703 7531706734302807335368055)
        ·
          refine ⟨11297560101454211003052083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7531706734302807335368055 11297560101454211003052083)
          ·
            refine ⟨16946340152181316504578125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11297560101454211003052083 16946340152181316504578125)
            ·
              refine ⟨6354877557067993689216797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16946340152181316504578125 6354877557067993689216797)
              ·
                refine ⟨2383079083900497633456299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6354877557067993689216797 2383079083900497633456299)
                ·
                  refine ⟨3574618625850746450184449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2383079083900497633456299 3574618625850746450184449)
                  ·
                    refine ⟨2680963969388059837638337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3574618625850746450184449 2680963969388059837638337)
                    ·
                      refine ⟨2010722977041044878228753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2680963969388059837638337 2010722977041044878228753)
                      ·
                        rfl

theorem cell23_3915869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_3915869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915869 prefixEnd_3915869 := by exact prefixLift 3915869
  have htrace : WordTrace (prefixWord ++ tailWord_3915869) baseStart_3915869 baseEnd_3915869 := by
    simpa [prefixWord, tailWord_3915869, baseEnd_3915869] using wordTrace_append hprefix tailTrace_3915869
  have hstable : (prefixWord ++ tailWord_3915869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915869).length < 2 ^ (prefixWord ++ tailWord_3915869).sum := by decide
  have hdescent : baseEnd_3915869 < baseStart_3915869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915904 : List Nat := [2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 4]
def baseStart_3915904 : Nat := 118140960795 + 3915904 * 2 ^ 59
def prefixEnd_3915904 : Nat := 4983230072969 + 3 ^ 40 * 3915904 * 2
def baseEnd_3915904 : Nat := 2010740948863952241291091

theorem tailTrace_3915904 : CollatzResearch.WordTrace tailWord_3915904 prefixEnd_3915904 2010740948863952241291091 := by
  unfold tailWord_3915904
  simp only [CollatzResearch.WordTrace]
  refine ⟨71412376202678033001881383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95216501603570710669175177 71412376202678033001881383)
  ·
    refine ⟨107118564304017049502822075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71412376202678033001881383 107118564304017049502822075)
    ·
      refine ⟨160677846456025574254233113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107118564304017049502822075 160677846456025574254233113)
      ·
        refine ⟨120508384842019180690674835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160677846456025574254233113 120508384842019180690674835)
        ·
          refine ⟨180762577263028771036012253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120508384842019180690674835 180762577263028771036012253)
          ·
            refine ⟨67785966473635789138504595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180762577263028771036012253 67785966473635789138504595)
            ·
              refine ⟨101678949710453683707756893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67785966473635789138504595 101678949710453683707756893)
              ·
                refine ⟨38129606141420131390408835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101678949710453683707756893 38129606141420131390408835)
                ·
                  refine ⟨57194409212130197085613253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38129606141420131390408835 57194409212130197085613253)
                  ·
                    refine ⟨10723951727274411953552485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57194409212130197085613253 10723951727274411953552485)
                    ·
                      refine ⟨2010740948863952241291091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10723951727274411953552485 2010740948863952241291091)
                      ·
                        rfl

theorem cell23_3915904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 4].length) (baseStart_3915904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915904 prefixEnd_3915904 := by exact prefixLift 3915904
  have htrace : WordTrace (prefixWord ++ tailWord_3915904) baseStart_3915904 baseEnd_3915904 := by
    simpa [prefixWord, tailWord_3915904, baseEnd_3915904] using wordTrace_append hprefix tailTrace_3915904
  have hstable : (prefixWord ++ tailWord_3915904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915904).length < 2 ^ (prefixWord ++ tailWord_3915904).sum := by decide
  have hdescent : baseEnd_3915904 < baseStart_3915904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915908 : List Nat := [2, 3, 2, 1, 2, 1, 2, 3, 1, 4, 2]
def baseStart_3915908 : Nat := 118140960795 + 3915908 * 2 ^ 59
def prefixEnd_3915908 : Nat := 4983230072969 + 3 ^ 40 * 3915908 * 2
def baseEnd_3915908 : Nat := 2010743002786570225641073

theorem tailTrace_3915908 : CollatzResearch.WordTrace tailWord_3915908 prefixEnd_3915908 2010743002786570225641073 := by
  unfold tailWord_3915908
  simp only [CollatzResearch.WordTrace]
  refine ⟨71412449148670787343454189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95216598864894383124605585 71412449148670787343454189)
  ·
    refine ⟨26779668430751545253795321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71412449148670787343454189 26779668430751545253795321)
    ·
      refine ⟨20084751323063658940346491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26779668430751545253795321 20084751323063658940346491)
      ·
        refine ⟨30127126984595488410519737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20084751323063658940346491 30127126984595488410519737)
        ·
          refine ⟨22595345238446616307889803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30127126984595488410519737 22595345238446616307889803)
          ·
            refine ⟨33893017857669924461834705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22595345238446616307889803 33893017857669924461834705)
            ·
              refine ⟨25419763393252443346376029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33893017857669924461834705 25419763393252443346376029)
              ·
                refine ⟨9532411272469666254891011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25419763393252443346376029 9532411272469666254891011)
                ·
                  refine ⟨14298616908704499382336517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9532411272469666254891011 14298616908704499382336517)
                  ·
                    refine ⟨2680990670382093634188097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14298616908704499382336517 2680990670382093634188097)
                    ·
                      refine ⟨2010743002786570225641073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2680990670382093634188097 2010743002786570225641073)
                      ·
                        rfl

theorem cell23_3915908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_3915908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915908 prefixEnd_3915908 := by exact prefixLift 3915908
  have htrace : WordTrace (prefixWord ++ tailWord_3915908) baseStart_3915908 baseEnd_3915908 := by
    simpa [prefixWord, tailWord_3915908, baseEnd_3915908] using wordTrace_append hprefix tailTrace_3915908
  have hstable : (prefixWord ++ tailWord_3915908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915908).length < 2 ^ (prefixWord ++ tailWord_3915908).sum := by decide
  have hdescent : baseEnd_3915908 < baseStart_3915908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915912 : List Nat := [2, 1, 3, 4, 1, 3, 1, 2, 1, 3, 2]
def baseStart_3915912 : Nat := 118140960795 + 3915912 * 2 ^ 59
def prefixEnd_3915912 : Nat := 4983230072969 + 3 ^ 40 * 3915912 * 2
def baseEnd_3915912 : Nat := 2010745056709188209991055

theorem tailTrace_3915912 : CollatzResearch.WordTrace tailWord_3915912 prefixEnd_3915912 2010745056709188209991055 := by
  unfold tailWord_3915912
  simp only [CollatzResearch.WordTrace]
  refine ⟨71412522094663541685026995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95216696126218055580035993 71412522094663541685026995)
  ·
    refine ⟨107118783141995312527540493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71412522094663541685026995 107118783141995312527540493)
    ·
      refine ⟨40169543678248242197827685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107118783141995312527540493 40169543678248242197827685)
      ·
        refine ⟨7531789439671545412092691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40169543678248242197827685 7531789439671545412092691)
        ·
          refine ⟨11297684159507318118139037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7531789439671545412092691 11297684159507318118139037)
          ·
            refine ⟨4236631559815244294302139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11297684159507318118139037 4236631559815244294302139)
            ·
              refine ⟨6354947339722866441453209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4236631559815244294302139 6354947339722866441453209)
              ·
                refine ⟨4766210504792149831089907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6354947339722866441453209 4766210504792149831089907)
                ·
                  refine ⟨7149315757188224746634861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4766210504792149831089907 7149315757188224746634861)
                  ·
                    refine ⟨2680993408945584279988073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7149315757188224746634861 2680993408945584279988073)
                    ·
                      refine ⟨2010745056709188209991055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2680993408945584279988073 2010745056709188209991055)
                      ·
                        rfl

theorem cell23_3915912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_3915912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915912 prefixEnd_3915912 := by exact prefixLift 3915912
  have htrace : WordTrace (prefixWord ++ tailWord_3915912) baseStart_3915912 baseEnd_3915912 := by
    simpa [prefixWord, tailWord_3915912, baseEnd_3915912] using wordTrace_append hprefix tailTrace_3915912
  have hstable : (prefixWord ++ tailWord_3915912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915912).length < 2 ^ (prefixWord ++ tailWord_3915912).sum := by decide
  have hdescent : baseEnd_3915912 < baseStart_3915912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915941 : List Nat := [1, 3, 1, 2, 1, 3, 2, 2, 2, 3, 3]
def baseStart_3915941 : Nat := 118140960795 + 3915941 * 2 ^ 59
def prefixEnd_3915941 : Nat := 4983230072969 + 3 ^ 40 * 3915941 * 2
def baseEnd_3915941 : Nat := 2010759947648168596528421

theorem tailTrace_3915941 : CollatzResearch.WordTrace tailWord_3915941 prefixEnd_3915941 2010759947648168596528421 := by
  unfold tailWord_3915941
  simp only [CollatzResearch.WordTrace]
  refine ⟨142826101906222021322859677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95217401270814680881906451 142826101906222021322859677)
  ·
    refine ⟨53559788214833257996072379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142826101906222021322859677 53559788214833257996072379)
    ·
      refine ⟨80339682322249886994108569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53559788214833257996072379 80339682322249886994108569)
      ·
        refine ⟨60254761741687415245581427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80339682322249886994108569 60254761741687415245581427)
        ·
          refine ⟨90382142612531122868372141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60254761741687415245581427 90382142612531122868372141)
          ·
            refine ⟨33893303479699171075639553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90382142612531122868372141 33893303479699171075639553)
            ·
              refine ⟨25419977609774378306729665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33893303479699171075639553 25419977609774378306729665)
              ·
                refine ⟨19064983207330783730047249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25419977609774378306729665 19064983207330783730047249)
                ·
                  refine ⟨14298737405498087797535437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19064983207330783730047249 14298737405498087797535437)
                  ·
                    refine ⟨5362026527061782924075789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14298737405498087797535437 5362026527061782924075789)
                    ·
                      refine ⟨2010759947648168596528421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5362026527061782924075789 2010759947648168596528421)
                      ·
                        rfl

theorem cell23_3915941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 3, 3].length) (baseStart_3915941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915941 prefixEnd_3915941 := by exact prefixLift 3915941
  have htrace : WordTrace (prefixWord ++ tailWord_3915941) baseStart_3915941 baseEnd_3915941 := by
    simpa [prefixWord, tailWord_3915941, baseEnd_3915941] using wordTrace_append hprefix tailTrace_3915941
  have hstable : (prefixWord ++ tailWord_3915941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915941).length < 2 ^ (prefixWord ++ tailWord_3915941).sum := by decide
  have hdescent : baseEnd_3915941 < baseStart_3915941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915991 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 7, 4]
def baseStart_3915991 : Nat := 118140960795 + 3915991 * 2 ^ 59
def prefixEnd_3915991 : Nat := 4983230072969 + 3 ^ 40 * 3915991 * 2
def baseEnd_3915991 : Nat := 670261873893631133634397

theorem tailTrace_3915991 : CollatzResearch.WordTrace tailWord_3915991 prefixEnd_3915991 670261873893631133634397 := by
  unfold tailWord_3915991
  simp only [CollatzResearch.WordTrace]
  refine ⟨142827925556040879862179827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95218617037360586574786551 142827925556040879862179827)
  ·
    refine ⟨214241888334061319793269741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142827925556040879862179827 214241888334061319793269741)
    ·
      refine ⟨80340708125272994922476153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214241888334061319793269741 80340708125272994922476153)
      ·
        refine ⟨60255531093954746191857115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80340708125272994922476153 60255531093954746191857115)
        ·
          refine ⟨90383296640932119287785673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60255531093954746191857115 90383296640932119287785673)
          ·
            refine ⟨67787472480699089465839255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90383296640932119287785673 67787472480699089465839255)
            ·
              refine ⟨101681208721048634198758883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67787472480699089465839255 101681208721048634198758883)
              ·
                refine ⟨152521813081572951298138325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101681208721048634198758883 152521813081572951298138325)
                ·
                  refine ⟨3574729994099366046050117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 152521813081572951298138325 3574729994099366046050117)
                  ·
                    refine ⟨670261873893631133634397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3574729994099366046050117 670261873893631133634397)
                    ·
                      rfl

theorem cell23_3915991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 7, 4].length) (baseStart_3915991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3915991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3915991 prefixEnd_3915991 := by exact prefixLift 3915991
  have htrace : WordTrace (prefixWord ++ tailWord_3915991) baseStart_3915991 baseEnd_3915991 := by
    simpa [prefixWord, tailWord_3915991, baseEnd_3915991] using wordTrace_append hprefix tailTrace_3915991
  have hstable : (prefixWord ++ tailWord_3915991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915991).length < 2 ^ (prefixWord ++ tailWord_3915991).sum := by decide
  have hdescent : baseEnd_3915991 < baseStart_3915991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916008 : List Nat := [2, 1, 4, 1, 2, 2, 1, 3, 3, 4]
def baseStart_3916008 : Nat := 118140960795 + 3916008 * 2 ^ 59
def prefixEnd_3916008 : Nat := 4983230072969 + 3 ^ 40 * 3916008 * 2
def baseEnd_3916008 : Nat := 670264783617339944796871

theorem tailTrace_3916008 : CollatzResearch.WordTrace tailWord_3916008 prefixEnd_3916008 670264783617339944796871 := by
  unfold tailWord_3916008
  simp only [CollatzResearch.WordTrace]
  refine ⟨71414272798489645882774339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95219030397986194510365785 71414272798489645882774339)
  ·
    refine ⟨107121409197734468824161509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71414272798489645882774339 107121409197734468824161509)
    ·
      refine ⟨20085264224575212904530283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107121409197734468824161509 20085264224575212904530283)
      ·
        refine ⟨30127896336862819356795425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20085264224575212904530283 30127896336862819356795425)
        ·
          refine ⟨22595922252647114517596569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30127896336862819356795425 22595922252647114517596569)
          ·
            refine ⟨16946941689485335888197427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22595922252647114517596569 16946941689485335888197427)
            ·
              refine ⟨25420412534228003832296141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16946941689485335888197427 25420412534228003832296141)
              ·
                refine ⟨9532654700335501437111053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25420412534228003832296141 9532654700335501437111053)
                ·
                  refine ⟨3574745512625813038916645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9532654700335501437111053 3574745512625813038916645)
                  ·
                    refine ⟨670264783617339944796871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3574745512625813038916645 670264783617339944796871)
                    ·
                      rfl

theorem cell23_3916008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_3916008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916008 prefixEnd_3916008 := by exact prefixLift 3916008
  have htrace : WordTrace (prefixWord ++ tailWord_3916008) baseStart_3916008 baseEnd_3916008 := by
    simpa [prefixWord, tailWord_3916008, baseEnd_3916008] using wordTrace_append hprefix tailTrace_3916008
  have hstable : (prefixWord ++ tailWord_3916008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916008).length < 2 ^ (prefixWord ++ tailWord_3916008).sum := by decide
  have hdescent : baseEnd_3916008 < baseStart_3916008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916018 : List Nat := [3, 2, 1, 3, 2, 1, 1, 2, 1, 4, 3]
def baseStart_3916018 : Nat := 118140960795 + 3916018 * 2 ^ 59
def prefixEnd_3916018 : Nat := 4983230072969 + 3 ^ 40 * 3916018 * 2
def baseEnd_3916018 : Nat := 2010799485658564795265567

theorem tailTrace_3916018 : CollatzResearch.WordTrace tailWord_3916018 prefixEnd_3916018 2010799485658564795265567 := by
  unfold tailWord_3916018
  simp only [CollatzResearch.WordTrace]
  refine ⟨35707227581735765868353177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95219273551295375648941805 35707227581735765868353177)
  ·
    refine ⟨26780420686301824401264883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35707227581735765868353177 26780420686301824401264883)
    ·
      refine ⟨40170631029452736601897325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26780420686301824401264883 40170631029452736601897325)
      ·
        refine ⟨15063986636044776225711497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40170631029452736601897325 15063986636044776225711497)
        ·
          refine ⟨11297989977033582169283623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15063986636044776225711497 11297989977033582169283623)
          ·
            refine ⟨16946984965550373253925435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11297989977033582169283623 16946984965550373253925435)
            ·
              refine ⟨25420477448325559880888153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16946984965550373253925435 25420477448325559880888153)
              ·
                refine ⟨19065358086244169910666115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25420477448325559880888153 19065358086244169910666115)
                ·
                  refine ⟨28598037129366254865999173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19065358086244169910666115 28598037129366254865999173)
                  ·
                    refine ⟨5362131961756172787374845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28598037129366254865999173 5362131961756172787374845)
                    ·
                      refine ⟨2010799485658564795265567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5362131961756172787374845 2010799485658564795265567)
                      ·
                        rfl

theorem cell23_3916018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_3916018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916018 prefixEnd_3916018 := by exact prefixLift 3916018
  have htrace : WordTrace (prefixWord ++ tailWord_3916018) baseStart_3916018 baseEnd_3916018 := by
    simpa [prefixWord, tailWord_3916018, baseEnd_3916018] using wordTrace_append hprefix tailTrace_3916018
  have hstable : (prefixWord ++ tailWord_3916018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916018).length < 2 ^ (prefixWord ++ tailWord_3916018).sum := by decide
  have hdescent : baseEnd_3916018 < baseStart_3916018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916031 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 2, 5, 3]
def baseStart_3916031 : Nat := 118140960795 + 3916031 * 2 ^ 59
def prefixEnd_3916031 : Nat := 4983230072969 + 3 ^ 40 * 3916031 * 2
def baseEnd_3916031 : Nat := 2010806160907073244403007

theorem tailTrace_3916031 : CollatzResearch.WordTrace tailWord_3916031 prefixEnd_3916031 2010806160907073244403007 := by
  unfold tailWord_3916031
  simp only [CollatzResearch.WordTrace]
  refine ⟨142829384475895966693635947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95219589650597311129090631 142829384475895966693635947)
  ·
    refine ⟨214244076713843950040453921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142829384475895966693635947 214244076713843950040453921)
    ·
      refine ⟨160683057535382962530340441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214244076713843950040453921 160683057535382962530340441)
      ·
        refine ⟨120512293151537221897755331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160683057535382962530340441 120512293151537221897755331)
        ·
          refine ⟨180768439727305832846632997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120512293151537221897755331 180768439727305832846632997)
          ·
            refine ⟨33894082448869843658743687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180768439727305832846632997 33894082448869843658743687)
            ·
              refine ⟨50841123673304765488115531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33894082448869843658743687 50841123673304765488115531)
              ·
                refine ⟨76261685509957148232173297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50841123673304765488115531 76261685509957148232173297)
                ·
                  refine ⟨57196264132467861174129973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76261685509957148232173297 57196264132467861174129973)
                  ·
                    refine ⟨5362149762418861985074685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57196264132467861174129973 5362149762418861985074685)
                    ·
                      refine ⟨2010806160907073244403007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5362149762418861985074685 2010806160907073244403007)
                      ·
                        rfl

theorem cell23_3916031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 5, 3].length) (baseStart_3916031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916031 prefixEnd_3916031 := by exact prefixLift 3916031
  have htrace : WordTrace (prefixWord ++ tailWord_3916031) baseStart_3916031 baseEnd_3916031 := by
    simpa [prefixWord, tailWord_3916031, baseEnd_3916031] using wordTrace_append hprefix tailTrace_3916031
  have hstable : (prefixWord ++ tailWord_3916031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916031).length < 2 ^ (prefixWord ++ tailWord_3916031).sum := by decide
  have hdescent : baseEnd_3916031 < baseStart_3916031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916065 : List Nat := [1, 2, 3, 2, 1, 1, 5, 1, 3, 1, 3]
def baseStart_3916065 : Nat := 118140960795 + 3916065 * 2 ^ 59
def prefixEnd_3916065 : Nat := 4983230072969 + 3 ^ 40 * 3916065 * 2
def baseEnd_3916065 : Nat := 2010823619249326111377851

theorem tailTrace_3916065 : CollatzResearch.WordTrace tailWord_3916065 prefixEnd_3916065 2010823619249326111377851 := by
  unfold tailWord_3916065
  simp only [CollatzResearch.WordTrace]
  refine ⟨142830624557772790500373649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95220416371848527000249099 142830624557772790500373649)
  ·
    refine ⟨107122968418329592875280237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142830624557772790500373649 107122968418329592875280237)
    ·
      refine ⟨40171113156873597328230089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107122968418329592875280237 40171113156873597328230089)
      ·
        refine ⟨30128334867655197996172567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40171113156873597328230089 30128334867655197996172567)
        ·
          refine ⟨45192502301482796994258851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30128334867655197996172567 45192502301482796994258851)
          ·
            refine ⟨67788753452224195491388277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45192502301482796994258851 67788753452224195491388277)
            ·
              refine ⟨6355195636146018327317651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67788753452224195491388277 6355195636146018327317651)
              ·
                refine ⟨9532793454219027490976477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6355195636146018327317651 9532793454219027490976477)
                ·
                  refine ⟨3574797545332135309116179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9532793454219027490976477 3574797545332135309116179)
                  ·
                    refine ⟨5362196317998202963674269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3574797545332135309116179 5362196317998202963674269)
                    ·
                      refine ⟨2010823619249326111377851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5362196317998202963674269 2010823619249326111377851)
                      ·
                        rfl

theorem cell23_3916065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_3916065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916065 prefixEnd_3916065 := by exact prefixLift 3916065
  have htrace : WordTrace (prefixWord ++ tailWord_3916065) baseStart_3916065 baseEnd_3916065 := by
    simpa [prefixWord, tailWord_3916065, baseEnd_3916065] using wordTrace_append hprefix tailTrace_3916065
  have hstable : (prefixWord ++ tailWord_3916065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916065).length < 2 ^ (prefixWord ++ tailWord_3916065).sum := by decide
  have hdescent : baseEnd_3916065 < baseStart_3916065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916072 : List Nat := [2, 1, 5, 1, 3, 2, 2, 1, 6]
def baseStart_3916072 : Nat := 118140960795 + 3916072 * 2 ^ 59
def prefixEnd_3916072 : Nat := 4983230072969 + 3 ^ 40 * 3916072 * 2
def baseEnd_3916072 : Nat := 223425245957100842665591

theorem tailTrace_3916072 : CollatzResearch.WordTrace tailWord_3916072 prefixEnd_3916072 223425245957100842665591 := by
  unfold tailWord_3916072
  simp only [CollatzResearch.WordTrace]
  refine ⟨71415439934373715347939235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95220586579164953797252313 71415439934373715347939235)
  ·
    refine ⟨107123159901560573021908853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71415439934373715347939235 107123159901560573021908853)
    ·
      refine ⟨10042796240771303720803955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107123159901560573021908853 10042796240771303720803955)
      ·
        refine ⟨15064194361156955581205933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10042796240771303720803955 15064194361156955581205933)
        ·
          refine ⟨5649072885433858342952225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15064194361156955581205933 5649072885433858342952225)
          ·
            refine ⟨4236804664075393757214169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5649072885433858342952225 4236804664075393757214169)
            ·
              refine ⟨3177603498056545317910627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4236804664075393757214169 3177603498056545317910627)
              ·
                refine ⟨4766405247084817976865941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3177603498056545317910627 4766405247084817976865941)
                ·
                  refine ⟨223425245957100842665591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4766405247084817976865941 223425245957100842665591)
                  ·
                    rfl

theorem cell23_3916072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 6].length) (baseStart_3916072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916072 prefixEnd_3916072 := by exact prefixLift 3916072
  have htrace : WordTrace (prefixWord ++ tailWord_3916072) baseStart_3916072 baseEnd_3916072 := by
    simpa [prefixWord, tailWord_3916072, baseEnd_3916072] using wordTrace_append hprefix tailTrace_3916072
  have hstable : (prefixWord ++ tailWord_3916072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916072).length < 2 ^ (prefixWord ++ tailWord_3916072).sum := by decide
  have hdescent : baseEnd_3916072 < baseStart_3916072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916088 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 2, 6, 2]
def baseStart_3916088 : Nat := 118140960795 + 3916088 * 2 ^ 59
def prefixEnd_3916088 : Nat := 4983230072969 + 3 ^ 40 * 3916088 * 2
def baseEnd_3916088 : Nat := 2010835429304379521390245

theorem tailTrace_3916088 : CollatzResearch.WordTrace tailWord_3916088 prefixEnd_3916088 2010835429304379521390245 := by
  unfold tailWord_3916088
  simp only [CollatzResearch.WordTrace]
  refine ⟨71415731718344732714230459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95220975624459643618973945 71415731718344732714230459)
  ·
    refine ⟨107123597577517099071345689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71415731718344732714230459 107123597577517099071345689)
    ·
      refine ⟨80342698183137824303509267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107123597577517099071345689 80342698183137824303509267)
      ·
        refine ⟨120514047274706736455263901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80342698183137824303509267 120514047274706736455263901)
        ·
          refine ⟨45192767728015026170723963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120514047274706736455263901 45192767728015026170723963)
          ·
            refine ⟨67789151592022539256085945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45192767728015026170723963 67789151592022539256085945)
            ·
              refine ⟨50841863694016904442064459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67789151592022539256085945 50841863694016904442064459)
              ·
                refine ⟨76262795541025356663096689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50841863694016904442064459 76262795541025356663096689)
                ·
                  refine ⟨57197096655769017497322517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76262795541025356663096689 57197096655769017497322517)
                  ·
                    refine ⟨2681113905739172695186993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 57197096655769017497322517 2681113905739172695186993)
                    ·
                      refine ⟨2010835429304379521390245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2681113905739172695186993 2010835429304379521390245)
                      ·
                        rfl

theorem cell23_3916088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 2, 6, 2].length) (baseStart_3916088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916088 prefixEnd_3916088 := by exact prefixLift 3916088
  have htrace : WordTrace (prefixWord ++ tailWord_3916088) baseStart_3916088 baseEnd_3916088 := by
    simpa [prefixWord, tailWord_3916088, baseEnd_3916088] using wordTrace_append hprefix tailTrace_3916088
  have hstable : (prefixWord ++ tailWord_3916088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916088).length < 2 ^ (prefixWord ++ tailWord_3916088).sum := by decide
  have hdescent : baseEnd_3916088 < baseStart_3916088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916116 : List Nat := [2, 4, 1, 1, 2, 4, 2, 2, 1, 1, 3]
def baseStart_3916116 : Nat := 118140960795 + 3916116 * 2 ^ 59
def prefixEnd_3916116 : Nat := 4983230072969 + 3 ^ 40 * 3916116 * 2
def baseEnd_3916116 : Nat := 2010849806762705411840117

theorem tailTrace_3916116 : CollatzResearch.WordTrace tailWord_3916116 prefixEnd_3916116 2010849806762705411840117 := by
  unfold tailWord_3916116
  simp only [CollatzResearch.WordTrace]
  refine ⟨71416242340294013105240101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95221656453725350806986801 71416242340294013105240101)
  ·
    refine ⟨13390545438805127457232519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71416242340294013105240101 13390545438805127457232519)
    ·
      refine ⟨20085818158207691185848779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13390545438805127457232519 20085818158207691185848779)
      ·
        refine ⟨30128727237311536778773169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20085818158207691185848779 30128727237311536778773169)
        ·
          refine ⟨22596545427983652584079877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30128727237311536778773169 22596545427983652584079877)
          ·
            refine ⟨4236852267746934859514977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22596545427983652584079877 4236852267746934859514977)
            ·
              refine ⟨3177639200810201144636233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4236852267746934859514977 3177639200810201144636233)
              ·
                refine ⟨2383229400607650858477175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3177639200810201144636233 2383229400607650858477175)
                ·
                  refine ⟨3574844100911476287715763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2383229400607650858477175 3574844100911476287715763)
                  ·
                    refine ⟨5362266151367214431573645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3574844100911476287715763 5362266151367214431573645)
                    ·
                      refine ⟨2010849806762705411840117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5362266151367214431573645 2010849806762705411840117)
                      ·
                        rfl

theorem cell23_3916116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 2, 1, 1, 3].length) (baseStart_3916116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916116 prefixEnd_3916116 := by exact prefixLift 3916116
  have htrace : WordTrace (prefixWord ++ tailWord_3916116) baseStart_3916116 baseEnd_3916116 := by
    simpa [prefixWord, tailWord_3916116, baseEnd_3916116] using wordTrace_append hprefix tailTrace_3916116
  have hstable : (prefixWord ++ tailWord_3916116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916116).length < 2 ^ (prefixWord ++ tailWord_3916116).sum := by decide
  have hdescent : baseEnd_3916116 < baseStart_3916116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916135 : List Nat := [1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 4]
def baseStart_3916135 : Nat := 118140960795 + 3916135 * 2 ^ 59
def prefixEnd_3916135 : Nat := 4983230072969 + 3 ^ 40 * 3916135 * 2
def baseEnd_3916135 : Nat := 2010859562895140837502529

theorem tailTrace_3916135 : CollatzResearch.WordTrace tailWord_3916135 prefixEnd_3916135 2010859562895140837502529 := by
  unfold tailWord_3916135
  simp only [CollatzResearch.WordTrace]
  refine ⟨142833177667519192455421859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95222118445012794970281239 142833177667519192455421859)
  ·
    refine ⟨214249766501278788683132789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142833177667519192455421859 214249766501278788683132789)
    ·
      refine ⟨20085915609494886439043699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 214249766501278788683132789 20085915609494886439043699)
      ·
        refine ⟨30128873414242329658565549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20085915609494886439043699 30128873414242329658565549)
        ·
          refine ⟨11298327530340873621962081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30128873414242329658565549 11298327530340873621962081)
          ·
            refine ⟨8473745647755655216471561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11298327530340873621962081 8473745647755655216471561)
            ·
              refine ⟨6355309235816741412353671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8473745647755655216471561 6355309235816741412353671)
              ·
                refine ⟨9532963853725112118530507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6355309235816741412353671 9532963853725112118530507)
                ·
                  refine ⟨14299445780587668177795761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9532963853725112118530507 14299445780587668177795761)
                  ·
                    refine ⟨10724584335440751133346821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14299445780587668177795761 10724584335440751133346821)
                    ·
                      refine ⟨2010859562895140837502529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10724584335440751133346821 2010859562895140837502529)
                      ·
                        rfl

theorem cell23_3916135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_3916135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916135 prefixEnd_3916135 := by exact prefixLift 3916135
  have htrace : WordTrace (prefixWord ++ tailWord_3916135) baseStart_3916135 baseEnd_3916135 := by
    simpa [prefixWord, tailWord_3916135, baseEnd_3916135] using wordTrace_append hprefix tailTrace_3916135
  have hstable : (prefixWord ++ tailWord_3916135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916135).length < 2 ^ (prefixWord ++ tailWord_3916135).sum := by decide
  have hdescent : baseEnd_3916135 < baseStart_3916135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916172 : List Nat := [2, 2, 1, 2, 1, 4, 3, 2, 2, 1, 3]
def baseStart_3916172 : Nat := 118140960795 + 3916172 * 2 ^ 59
def prefixEnd_3916172 : Nat := 4983230072969 + 3 ^ 40 * 3916172 * 2
def baseEnd_3916172 : Nat := 2010878561679357192739859

theorem tailTrace_3916172 : CollatzResearch.WordTrace tailWord_3916172 prefixEnd_3916172 2010878561679357192739859 := by
  unfold tailWord_3916172
  simp only [CollatzResearch.WordTrace]
  refine ⟨71417263584192573887259385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95223018112256765183012513 71417263584192573887259385)
  ·
    refine ⟨53562947688144430415444539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71417263584192573887259385 53562947688144430415444539)
    ·
      refine ⟨80344421532216645623166809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53562947688144430415444539 80344421532216645623166809)
      ·
        refine ⟨60258316149162484217375107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80344421532216645623166809 60258316149162484217375107)
        ·
          refine ⟨90387474223743726326062661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60258316149162484217375107 90387474223743726326062661)
          ·
            refine ⟨16947651416951948686136749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90387474223743726326062661 16947651416951948686136749)
            ·
              refine ⟨6355369281356980757301281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16947651416951948686136749 6355369281356980757301281)
              ·
                refine ⟨4766526961017735567975961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6355369281356980757301281 4766526961017735567975961)
                ·
                  refine ⟨3574895220763301675981971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4766526961017735567975961 3574895220763301675981971)
                  ·
                    refine ⟨5362342831144952513972957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3574895220763301675981971 5362342831144952513972957)
                    ·
                      refine ⟨2010878561679357192739859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5362342831144952513972957 2010878561679357192739859)
                      ·
                        rfl

theorem cell23_3916172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 2, 1, 3].length) (baseStart_3916172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916172 prefixEnd_3916172 := by exact prefixLift 3916172
  have htrace : WordTrace (prefixWord ++ tailWord_3916172) baseStart_3916172 baseEnd_3916172 := by
    simpa [prefixWord, tailWord_3916172, baseEnd_3916172] using wordTrace_append hprefix tailTrace_3916172
  have hstable : (prefixWord ++ tailWord_3916172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916172).length < 2 ^ (prefixWord ++ tailWord_3916172).sum := by decide
  have hdescent : baseEnd_3916172 < baseStart_3916172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916189 : List Nat := [1, 4, 2, 1, 5, 1, 1, 1, 1, 3, 3]
def baseStart_3916189 : Nat := 118140960795 + 3916189 * 2 ^ 59
def prefixEnd_3916189 : Nat := 4983230072969 + 3 ^ 40 * 3916189 * 2
def baseEnd_3916189 : Nat := 2010887290850483626227281

theorem tailTrace_3916189 : CollatzResearch.WordTrace tailWord_3916189 prefixEnd_3916189 2010887290850483626227281 := by
  unfold tailWord_3916189
  simp only [CollatzResearch.WordTrace]
  refine ⟨142835147209323559677887621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95223431472882373118591747 142835147209323559677887621)
  ·
    refine ⟨26781590101748167439603929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142835147209323559677887621 26781590101748167439603929)
    ·
      refine ⟨20086192576311125579702947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26781590101748167439603929 20086192576311125579702947)
      ·
        refine ⟨30129288864466688369554421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20086192576311125579702947 30129288864466688369554421)
        ·
          refine ⟨2824620831043752034645727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30129288864466688369554421 2824620831043752034645727)
          ·
            refine ⟨4236931246565628051968591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2824620831043752034645727 4236931246565628051968591)
            ·
              refine ⟨6355396869848442077952887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4236931246565628051968591 6355396869848442077952887)
              ·
                refine ⟨9533095304772663116929331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6355396869848442077952887 9533095304772663116929331)
                ·
                  refine ⟨14299642957158994675393997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9533095304772663116929331 14299642957158994675393997)
                  ·
                    refine ⟨5362366108934623003272749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14299642957158994675393997 5362366108934623003272749)
                    ·
                      refine ⟨2010887290850483626227281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5362366108934623003272749 2010887290850483626227281)
                      ·
                        rfl

theorem cell23_3916189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_3916189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916189 prefixEnd_3916189 := by exact prefixLift 3916189
  have htrace : WordTrace (prefixWord ++ tailWord_3916189) baseStart_3916189 baseEnd_3916189 := by
    simpa [prefixWord, tailWord_3916189, baseEnd_3916189] using wordTrace_append hprefix tailTrace_3916189
  have hstable : (prefixWord ++ tailWord_3916189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916189).length < 2 ^ (prefixWord ++ tailWord_3916189).sum := by decide
  have hdescent : baseEnd_3916189 < baseStart_3916189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916199 : List Nat := [1, 1, 6, 1, 1, 3, 2, 2, 1, 3, 2]
def baseStart_3916199 : Nat := 118140960795 + 3916199 * 2 ^ 59
def prefixEnd_3916199 : Nat := 4983230072969 + 3 ^ 40 * 3916199 * 2
def baseEnd_3916199 : Nat := 2010892425657028587102235

theorem tailTrace_3916199 : CollatzResearch.WordTrace tailWord_3916199 prefixEnd_3916199 2010892425657028587102235 := by
  unfold tailWord_3916199
  simp only [CollatzResearch.WordTrace]
  refine ⟨142835511939287331385751651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95223674626191554257167767 142835511939287331385751651)
  ·
    refine ⟨214253267908930997078627477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142835511939287331385751651 214253267908930997078627477)
    ·
      refine ⟨10043121933231140488060663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 214253267908930997078627477 10043121933231140488060663)
      ·
        refine ⟨15064682899846710732090995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10043121933231140488060663 15064682899846710732090995)
        ·
          refine ⟨22597024349770066098136493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15064682899846710732090995 22597024349770066098136493)
          ·
            refine ⟨8473884131163774786801185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22597024349770066098136493 8473884131163774786801185)
            ·
              refine ⟨6355413098372831090100889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8473884131163774786801185 6355413098372831090100889)
              ·
                refine ⟨4766559823779623317575667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6355413098372831090100889 4766559823779623317575667)
                ·
                  refine ⟨7149839735669434976363501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4766559823779623317575667 7149839735669434976363501)
                  ·
                    refine ⟨2681189900876038116136313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7149839735669434976363501 2681189900876038116136313)
                    ·
                      refine ⟨2010892425657028587102235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2681189900876038116136313 2010892425657028587102235)
                      ·
                        rfl

theorem cell23_3916199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_3916199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916199 prefixEnd_3916199 := by exact prefixLift 3916199
  have htrace : WordTrace (prefixWord ++ tailWord_3916199) baseStart_3916199 baseEnd_3916199 := by
    simpa [prefixWord, tailWord_3916199, baseEnd_3916199] using wordTrace_append hprefix tailTrace_3916199
  have hstable : (prefixWord ++ tailWord_3916199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916199).length < 2 ^ (prefixWord ++ tailWord_3916199).sum := by decide
  have hdescent : baseEnd_3916199 < baseStart_3916199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916246 : List Nat := [5, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2]
def baseStart_3916246 : Nat := 118140960795 + 3916246 * 2 ^ 59
def prefixEnd_3916246 : Nat := 4983230072969 + 3 ^ 40 * 3916246 * 2
def baseEnd_3916246 : Nat := 2010916559247789903214519

theorem tailTrace_3916246 : CollatzResearch.WordTrace tailWord_3916246 prefixEnd_3916246 2010916559247789903214519 := by
  unfold tailWord_3916246
  simp only [CollatzResearch.WordTrace]
  refine ⟨8927326635632316150794537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95224817446744705608475061 8927326635632316150794537)
  ·
    refine ⟨6695494976724237113095903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8927326635632316150794537 6695494976724237113095903)
    ·
      refine ⟨10043242465086355669643855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6695494976724237113095903 10043242465086355669643855)
      ·
        refine ⟨15064863697629533504465783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10043242465086355669643855 15064863697629533504465783)
        ·
          refine ⟨22597295546444300256698675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15064863697629533504465783 22597295546444300256698675)
          ·
            refine ⟨33895943319666450385048013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22597295546444300256698675 33895943319666450385048013)
            ·
              refine ⟨12710978744874918894393005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33895943319666450385048013 12710978744874918894393005)
              ·
                refine ⟨4766617029328094585397377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12710978744874918894393005 4766617029328094585397377)
                ·
                  refine ⟨3574962771996070939048033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4766617029328094585397377 3574962771996070939048033)
                  ·
                    refine ⟨2681222078997053204286025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3574962771996070939048033 2681222078997053204286025)
                    ·
                      refine ⟨2010916559247789903214519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2681222078997053204286025 2010916559247789903214519)
                      ·
                        rfl

theorem cell23_3916246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_3916246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916246 prefixEnd_3916246 := by exact prefixLift 3916246
  have htrace : WordTrace (prefixWord ++ tailWord_3916246) baseStart_3916246 baseEnd_3916246 := by
    simpa [prefixWord, tailWord_3916246, baseEnd_3916246] using wordTrace_append hprefix tailTrace_3916246
  have hstable : (prefixWord ++ tailWord_3916246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916246).length < 2 ^ (prefixWord ++ tailWord_3916246).sum := by decide
  have hdescent : baseEnd_3916246 < baseStart_3916246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916248 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 6, 5]
def baseStart_3916248 : Nat := 118140960795 + 3916248 * 2 ^ 59
def prefixEnd_3916248 : Nat := 4983230072969 + 3 ^ 40 * 3916248 * 2
def baseEnd_3916248 : Nat := 670305862069699631796503

theorem tailTrace_3916248 : CollatzResearch.WordTrace tailWord_3916248 prefixEnd_3916248 670305862069699631796503 := by
  unfold tailWord_3916248
  simp only [CollatzResearch.WordTrace]
  refine ⟨71418649558054906377142699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95224866077406541836190265 71418649558054906377142699)
  ·
    refine ⟨107127974337082359565714049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71418649558054906377142699 107127974337082359565714049)
    ·
      refine ⟨80345980752811769674285537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107127974337082359565714049 80345980752811769674285537)
      ·
        refine ⟨60259485564608827255714153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80345980752811769674285537 60259485564608827255714153)
        ·
          refine ⟨45194614173456620441785615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60259485564608827255714153 45194614173456620441785615)
          ·
            refine ⟨67791921260184930662678423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45194614173456620441785615 67791921260184930662678423)
            ·
              refine ⟨101687881890277395994017635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67791921260184930662678423 101687881890277395994017635)
              ·
                refine ⟨152531822835416093991026453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101687881890277395994017635 152531822835416093991026453)
                ·
                  refine ⟨7149929195410129405829365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 152531822835416093991026453 7149929195410129405829365)
                  ·
                    refine ⟨670305862069699631796503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7149929195410129405829365 670305862069699631796503)
                    ·
                      rfl

theorem cell23_3916248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 6, 5].length) (baseStart_3916248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916248 prefixEnd_3916248 := by exact prefixLift 3916248
  have htrace : WordTrace (prefixWord ++ tailWord_3916248) baseStart_3916248 baseEnd_3916248 := by
    simpa [prefixWord, tailWord_3916248, baseEnd_3916248] using wordTrace_append hprefix tailTrace_3916248
  have hstable : (prefixWord ++ tailWord_3916248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916248).length < 2 ^ (prefixWord ++ tailWord_3916248).sum := by decide
  have hdescent : baseEnd_3916248 < baseStart_3916248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916285 : List Nat := [1, 4, 1, 1, 1, 3, 1, 4, 2, 1, 4]
def baseStart_3916285 : Nat := 118140960795 + 3916285 * 2 ^ 59
def prefixEnd_3916285 : Nat := 4983230072969 + 3 ^ 40 * 3916285 * 2
def baseEnd_3916285 : Nat := 2010936584993315250626839

theorem tailTrace_3916285 : CollatzResearch.WordTrace tailWord_3916285 prefixEnd_3916285 2010936584993315250626839 := by
  unfold tailWord_3916285
  simp only [CollatzResearch.WordTrace]
  refine ⟨142838648616975768073382309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95225765744650512048921539 142838648616975768073382309)
  ·
    refine ⟨26782246615682956513759183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142838648616975768073382309 26782246615682956513759183)
    ·
      refine ⟨40173369923524434770638775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26782246615682956513759183 40173369923524434770638775)
      ·
        refine ⟨60260054885286652155958163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40173369923524434770638775 60260054885286652155958163)
        ·
          refine ⟨90390082327929978233937245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60260054885286652155958163 90390082327929978233937245)
          ·
            refine ⟨33896280872973741837726467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90390082327929978233937245 33896280872973741837726467)
            ·
              refine ⟨50844421309460612756589701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33896280872973741837726467 50844421309460612756589701)
              ·
                refine ⟨9533328995523864891860569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50844421309460612756589701 9533328995523864891860569)
                ·
                  refine ⟨7149996746642898668895427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9533328995523864891860569 7149996746642898668895427)
                  ·
                    refine ⟨10724995119964348003343141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7149996746642898668895427 10724995119964348003343141)
                    ·
                      refine ⟨2010936584993315250626839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10724995119964348003343141 2010936584993315250626839)
                      ·
                        rfl

theorem cell23_3916285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_3916285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916285 prefixEnd_3916285 := by exact prefixLift 3916285
  have htrace : WordTrace (prefixWord ++ tailWord_3916285) baseStart_3916285 baseEnd_3916285 := by
    simpa [prefixWord, tailWord_3916285, baseEnd_3916285] using wordTrace_append hprefix tailTrace_3916285
  have hstable : (prefixWord ++ tailWord_3916285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916285).length < 2 ^ (prefixWord ++ tailWord_3916285).sum := by decide
  have hdescent : baseEnd_3916285 < baseStart_3916285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916302 : List Nat := [4, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2]
def baseStart_3916302 : Nat := 118140960795 + 3916302 * 2 ^ 59
def prefixEnd_3916302 : Nat := 4983230072969 + 3 ^ 40 * 3916302 * 2
def baseEnd_3916302 : Nat := 2010945314164441684114261

theorem tailTrace_3916302 : CollatzResearch.WordTrace tailWord_3916302 prefixEnd_3916302 2010945314164441684114261 := by
  unfold tailWord_3916302
  simp only [CollatzResearch.WordTrace]
  refine ⟨17854908582239272497093895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95226179105276119984500773 17854908582239272497093895)
  ·
    refine ⟨26782362873358908745640843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17854908582239272497093895 26782362873358908745640843)
    ·
      refine ⟨40173544310038363118461265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26782362873358908745640843 40173544310038363118461265)
      ·
        refine ⟨30130158232528772338845949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40173544310038363118461265 30130158232528772338845949)
        ·
          refine ⟨11298809337198289627067231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30130158232528772338845949 11298809337198289627067231)
          ·
            refine ⟨16948214005797434440600847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11298809337198289627067231 16948214005797434440600847)
            ·
              refine ⟨25422321008696151660901271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16948214005797434440600847 25422321008696151660901271)
              ·
                refine ⟨38133481513044227491351907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25422321008696151660901271 38133481513044227491351907)
                ·
                  refine ⟨57200222269566341237027861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38133481513044227491351907 57200222269566341237027861)
                  ·
                    refine ⟨2681260418885922245485681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 57200222269566341237027861 2681260418885922245485681)
                    ·
                      refine ⟨2010945314164441684114261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2681260418885922245485681 2010945314164441684114261)
                      ·
                        rfl

theorem cell23_3916302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_3916302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916302 prefixEnd_3916302 := by exact prefixLift 3916302
  have htrace : WordTrace (prefixWord ++ tailWord_3916302) baseStart_3916302 baseEnd_3916302 := by
    simpa [prefixWord, tailWord_3916302, baseEnd_3916302] using wordTrace_append hprefix tailTrace_3916302
  have hstable : (prefixWord ++ tailWord_3916302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916302).length < 2 ^ (prefixWord ++ tailWord_3916302).sum := by decide
  have hdescent : baseEnd_3916302 < baseStart_3916302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916312 : List Nat := [2, 1, 2, 3, 3, 2, 1, 2, 3, 4]
def baseStart_3916312 : Nat := 118140960795 + 3916312 * 2 ^ 59
def prefixEnd_3916312 : Nat := 4983230072969 + 3 ^ 40 * 3916312 * 2
def baseEnd_3916312 : Nat := 670316816323662214996405

theorem tailTrace_3916312 : CollatzResearch.WordTrace tailWord_3916312 prefixEnd_3916312 670316816323662214996405 := by
  unfold tailWord_3916312
  simp only [CollatzResearch.WordTrace]
  refine ⟨71419816693938975842307595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95226422258585301123076793 71419816693938975842307595)
  ·
    refine ⟨107129725040908463763461393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71419816693938975842307595 107129725040908463763461393)
    ·
      refine ⟨80347293780681347822596045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107129725040908463763461393 80347293780681347822596045)
      ·
        refine ⟨30130235167755505433473517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80347293780681347822596045 30130235167755505433473517)
        ·
          refine ⟨11298838187908314537552569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30130235167755505433473517 11298838187908314537552569)
          ·
            refine ⟨8474128640931235903164427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11298838187908314537552569 8474128640931235903164427)
            ·
              refine ⟨12711192961396853854746641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8474128640931235903164427 12711192961396853854746641)
              ·
                refine ⟨9533394721047640391059981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12711192961396853854746641 9533394721047640391059981)
                ·
                  refine ⟨3575023020392865146647493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9533394721047640391059981 3575023020392865146647493)
                  ·
                    refine ⟨670316816323662214996405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3575023020392865146647493 670316816323662214996405)
                    ·
                      rfl

theorem cell23_3916312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 3, 4].length) (baseStart_3916312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916312 prefixEnd_3916312 := by exact prefixLift 3916312
  have htrace : WordTrace (prefixWord ++ tailWord_3916312) baseStart_3916312 baseEnd_3916312 := by
    simpa [prefixWord, tailWord_3916312, baseEnd_3916312] using wordTrace_append hprefix tailTrace_3916312
  have hstable : (prefixWord ++ tailWord_3916312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916312).length < 2 ^ (prefixWord ++ tailWord_3916312).sum := by decide
  have hdescent : baseEnd_3916312 < baseStart_3916312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916342 : List Nat := [5, 1, 2, 1, 2, 2, 1, 1, 8]
def baseStart_3916342 : Nat := 118140960795 + 3916342 * 2 ^ 59
def prefixEnd_3916342 : Nat := 4983230072969 + 3 ^ 40 * 3916342 * 2
def baseEnd_3916342 : Nat := 223440650376735725290453

theorem tailTrace_3916342 : CollatzResearch.WordTrace tailWord_3916342 prefixEnd_3916342 223440650376735725290453 := by
  unfold tailWord_3916342
  simp only [CollatzResearch.WordTrace]
  refine ⟨8927545473610579175512955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95227151718512844538804853 8927545473610579175512955)
  ·
    refine ⟨13391318210415868763269433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8927545473610579175512955 13391318210415868763269433)
    ·
      refine ⟨10043488657811901572452075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13391318210415868763269433 10043488657811901572452075)
      ·
        refine ⟨15065232986717852358678113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10043488657811901572452075 15065232986717852358678113)
        ·
          refine ⟨11298924740038389269008585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15065232986717852358678113 11298924740038389269008585)
          ·
            refine ⟨8474193555028791951756439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11298924740038389269008585 8474193555028791951756439)
            ·
              refine ⟨12711290332543187927634659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8474193555028791951756439 12711290332543187927634659)
              ·
                refine ⟨19066935498814781891451989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12711290332543187927634659 19066935498814781891451989)
                ·
                  refine ⟨223440650376735725290453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19066935498814781891451989 223440650376735725290453)
                  ·
                    rfl

theorem cell23_3916342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_3916342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916342 prefixEnd_3916342 := by exact prefixLift 3916342
  have htrace : WordTrace (prefixWord ++ tailWord_3916342) baseStart_3916342 baseEnd_3916342 := by
    simpa [prefixWord, tailWord_3916342, baseEnd_3916342] using wordTrace_append hprefix tailTrace_3916342
  have hstable : (prefixWord ++ tailWord_3916342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916342).length < 2 ^ (prefixWord ++ tailWord_3916342).sum := by decide
  have hdescent : baseEnd_3916342 < baseStart_3916342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916352 : List Nat := [2, 1, 1, 2, 2, 2, 3, 3, 3, 1, 3]
def baseStart_3916352 : Nat := 118140960795 + 3916352 * 2 ^ 59
def prefixEnd_3916352 : Nat := 4983230072969 + 3 ^ 40 * 3916352 * 2
def baseEnd_3916352 : Nat := 2010970988197166488489031

theorem tailTrace_3916352 : CollatzResearch.WordTrace tailWord_3916352 prefixEnd_3916352 2010970988197166488489031 := by
  unfold tailWord_3916352
  simp only [CollatzResearch.WordTrace]
  refine ⟨71420546153866519258035655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95227394871822025677380873 71420546153866519258035655)
  ·
    refine ⟨107130819230799778887053483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71420546153866519258035655 107130819230799778887053483)
    ·
      refine ⟨160696228846199668330580225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107130819230799778887053483 160696228846199668330580225)
      ·
        refine ⟨120522171634649751247935169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160696228846199668330580225 120522171634649751247935169)
        ·
          refine ⟨90391628725987313435951377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120522171634649751247935169 90391628725987313435951377)
          ·
            refine ⟨67793721544490485076963533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90391628725987313435951377 67793721544490485076963533)
            ·
              refine ⟨25422645579183931903861325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67793721544490485076963533 25422645579183931903861325)
              ·
                refine ⟨9533492092193974463947997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25422645579183931903861325 9533492092193974463947997)
                ·
                  refine ⟨3575059534572740423980499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9533492092193974463947997 3575059534572740423980499)
                  ·
                    refine ⟨5362589301859110635970749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3575059534572740423980499 5362589301859110635970749)
                    ·
                      refine ⟨2010970988197166488489031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5362589301859110635970749 2010970988197166488489031)
                      ·
                        rfl

theorem cell23_3916352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 3, 1, 3].length) (baseStart_3916352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916352 prefixEnd_3916352 := by exact prefixLift 3916352
  have htrace : WordTrace (prefixWord ++ tailWord_3916352) baseStart_3916352 baseEnd_3916352 := by
    simpa [prefixWord, tailWord_3916352, baseEnd_3916352] using wordTrace_append hprefix tailTrace_3916352
  have hstable : (prefixWord ++ tailWord_3916352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916352).length < 2 ^ (prefixWord ++ tailWord_3916352).sum := by decide
  have hdescent : baseEnd_3916352 < baseStart_3916352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916362 : List Nat := [3, 1, 2, 1, 1, 4, 1, 2, 1, 5, 2]
def baseStart_3916362 : Nat := 118140960795 + 3916362 * 2 ^ 59
def prefixEnd_3916362 : Nat := 4983230072969 + 3 ^ 40 * 3916362 * 2
def baseEnd_3916362 : Nat := 2010976123003711449363985

theorem tailTrace_3916362 : CollatzResearch.WordTrace tailWord_3916362 prefixEnd_3916362 2010976123003711449363985 := by
  unfold tailWord_3916362
  simp only [CollatzResearch.WordTrace]
  refine ⟨35710364259424202555983835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95227638025131206815956893 35710364259424202555983835)
  ·
    refine ⟨53565546389136303833975753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35710364259424202555983835 53565546389136303833975753)
    ·
      refine ⟨40174159791852227875481815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53565546389136303833975753 40174159791852227875481815)
      ·
        refine ⟨60261239687778341813222723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40174159791852227875481815 60261239687778341813222723)
        ·
          refine ⟨90391859531667512719834085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60261239687778341813222723 90391859531667512719834085)
          ·
            refine ⟨16948473662187658634968891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90391859531667512719834085 16948473662187658634968891)
            ·
              refine ⟨25422710493281487952453337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16948473662187658634968891 25422710493281487952453337)
              ·
                refine ⟨19067032869961115964340003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25422710493281487952453337 19067032869961115964340003)
                ·
                  refine ⟨28600549304941673946510005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19067032869961115964340003 28600549304941673946510005)
                  ·
                    refine ⟨2681301497338281932485313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28600549304941673946510005 2681301497338281932485313)
                    ·
                      refine ⟨2010976123003711449363985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2681301497338281932485313 2010976123003711449363985)
                      ·
                        rfl

theorem cell23_3916362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 1, 5, 2].length) (baseStart_3916362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916362 prefixEnd_3916362 := by exact prefixLift 3916362
  have htrace : WordTrace (prefixWord ++ tailWord_3916362) baseStart_3916362 baseEnd_3916362 := by
    simpa [prefixWord, tailWord_3916362, baseEnd_3916362] using wordTrace_append hprefix tailTrace_3916362
  have hstable : (prefixWord ++ tailWord_3916362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916362).length < 2 ^ (prefixWord ++ tailWord_3916362).sum := by decide
  have hdescent : baseEnd_3916362 < baseStart_3916362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916372 : List Nat := [2, 4, 1, 1, 1, 3, 1, 4, 1, 5]
def baseStart_3916372 : Nat := 118140960795 + 3916372 * 2 ^ 59
def prefixEnd_3916372 : Nat := 4983230072969 + 3 ^ 40 * 3916372 * 2
def baseEnd_3916372 : Nat := 670327085936752136746313

theorem tailTrace_3916372 : CollatzResearch.WordTrace tailWord_3916372 prefixEnd_3916372 670327085936752136746313 := by
  unfold tailWord_3916372
  simp only [CollatzResearch.WordTrace]
  refine ⟨71420910883830290965899685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95227881178440387954532913 71420910883830290965899685)
  ·
    refine ⟨13391420790718179556106191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71420910883830290965899685 13391420790718179556106191)
    ·
      refine ⟨20087131186077269334159287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13391420790718179556106191 20087131186077269334159287)
      ·
        refine ⟨30130696779115904001238931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20087131186077269334159287 30130696779115904001238931)
        ·
          refine ⟨45196045168673856001858397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30130696779115904001238931 45196045168673856001858397)
          ·
            refine ⟨16948516938252696000696899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45196045168673856001858397 16948516938252696000696899)
            ·
              refine ⟨25422775407379044001045349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16948516938252696000696899 25422775407379044001045349)
              ·
                refine ⟨4766770388883570750196003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25422775407379044001045349 4766770388883570750196003)
                ·
                  refine ⟨7150155583325356125294005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4766770388883570750196003 7150155583325356125294005)
                  ·
                    refine ⟨670327085936752136746313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7150155583325356125294005 670327085936752136746313)
                    ·
                      rfl

theorem cell23_3916372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_3916372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916372 prefixEnd_3916372 := by exact prefixLift 3916372
  have htrace : WordTrace (prefixWord ++ tailWord_3916372) baseStart_3916372 baseEnd_3916372 := by
    simpa [prefixWord, tailWord_3916372, baseEnd_3916372] using wordTrace_append hprefix tailTrace_3916372
  have hstable : (prefixWord ++ tailWord_3916372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916372).length < 2 ^ (prefixWord ++ tailWord_3916372).sum := by decide
  have hdescent : baseEnd_3916372 < baseStart_3916372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916419 : List Nat := [1, 1, 1, 3, 3, 1, 6, 1, 2, 4]
def baseStart_3916419 : Nat := 118140960795 + 3916419 * 2 ^ 59
def prefixEnd_3916419 : Nat := 4983230072969 + 3 ^ 40 * 3916419 * 2
def baseEnd_3916419 : Nat := 670335130467005908783741

theorem tailTrace_3916419 : CollatzResearch.WordTrace tailWord_3916419 prefixEnd_3916419 670335130467005908783741 := by
  unfold tailWord_3916419
  simp only [CollatzResearch.WordTrace]
  refine ⟨142843535998490308958760311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95229023998993539305840207 142843535998490308958760311)
  ·
    refine ⟨214265303997735463438140467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142843535998490308958760311 214265303997735463438140467)
    ·
      refine ⟨321397955996603195157210701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214265303997735463438140467 321397955996603195157210701)
      ·
        refine ⟨120524233498726198183954013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321397955996603195157210701 120524233498726198183954013)
        ·
          refine ⟨45196587562022324318982755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120524233498726198183954013 45196587562022324318982755)
          ·
            refine ⟨67794881343033486478474133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45196587562022324318982755 67794881343033486478474133)
            ·
              refine ⟨3177885062954694678678475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 67794881343033486478474133 3177885062954694678678475)
              ·
                refine ⟨4766827594432042018017713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3177885062954694678678475 4766827594432042018017713)
                ·
                  refine ⟨3575120695824031513513285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4766827594432042018017713 3575120695824031513513285)
                  ·
                    refine ⟨670335130467005908783741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3575120695824031513513285 670335130467005908783741)
                    ·
                      rfl

theorem cell23_3916419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 2, 4].length) (baseStart_3916419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916419 prefixEnd_3916419 := by exact prefixLift 3916419
  have htrace : WordTrace (prefixWord ++ tailWord_3916419) baseStart_3916419 baseEnd_3916419 := by
    simpa [prefixWord, tailWord_3916419, baseEnd_3916419] using wordTrace_append hprefix tailTrace_3916419
  have hstable : (prefixWord ++ tailWord_3916419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916419).length < 2 ^ (prefixWord ++ tailWord_3916419).sum := by decide
  have hdescent : baseEnd_3916419 < baseStart_3916419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916426 : List Nat := [3, 1, 2, 3, 3, 2, 1, 2, 1, 1, 4]
def baseStart_3916426 : Nat := 118140960795 + 3916426 * 2 ^ 59
def prefixEnd_3916426 : Nat := 4983230072969 + 3 ^ 40 * 3916426 * 2
def baseEnd_3916426 : Nat := 2011008985765599198963691

theorem tailTrace_3916426 : CollatzResearch.WordTrace tailWord_3916426 prefixEnd_3916426 2011008985765599198963691 := by
  unfold tailWord_3916426
  simp only [CollatzResearch.WordTrace]
  refine ⟨35710947827366237288566283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95229194206309966102843421 35710947827366237288566283)
  ·
    refine ⟨53566421741049355932849425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35710947827366237288566283 53566421741049355932849425)
    ·
      refine ⟨40174816305787016949637069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53566421741049355932849425 40174816305787016949637069)
      ·
        refine ⟨15065556114670131356113901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40174816305787016949637069 15065556114670131356113901)
        ·
          refine ⟨5649583543001299258542713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15065556114670131356113901 5649583543001299258542713)
          ·
            refine ⟨4237187657250974443907035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5649583543001299258542713 4237187657250974443907035)
            ·
              refine ⟨6355781485876461665860553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4237187657250974443907035 6355781485876461665860553)
              ·
                refine ⟨4766836114407346249395415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6355781485876461665860553 4766836114407346249395415)
                ·
                  refine ⟨7150254171611019374093123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4766836114407346249395415 7150254171611019374093123)
                  ·
                    refine ⟨10725381257416529061139685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7150254171611019374093123 10725381257416529061139685)
                    ·
                      refine ⟨2011008985765599198963691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10725381257416529061139685 2011008985765599198963691)
                      ·
                        rfl

theorem cell23_3916426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_3916426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916426 prefixEnd_3916426 := by exact prefixLift 3916426
  have htrace : WordTrace (prefixWord ++ tailWord_3916426) baseStart_3916426 baseEnd_3916426 := by
    simpa [prefixWord, tailWord_3916426, baseEnd_3916426] using wordTrace_append hprefix tailTrace_3916426
  have hstable : (prefixWord ++ tailWord_3916426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916426).length < 2 ^ (prefixWord ++ tailWord_3916426).sum := by decide
  have hdescent : baseEnd_3916426 < baseStart_3916426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916503 : List Nat := [1, 1, 3, 2, 1, 6, 2, 1, 1, 3, 2]
def baseStart_3916503 : Nat := 118140960795 + 3916503 * 2 ^ 59
def prefixEnd_3916503 : Nat := 4983230072969 + 3 ^ 40 * 3916503 * 2
def baseEnd_3916503 : Nat := 2011048523775995397700837

theorem tailTrace_3916503 : CollatzResearch.WordTrace tailWord_3916503 prefixEnd_3916503 2011048523775995397700837 := by
  unfold tailWord_3916503
  simp only [CollatzResearch.WordTrace]
  refine ⟨142846599730185991304818163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95231066486790660869878775 142846599730185991304818163)
  ·
    refine ⟨214269899595278986957227245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142846599730185991304818163 214269899595278986957227245)
    ·
      refine ⟨80351212348229620108960217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214269899595278986957227245 80351212348229620108960217)
      ·
        refine ⟨60263409261172215081720163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80351212348229620108960217 60263409261172215081720163)
        ·
          refine ⟨90395113891758322622580245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60263409261172215081720163 90395113891758322622580245)
          ·
            refine ⟨4237270963676171372933449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 90395113891758322622580245 4237270963676171372933449)
            ·
              refine ⟨3177953222757128529700087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4237270963676171372933449 3177953222757128529700087)
              ·
                refine ⟨4766929834135692794550131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3177953222757128529700087 4766929834135692794550131)
                ·
                  refine ⟨7150394751203539191825197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4766929834135692794550131 7150394751203539191825197)
                  ·
                    refine ⟨2681398031701327196934449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7150394751203539191825197 2681398031701327196934449)
                    ·
                      refine ⟨2011048523775995397700837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2681398031701327196934449 2011048523775995397700837)
                      ·
                        rfl

theorem cell23_3916503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 1, 3, 2].length) (baseStart_3916503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916503 prefixEnd_3916503 := by exact prefixLift 3916503
  have htrace : WordTrace (prefixWord ++ tailWord_3916503) baseStart_3916503 baseEnd_3916503 := by
    simpa [prefixWord, tailWord_3916503, baseEnd_3916503] using wordTrace_append hprefix tailTrace_3916503
  have hstable : (prefixWord ++ tailWord_3916503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916503).length < 2 ^ (prefixWord ++ tailWord_3916503).sum := by decide
  have hdescent : baseEnd_3916503 < baseStart_3916503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916505 : List Nat := [1, 2, 1, 2, 3, 2, 1, 2, 9]
def baseStart_3916505 : Nat := 118140960795 + 3916505 * 2 ^ 59
def prefixEnd_3916505 : Nat := 4983230072969 + 3 ^ 40 * 3916505 * 2
def baseEnd_3916505 : Nat := 223449950081922709986203

theorem tailTrace_3916505 : CollatzResearch.WordTrace tailWord_3916505 prefixEnd_3916505 223449950081922709986203 := by
  unfold tailWord_3916505
  simp only [CollatzResearch.WordTrace]
  refine ⟨142846672676178745646390969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95231115117452497097593979 142846672676178745646390969)
  ·
    refine ⟨107135004507134059234793227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142846672676178745646390969 107135004507134059234793227)
    ·
      refine ⟨160702506760701088852189841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107135004507134059234793227 160702506760701088852189841)
      ·
        refine ⟨120526880070525816639142381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160702506760701088852189841 120526880070525816639142381)
        ·
          refine ⟨45197580026447181239678393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120526880070525816639142381 45197580026447181239678393)
          ·
            refine ⟨33898185019835385929758795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45197580026447181239678393 33898185019835385929758795)
            ·
              refine ⟨50847277529753078894638193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33898185019835385929758795 50847277529753078894638193)
              ·
                refine ⟨38135458147314809170978645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50847277529753078894638193 38135458147314809170978645)
                ·
                  refine ⟨223449950081922709986203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 38135458147314809170978645 223449950081922709986203)
                  ·
                    rfl

theorem cell23_3916505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 9].length) (baseStart_3916505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916505 prefixEnd_3916505 := by exact prefixLift 3916505
  have htrace : WordTrace (prefixWord ++ tailWord_3916505) baseStart_3916505 baseEnd_3916505 := by
    simpa [prefixWord, tailWord_3916505, baseEnd_3916505] using wordTrace_append hprefix tailTrace_3916505
  have hstable : (prefixWord ++ tailWord_3916505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916505).length < 2 ^ (prefixWord ++ tailWord_3916505).sum := by decide
  have hdescent : baseEnd_3916505 < baseStart_3916505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916516 : List Nat := [2, 3, 1, 1, 1, 5, 1, 1, 4, 2, 2]
def baseStart_3916516 : Nat := 118140960795 + 3916516 * 2 ^ 59
def prefixEnd_3916516 : Nat := 4983230072969 + 3 ^ 40 * 3916516 * 2
def baseEnd_3916516 : Nat := 2011055199024503846838277

theorem tailTrace_3916516 : CollatzResearch.WordTrace tailWord_3916516 prefixEnd_3916516 2011055199024503846838277 := by
  unfold tailWord_3916516
  simp only [CollatzResearch.WordTrace]
  refine ⟨71423536939569447262520701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95231382586092596350027601 71423536939569447262520701)
  ·
    refine ⟨26783826352338542723445263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71423536939569447262520701 26783826352338542723445263)
    ·
      refine ⟨40175739528507814085167895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26783826352338542723445263 40175739528507814085167895)
      ·
        refine ⟨60263609292761721127751843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40175739528507814085167895 60263609292761721127751843)
        ·
          refine ⟨90395413939142581691627765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60263609292761721127751843 90395413939142581691627765)
          ·
            refine ⟨8474570056794617033590103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90395413939142581691627765 8474570056794617033590103)
            ·
              refine ⟨12711855085191925550385155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8474570056794617033590103 12711855085191925550385155)
              ·
                refine ⟨19067782627787888325577733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12711855085191925550385155 19067782627787888325577733)
                ·
                  refine ⟨3575209242710229061045825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19067782627787888325577733 3575209242710229061045825)
                  ·
                    refine ⟨2681406932032671795784369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3575209242710229061045825 2681406932032671795784369)
                    ·
                      refine ⟨2011055199024503846838277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2681406932032671795784369 2011055199024503846838277)
                      ·
                        rfl

theorem cell23_3916516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 4, 2, 2].length) (baseStart_3916516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916516 prefixEnd_3916516 := by exact prefixLift 3916516
  have htrace : WordTrace (prefixWord ++ tailWord_3916516) baseStart_3916516 baseEnd_3916516 := by
    simpa [prefixWord, tailWord_3916516, baseEnd_3916516] using wordTrace_append hprefix tailTrace_3916516
  have hstable : (prefixWord ++ tailWord_3916516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916516).length < 2 ^ (prefixWord ++ tailWord_3916516).sum := by decide
  have hdescent : baseEnd_3916516 < baseStart_3916516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916552 : List Nat := [2, 1, 3, 2, 2, 2, 2, 1, 1, 7]
def baseStart_3916552 : Nat := 118140960795 + 3916552 * 2 ^ 59
def prefixEnd_3916552 : Nat := 4983230072969 + 3 ^ 40 * 3916552 * 2
def baseEnd_3916552 : Nat := 670357894776021901996037

theorem tailTrace_3916552 : CollatzResearch.WordTrace tailWord_3916552 prefixEnd_3916552 670357894776021901996037 := by
  unfold tailWord_3916552
  simp only [CollatzResearch.WordTrace]
  refine ⟨71424193453504236336675955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95232257938005648448901273 71424193453504236336675955)
  ·
    refine ⟨107136290180256354505013933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71424193453504236336675955 107136290180256354505013933)
    ·
      refine ⟨40176108817596132939380225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107136290180256354505013933 40176108817596132939380225)
      ·
        refine ⟨30132081613197099704535169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40176108817596132939380225 30132081613197099704535169)
        ·
          refine ⟨22599061209897824778401377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30132081613197099704535169 22599061209897824778401377)
          ·
            refine ⟨16949295907423368583801033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22599061209897824778401377 16949295907423368583801033)
            ·
              refine ⟨12711971930567526437850775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16949295907423368583801033 12711971930567526437850775)
              ·
                refine ⟨19067957895851289656776163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12711971930567526437850775 19067957895851289656776163)
                ·
                  refine ⟨28601936843776934485164245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19067957895851289656776163 28601936843776934485164245)
                  ·
                    refine ⟨670357894776021901996037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28601936843776934485164245 670357894776021901996037)
                    ·
                      rfl

theorem cell23_3916552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_3916552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916552 prefixEnd_3916552 := by exact prefixLift 3916552
  have htrace : WordTrace (prefixWord ++ tailWord_3916552) baseStart_3916552 baseEnd_3916552 := by
    simpa [prefixWord, tailWord_3916552, baseEnd_3916552] using wordTrace_append hprefix tailTrace_3916552
  have hstable : (prefixWord ++ tailWord_3916552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916552).length < 2 ^ (prefixWord ++ tailWord_3916552).sum := by decide
  have hdescent : baseEnd_3916552 < baseStart_3916552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916573 : List Nat := [1, 4, 2, 4, 2, 1, 1, 1, 7]
def baseStart_3916573 : Nat := 118140960795 + 3916573 * 2 ^ 59
def prefixEnd_3916573 : Nat := 4983230072969 + 3 ^ 40 * 3916573 * 2
def baseEnd_3916573 : Nat := 223453829713534458202835

theorem tailTrace_3916573 : CollatzResearch.WordTrace tailWord_3916573 prefixEnd_3916573 223453829713534458202835 := by
  unfold tailWord_3916573
  simp only [CollatzResearch.WordTrace]
  refine ⟨142849152839932393259866373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95232768559954928839910915 142849152839932393259866373)
  ·
    refine ⟨26784216157487323736224945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142849152839932393259866373 26784216157487323736224945)
    ·
      refine ⟨20088162118115492802168709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26784216157487323736224945 20088162118115492802168709)
      ·
        refine ⟨3766530397146654900406633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20088162118115492802168709 3766530397146654900406633)
        ·
          refine ⟨2824897797859991175304975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3766530397146654900406633 2824897797859991175304975)
          ·
            refine ⟨4237346696789986762957463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2824897797859991175304975 4237346696789986762957463)
            ·
              refine ⟨6356020045184980144436195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4237346696789986762957463 6356020045184980144436195)
              ·
                refine ⟨9534030067777470216654293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6356020045184980144436195 9534030067777470216654293)
                ·
                  refine ⟨223453829713534458202835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9534030067777470216654293 223453829713534458202835)
                  ·
                    rfl

theorem cell23_3916573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 7].length) (baseStart_3916573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916573 prefixEnd_3916573 := by exact prefixLift 3916573
  have htrace : WordTrace (prefixWord ++ tailWord_3916573) baseStart_3916573 baseEnd_3916573 := by
    simpa [prefixWord, tailWord_3916573, baseEnd_3916573] using wordTrace_append hprefix tailTrace_3916573
  have hstable : (prefixWord ++ tailWord_3916573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916573).length < 2 ^ (prefixWord ++ tailWord_3916573).sum := by decide
  have hdescent : baseEnd_3916573 < baseStart_3916573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916592 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 3]
def baseStart_3916592 : Nat := 118140960795 + 3916592 * 2 ^ 59
def prefixEnd_3916592 : Nat := 4983230072969 + 3 ^ 40 * 3916592 * 2
def baseEnd_3916592 : Nat := 2011094223554245549487927

theorem tailTrace_3916592 : CollatzResearch.WordTrace tailWord_3916592 prefixEnd_3916592 2011094223554245549487927 := by
  unfold tailWord_3916592
  simp only [CollatzResearch.WordTrace]
  refine ⟨71424922913431779752404015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95233230551242373003205353 71424922913431779752404015)
  ·
    refine ⟨107137384370147669628606023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71424922913431779752404015 107137384370147669628606023)
    ·
      refine ⟨160706076555221504442909035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107137384370147669628606023 160706076555221504442909035)
      ·
        refine ⟨241059114832832256664363553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160706076555221504442909035 241059114832832256664363553)
        ·
          refine ⟨180794336124624192498272665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241059114832832256664363553 180794336124624192498272665)
          ·
            refine ⟨135595752093468144373704499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180794336124624192498272665 135595752093468144373704499)
            ·
              refine ⟨203393628140202216560556749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135595752093468144373704499 203393628140202216560556749)
              ·
                refine ⟨76272610552575831210208781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203393628140202216560556749 76272610552575831210208781)
                ·
                  refine ⟨28602228957215936703828293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76272610552575831210208781 28602228957215936703828293)
                  ·
                    refine ⟨5362917929477988131967805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28602228957215936703828293 5362917929477988131967805)
                    ·
                      refine ⟨2011094223554245549487927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5362917929477988131967805 2011094223554245549487927)
                      ·
                        rfl

theorem cell23_3916592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 3].length) (baseStart_3916592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916592 prefixEnd_3916592 := by exact prefixLift 3916592
  have htrace : WordTrace (prefixWord ++ tailWord_3916592) baseStart_3916592 baseEnd_3916592 := by
    simpa [prefixWord, tailWord_3916592, baseEnd_3916592] using wordTrace_append hprefix tailTrace_3916592
  have hstable : (prefixWord ++ tailWord_3916592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916592).length < 2 ^ (prefixWord ++ tailWord_3916592).sum := by decide
  have hdescent : baseEnd_3916592 < baseStart_3916592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916616 : List Nat := [2, 1, 3, 1, 1, 3, 2, 5, 1, 4]
def baseStart_3916616 : Nat := 118140960795 + 3916616 * 2 ^ 59
def prefixEnd_3916616 : Nat := 4983230072969 + 3 ^ 40 * 3916616 * 2
def baseEnd_3916616 : Nat := 670368849029984485195939

theorem tailTrace_3916616 : CollatzResearch.WordTrace tailWord_3916616 prefixEnd_3916616 670368849029984485195939 := by
  unfold tailWord_3916616
  simp only [CollatzResearch.WordTrace]
  refine ⟨71425360589388305801840851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95233814119184407735787801 71425360589388305801840851)
  ·
    refine ⟨107138040884082458702761277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71425360589388305801840851 107138040884082458702761277)
    ·
      refine ⟨40176765331530922013535479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107138040884082458702761277 40176765331530922013535479)
      ·
        refine ⟨60265147997296383020303219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40176765331530922013535479 60265147997296383020303219)
        ·
          refine ⟨90397721995944574530454829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60265147997296383020303219 90397721995944574530454829)
          ·
            refine ⟨33899145748479215448920561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90397721995944574530454829 33899145748479215448920561)
            ·
              refine ⟨25424359311359411586690421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33899145748479215448920561 25424359311359411586690421)
              ·
                refine ⟨2383533685439944836252227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25424359311359411586690421 2383533685439944836252227)
                ·
                  refine ⟨3575300528159917254378341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2383533685439944836252227 3575300528159917254378341)
                  ·
                    refine ⟨670368849029984485195939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3575300528159917254378341 670368849029984485195939)
                    ·
                      rfl

theorem cell23_3916616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 5, 1, 4].length) (baseStart_3916616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916616 prefixEnd_3916616 := by exact prefixLift 3916616
  have htrace : WordTrace (prefixWord ++ tailWord_3916616) baseStart_3916616 baseEnd_3916616 := by
    simpa [prefixWord, tailWord_3916616, baseEnd_3916616] using wordTrace_append hprefix tailTrace_3916616
  have hstable : (prefixWord ++ tailWord_3916616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916616).length < 2 ^ (prefixWord ++ tailWord_3916616).sum := by decide
  have hdescent : baseEnd_3916616 < baseStart_3916616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916629 : List Nat := [1, 3, 2, 2, 2, 1, 4, 2, 6]
def baseStart_3916629 : Nat := 118140960795 + 3916629 * 2 ^ 59
def prefixEnd_3916629 : Nat := 4983230072969 + 3 ^ 40 * 3916629 * 2
def baseEnd_3916629 : Nat := 223457024704273544969473

theorem tailTrace_3916629 : CollatzResearch.WordTrace tailWord_3916629 prefixEnd_3916629 223457024704273544969473 := by
  unfold tailWord_3916629
  simp only [CollatzResearch.WordTrace]
  refine ⟨142851195327729514823904941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95234130218486343215936627 142851195327729514823904941)
  ·
    refine ⟨53569198247898568058964353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142851195327729514823904941 53569198247898568058964353)
    ·
      refine ⟨40176898685923926044223265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53569198247898568058964353 40176898685923926044223265)
      ·
        refine ⟨30132674014442944533167449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40176898685923926044223265 30132674014442944533167449)
        ·
          refine ⟨22599505510832208399875587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30132674014442944533167449 22599505510832208399875587)
          ·
            refine ⟨33899258266248312599813381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22599505510832208399875587 33899258266248312599813381)
            ·
              refine ⟨6356110924921558612465009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33899258266248312599813381 6356110924921558612465009)
              ·
                refine ⟨4767083193691168959348757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6356110924921558612465009 4767083193691168959348757)
                ·
                  refine ⟨223457024704273544969473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4767083193691168959348757 223457024704273544969473)
                  ·
                    rfl

theorem cell23_3916629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 6].length) (baseStart_3916629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916629 prefixEnd_3916629 := by exact prefixLift 3916629
  have htrace : WordTrace (prefixWord ++ tailWord_3916629) baseStart_3916629 baseEnd_3916629 := by
    simpa [prefixWord, tailWord_3916629, baseEnd_3916629] using wordTrace_append hprefix tailTrace_3916629
  have hstable : (prefixWord ++ tailWord_3916629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916629).length < 2 ^ (prefixWord ++ tailWord_3916629).sum := by decide
  have hdescent : baseEnd_3916629 < baseStart_3916629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916633 : List Nat := [1, 2, 1, 2, 2, 4, 4, 2, 1, 4]
def baseStart_3916633 : Nat := 118140960795 + 3916633 * 2 ^ 59
def prefixEnd_3916633 : Nat := 4983230072969 + 3 ^ 40 * 3916633 * 2
def baseEnd_3916633 : Nat := 670371758753693296358413

theorem tailTrace_3916633 : CollatzResearch.WordTrace tailWord_3916633 prefixEnd_3916633 670371758753693296358413 := by
  unfold tailWord_3916633
  simp only [CollatzResearch.WordTrace]
  refine ⟨142851341219715023507050553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95234227479810015671367035 142851341219715023507050553)
  ·
    refine ⟨107138505914786267630287915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142851341219715023507050553 107138505914786267630287915)
    ·
      refine ⟨160707758872179401445431873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107138505914786267630287915 160707758872179401445431873)
      ·
        refine ⟨120530819154134551084073905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160707758872179401445431873 120530819154134551084073905)
        ·
          refine ⟨90398114365600913313055429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120530819154134551084073905 90398114365600913313055429)
          ·
            refine ⟨16949646443550171246197893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90398114365600913313055429 16949646443550171246197893)
            ·
              refine ⟨3178058708165657108662105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16949646443550171246197893 3178058708165657108662105)
              ·
                refine ⟨2383544031124242831496579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3178058708165657108662105 2383544031124242831496579)
                ·
                  refine ⟨3575316046686364247244869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2383544031124242831496579 3575316046686364247244869)
                  ·
                    refine ⟨670371758753693296358413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3575316046686364247244869 670371758753693296358413)
                    ·
                      rfl

theorem cell23_3916633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 2, 1, 4].length) (baseStart_3916633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916633 prefixEnd_3916633 := by exact prefixLift 3916633
  have htrace : WordTrace (prefixWord ++ tailWord_3916633) baseStart_3916633 baseEnd_3916633 := by
    simpa [prefixWord, tailWord_3916633, baseEnd_3916633] using wordTrace_append hprefix tailTrace_3916633
  have hstable : (prefixWord ++ tailWord_3916633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916633).length < 2 ^ (prefixWord ++ tailWord_3916633).sum := by decide
  have hdescent : baseEnd_3916633 < baseStart_3916633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916652 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 7]
def baseStart_3916652 : Nat := 118140960795 + 3916652 * 2 ^ 59
def prefixEnd_3916652 : Nat := 4983230072969 + 3 ^ 40 * 3916652 * 2
def baseEnd_3916652 : Nat := 2011125032393515314737651

theorem tailTrace_3916652 : CollatzResearch.WordTrace tailWord_3916652 prefixEnd_3916652 2011125032393515314737651 := by
  unfold tailWord_3916652
  simp only [CollatzResearch.WordTrace]
  refine ⟨71426017103323094875996105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95234689471097459834661473 71426017103323094875996105)
  ·
    refine ⟨53569512827492321156997079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71426017103323094875996105 53569512827492321156997079)
    ·
      refine ⟨80354269241238481735495619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53569512827492321156997079 80354269241238481735495619)
      ·
        refine ⟨120531403861857722603243429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80354269241238481735495619 120531403861857722603243429)
        ·
          refine ⟨22599638224098322988108143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120531403861857722603243429 22599638224098322988108143)
          ·
            refine ⟨33899457336147484482162215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22599638224098322988108143 33899457336147484482162215)
            ·
              refine ⟨50849186004221226723243323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33899457336147484482162215 50849186004221226723243323)
              ·
                refine ⟨76273779006331840084864985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50849186004221226723243323 76273779006331840084864985)
                ·
                  refine ⟨57205334254748880063648739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76273779006331840084864985 57205334254748880063648739)
                  ·
                    refine ⟨85808001382123320095473109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57205334254748880063648739 85808001382123320095473109)
                    ·
                      refine ⟨2011125032393515314737651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 85808001382123320095473109 2011125032393515314737651)
                      ·
                        rfl

theorem cell23_3916652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_3916652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916652 prefixEnd_3916652 := by exact prefixLift 3916652
  have htrace : WordTrace (prefixWord ++ tailWord_3916652) baseStart_3916652 baseEnd_3916652 := by
    simpa [prefixWord, tailWord_3916652, baseEnd_3916652] using wordTrace_append hprefix tailTrace_3916652
  have hstable : (prefixWord ++ tailWord_3916652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916652).length < 2 ^ (prefixWord ++ tailWord_3916652).sum := by decide
  have hdescent : baseEnd_3916652 < baseStart_3916652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916672 : List Nat := [2, 1, 1, 2, 1, 2, 2, 3, 3, 6]
def baseStart_3916672 : Nat := 118140960795 + 3916672 * 2 ^ 59
def prefixEnd_3916672 : Nat := 4983230072969 + 3 ^ 40 * 3916672 * 2
def baseEnd_3916672 : Nat := 670378434002201745495853

theorem tailTrace_3916672 : CollatzResearch.WordTrace tailWord_3916672 prefixEnd_3916672 670378434002201745495853 := by
  unfold tailWord_3916672
  simp only [CollatzResearch.WordTrace]
  refine ⟨71426381833286866583860135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95235175777715822111813513 71426381833286866583860135)
  ·
    refine ⟨107139572749930299875790203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71426381833286866583860135 107139572749930299875790203)
    ·
      refine ⟨160709359124895449813685305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107139572749930299875790203 160709359124895449813685305)
      ·
        refine ⟨120532019343671587360263979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160709359124895449813685305 120532019343671587360263979)
        ·
          refine ⟨180798029015507381040395969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120532019343671587360263979 180798029015507381040395969)
          ·
            refine ⟨135598521761630535780296977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180798029015507381040395969 135598521761630535780296977)
            ·
              refine ⟨101698891321222901835222733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135598521761630535780296977 101698891321222901835222733)
              ·
                refine ⟨38137084245458588188208525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101698891321222901835222733 38137084245458588188208525)
                ·
                  refine ⟨14301406592046970570578197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38137084245458588188208525 14301406592046970570578197)
                  ·
                    refine ⟨670378434002201745495853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14301406592046970570578197 670378434002201745495853)
                    ·
                      rfl

theorem cell23_3916672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 3, 6].length) (baseStart_3916672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916672 prefixEnd_3916672 := by exact prefixLift 3916672
  have htrace : WordTrace (prefixWord ++ tailWord_3916672) baseStart_3916672 baseEnd_3916672 := by
    simpa [prefixWord, tailWord_3916672, baseEnd_3916672] using wordTrace_append hprefix tailTrace_3916672
  have hstable : (prefixWord ++ tailWord_3916672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916672).length < 2 ^ (prefixWord ++ tailWord_3916672).sum := by decide
  have hdescent : baseEnd_3916672 < baseStart_3916672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916690 : List Nat := [3, 2, 3, 2, 2, 1, 2, 1, 3, 1, 3]
def baseStart_3916690 : Nat := 118140960795 + 3916690 * 2 ^ 59
def prefixEnd_3916690 : Nat := 4983230072969 + 3 ^ 40 * 3916690 * 2
def baseEnd_3916690 : Nat := 2011144544658386166062477

theorem tailTrace_3916690 : CollatzResearch.WordTrace tailWord_3916690 prefixEnd_3916690 2011144544658386166062477 := by
  unfold tailWord_3916690
  simp only [CollatzResearch.WordTrace]
  refine ⟨35713355045127130560468881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95235613453672348161250349 35713355045127130560468881)
  ·
    refine ⟨26785016283845347920351661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35713355045127130560468881 26785016283845347920351661)
    ·
      refine ⟨10044381106442005470131873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26785016283845347920351661 10044381106442005470131873)
      ·
        refine ⟨7533285829831504102598905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10044381106442005470131873 7533285829831504102598905)
        ·
          refine ⟨5649964372373628076949179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7533285829831504102598905 5649964372373628076949179)
          ·
            refine ⟨8474946558560442115423769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5649964372373628076949179 8474946558560442115423769)
            ·
              refine ⟨6356209918920331586567827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8474946558560442115423769 6356209918920331586567827)
              ·
                refine ⟨9534314878380497379851741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6356209918920331586567827 9534314878380497379851741)
                ·
                  refine ⟨3575368079392686517444403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9534314878380497379851741 3575368079392686517444403)
                  ·
                    refine ⟨5363052119089029776166605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3575368079392686517444403 5363052119089029776166605)
                    ·
                      refine ⟨2011144544658386166062477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5363052119089029776166605 2011144544658386166062477)
                      ·
                        rfl

theorem cell23_3916690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_3916690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916690 prefixEnd_3916690 := by exact prefixLift 3916690
  have htrace : WordTrace (prefixWord ++ tailWord_3916690) baseStart_3916690 baseEnd_3916690 := by
    simpa [prefixWord, tailWord_3916690, baseEnd_3916690] using wordTrace_append hprefix tailTrace_3916690
  have hstable : (prefixWord ++ tailWord_3916690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916690).length < 2 ^ (prefixWord ++ tailWord_3916690).sum := by decide
  have hdescent : baseEnd_3916690 < baseStart_3916690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916706 : List Nat := [3, 3, 1, 2, 2, 1, 3, 1, 1, 6]
def baseStart_3916706 : Nat := 118140960795 + 3916706 * 2 ^ 59
def prefixEnd_3916706 : Nat := 4983230072969 + 3 ^ 40 * 3916706 * 2
def baseEnd_3916706 : Nat := 670384253449619367820801

theorem tailTrace_3916706 : CollatzResearch.WordTrace tailWord_3916706 prefixEnd_3916706 670384253449619367820801 := by
  unfold tailWord_3916706
  simp only [CollatzResearch.WordTrace]
  refine ⟨35713500937112639243614493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95236002498967037982971981 35713500937112639243614493)
  ·
    refine ⟨13392562851417239716355435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35713500937112639243614493 13392562851417239716355435)
    ·
      refine ⟨20088844277125859574533153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13392562851417239716355435 20088844277125859574533153)
      ·
        refine ⟨15066633207844394680899865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20088844277125859574533153 15066633207844394680899865)
        ·
          refine ⟨11299974905883296010674899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15066633207844394680899865 11299974905883296010674899)
          ·
            refine ⟨16949962358824944016012349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11299974905883296010674899 16949962358824944016012349)
            ·
              refine ⟨6356235884559354006004631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16949962358824944016012349 6356235884559354006004631)
              ·
                refine ⟨9534353826839031009006947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6356235884559354006004631 9534353826839031009006947)
                ·
                  refine ⟨14301530740258546513510421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9534353826839031009006947 14301530740258546513510421)
                  ·
                    refine ⟨670384253449619367820801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14301530740258546513510421 670384253449619367820801)
                    ·
                      rfl

theorem cell23_3916706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_3916706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916706 prefixEnd_3916706 := by exact prefixLift 3916706
  have htrace : WordTrace (prefixWord ++ tailWord_3916706) baseStart_3916706 baseEnd_3916706 := by
    simpa [prefixWord, tailWord_3916706, baseEnd_3916706] using wordTrace_append hprefix tailTrace_3916706
  have hstable : (prefixWord ++ tailWord_3916706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916706).length < 2 ^ (prefixWord ++ tailWord_3916706).sum := by decide
  have hdescent : baseEnd_3916706 < baseStart_3916706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916724 : List Nat := [2, 5, 2, 1, 1, 3, 1, 3, 1, 1, 3]
def baseStart_3916724 : Nat := 118140960795 + 3916724 * 2 ^ 59
def prefixEnd_3916724 : Nat := 4983230072969 + 3 ^ 40 * 3916724 * 2
def baseEnd_3916724 : Nat := 2011162003000639033037321

theorem tailTrace_3916724 : CollatzResearch.WordTrace tailWord_3916724 prefixEnd_3916724 2011162003000639033037321 := by
  unfold tailWord_3916724
  simp only [CollatzResearch.WordTrace]
  refine ⟨71427330131192673024306613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95236440174923564032408817 71427330131192673024306613)
  ·
    refine ⟨6696312199799313096028745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71427330131192673024306613 6696312199799313096028745)
    ·
      refine ⟨5022234149849484822021559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6696312199799313096028745 5022234149849484822021559)
      ·
        refine ⟨7533351224774227233032339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5022234149849484822021559 7533351224774227233032339)
        ·
          refine ⟨11300026837161340849548509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7533351224774227233032339 11300026837161340849548509)
          ·
            refine ⟨4237510063935502818580691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11300026837161340849548509 4237510063935502818580691)
            ·
              refine ⟨6356265095903254227871037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4237510063935502818580691 6356265095903254227871037)
              ·
                refine ⟨2383599410963720335451639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6356265095903254227871037 2383599410963720335451639)
                ·
                  refine ⟨3575399116445580503177459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2383599410963720335451639 3575399116445580503177459)
                  ·
                    refine ⟨5363098674668370754766189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3575399116445580503177459 5363098674668370754766189)
                    ·
                      refine ⟨2011162003000639033037321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5363098674668370754766189 2011162003000639033037321)
                      ·
                        rfl

theorem cell23_3916724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_3916724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916724 prefixEnd_3916724 := by exact prefixLift 3916724
  have htrace : WordTrace (prefixWord ++ tailWord_3916724) baseStart_3916724 baseEnd_3916724 := by
    simpa [prefixWord, tailWord_3916724, baseEnd_3916724] using wordTrace_append hprefix tailTrace_3916724
  have hstable : (prefixWord ++ tailWord_3916724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916724).length < 2 ^ (prefixWord ++ tailWord_3916724).sum := by decide
  have hdescent : baseEnd_3916724 < baseStart_3916724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916747 : List Nat := [1, 1, 1, 1, 3, 6, 3, 2, 1, 2, 2]
def baseStart_3916747 : Nat := 118140960795 + 3916747 * 2 ^ 59
def prefixEnd_3916747 : Nat := 4983230072969 + 3 ^ 40 * 3916747 * 2
def baseEnd_3916747 : Nat := 2011173813055692443049715

theorem tailTrace_3916747 : CollatzResearch.WordTrace tailWord_3916747 prefixEnd_3916747 2011173813055692443049715 := by
  unfold tailWord_3916747
  simp only [CollatzResearch.WordTrace]
  refine ⟨142855499141302020976700495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95236999427534680651133663 142855499141302020976700495)
  ·
    refine ⟨214283248711953031465050743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142855499141302020976700495 214283248711953031465050743)
    ·
      refine ⟨321424873067929547197576115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214283248711953031465050743 321424873067929547197576115)
      ·
        refine ⟨482137309601894320796364173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321424873067929547197576115 482137309601894320796364173)
        ·
          refine ⟨180801491100710370298636565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 482137309601894320796364173 180801491100710370298636565)
          ·
            refine ⟨8475069895345798607748589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 180801491100710370298636565 8475069895345798607748589)
            ·
              refine ⟨3178151210754674477905721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8475069895345798607748589 3178151210754674477905721)
              ·
                refine ⟨2383613408066005858429291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3178151210754674477905721 2383613408066005858429291)
                ·
                  refine ⟨3575420112099008787643937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2383613408066005858429291 3575420112099008787643937)
                  ·
                    refine ⟨2681565084074256590732953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3575420112099008787643937 2681565084074256590732953)
                    ·
                      refine ⟨2011173813055692443049715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2681565084074256590732953 2011173813055692443049715)
                      ·
                        rfl

theorem cell23_3916747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 2, 1, 2, 2].length) (baseStart_3916747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916747 prefixEnd_3916747 := by exact prefixLift 3916747
  have htrace : WordTrace (prefixWord ++ tailWord_3916747) baseStart_3916747 baseEnd_3916747 := by
    simpa [prefixWord, tailWord_3916747, baseEnd_3916747] using wordTrace_append hprefix tailTrace_3916747
  have hstable : (prefixWord ++ tailWord_3916747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916747).length < 2 ^ (prefixWord ++ tailWord_3916747).sum := by decide
  have hdescent : baseEnd_3916747 < baseStart_3916747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916757 : List Nat := [1, 3, 2, 3, 4, 1, 2, 1, 2, 4]
def baseStart_3916757 : Nat := 118140960795 + 3916757 * 2 ^ 59
def prefixEnd_3916757 : Nat := 4983230072969 + 3 ^ 40 * 3916757 * 2
def baseEnd_3916757 : Nat := 670392982620745801308223

theorem tailTrace_3916757 : CollatzResearch.WordTrace tailWord_3916757 prefixEnd_3916757 670392982620745801308223 := by
  unfold tailWord_3916757
  simp only [CollatzResearch.WordTrace]
  refine ⟨142855863871265792684564525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95237242580843861789709683 142855863871265792684564525)
  ·
    refine ⟨53570948951724672256711697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142855863871265792684564525 53570948951724672256711697)
    ·
      refine ⟨40178211713793504192533773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53570948951724672256711697 40178211713793504192533773)
      ·
        refine ⟨15066829392672564072200165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40178211713793504192533773 15066829392672564072200165)
        ·
          refine ⟨2825030511126105763537531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15066829392672564072200165 2825030511126105763537531)
          ·
            refine ⟨4237545766689158645306297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2825030511126105763537531 4237545766689158645306297)
            ·
              refine ⟨3178159325016868983979723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4237545766689158645306297 3178159325016868983979723)
              ·
                refine ⟨4767238987525303475969585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3178159325016868983979723 4767238987525303475969585)
                ·
                  refine ⟨3575429240643977606977189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4767238987525303475969585 3575429240643977606977189)
                  ·
                    refine ⟨670392982620745801308223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3575429240643977606977189 670392982620745801308223)
                    ·
                      rfl

theorem cell23_3916757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 2, 4].length) (baseStart_3916757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916757 prefixEnd_3916757 := by exact prefixLift 3916757
  have htrace : WordTrace (prefixWord ++ tailWord_3916757) baseStart_3916757 baseEnd_3916757 := by
    simpa [prefixWord, tailWord_3916757, baseEnd_3916757] using wordTrace_append hprefix tailTrace_3916757
  have hstable : (prefixWord ++ tailWord_3916757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916757).length < 2 ^ (prefixWord ++ tailWord_3916757).sum := by decide
  have hdescent : baseEnd_3916757 < baseStart_3916757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916798 : List Nat := [4, 2, 2, 2, 3, 1, 2, 2, 1, 2, 2]
def baseStart_3916798 : Nat := 118140960795 + 3916798 * 2 ^ 59
def prefixEnd_3916798 : Nat := 4983230072969 + 3 ^ 40 * 3916798 * 2
def baseEnd_3916798 : Nat := 2011200000569071743511981

theorem tailTrace_3916798 : CollatzResearch.WordTrace tailWord_3916798 prefixEnd_3916798 2011200000569071743511981 := by
  unfold tailWord_3916798
  simp only [CollatzResearch.WordTrace]
  refine ⟨17857169908014657085850881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95238239509411504457871365 17857169908014657085850881)
  ·
    refine ⟨13392877431010992814388161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17857169908014657085850881 13392877431010992814388161)
    ·
      refine ⟨10044658073258244610791121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13392877431010992814388161 10044658073258244610791121)
      ·
        refine ⟨7533493554943683458093341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10044658073258244610791121 7533493554943683458093341)
        ·
          refine ⟨2825060083103881296785003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7533493554943683458093341 2825060083103881296785003)
          ·
            refine ⟨4237590124655821945177505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2825060083103881296785003 4237590124655821945177505)
            ·
              refine ⟨3178192593491866458883129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4237590124655821945177505 3178192593491866458883129)
              ·
                refine ⟨2383644445118899844162347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3178192593491866458883129 2383644445118899844162347)
                ·
                  refine ⟨3575466667678349766243521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2383644445118899844162347 3575466667678349766243521)
                  ·
                    refine ⟨2681600000758762324682641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3575466667678349766243521 2681600000758762324682641)
                    ·
                      refine ⟨2011200000569071743511981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2681600000758762324682641 2011200000569071743511981)
                      ·
                        rfl

theorem cell23_3916798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_3916798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916798 prefixEnd_3916798 := by exact prefixLift 3916798
  have htrace : WordTrace (prefixWord ++ tailWord_3916798) baseStart_3916798 baseEnd_3916798 := by
    simpa [prefixWord, tailWord_3916798, baseEnd_3916798] using wordTrace_append hprefix tailTrace_3916798
  have hstable : (prefixWord ++ tailWord_3916798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916798).length < 2 ^ (prefixWord ++ tailWord_3916798).sum := by decide
  have hdescent : baseEnd_3916798 < baseStart_3916798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916854 : List Nat := [5, 1, 2, 1, 1, 4, 1, 2, 2, 2, 2]
def baseStart_3916854 : Nat := 118140960795 + 3916854 * 2 ^ 59
def prefixEnd_3916854 : Nat := 4983230072969 + 3 ^ 40 * 3916854 * 2
def baseEnd_3916854 : Nat := 2011228755485723524411723

theorem tailTrace_3916854 : CollatzResearch.WordTrace tailWord_3916854 prefixEnd_3916854 2011228755485723524411723 := by
  unfold tailWord_3916854
  simp only [CollatzResearch.WordTrace]
  refine ⟨8928712609494648640677851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95239601167942918833897077 8928712609494648640677851)
  ·
    refine ⟨13393068914241972961016777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8928712609494648640677851 13393068914241972961016777)
    ·
      refine ⟨10044801685681479720762583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13393068914241972961016777 10044801685681479720762583)
      ·
        refine ⟨15067202528522219581143875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10044801685681479720762583 15067202528522219581143875)
        ·
          refine ⟨22600803792783329371715813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15067202528522219581143875 22600803792783329371715813)
          ·
            refine ⟨4237650711146874257196715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22600803792783329371715813 4237650711146874257196715)
            ·
              refine ⟨6356476066720311385795073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4237650711146874257196715 6356476066720311385795073)
              ·
                refine ⟨4767357050040233539346305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6356476066720311385795073 4767357050040233539346305)
                ·
                  refine ⟨3575517787530175154509729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4767357050040233539346305 3575517787530175154509729)
                  ·
                    refine ⟨2681638340647631365882297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3575517787530175154509729 2681638340647631365882297)
                    ·
                      refine ⟨2011228755485723524411723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2681638340647631365882297 2011228755485723524411723)
                      ·
                        rfl

theorem cell23_3916854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_3916854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916854 prefixEnd_3916854 := by exact prefixLift 3916854
  have htrace : WordTrace (prefixWord ++ tailWord_3916854) baseStart_3916854 baseEnd_3916854 := by
    simpa [prefixWord, tailWord_3916854, baseEnd_3916854] using wordTrace_append hprefix tailTrace_3916854
  have hstable : (prefixWord ++ tailWord_3916854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916854).length < 2 ^ (prefixWord ++ tailWord_3916854).sum := by decide
  have hdescent : baseEnd_3916854 < baseStart_3916854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916859 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 4]
def baseStart_3916859 : Nat := 118140960795 + 3916859 * 2 ^ 59
def prefixEnd_3916859 : Nat := 4983230072969 + 3 ^ 40 * 3916859 * 2
def baseEnd_3916859 : Nat := 2011231322888996004849199

theorem tailTrace_3916859 : CollatzResearch.WordTrace tailWord_3916859 prefixEnd_3916859 2011231322888996004849199 := by
  unfold tailWord_3916859
  simp only [CollatzResearch.WordTrace]
  refine ⟨142859584116896264104777631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95239722744597509403185087 142859584116896264104777631)
  ·
    refine ⟨214289376175344396157166447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142859584116896264104777631 214289376175344396157166447)
    ·
      refine ⟨321434064263016594235749671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214289376175344396157166447 321434064263016594235749671)
      ·
        refine ⟨482151096394524891353624507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321434064263016594235749671 482151096394524891353624507)
        ·
          refine ⟨723226644591787337030436761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482151096394524891353624507 723226644591787337030436761)
          ·
            refine ⟨542419983443840502772827571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 723226644591787337030436761 542419983443840502772827571)
            ·
              refine ⟨813629975165760754159241357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 542419983443840502772827571 813629975165760754159241357)
              ·
                refine ⟨305111240687160282809715509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 813629975165760754159241357 305111240687160282809715509)
                ·
                  refine ⟨28604178814421276513410829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 305111240687160282809715509 28604178814421276513410829)
                  ·
                    refine ⟨10726567055407978692529061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28604178814421276513410829 10726567055407978692529061)
                    ·
                      refine ⟨2011231322888996004849199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10726567055407978692529061 2011231322888996004849199)
                      ·
                        rfl

theorem cell23_3916859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 4].length) (baseStart_3916859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916859 prefixEnd_3916859 := by exact prefixLift 3916859
  have htrace : WordTrace (prefixWord ++ tailWord_3916859) baseStart_3916859 baseEnd_3916859 := by
    simpa [prefixWord, tailWord_3916859, baseEnd_3916859] using wordTrace_append hprefix tailTrace_3916859
  have hstable : (prefixWord ++ tailWord_3916859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916859).length < 2 ^ (prefixWord ++ tailWord_3916859).sum := by decide
  have hdescent : baseEnd_3916859 < baseStart_3916859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916870 : List Nat := [6, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3]
def baseStart_3916870 : Nat := 118140960795 + 3916870 * 2 ^ 59
def prefixEnd_3916870 : Nat := 4983230072969 + 3 ^ 40 * 3916870 * 2
def baseEnd_3916870 : Nat := 2011236971176195461811649

theorem tailTrace_3916870 : CollatzResearch.WordTrace tailWord_3916870 prefixEnd_3916870 2011236971176195461811649 := by
  unfold tailWord_3916870
  simp only [CollatzResearch.WordTrace]
  refine ⟨4464374541245512905732127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 95239990213237608655618709 4464374541245512905732127)
  ·
    refine ⟨6696561811868269358598191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4464374541245512905732127 6696561811868269358598191)
    ·
      refine ⟨10044842717802404037897287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6696561811868269358598191 10044842717802404037897287)
      ·
        refine ⟨15067264076703606056845931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10044842717802404037897287 15067264076703606056845931)
        ·
          refine ⟨22600896115055409085268897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15067264076703606056845931 22600896115055409085268897)
          ·
            refine ⟨16950672086291556813951673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22600896115055409085268897 16950672086291556813951673)
            ·
              refine ⟨12713004064718667610463755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16950672086291556813951673 12713004064718667610463755)
              ·
                refine ⟨19069506097078001415695633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12713004064718667610463755 19069506097078001415695633)
                ·
                  refine ⟨14302129572808501061771725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19069506097078001415695633 14302129572808501061771725)
                  ·
                    refine ⟨5363298589803187898164397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14302129572808501061771725 5363298589803187898164397)
                    ·
                      refine ⟨2011236971176195461811649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5363298589803187898164397 2011236971176195461811649)
                      ·
                        rfl

theorem cell23_3916870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_3916870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916870 prefixEnd_3916870 := by exact prefixLift 3916870
  have htrace : WordTrace (prefixWord ++ tailWord_3916870) baseStart_3916870 baseEnd_3916870 := by
    simpa [prefixWord, tailWord_3916870, baseEnd_3916870] using wordTrace_append hprefix tailTrace_3916870
  have hstable : (prefixWord ++ tailWord_3916870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916870).length < 2 ^ (prefixWord ++ tailWord_3916870).sum := by decide
  have hdescent : baseEnd_3916870 < baseStart_3916870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916889 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 1, 3, 6]
def baseStart_3916889 : Nat := 118140960795 + 3916889 * 2 ^ 59
def prefixEnd_3916889 : Nat := 4983230072969 + 3 ^ 40 * 3916889 * 2
def baseEnd_3916889 : Nat := 2011246727308630887474061

theorem tailTrace_3916889 : CollatzResearch.WordTrace tailWord_3916889 prefixEnd_3916889 2011246727308630887474061 := by
  unfold tailWord_3916889
  simp only [CollatzResearch.WordTrace]
  refine ⟨142860678306787579228369721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95240452204525052818913147 142860678306787579228369721)
  ·
    refine ⟨107145508730090684421277291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142860678306787579228369721 107145508730090684421277291)
    ·
      refine ⟨160718263095136026631915937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107145508730090684421277291 160718263095136026631915937)
      ·
        refine ⟨120538697321352019973936953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160718263095136026631915937 120538697321352019973936953)
        ·
          refine ⟨90404022991014014980452715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120538697321352019973936953 90404022991014014980452715)
          ·
            refine ⟨135606034486521022470679073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90404022991014014980452715 135606034486521022470679073)
            ·
              refine ⟨101704525864890766853009305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135606034486521022470679073 101704525864890766853009305)
              ·
                refine ⟨76278394398668075139756979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101704525864890766853009305 76278394398668075139756979)
                ·
                  refine ⟨114417591598002112709635469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76278394398668075139756979 114417591598002112709635469)
                  ·
                    refine ⟨42906596849250792266113301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 114417591598002112709635469 42906596849250792266113301)
                    ·
                      refine ⟨2011246727308630887474061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42906596849250792266113301 2011246727308630887474061)
                      ·
                        rfl

theorem cell23_3916889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_3916889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916889 prefixEnd_3916889 := by exact prefixLift 3916889
  have htrace : WordTrace (prefixWord ++ tailWord_3916889) baseStart_3916889 baseEnd_3916889 := by
    simpa [prefixWord, tailWord_3916889, baseEnd_3916889] using wordTrace_append hprefix tailTrace_3916889
  have hstable : (prefixWord ++ tailWord_3916889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916889).length < 2 ^ (prefixWord ++ tailWord_3916889).sum := by decide
  have hdescent : baseEnd_3916889 < baseStart_3916889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916894 : List Nat := [4, 4, 1, 1, 1, 3, 1, 3, 5]
def baseStart_3916894 : Nat := 118140960795 + 3916894 * 2 ^ 59
def prefixEnd_3916894 : Nat := 4983230072969 + 3 ^ 40 * 3916894 * 2
def baseEnd_3916894 : Nat := 223472143856878151990171

theorem tailTrace_3916894 : CollatzResearch.WordTrace tailWord_3916894 prefixEnd_3916894 223472143856878151990171 := by
  unfold tailWord_3916894
  simp only [CollatzResearch.WordTrace]
  refine ⟨17857607583971183135287717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95240573781179643388201157 17857607583971183135287717)
  ·
    refine ⟨3348301421994596837866447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17857607583971183135287717 3348301421994596837866447)
    ·
      refine ⟨5022452132991895256799671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3348301421994596837866447 5022452132991895256799671)
      ·
        refine ⟨7533678199487842885199507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5022452132991895256799671 7533678199487842885199507)
        ·
          refine ⟨11300517299231764327799261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7533678199487842885199507 11300517299231764327799261)
          ·
            refine ⟨4237693987211911622924723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11300517299231764327799261 4237693987211911622924723)
            ·
              refine ⟨6356540980817867434387085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4237693987211911622924723 6356540980817867434387085)
              ·
                refine ⟨2383702867806700287895157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6356540980817867434387085 2383702867806700287895157)
                ·
                  refine ⟨223472143856878151990171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2383702867806700287895157 223472143856878151990171)
                  ·
                    rfl

theorem cell23_3916894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_3916894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916894 prefixEnd_3916894 := by exact prefixLift 3916894
  have htrace : WordTrace (prefixWord ++ tailWord_3916894) baseStart_3916894 baseEnd_3916894 := by
    simpa [prefixWord, tailWord_3916894, baseEnd_3916894] using wordTrace_append hprefix tailTrace_3916894
  have hstable : (prefixWord ++ tailWord_3916894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916894).length < 2 ^ (prefixWord ++ tailWord_3916894).sum := by decide
  have hdescent : baseEnd_3916894 < baseStart_3916894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916896 : List Nat := [2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 3]
def baseStart_3916896 : Nat := 118140960795 + 3916896 * 2 ^ 59
def prefixEnd_3916896 : Nat := 4983230072969 + 3 ^ 40 * 3916896 * 2
def baseEnd_3916896 : Nat := 2011250321673212360086529

theorem tailTrace_3916896 : CollatzResearch.WordTrace tailWord_3916896 prefixEnd_3916896 2011250321673212360086529 := by
  unfold tailWord_3916896
  simp only [CollatzResearch.WordTrace]
  refine ⟨71430466808881109711937271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95240622411841479615916361 71430466808881109711937271)
  ·
    refine ⟨107145700213321664567905907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71430466808881109711937271 107145700213321664567905907)
    ·
      refine ⟨160718550319982496851858861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107145700213321664567905907 160718550319982496851858861)
      ·
        refine ⟨60269456369993436319447073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160718550319982496851858861 60269456369993436319447073)
        ·
          refine ⟨45202092277495077239585305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60269456369993436319447073 45202092277495077239585305)
          ·
            refine ⟨33901569208121307929688979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45202092277495077239585305 33901569208121307929688979)
            ·
              refine ⟨50852353812181961894533469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33901569208121307929688979 50852353812181961894533469)
              ·
                refine ⟨19069632679568235710450051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50852353812181961894533469 19069632679568235710450051)
                ·
                  refine ⟨28604449019352353565675077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19069632679568235710450051 28604449019352353565675077)
                  ·
                    refine ⟨5363334191128566293564077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28604449019352353565675077 5363334191128566293564077)
                    ·
                      refine ⟨2011250321673212360086529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5363334191128566293564077 2011250321673212360086529)
                      ·
                        rfl

theorem cell23_3916896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 3].length) (baseStart_3916896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916896 prefixEnd_3916896 := by exact prefixLift 3916896
  have htrace : WordTrace (prefixWord ++ tailWord_3916896) baseStart_3916896 baseEnd_3916896 := by
    simpa [prefixWord, tailWord_3916896, baseEnd_3916896] using wordTrace_append hprefix tailTrace_3916896
  have hstable : (prefixWord ++ tailWord_3916896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916896).length < 2 ^ (prefixWord ++ tailWord_3916896).sum := by decide
  have hdescent : baseEnd_3916896 < baseStart_3916896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916933 : List Nat := [1, 3, 1, 1, 6, 1, 1, 3, 6]
def baseStart_3916933 : Nat := 118140960795 + 3916933 * 2 ^ 59
def prefixEnd_3916933 : Nat := 4983230072969 + 3 ^ 40 * 3916933 * 2
def baseEnd_3916933 : Nat := 223474368939714301702651

theorem tailTrace_3916933 : CollatzResearch.WordTrace tailWord_3916933 prefixEnd_3916933 223474368939714301702651 := by
  unfold tailWord_3916933
  simp only [CollatzResearch.WordTrace]
  refine ⟨142862283118628174742971453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95241522079085449828647635 142862283118628174742971453)
  ·
    refine ⟨53573356169485565528614295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142862283118628174742971453 53573356169485565528614295)
    ·
      refine ⟨80360034254228348292921443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53573356169485565528614295 80360034254228348292921443)
      ·
        refine ⟨120540051381342522439382165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80360034254228348292921443 120540051381342522439382165)
        ·
          refine ⟨5650314908500430739346039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 120540051381342522439382165 5650314908500430739346039)
          ·
            refine ⟨8475472362750646109019059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5650314908500430739346039 8475472362750646109019059)
            ·
              refine ⟨12713208544125969163528589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8475472362750646109019059 12713208544125969163528589)
              ·
                refine ⟨4767453204047238436323221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12713208544125969163528589 4767453204047238436323221)
                ·
                  refine ⟨223474368939714301702651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4767453204047238436323221 223474368939714301702651)
                  ·
                    rfl

theorem cell23_3916933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 6].length) (baseStart_3916933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916933 prefixEnd_3916933 := by exact prefixLift 3916933
  have htrace : WordTrace (prefixWord ++ tailWord_3916933) baseStart_3916933 baseEnd_3916933 := by
    simpa [prefixWord, tailWord_3916933, baseEnd_3916933] using wordTrace_append hprefix tailTrace_3916933
  have hstable : (prefixWord ++ tailWord_3916933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916933).length < 2 ^ (prefixWord ++ tailWord_3916933).sum := by decide
  have hdescent : baseEnd_3916933 < baseStart_3916933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916986 : List Nat := [3, 1, 1, 1, 2, 2, 1, 3, 3, 1, 5]
def baseStart_3916986 : Nat := 118140960795 + 3916986 * 2 ^ 59
def prefixEnd_3916986 : Nat := 4983230072969 + 3 ^ 40 * 3916986 * 2
def baseEnd_3916986 : Nat := 2011296534932117007961115

theorem tailTrace_3916986 : CollatzResearch.WordTrace tailWord_3916986 prefixEnd_3916986 2011296534932117007961115 := by
  unfold tailWord_3916986
  simp only [CollatzResearch.WordTrace]
  refine ⟨35716054046859041198662703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95242810791624109863100541 35716054046859041198662703)
  ·
    refine ⟨53574081070288561797994055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35716054046859041198662703 53574081070288561797994055)
    ·
      refine ⟨80361121605432842696991083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53574081070288561797994055 80361121605432842696991083)
      ·
        refine ⟨120541682408149264045486625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80361121605432842696991083 120541682408149264045486625)
        ·
          refine ⟨90406261806111948034114969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120541682408149264045486625 90406261806111948034114969)
          ·
            refine ⟨67804696354583961025586227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90406261806111948034114969 67804696354583961025586227)
            ·
              refine ⟨101707044531875941538379341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67804696354583961025586227 101707044531875941538379341)
              ·
                refine ⟨38140141699453478076892253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101707044531875941538379341 38140141699453478076892253)
                ·
                  refine ⟨14302553137295054278834595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38140141699453478076892253 14302553137295054278834595)
                  ·
                    refine ⟨21453829705942581418251893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14302553137295054278834595 21453829705942581418251893)
                    ·
                      refine ⟨2011296534932117007961115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21453829705942581418251893 2011296534932117007961115)
                      ·
                        rfl

theorem cell23_3916986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 3, 1, 5].length) (baseStart_3916986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916986 prefixEnd_3916986 := by exact prefixLift 3916986
  have htrace : WordTrace (prefixWord ++ tailWord_3916986) baseStart_3916986 baseEnd_3916986 := by
    simpa [prefixWord, tailWord_3916986, baseEnd_3916986] using wordTrace_append hprefix tailTrace_3916986
  have hstable : (prefixWord ++ tailWord_3916986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916986).length < 2 ^ (prefixWord ++ tailWord_3916986).sum := by decide
  have hdescent : baseEnd_3916986 < baseStart_3916986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916998 : List Nat := [6, 1, 2, 2, 2, 1, 1, 1, 2, 2, 3]
def baseStart_3916998 : Nat := 118140960795 + 3916998 * 2 ^ 59
def prefixEnd_3916998 : Nat := 4983230072969 + 3 ^ 40 * 3916998 * 2
def baseEnd_3916998 : Nat := 2011302696699970961011061

theorem tailTrace_3916998 : CollatzResearch.WordTrace tailWord_3916998 prefixEnd_3916998 2011302696699970961011061 := by
  unfold tailWord_3916998
  simp only [CollatzResearch.WordTrace]
  refine ⟨4464520433231021588877739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 95243102575595127229391765 4464520433231021588877739)
  ·
    refine ⟨6696780649846532383316609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4464520433231021588877739 6696780649846532383316609)
    ·
      refine ⟨5022585487384899287487457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6696780649846532383316609 5022585487384899287487457)
      ·
        refine ⟨3766939115538674465615593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5022585487384899287487457 3766939115538674465615593)
        ·
          refine ⟨2825204336654005849211695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3766939115538674465615593 2825204336654005849211695)
          ·
            refine ⟨4237806504981008773817543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2825204336654005849211695 4237806504981008773817543)
            ·
              refine ⟨6356709757471513160726315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4237806504981008773817543 6356709757471513160726315)
              ·
                refine ⟨9535064636207269741089473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6356709757471513160726315 9535064636207269741089473)
                ·
                  refine ⟨7151298477155452305817105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9535064636207269741089473 7151298477155452305817105)
                  ·
                    refine ⟨5363473857866589229362829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7151298477155452305817105 5363473857866589229362829)
                    ·
                      refine ⟨2011302696699970961011061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5363473857866589229362829 2011302696699970961011061)
                      ·
                        rfl

theorem cell23_3916998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_3916998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916998 prefixEnd_3916998 := by exact prefixLift 3916998
  have htrace : WordTrace (prefixWord ++ tailWord_3916998) baseStart_3916998 baseEnd_3916998 := by
    simpa [prefixWord, tailWord_3916998, baseEnd_3916998] using wordTrace_append hprefix tailTrace_3916998
  have hstable : (prefixWord ++ tailWord_3916998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916998).length < 2 ^ (prefixWord ++ tailWord_3916998).sum := by decide
  have hdescent : baseEnd_3916998 < baseStart_3916998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917000 : List Nat := [2, 1, 3, 1, 2, 1, 3, 1, 5, 2, 2]
def baseStart_3917000 : Nat := 118140960795 + 3917000 * 2 ^ 59
def prefixEnd_3917000 : Nat := 4983230072969 + 3 ^ 40 * 3917000 * 2
def baseEnd_3917000 : Nat := 2011303723661279953186051

theorem tailTrace_3917000 : CollatzResearch.WordTrace tailWord_3917000 prefixEnd_3917000 2011303723661279953186051 := by
  unfold tailWord_3917000
  simp only [CollatzResearch.WordTrace]
  refine ⟨71432363404692722592830227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95243151206256963457106969 71432363404692722592830227)
  ·
    refine ⟨107148545107039083889245341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71432363404692722592830227 107148545107039083889245341)
    ·
      refine ⟨40180704415139656458467003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107148545107039083889245341 40180704415139656458467003)
      ·
        refine ⟨60271056622709484687700505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40180704415139656458467003 60271056622709484687700505)
        ·
          refine ⟨45203292467032113515775379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60271056622709484687700505 45203292467032113515775379)
          ·
            refine ⟨67804938700548170273663069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45203292467032113515775379 67804938700548170273663069)
            ·
              refine ⟨25426852012705563852623651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67804938700548170273663069 25426852012705563852623651)
              ·
                refine ⟨38140278019058345778935477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25426852012705563852623651 38140278019058345778935477)
                ·
                  refine ⟨3575651064286719916775201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38140278019058345778935477 3575651064286719916775201)
                  ·
                    refine ⟨2681738298215039937581401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3575651064286719916775201 2681738298215039937581401)
                    ·
                      refine ⟨2011303723661279953186051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2681738298215039937581401 2011303723661279953186051)
                      ·
                        rfl

theorem cell23_3917000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 5, 2, 2].length) (baseStart_3917000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917000 prefixEnd_3917000 := by exact prefixLift 3917000
  have htrace : WordTrace (prefixWord ++ tailWord_3917000) baseStart_3917000 baseEnd_3917000 := by
    simpa [prefixWord, tailWord_3917000, baseEnd_3917000] using wordTrace_append hprefix tailTrace_3917000
  have hstable : (prefixWord ++ tailWord_3917000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917000).length < 2 ^ (prefixWord ++ tailWord_3917000).sum := by decide
  have hdescent : baseEnd_3917000 < baseStart_3917000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917034 : List Nat := [3, 1, 3, 1, 1, 3, 2, 4, 1, 2, 2]
def baseStart_3917034 : Nat := 118140960795 + 3917034 * 2 ^ 59
def prefixEnd_3917034 : Nat := 4983230072969 + 3 ^ 40 * 3917034 * 2
def baseEnd_3917034 : Nat := 2011321182003532820160895

theorem tailTrace_3917034 : CollatzResearch.WordTrace tailWord_3917034 prefixEnd_3917034 2011321182003532820160895 := by
  unfold tailWord_3917034
  simp only [CollatzResearch.WordTrace]
  refine ⟨35716491722815567248099539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95243977927508179328265437 35716491722815567248099539)
  ·
    refine ⟨53574737584223350872149309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35716491722815567248099539 53574737584223350872149309)
    ·
      refine ⟨20090526594083756577055991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53574737584223350872149309 20090526594083756577055991)
      ·
        refine ⟨30135789891125634865583987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20090526594083756577055991 30135789891125634865583987)
        ·
          refine ⟨45203684836688452298375981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30135789891125634865583987 45203684836688452298375981)
          ·
            refine ⟨16951381813758169611890993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45203684836688452298375981 16951381813758169611890993)
            ·
              refine ⟨12713536360318627208918245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16951381813758169611890993 12713536360318627208918245)
              ·
                refine ⟨2383788067559742601672171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12713536360318627208918245 2383788067559742601672171)
                ·
                  refine ⟨3575682101339613902508257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2383788067559742601672171 3575682101339613902508257)
                  ·
                    refine ⟨2681761576004710426881193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3575682101339613902508257 2681761576004710426881193)
                    ·
                      refine ⟨2011321182003532820160895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2681761576004710426881193 2011321182003532820160895)
                      ·
                        rfl

theorem cell23_3917034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 4, 1, 2, 2].length) (baseStart_3917034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917034 prefixEnd_3917034 := by exact prefixLift 3917034
  have htrace : WordTrace (prefixWord ++ tailWord_3917034) baseStart_3917034 baseEnd_3917034 := by
    simpa [prefixWord, tailWord_3917034, baseEnd_3917034] using wordTrace_append hprefix tailTrace_3917034
  have hstable : (prefixWord ++ tailWord_3917034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917034).length < 2 ^ (prefixWord ++ tailWord_3917034).sum := by decide
  have hdescent : baseEnd_3917034 < baseStart_3917034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917101 : List Nat := [1, 5, 3, 1, 1, 1, 4, 1, 2, 1, 3]
def baseStart_3917101 : Nat := 118140960795 + 3917101 * 2 ^ 59
def prefixEnd_3917101 : Nat := 4983230072969 + 3 ^ 40 * 3917101 * 2
def baseEnd_3917101 : Nat := 2011355585207384058023087

theorem tailTrace_3917101 : CollatzResearch.WordTrace tailWord_3917101 prefixEnd_3917101 2011355585207384058023087 := by
  unfold tailWord_3917101
  simp only [CollatzResearch.WordTrace]
  refine ⟨142868410582019539435087157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95245607054679692956724771 142868410582019539435087157)
  ·
    refine ⟨13393913492064331822039421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142868410582019539435087157 13393913492064331822039421)
    ·
      refine ⟨5022717559524124433264783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13393913492064331822039421 5022717559524124433264783)
      ·
        refine ⟨7534076339286186649897175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5022717559524124433264783 7534076339286186649897175)
        ·
          refine ⟨11301114508929279974845763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7534076339286186649897175 11301114508929279974845763)
          ·
            refine ⟨16951671763393919962268645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11301114508929279974845763 16951671763393919962268645)
            ·
              refine ⟨3178438455636359992925371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16951671763393919962268645 3178438455636359992925371)
              ·
                refine ⟨4767657683454539989388057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3178438455636359992925371 4767657683454539989388057)
                ·
                  refine ⟨3575743262590904992041043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4767657683454539989388057 3575743262590904992041043)
                  ·
                    refine ⟨5363614893886357488061565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3575743262590904992041043 5363614893886357488061565)
                    ·
                      refine ⟨2011355585207384058023087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5363614893886357488061565 2011355585207384058023087)
                      ·
                        rfl

theorem cell23_3917101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_3917101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917101 prefixEnd_3917101 := by exact prefixLift 3917101
  have htrace : WordTrace (prefixWord ++ tailWord_3917101) baseStart_3917101 baseEnd_3917101 := by
    simpa [prefixWord, tailWord_3917101, baseEnd_3917101] using wordTrace_append hprefix tailTrace_3917101
  have hstable : (prefixWord ++ tailWord_3917101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917101).length < 2 ^ (prefixWord ++ tailWord_3917101).sum := by decide
  have hdescent : baseEnd_3917101 < baseStart_3917101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917123 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 4, 3, 3]
def baseStart_3917123 : Nat := 118140960795 + 3917123 * 2 ^ 59
def prefixEnd_3917123 : Nat := 4983230072969 + 3 ^ 40 * 3917123 * 2
def baseEnd_3917123 : Nat := 2011366881781782971947985

theorem tailTrace_3917123 : CollatzResearch.WordTrace tailWord_3917123 prefixEnd_3917123 2011366881781782971947985 := by
  unfold tailWord_3917123
  simp only [CollatzResearch.WordTrace]
  refine ⟨142869212987939837192388023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95246141991959891461592015 142869212987939837192388023)
  ·
    refine ⟨214303819481909755788582035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142869212987939837192388023 214303819481909755788582035)
    ·
      refine ⟨321455729222864633682873053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214303819481909755788582035 321455729222864633682873053)
      ·
        refine ⟨120545898458574237631077395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321455729222864633682873053 120545898458574237631077395)
        ·
          refine ⟨180818847687861356446616093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120545898458574237631077395 180818847687861356446616093)
          ·
            refine ⟨67807067882948008667481035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180818847687861356446616093 67807067882948008667481035)
            ·
              refine ⟨101710601824422013001221553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67807067882948008667481035 101710601824422013001221553)
              ·
                refine ⟨76282951368316509750916165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101710601824422013001221553 76282951368316509750916165)
                ·
                  refine ⟨14303053381559345578296781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76282951368316509750916165 14303053381559345578296781)
                  ·
                    refine ⟨5363645018084754591861293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14303053381559345578296781 5363645018084754591861293)
                    ·
                      refine ⟨2011366881781782971947985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5363645018084754591861293 2011366881781782971947985)
                      ·
                        rfl

theorem cell23_3917123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 3, 3].length) (baseStart_3917123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917123 prefixEnd_3917123 := by exact prefixLift 3917123
  have htrace : WordTrace (prefixWord ++ tailWord_3917123) baseStart_3917123 baseEnd_3917123 := by
    simpa [prefixWord, tailWord_3917123, baseEnd_3917123] using wordTrace_append hprefix tailTrace_3917123
  have hstable : (prefixWord ++ tailWord_3917123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917123).length < 2 ^ (prefixWord ++ tailWord_3917123).sum := by decide
  have hdescent : baseEnd_3917123 < baseStart_3917123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917124 : List Nat := [2, 3, 4, 1, 1, 2, 1, 2, 1, 4, 2]
def baseStart_3917124 : Nat := 118140960795 + 3917124 * 2 ^ 59
def prefixEnd_3917124 : Nat := 4983230072969 + 3 ^ 40 * 3917124 * 2
def baseEnd_3917124 : Nat := 2011367395262437468035481

theorem tailTrace_3917124 : CollatzResearch.WordTrace tailWord_3917124 prefixEnd_3917124 2011367395262437468035481 := by
  unfold tailWord_3917124
  simp only [CollatzResearch.WordTrace]
  refine ⟨71434624730468107181587213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95246166307290809575449617 71434624730468107181587213)
  ·
    refine ⟨26787984273925540193095205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71434624730468107181587213 26787984273925540193095205)
    ·
      refine ⟨5022747051361038786205351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26787984273925540193095205 5022747051361038786205351)
      ·
        refine ⟨7534120577041558179308027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5022747051361038786205351 7534120577041558179308027)
        ·
          refine ⟨11301180865562337268962041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7534120577041558179308027 11301180865562337268962041)
          ·
            refine ⟨8475885649171752951721531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11301180865562337268962041 8475885649171752951721531)
            ·
              refine ⟨12713828473757629427582297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8475885649171752951721531 12713828473757629427582297)
              ·
                refine ⟨9535371355318222070686723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12713828473757629427582297 9535371355318222070686723)
                ·
                  refine ⟨14303057032977333106030085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9535371355318222070686723 14303057032977333106030085)
                  ·
                    refine ⟨2681823193683249957380641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14303057032977333106030085 2681823193683249957380641)
                    ·
                      refine ⟨2011367395262437468035481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2681823193683249957380641 2011367395262437468035481)
                      ·
                        rfl

theorem cell23_3917124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_3917124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917124 prefixEnd_3917124 := by exact prefixLift 3917124
  have htrace : WordTrace (prefixWord ++ tailWord_3917124) baseStart_3917124 baseEnd_3917124 := by
    simpa [prefixWord, tailWord_3917124, baseEnd_3917124] using wordTrace_append hprefix tailTrace_3917124
  have hstable : (prefixWord ++ tailWord_3917124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917124).length < 2 ^ (prefixWord ++ tailWord_3917124).sum := by decide
  have hdescent : baseEnd_3917124 < baseStart_3917124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917140 : List Nat := [2, 4, 1, 1, 2, 1, 2, 2, 2, 3, 3]
def baseStart_3917140 : Nat := 118140960795 + 3917140 * 2 ^ 59
def prefixEnd_3917140 : Nat := 4983230072969 + 3 ^ 40 * 3917140 * 2
def baseEnd_3917140 : Nat := 2011375610952909405435407

theorem tailTrace_3917140 : CollatzResearch.WordTrace tailWord_3917140 prefixEnd_3917140 2011375610952909405435407 := by
  unfold tailWord_3917140
  simp only [CollatzResearch.WordTrace]
  refine ⟨71434916514439124547878437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95246555352585499397171249 71434916514439124547878437)
  ·
    refine ⟨13394046846457335852727207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71434916514439124547878437 13394046846457335852727207)
    ·
      refine ⟨20091070269686003779090811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13394046846457335852727207 20091070269686003779090811)
      ·
        refine ⟨30136605404529005668636217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20091070269686003779090811 30136605404529005668636217)
        ·
          refine ⟨22602454053396754251477163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30136605404529005668636217 22602454053396754251477163)
          ·
            refine ⟨33903681080095131377215745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22602454053396754251477163 33903681080095131377215745)
            ·
              refine ⟨25427760810071348532911809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33903681080095131377215745 25427760810071348532911809)
              ·
                refine ⟨19070820607553511399683857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25427760810071348532911809 19070820607553511399683857)
                ·
                  refine ⟨14303115455665133549762893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19070820607553511399683857 14303115455665133549762893)
                  ·
                    refine ⟨5363668295874425081161085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14303115455665133549762893 5363668295874425081161085)
                    ·
                      refine ⟨2011375610952909405435407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5363668295874425081161085 2011375610952909405435407)
                      ·
                        rfl

theorem cell23_3917140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_3917140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917140 prefixEnd_3917140 := by exact prefixLift 3917140
  have htrace : WordTrace (prefixWord ++ tailWord_3917140) baseStart_3917140 baseEnd_3917140 := by
    simpa [prefixWord, tailWord_3917140, baseEnd_3917140] using wordTrace_append hprefix tailTrace_3917140
  have hstable : (prefixWord ++ tailWord_3917140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917140).length < 2 ^ (prefixWord ++ tailWord_3917140).sum := by decide
  have hdescent : baseEnd_3917140 < baseStart_3917140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917180 : List Nat := [2, 2, 2, 1, 1, 1, 3, 2, 1, 6, 2]
def baseStart_3917180 : Nat := 118140960795 + 3917180 * 2 ^ 59
def prefixEnd_3917180 : Nat := 4983230072969 + 3 ^ 40 * 3917180 * 2
def baseEnd_3917180 : Nat := 2011396150179089248935223

theorem tailTrace_3917180 : CollatzResearch.WordTrace tailWord_3917180 prefixEnd_3917180 2011396150179089248935223 := by
  unfold tailWord_3917180
  simp only [CollatzResearch.WordTrace]
  refine ⟨71435645974366667963606497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95247527965822223951475329 71435645974366667963606497)
  ·
    refine ⟨53576734480775000972704873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71435645974366667963606497 53576734480775000972704873)
    ·
      refine ⟨40182550860581250729528655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53576734480775000972704873 40182550860581250729528655)
      ·
        refine ⟨60273826290871876094292983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40182550860581250729528655 60273826290871876094292983)
        ·
          refine ⟨90410739436307814141439475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60273826290871876094292983 90410739436307814141439475)
          ·
            refine ⟨135616109154461721212159213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90410739436307814141439475 135616109154461721212159213)
            ·
              refine ⟨50856040932923145454559705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135616109154461721212159213 50856040932923145454559705)
              ·
                refine ⟨38142030699692359090919779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50856040932923145454559705 38142030699692359090919779)
                ·
                  refine ⟨57213046049538538636379669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38142030699692359090919779 57213046049538538636379669)
                  ·
                    refine ⟨2681861533572118998580297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 57213046049538538636379669 2681861533572118998580297)
                    ·
                      refine ⟨2011396150179089248935223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2681861533572118998580297 2011396150179089248935223)
                      ·
                        rfl

theorem cell23_3917180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 1, 6, 2].length) (baseStart_3917180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917180 prefixEnd_3917180 := by exact prefixLift 3917180
  have htrace : WordTrace (prefixWord ++ tailWord_3917180) baseStart_3917180 baseEnd_3917180 := by
    simpa [prefixWord, tailWord_3917180, baseEnd_3917180] using wordTrace_append hprefix tailTrace_3917180
  have hstable : (prefixWord ++ tailWord_3917180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917180).length < 2 ^ (prefixWord ++ tailWord_3917180).sum := by decide
  have hdescent : baseEnd_3917180 < baseStart_3917180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917241 : List Nat := [1, 2, 1, 4, 4, 2, 1, 3, 1, 4]
def baseStart_3917241 : Nat := 118140960795 + 3917241 * 2 ^ 59
def prefixEnd_3917241 : Nat := 4983230072969 + 3 ^ 40 * 3917241 * 2
def baseEnd_3917241 : Nat := 670475824166337836757481

theorem tailTrace_3917241 : CollatzResearch.WordTrace tailWord_3917241 prefixEnd_3917241 670475824166337836757481 := by
  unfold tailWord_3917241
  simp only [CollatzResearch.WordTrace]
  refine ⟨142873516801512343345183577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95249011201008228896789051 142873516801512343345183577)
  ·
    refine ⟨107155137601134257508887683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142873516801512343345183577 107155137601134257508887683)
    ·
      refine ⟨160732706401701386263331525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107155137601134257508887683 160732706401701386263331525)
      ·
        refine ⟨30137382450319009924374661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160732706401701386263331525 30137382450319009924374661)
        ·
          refine ⟨5650759209434814360820249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30137382450319009924374661 5650759209434814360820249)
          ·
            refine ⟨4238069407076110770615187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5650759209434814360820249 4238069407076110770615187)
            ·
              refine ⟨6357104110614166155922781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4238069407076110770615187 6357104110614166155922781)
              ·
                refine ⟨2383914041480312308471043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6357104110614166155922781 2383914041480312308471043)
                ·
                  refine ⟨3575871062220468462706565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2383914041480312308471043 3575871062220468462706565)
                  ·
                    refine ⟨670475824166337836757481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3575871062220468462706565 670475824166337836757481)
                    ·
                      rfl

theorem cell23_3917241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 3, 1, 4].length) (baseStart_3917241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917241 prefixEnd_3917241 := by exact prefixLift 3917241
  have htrace : WordTrace (prefixWord ++ tailWord_3917241) baseStart_3917241 baseEnd_3917241 := by
    simpa [prefixWord, tailWord_3917241, baseEnd_3917241] using wordTrace_append hprefix tailTrace_3917241
  have hstable : (prefixWord ++ tailWord_3917241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917241).length < 2 ^ (prefixWord ++ tailWord_3917241).sum := by decide
  have hdescent : baseEnd_3917241 < baseStart_3917241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917280 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 6, 4]
def baseStart_3917280 : Nat := 118140960795 + 3917280 * 2 ^ 59
def prefixEnd_3917280 : Nat := 4983230072969 + 3 ^ 40 * 3917280 * 2
def baseEnd_3917280 : Nat := 670482499414846285894921

theorem tailTrace_3917280 : CollatzResearch.WordTrace tailWord_3917280 prefixEnd_3917280 670482499414846285894921 := by
  unfold tailWord_3917280
  simp only [CollatzResearch.WordTrace]
  refine ⟨71437469624185526502926647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95249959498914035337235529 71437469624185526502926647)
  ·
    refine ⟨107156204436278289754389971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71437469624185526502926647 107156204436278289754389971)
    ·
      refine ⟨160734306654417434631584957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107156204436278289754389971 160734306654417434631584957)
      ·
        refine ⟨60275364995406537986844359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160734306654417434631584957 60275364995406537986844359)
        ·
          refine ⟨90413047493109806980266539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60275364995406537986844359 90413047493109806980266539)
          ·
            refine ⟨135619571239664710470399809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90413047493109806980266539 135619571239664710470399809)
            ·
              refine ⟨101714678429748532852799857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135619571239664710470399809 101714678429748532852799857)
              ·
                refine ⟨76286008822311399639599893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101714678429748532852799857 76286008822311399639599893)
                ·
                  refine ⟨3575906663545846858106245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 76286008822311399639599893 3575906663545846858106245)
                  ·
                    refine ⟨670482499414846285894921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3575906663545846858106245 670482499414846285894921)
                    ·
                      rfl

theorem cell23_3917280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 6, 4].length) (baseStart_3917280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917280 prefixEnd_3917280 := by exact prefixLift 3917280
  have htrace : WordTrace (prefixWord ++ tailWord_3917280) baseStart_3917280 baseEnd_3917280 := by
    simpa [prefixWord, tailWord_3917280, baseEnd_3917280] using wordTrace_append hprefix tailTrace_3917280
  have hstable : (prefixWord ++ tailWord_3917280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917280).length < 2 ^ (prefixWord ++ tailWord_3917280).sum := by decide
  have hdescent : baseEnd_3917280 < baseStart_3917280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917287 : List Nat := [1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 4]
def baseStart_3917287 : Nat := 118140960795 + 3917287 * 2 ^ 59
def prefixEnd_3917287 : Nat := 4983230072969 + 3 ^ 40 * 3917287 * 2
def baseEnd_3917287 : Nat := 2011451092609120330297231

theorem tailTrace_3917287 : CollatzResearch.WordTrace tailWord_3917287 prefixEnd_3917287 2011451092609120330297231 := by
  unfold tailWord_3917287
  simp only [CollatzResearch.WordTrace]
  refine ⟨142875194559345693201358115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95250129706230462134238743 142875194559345693201358115)
  ·
    refine ⟨214312791839018539802037173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142875194559345693201358115 214312791839018539802037173)
    ·
      refine ⟨20091824234907988106440985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 214312791839018539802037173 20091824234907988106440985)
      ·
        refine ⟨15068868176180991079830739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20091824234907988106440985 15068868176180991079830739)
        ·
          refine ⟨22603302264271486619746109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15068868176180991079830739 22603302264271486619746109)
          ·
            refine ⟨8476238349101807482404791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22603302264271486619746109 8476238349101807482404791)
            ·
              refine ⟨12714357523652711223607187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8476238349101807482404791 12714357523652711223607187)
              ·
                refine ⟨19071536285479066835410781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12714357523652711223607187 19071536285479066835410781)
                ·
                  refine ⟨7151826107054650063279043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19071536285479066835410781 7151826107054650063279043)
                  ·
                    refine ⟨10727739160581975094918565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7151826107054650063279043 10727739160581975094918565)
                    ·
                      refine ⟨2011451092609120330297231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10727739160581975094918565 2011451092609120330297231)
                      ·
                        rfl

theorem cell23_3917287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_3917287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917287 prefixEnd_3917287 := by exact prefixLift 3917287
  have htrace : WordTrace (prefixWord ++ tailWord_3917287) baseStart_3917287 baseEnd_3917287 := by
    simpa [prefixWord, tailWord_3917287, baseEnd_3917287] using wordTrace_append hprefix tailTrace_3917287
  have hstable : (prefixWord ++ tailWord_3917287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917287).length < 2 ^ (prefixWord ++ tailWord_3917287).sum := by decide
  have hdescent : baseEnd_3917287 < baseStart_3917287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917301 : List Nat := [1, 3, 5, 1, 1, 2, 3, 1, 1, 5]
def baseStart_3917301 : Nat := 118140960795 + 3917301 * 2 ^ 59
def prefixEnd_3917301 : Nat := 4983230072969 + 3 ^ 40 * 3917301 * 2
def baseEnd_3917301 : Nat := 670486093779427758507389

theorem tailTrace_3917301 : CollatzResearch.WordTrace tailWord_3917301 prefixEnd_3917301 670486093779427758507389 := by
  unfold tailWord_3917301
  simp only [CollatzResearch.WordTrace]
  refine ⟨142875705181294973592367757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95250470120863315728245171 142875705181294973592367757)
  ·
    refine ⟨53578389442985615097137909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142875705181294973592367757 53578389442985615097137909)
    ·
      refine ⟨5022974010279901415356679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53578389442985615097137909 5022974010279901415356679)
      ·
        refine ⟨7534461015419852123035019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5022974010279901415356679 7534461015419852123035019)
        ·
          refine ⟨11301691523129778184552529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7534461015419852123035019 11301691523129778184552529)
          ·
            refine ⟨8476268642347333638414397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11301691523129778184552529 8476268642347333638414397)
            ·
              refine ⟨3178600740880250114405399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8476268642347333638414397 3178600740880250114405399)
              ·
                refine ⟨4767901111320375171608099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3178600740880250114405399 4767901111320375171608099)
                ·
                  refine ⟨7151851666980562757412149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4767901111320375171608099 7151851666980562757412149)
                  ·
                    refine ⟨670486093779427758507389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7151851666980562757412149 670486093779427758507389)
                    ·
                      rfl

theorem cell23_3917301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_3917301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917301 prefixEnd_3917301 := by exact prefixLift 3917301
  have htrace : WordTrace (prefixWord ++ tailWord_3917301) baseStart_3917301 baseEnd_3917301 := by
    simpa [prefixWord, tailWord_3917301, baseEnd_3917301] using wordTrace_append hprefix tailTrace_3917301
  have hstable : (prefixWord ++ tailWord_3917301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917301).length < 2 ^ (prefixWord ++ tailWord_3917301).sum := by decide
  have hdescent : baseEnd_3917301 < baseStart_3917301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917304 : List Nat := [2, 1, 2, 1, 1, 6, 3, 1, 1, 1, 4]
def baseStart_3917304 : Nat := 118140960795 + 3917304 * 2 ^ 59
def prefixEnd_3917304 : Nat := 4983230072969 + 3 ^ 40 * 3917304 * 2
def baseEnd_3917304 : Nat := 2011459821780246763784653

theorem tailTrace_3917304 : CollatzResearch.WordTrace tailWord_3917304 prefixEnd_3917304 2011459821780246763784653 := by
  unfold tailWord_3917304
  simp only [CollatzResearch.WordTrace]
  refine ⟨71437907300142052552363483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95250543066856070069817977 71437907300142052552363483)
  ·
    refine ⟨107156860950213078828545225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71437907300142052552363483 107156860950213078828545225)
    ·
      refine ⟨80367645712659809121408919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107156860950213078828545225 80367645712659809121408919)
      ·
        refine ⟨120551468568989713682113379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80367645712659809121408919 120551468568989713682113379)
        ·
          refine ⟨180827202853484570523170069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120551468568989713682113379 180827202853484570523170069)
          ·
            refine ⟨8476275133757089243273597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 180827202853484570523170069 8476275133757089243273597)
            ·
              refine ⟨3178603175158908466227599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8476275133757089243273597 3178603175158908466227599)
              ·
                refine ⟨4767904762738362699341399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3178603175158908466227599 4767904762738362699341399)
                ·
                  refine ⟨7151857144107544049012099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4767904762738362699341399 7151857144107544049012099)
                  ·
                    refine ⟨10727785716161316073518149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7151857144107544049012099 10727785716161316073518149)
                    ·
                      refine ⟨2011459821780246763784653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10727785716161316073518149 2011459821780246763784653)
                      ·
                        rfl

theorem cell23_3917304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 1, 1, 4].length) (baseStart_3917304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917304 prefixEnd_3917304 := by exact prefixLift 3917304
  have htrace : WordTrace (prefixWord ++ tailWord_3917304) baseStart_3917304 baseEnd_3917304 := by
    simpa [prefixWord, tailWord_3917304, baseEnd_3917304] using wordTrace_append hprefix tailTrace_3917304
  have hstable : (prefixWord ++ tailWord_3917304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917304).length < 2 ^ (prefixWord ++ tailWord_3917304).sum := by decide
  have hdescent : baseEnd_3917304 < baseStart_3917304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917321 : List Nat := [1, 2, 1, 1, 3, 1, 5, 4, 1, 2, 2]
def baseStart_3917321 : Nat := 118140960795 + 3917321 * 2 ^ 59
def prefixEnd_3917321 : Nat := 4983230072969 + 3 ^ 40 * 3917321 * 2
def baseEnd_3917321 : Nat := 2011468550951373197272075

theorem tailTrace_3917321 : CollatzResearch.WordTrace tailWord_3917321 prefixEnd_3917321 2011468550951373197272075 := by
  unfold tailWord_3917321
  simp only [CollatzResearch.WordTrace]
  refine ⟨142876434641222517008095817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95250956427481678005397211 142876434641222517008095817)
  ·
    refine ⟨107157325980916887756071863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142876434641222517008095817 107157325980916887756071863)
    ·
      refine ⟨160735988971375331634107795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107157325980916887756071863 160735988971375331634107795)
      ·
        refine ⟨241103983457062997451161693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160735988971375331634107795 241103983457062997451161693)
        ·
          refine ⟨90413993796398624044185635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241103983457062997451161693 90413993796398624044185635)
          ·
            refine ⟨135620990694597936066278453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90413993796398624044185635 135620990694597936066278453)
            ·
              refine ⟨12714467877618556506213605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135620990694597936066278453 12714467877618556506213605)
              ·
                refine ⟨2383962727053479344915051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12714467877618556506213605 2383962727053479344915051)
                ·
                  refine ⟨3575944090580219017372577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2383962727053479344915051 3575944090580219017372577)
                  ·
                    refine ⟨2681958067935164263029433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3575944090580219017372577 2681958067935164263029433)
                    ·
                      refine ⟨2011468550951373197272075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2681958067935164263029433 2011468550951373197272075)
                      ·
                        rfl

theorem cell23_3917321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 4, 1, 2, 2].length) (baseStart_3917321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917321 prefixEnd_3917321 := by exact prefixLift 3917321
  have htrace : WordTrace (prefixWord ++ tailWord_3917321) baseStart_3917321 baseEnd_3917321 := by
    simpa [prefixWord, tailWord_3917321, baseEnd_3917321] using wordTrace_append hprefix tailTrace_3917321
  have hstable : (prefixWord ++ tailWord_3917321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917321).length < 2 ^ (prefixWord ++ tailWord_3917321).sum := by decide
  have hdescent : baseEnd_3917321 < baseStart_3917321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917340 : List Nat := [2, 2, 3, 1, 2, 1, 1, 2, 2, 7]
def baseStart_3917340 : Nat := 118140960795 + 3917340 * 2 ^ 59
def prefixEnd_3917340 : Nat := 4983230072969 + 3 ^ 40 * 3917340 * 2
def baseEnd_3917340 : Nat := 670492769027936207644829

theorem tailTrace_3917340 : CollatzResearch.WordTrace tailWord_3917340 prefixEnd_3917340 670492769027936207644829 := by
  unfold tailWord_3917340
  simp only [CollatzResearch.WordTrace]
  refine ⟨71438563814076841626518737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95251418418769122168691649 71438563814076841626518737)
  ·
    refine ⟨53578922860557631219889053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71438563814076841626518737 53578922860557631219889053)
    ·
      refine ⟨20092096072709111707458395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53578922860557631219889053 20092096072709111707458395)
      ·
        refine ⟨30138144109063667561187593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20092096072709111707458395 30138144109063667561187593)
        ·
          refine ⟨22603608081797750670890695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30138144109063667561187593 22603608081797750670890695)
          ·
            refine ⟨33905412122696626006336043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22603608081797750670890695 33905412122696626006336043)
            ·
              refine ⟨50858118184044939009504065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33905412122696626006336043 50858118184044939009504065)
              ·
                refine ⟨38143588638033704257128049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50858118184044939009504065 38143588638033704257128049)
                ·
                  refine ⟨28607691478525278192846037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38143588638033704257128049 28607691478525278192846037)
                  ·
                    refine ⟨670492769027936207644829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28607691478525278192846037 670492769027936207644829)
                    ·
                      rfl

theorem cell23_3917340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_3917340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917340 prefixEnd_3917340 := by exact prefixLift 3917340
  have htrace : WordTrace (prefixWord ++ tailWord_3917340) baseStart_3917340 baseEnd_3917340 := by
    simpa [prefixWord, tailWord_3917340, baseEnd_3917340] using wordTrace_append hprefix tailTrace_3917340
  have hstable : (prefixWord ++ tailWord_3917340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917340).length < 2 ^ (prefixWord ++ tailWord_3917340).sum := by decide
  have hdescent : baseEnd_3917340 < baseStart_3917340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917342 : List Nat := [4, 3, 3, 1, 1, 2, 1, 1, 2, 3, 2]
def baseStart_3917342 : Nat := 118140960795 + 3917342 * 2 ^ 59
def prefixEnd_3917342 : Nat := 4983230072969 + 3 ^ 40 * 3917342 * 2
def baseEnd_3917342 : Nat := 2011479334045117615109479

theorem tailTrace_3917342 : CollatzResearch.WordTrace tailWord_3917342 prefixEnd_3917342 2011479334045117615109479 := by
  unfold tailWord_3917342
  simp only [CollatzResearch.WordTrace]
  refine ⟨17859650071768304699326285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95251467049430958396406853 17859650071768304699326285)
  ·
    refine ⟨6697368776913114262247357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17859650071768304699326285 6697368776913114262247357)
    ·
      refine ⟨2511513291342417848342759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6697368776913114262247357 2511513291342417848342759)
      ·
        refine ⟨3767269937013626772514139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2511513291342417848342759 3767269937013626772514139)
        ·
          refine ⟨5650904905520440158771209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3767269937013626772514139 5650904905520440158771209)
          ·
            refine ⟨4238178679140330119078407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5650904905520440158771209 4238178679140330119078407)
            ·
              refine ⟨6357268018710495178617611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4238178679140330119078407 6357268018710495178617611)
              ·
                refine ⟨9535902028065742767926417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6357268018710495178617611 9535902028065742767926417)
                ·
                  refine ⟨7151926521049307075944813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9535902028065742767926417 7151926521049307075944813)
                  ·
                    refine ⟨2681972445393490153479305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7151926521049307075944813 2681972445393490153479305)
                    ·
                      refine ⟨2011479334045117615109479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2681972445393490153479305 2011479334045117615109479)
                      ·
                        rfl

theorem cell23_3917342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_3917342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917342 prefixEnd_3917342 := by exact prefixLift 3917342
  have htrace : WordTrace (prefixWord ++ tailWord_3917342) baseStart_3917342 baseEnd_3917342 := by
    simpa [prefixWord, tailWord_3917342, baseEnd_3917342] using wordTrace_append hprefix tailTrace_3917342
  have hstable : (prefixWord ++ tailWord_3917342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917342).length < 2 ^ (prefixWord ++ tailWord_3917342).sum := by decide
  have hdescent : baseEnd_3917342 < baseStart_3917342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917354 : List Nat := [3, 1, 4, 1, 1, 1, 2, 2, 4, 1, 3]
def baseStart_3917354 : Nat := 118140960795 + 3917354 * 2 ^ 59
def prefixEnd_3917354 : Nat := 4983230072969 + 3 ^ 40 * 3917354 * 2
def baseEnd_3917354 : Nat := 2011485495812971568159423

theorem tailTrace_3917354 : CollatzResearch.WordTrace tailWord_3917354 prefixEnd_3917354 2011485495812971568159423 := by
  unfold tailWord_3917354
  simp only [CollatzResearch.WordTrace]
  refine ⟨35719409562525740911011779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95251758833401975762698077 35719409562525740911011779)
  ·
    refine ⟨53579114343788611366517669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35719409562525740911011779 53579114343788611366517669)
    ·
      refine ⟨10046083939460364631222063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53579114343788611366517669 10046083939460364631222063)
      ·
        refine ⟨15069125909190546946833095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10046083939460364631222063 15069125909190546946833095)
        ·
          refine ⟨22603688863785820420249643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15069125909190546946833095 22603688863785820420249643)
          ·
            refine ⟨33905533295678730630374465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22603688863785820420249643 33905533295678730630374465)
            ·
              refine ⟨25429149971759047972780849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33905533295678730630374465 25429149971759047972780849)
              ·
                refine ⟨19071862478819285979585637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25429149971759047972780849 19071862478819285979585637)
                ·
                  refine ⟨3575974214778616121172307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19071862478819285979585637 3575974214778616121172307)
                  ·
                    refine ⟨5363961322167924181758461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3575974214778616121172307 5363961322167924181758461)
                    ·
                      refine ⟨2011485495812971568159423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5363961322167924181758461 2011485495812971568159423)
                      ·
                        rfl

theorem cell23_3917354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_3917354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917354 prefixEnd_3917354 := by exact prefixLift 3917354
  have htrace : WordTrace (prefixWord ++ tailWord_3917354) baseStart_3917354 baseEnd_3917354 := by
    simpa [prefixWord, tailWord_3917354, baseEnd_3917354] using wordTrace_append hprefix tailTrace_3917354
  have hstable : (prefixWord ++ tailWord_3917354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917354).length < 2 ^ (prefixWord ++ tailWord_3917354).sum := by decide
  have hdescent : baseEnd_3917354 < baseStart_3917354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917358 : List Nat := [4, 1, 3, 1, 2, 3, 2, 1, 1, 2, 3]
def baseStart_3917358 : Nat := 118140960795 + 3917358 * 2 ^ 59
def prefixEnd_3917358 : Nat := 4983230072969 + 3 ^ 40 * 3917358 * 2
def baseEnd_3917358 : Nat := 2011487549735589552509405

theorem tailTrace_3917358 : CollatzResearch.WordTrace tailWord_3917358 prefixEnd_3917358 2011487549735589552509405 := by
  unfold tailWord_3917358
  simp only [CollatzResearch.WordTrace]
  refine ⟨17859723017761059040899091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95251856094725648218128485 17859723017761059040899091)
  ·
    refine ⟨26789584526641588561348637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17859723017761059040899091 26789584526641588561348637)
    ·
      refine ⟨10046094197490595710505739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26789584526641588561348637 10046094197490595710505739)
      ·
        refine ⟨15069141296235893565758609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10046094197490595710505739 15069141296235893565758609)
        ·
          refine ⟨11301855972176920174318957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15069141296235893565758609 11301855972176920174318957)
          ·
            refine ⟨4238195989566345065369609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11301855972176920174318957 4238195989566345065369609)
            ·
              refine ⟨3178646992174758799027207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4238195989566345065369609 3178646992174758799027207)
              ·
                refine ⟨4767970488262138198540811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3178646992174758799027207 4767970488262138198540811)
                ·
                  refine ⟨7151955732393207297811217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4767970488262138198540811 7151955732393207297811217)
                  ·
                    refine ⟨5363966799294905473358413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7151955732393207297811217 5363966799294905473358413)
                    ·
                      refine ⟨2011487549735589552509405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5363966799294905473358413 2011487549735589552509405)
                      ·
                        rfl

theorem cell23_3917358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_3917358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917358 prefixEnd_3917358 := by exact prefixLift 3917358
  have htrace : WordTrace (prefixWord ++ tailWord_3917358) baseStart_3917358 baseEnd_3917358 := by
    simpa [prefixWord, tailWord_3917358, baseEnd_3917358] using wordTrace_append hprefix tailTrace_3917358
  have hstable : (prefixWord ++ tailWord_3917358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917358).length < 2 ^ (prefixWord ++ tailWord_3917358).sum := by decide
  have hdescent : baseEnd_3917358 < baseStart_3917358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917370 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 4, 6]
def baseStart_3917370 : Nat := 118140960795 + 3917370 * 2 ^ 59
def prefixEnd_3917370 : Nat := 4983230072969 + 3 ^ 40 * 3917370 * 2
def baseEnd_3917370 : Nat := 670497903834481168519783

theorem tailTrace_3917370 : CollatzResearch.WordTrace tailWord_3917370 prefixEnd_3917370 670497903834481168519783 := by
  unfold tailWord_3917370
  simp only [CollatzResearch.WordTrace]
  refine ⟨35719555454511249594157391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95252147878696665584419709 35719555454511249594157391)
  ·
    refine ⟨53579333181766874391236087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35719555454511249594157391 53579333181766874391236087)
    ·
      refine ⟨80368999772650311586854131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53579333181766874391236087 80368999772650311586854131)
      ·
        refine ⟨120553499658975467380281197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80368999772650311586854131 120553499658975467380281197)
        ·
          refine ⟨45207562372115800267605449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120553499658975467380281197 45207562372115800267605449)
          ·
            refine ⟨33905671779086850200704087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45207562372115800267605449 33905671779086850200704087)
            ·
              refine ⟨50858507668630275301056131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33905671779086850200704087 50858507668630275301056131)
              ·
                refine ⟨76287761502945412951584197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50858507668630275301056131 76287761502945412951584197)
                ·
                  refine ⟨14303955281802264928422037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76287761502945412951584197 14303955281802264928422037)
                  ·
                    refine ⟨670497903834481168519783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14303955281802264928422037 670497903834481168519783)
                    ·
                      rfl

theorem cell23_3917370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 4, 6].length) (baseStart_3917370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917370 prefixEnd_3917370 := by exact prefixLift 3917370
  have htrace : WordTrace (prefixWord ++ tailWord_3917370) baseStart_3917370 baseEnd_3917370 := by
    simpa [prefixWord, tailWord_3917370, baseEnd_3917370] using wordTrace_append hprefix tailTrace_3917370
  have hstable : (prefixWord ++ tailWord_3917370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917370).length < 2 ^ (prefixWord ++ tailWord_3917370).sum := by decide
  have hdescent : baseEnd_3917370 < baseStart_3917370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917464 : List Nat := [2, 1, 2, 4, 1, 3, 2, 1, 2, 5]
def baseStart_3917464 : Nat := 118140960795 + 3917464 * 2 ^ 59
def prefixEnd_3917464 : Nat := 4983230072969 + 3 ^ 40 * 3917464 * 2
def baseEnd_3917464 : Nat := 670513992894988712594639

theorem tailTrace_3917464 : CollatzResearch.WordTrace tailWord_3917464 prefixEnd_3917464 670513992894988712594639 := by
  unfold tailWord_3917464
  simp only [CollatzResearch.WordTrace]
  refine ⟨71440825139852226215275723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95254433519802968287034297 71440825139852226215275723)
  ·
    refine ⟨107161237709778339322913585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71440825139852226215275723 107161237709778339322913585)
    ·
      refine ⟨80370928282333754492185189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107161237709778339322913585 80370928282333754492185189)
      ·
        refine ⟨15069549052937578967284723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80370928282333754492185189 15069549052937578967284723)
        ·
          refine ⟨22604323579406368450927085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15069549052937578967284723 22604323579406368450927085)
          ·
            refine ⟨8476621342277388169097657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22604323579406368450927085 8476621342277388169097657)
            ·
              refine ⟨6357466006708041126823243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8476621342277388169097657 6357466006708041126823243)
              ·
                refine ⟨9536199010062061690234865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6357466006708041126823243 9536199010062061690234865)
                ·
                  refine ⟨7152149257546546267676149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9536199010062061690234865 7152149257546546267676149)
                  ·
                    refine ⟨670513992894988712594639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7152149257546546267676149 670513992894988712594639)
                    ·
                      rfl

theorem cell23_3917464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 2, 5].length) (baseStart_3917464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917464 prefixEnd_3917464 := by exact prefixLift 3917464
  have htrace : WordTrace (prefixWord ++ tailWord_3917464) baseStart_3917464 baseEnd_3917464 := by
    simpa [prefixWord, tailWord_3917464, baseEnd_3917464] using wordTrace_append hprefix tailTrace_3917464
  have hstable : (prefixWord ++ tailWord_3917464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917464).length < 2 ^ (prefixWord ++ tailWord_3917464).sum := by decide
  have hdescent : baseEnd_3917464 < baseStart_3917464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917521 : List Nat := [1, 2, 2, 1, 2, 6, 1, 1, 2, 2, 3]
def baseStart_3917521 : Nat := 118140960795 + 3917521 * 2 ^ 59
def prefixEnd_3917521 : Nat := 4983230072969 + 3 ^ 40 * 3917521 * 2
def baseEnd_3917521 : Nat := 2011571247082272414771155

theorem tailTrace_3917521 : CollatzResearch.WordTrace tailWord_3917521 prefixEnd_3917521 2011571247082272414771155 := by
  unfold tailWord_3917521
  simp only [CollatzResearch.WordTrace]
  refine ⟨142883729240497951165376417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95255819493665300776917611 142883729240497951165376417)
  ·
    refine ⟨107162796930373463374032313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142883729240497951165376417 107162796930373463374032313)
    ·
      refine ⟨80372097697780097530524235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107162796930373463374032313 80372097697780097530524235)
      ·
        refine ⟨120558146546670146295786353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80372097697780097530524235 120558146546670146295786353)
        ·
          refine ⟨90418609910002609721839765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120558146546670146295786353 90418609910002609721839765)
          ·
            refine ⟨4238372339531372330711239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 90418609910002609721839765 4238372339531372330711239)
            ·
              refine ⟨6357558509297058496066859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4238372339531372330711239 6357558509297058496066859)
              ·
                refine ⟨9536337763945587744100289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6357558509297058496066859 9536337763945587744100289)
                ·
                  refine ⟨7152253322959190808075217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9536337763945587744100289 7152253322959190808075217)
                  ·
                    refine ⟨5364189992219393106056413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7152253322959190808075217 5364189992219393106056413)
                    ·
                      refine ⟨2011571247082272414771155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5364189992219393106056413 2011571247082272414771155)
                      ·
                        rfl

theorem cell23_3917521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 2, 3].length) (baseStart_3917521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917521 prefixEnd_3917521 := by exact prefixLift 3917521
  have htrace : WordTrace (prefixWord ++ tailWord_3917521) baseStart_3917521 baseEnd_3917521 := by
    simpa [prefixWord, tailWord_3917521, baseEnd_3917521] using wordTrace_append hprefix tailTrace_3917521
  have hstable : (prefixWord ++ tailWord_3917521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917521).length < 2 ^ (prefixWord ++ tailWord_3917521).sum := by decide
  have hdescent : baseEnd_3917521 < baseStart_3917521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917551 : List Nat := [1, 1, 2, 1, 5, 1, 4, 1, 3, 1, 3]
def baseStart_3917551 : Nat := 118140960795 + 3917551 * 2 ^ 59
def prefixEnd_3917551 : Nat := 4983230072969 + 3 ^ 40 * 3917551 * 2
def baseEnd_3917551 : Nat := 2011586651501907297396017

theorem tailTrace_3917551 : CollatzResearch.WordTrace tailWord_3917551 prefixEnd_3917551 2011586651501907297396017 := by
  unfold tailWord_3917551
  simp only [CollatzResearch.WordTrace]
  refine ⟨142884823430389266288968507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95256548953592844192645671 142884823430389266288968507)
  ·
    refine ⟨214327235145583899433452761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142884823430389266288968507 214327235145583899433452761)
    ·
      refine ⟨160745426359187924575089571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214327235145583899433452761 160745426359187924575089571)
      ·
        refine ⟨241118139538781886862634357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160745426359187924575089571 241118139538781886862634357)
        ·
          refine ⟨22604825581760801893371971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 241118139538781886862634357 22604825581760801893371971)
          ·
            refine ⟨33907238372641202840057957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22604825581760801893371971 33907238372641202840057957)
            ·
              refine ⟨6357607194870225532510867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33907238372641202840057957 6357607194870225532510867)
              ·
                refine ⟨9536410792305338298766301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6357607194870225532510867 9536410792305338298766301)
                ·
                  refine ⟨3576154047114501862037363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9536410792305338298766301 3576154047114501862037363)
                  ·
                    refine ⟨5364231070671752793056045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3576154047114501862037363 5364231070671752793056045)
                    ·
                      refine ⟨2011586651501907297396017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5364231070671752793056045 2011586651501907297396017)
                      ·
                        rfl

theorem cell23_3917551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 3, 1, 3].length) (baseStart_3917551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917551 prefixEnd_3917551 := by exact prefixLift 3917551
  have htrace : WordTrace (prefixWord ++ tailWord_3917551) baseStart_3917551 baseEnd_3917551 := by
    simpa [prefixWord, tailWord_3917551, baseEnd_3917551] using wordTrace_append hprefix tailTrace_3917551
  have hstable : (prefixWord ++ tailWord_3917551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917551).length < 2 ^ (prefixWord ++ tailWord_3917551).sum := by decide
  have hdescent : baseEnd_3917551 < baseStart_3917551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917577 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 5, 1, 5]
def baseStart_3917577 : Nat := 118140960795 + 3917577 * 2 ^ 59
def prefixEnd_3917577 : Nat := 4983230072969 + 3 ^ 40 * 3917577 * 2
def baseEnd_3917577 : Nat := 2011600001998924195670897

theorem tailTrace_3917577 : CollatzResearch.WordTrace tailWord_3917577 prefixEnd_3917577 2011600001998924195670897 := by
  unfold tailWord_3917577
  simp only [CollatzResearch.WordTrace]
  refine ⟨142885771728295072729414985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95257181152196715152943323 142885771728295072729414985)
  ·
    refine ⟨107164328796221304547061239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142885771728295072729414985 107164328796221304547061239)
    ·
      refine ⟨160746493194331956820591859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107164328796221304547061239 160746493194331956820591859)
      ·
        refine ⟨241119739791497935230887789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160746493194331956820591859 241119739791497935230887789)
        ·
          refine ⟨90419902421811725711582921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241119739791497935230887789 90419902421811725711582921)
          ·
            refine ⟨67814926816358794283687191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90419902421811725711582921 67814926816358794283687191)
            ·
              refine ⟨101722390224538191425530787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67814926816358794283687191 101722390224538191425530787)
              ·
                refine ⟨152583585336807287138296181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101722390224538191425530787 152583585336807287138296181)
                ·
                  refine ⟨14304711125325683169215267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 152583585336807287138296181 14304711125325683169215267)
                  ·
                    refine ⟨21457066687988524753822901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14304711125325683169215267 21457066687988524753822901)
                    ·
                      refine ⟨2011600001998924195670897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21457066687988524753822901 2011600001998924195670897)
                      ·
                        rfl

theorem cell23_3917577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 1, 5].length) (baseStart_3917577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917577 prefixEnd_3917577 := by exact prefixLift 3917577
  have htrace : WordTrace (prefixWord ++ tailWord_3917577) baseStart_3917577 baseEnd_3917577 := by
    simpa [prefixWord, tailWord_3917577, baseEnd_3917577] using wordTrace_append hprefix tailTrace_3917577
  have hstable : (prefixWord ++ tailWord_3917577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917577).length < 2 ^ (prefixWord ++ tailWord_3917577).sum := by decide
  have hdescent : baseEnd_3917577 < baseStart_3917577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917591 : List Nat := [1, 1, 3, 4, 2, 1, 2, 3, 1, 1, 4]
def baseStart_3917591 : Nat := 118140960795 + 3917591 * 2 ^ 59
def prefixEnd_3917591 : Nat := 4983230072969 + 3 ^ 40 * 3917591 * 2
def baseEnd_3917591 : Nat := 2011607190728087140895833

theorem tailTrace_3917591 : CollatzResearch.WordTrace tailWord_3917591 prefixEnd_3917591 2011607190728087140895833 := by
  unfold tailWord_3917591
  simp only [CollatzResearch.WordTrace]
  refine ⟨142886282350244353120424627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95257521566829568746949751 142886282350244353120424627)
  ·
    refine ⟨214329423525366529680636941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142886282350244353120424627 214329423525366529680636941)
    ·
      refine ⟨80373533822012448630238853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214329423525366529680636941 80373533822012448630238853)
      ·
        refine ⟨15070037591627334118169785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80373533822012448630238853 15070037591627334118169785)
        ·
          refine ⟨11302528193720500588627339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15070037591627334118169785 11302528193720500588627339)
          ·
            refine ⟨16953792290580750882941009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11302528193720500588627339 16953792290580750882941009)
            ·
              refine ⟨12715344217935563162205757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16953792290580750882941009 12715344217935563162205757)
              ·
                refine ⟨4768254081725836185827159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12715344217935563162205757 4768254081725836185827159)
                ·
                  refine ⟨7152381122588754278740739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4768254081725836185827159 7152381122588754278740739)
                  ·
                    refine ⟨10728571683883131418111109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7152381122588754278740739 10728571683883131418111109)
                    ·
                      refine ⟨2011607190728087140895833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10728571683883131418111109 2011607190728087140895833)
                      ·
                        rfl

theorem cell23_3917591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_3917591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917591 prefixEnd_3917591 := by exact prefixLift 3917591
  have htrace : WordTrace (prefixWord ++ tailWord_3917591) baseStart_3917591 baseEnd_3917591 := by
    simpa [prefixWord, tailWord_3917591, baseEnd_3917591] using wordTrace_append hprefix tailTrace_3917591
  have hstable : (prefixWord ++ tailWord_3917591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917591).length < 2 ^ (prefixWord ++ tailWord_3917591).sum := by decide
  have hdescent : baseEnd_3917591 < baseStart_3917591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917594 : List Nat := [3, 1, 1, 3, 2, 2, 1, 3, 1, 1, 5]
def baseStart_3917594 : Nat := 118140960795 + 3917594 * 2 ^ 59
def prefixEnd_3917594 : Nat := 4983230072969 + 3 ^ 40 * 3917594 * 2
def baseEnd_3917594 : Nat := 2011608731170050629158319

theorem tailTrace_3917594 : CollatzResearch.WordTrace tailWord_3917594 prefixEnd_3917594 2011608731170050629158319 := by
  unfold tailWord_3917594
  simp only [CollatzResearch.WordTrace]
  refine ⟨35721597942308371158195959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95257594512822323088522557 35721597942308371158195959)
  ·
    refine ⟨53582396913462556737293939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35721597942308371158195959 53582396913462556737293939)
    ·
      refine ⟨80373595370193835105940909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53582396913462556737293939 80373595370193835105940909)
      ·
        refine ⟨30140098263822688164727841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80373595370193835105940909 30140098263822688164727841)
        ·
          refine ⟨22605073697867016123545881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30140098263822688164727841 22605073697867016123545881)
          ·
            refine ⟨16953805273400262092659411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22605073697867016123545881 16953805273400262092659411)
            ·
              refine ⟨25430707910100393138989117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16953805273400262092659411 25430707910100393138989117)
              ·
                refine ⟨9536515466287647427120919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25430707910100393138989117 9536515466287647427120919)
                ·
                  refine ⟨14304773199431471140681379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9536515466287647427120919 14304773199431471140681379)
                  ·
                    refine ⟨21457159799147206711022069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14304773199431471140681379 21457159799147206711022069)
                    ·
                      refine ⟨2011608731170050629158319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21457159799147206711022069 2011608731170050629158319)
                      ·
                        rfl

theorem cell23_3917594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_3917594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917594 prefixEnd_3917594 := by exact prefixLift 3917594
  have htrace : WordTrace (prefixWord ++ tailWord_3917594) baseStart_3917594 baseEnd_3917594 := by
    simpa [prefixWord, tailWord_3917594, baseEnd_3917594] using wordTrace_append hprefix tailTrace_3917594
  have hstable : (prefixWord ++ tailWord_3917594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917594).length < 2 ^ (prefixWord ++ tailWord_3917594).sum := by decide
  have hdescent : baseEnd_3917594 < baseStart_3917594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917604 : List Nat := [2, 3, 1, 3, 2, 1, 1, 2, 1, 1, 6]
def baseStart_3917604 : Nat := 118140960795 + 3917604 * 2 ^ 59
def prefixEnd_3917604 : Nat := 4983230072969 + 3 ^ 40 * 3917604 * 2
def baseEnd_3917604 : Nat := 2011613865976595590033273

theorem tailTrace_3917604 : CollatzResearch.WordTrace tailWord_3917604 prefixEnd_3917604 2011613865976595590033273 := by
  unfold tailWord_3917604
  simp only [CollatzResearch.WordTrace]
  refine ⟨71443378249598628170323933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95257837666131504227098577 71443378249598628170323933)
  ·
    refine ⟨26791266843599485563871475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71443378249598628170323933 26791266843599485563871475)
    ·
      refine ⟨40186900265399228345807213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26791266843599485563871475 40186900265399228345807213)
      ·
        refine ⟨15070087599524710629677705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40186900265399228345807213 15070087599524710629677705)
        ·
          refine ⟨11302565699643532972258279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15070087599524710629677705 11302565699643532972258279)
          ·
            refine ⟨16953848549465299458387419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11302565699643532972258279 16953848549465299458387419)
            ·
              refine ⟨25430772824197949187581129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16953848549465299458387419 25430772824197949187581129)
              ·
                refine ⟨19073079618148461890685847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25430772824197949187581129 19073079618148461890685847)
                ·
                  refine ⟨28609619427222692836028771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19073079618148461890685847 28609619427222692836028771)
                  ·
                    refine ⟨42914429140834039254043157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28609619427222692836028771 42914429140834039254043157)
                    ·
                      refine ⟨2011613865976595590033273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42914429140834039254043157 2011613865976595590033273)
                      ·
                        rfl

theorem cell23_3917604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_3917604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917604 prefixEnd_3917604 := by exact prefixLift 3917604
  have htrace : WordTrace (prefixWord ++ tailWord_3917604) baseStart_3917604 baseEnd_3917604 := by
    simpa [prefixWord, tailWord_3917604, baseEnd_3917604] using wordTrace_append hprefix tailTrace_3917604
  have hstable : (prefixWord ++ tailWord_3917604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917604).length < 2 ^ (prefixWord ++ tailWord_3917604).sum := by decide
  have hdescent : baseEnd_3917604 < baseStart_3917604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917618 : List Nat := [3, 2, 1, 1, 3, 2, 4, 1, 2, 4]
def baseStart_3917618 : Nat := 118140960795 + 3917618 * 2 ^ 59
def prefixEnd_3917618 : Nat := 4983230072969 + 3 ^ 40 * 3917618 * 2
def baseEnd_3917618 : Nat := 670540351568586178419403

theorem tailTrace_3917618 : CollatzResearch.WordTrace tailWord_3917618 prefixEnd_3917618 670540351568586178419403 := by
  unfold tailWord_3917618
  simp only [CollatzResearch.WordTrace]
  refine ⟨35721816780286634182914377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95258178080764357821105005 35721816780286634182914377)
  ·
    refine ⟨26791362585214975637185783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35721816780286634182914377 26791362585214975637185783)
    ·
      refine ⟨40187043877822463455778675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26791362585214975637185783 40187043877822463455778675)
      ·
        refine ⟨60280565816733695183668013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40187043877822463455778675 60280565816733695183668013)
        ·
          refine ⟨22605212181275135693875505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60280565816733695183668013 22605212181275135693875505)
          ·
            refine ⟨16953909135956351770406629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22605212181275135693875505 16953909135956351770406629)
            ·
              refine ⟨3178857962991815956951243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16953909135956351770406629 3178857962991815956951243)
              ·
                refine ⟨4768286944487723935426865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3178857962991815956951243 4768286944487723935426865)
                ·
                  refine ⟨3576215208365792951570149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4768286944487723935426865 3576215208365792951570149)
                  ·
                    refine ⟨670540351568586178419403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3576215208365792951570149 670540351568586178419403)
                    ·
                      rfl

theorem cell23_3917618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 2, 4].length) (baseStart_3917618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917618 prefixEnd_3917618 := by exact prefixLift 3917618
  have htrace : WordTrace (prefixWord ++ tailWord_3917618) baseStart_3917618 baseEnd_3917618 := by
    simpa [prefixWord, tailWord_3917618, baseEnd_3917618] using wordTrace_append hprefix tailTrace_3917618
  have hstable : (prefixWord ++ tailWord_3917618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917618).length < 2 ^ (prefixWord ++ tailWord_3917618).sum := by decide
  have hdescent : baseEnd_3917618 < baseStart_3917618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917625 : List Nat := [1, 2, 1, 7, 1, 2, 1, 2, 1, 1, 4]
def baseStart_3917625 : Nat := 118140960795 + 3917625 * 2 ^ 59
def prefixEnd_3917625 : Nat := 4983230072969 + 3 ^ 40 * 3917625 * 2
def baseEnd_3917625 : Nat := 2011624649070340007870677

theorem tailTrace_3917625 : CollatzResearch.WordTrace tailWord_3917625 prefixEnd_3917625 2011624649070340007870677 := by
  unfold tailWord_3917625
  simp only [CollatzResearch.WordTrace]
  refine ⟨142887522432121176927162329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95258348288080784618108219 142887522432121176927162329)
  ·
    refine ⟨107165641824090882695371747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142887522432121176927162329 107165641824090882695371747)
    ·
      refine ⟨160748462736136324043057621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107165641824090882695371747 160748462736136324043057621)
      ·
        refine ⟨3767542095378195094759163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 160748462736136324043057621 3767542095378195094759163)
        ·
          refine ⟨5651313143067292642138745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3767542095378195094759163 5651313143067292642138745)
          ·
            refine ⟨4238484857300469481604059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5651313143067292642138745 4238484857300469481604059)
            ·
              refine ⟨6357727285950704222406089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4238484857300469481604059 6357727285950704222406089)
              ·
                refine ⟨4768295464463028166804567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6357727285950704222406089 4768295464463028166804567)
                ·
                  refine ⟨7152443196694542250206851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4768295464463028166804567 7152443196694542250206851)
                  ·
                    refine ⟨10728664795041813375310277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7152443196694542250206851 10728664795041813375310277)
                    ·
                      refine ⟨2011624649070340007870677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10728664795041813375310277 2011624649070340007870677)
                      ·
                        rfl

theorem cell23_3917625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_3917625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917625 prefixEnd_3917625 := by exact prefixLift 3917625
  have htrace : WordTrace (prefixWord ++ tailWord_3917625) baseStart_3917625 baseEnd_3917625 := by
    simpa [prefixWord, tailWord_3917625, baseEnd_3917625] using wordTrace_append hprefix tailTrace_3917625
  have hstable : (prefixWord ++ tailWord_3917625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917625).length < 2 ^ (prefixWord ++ tailWord_3917625).sum := by decide
  have hdescent : baseEnd_3917625 < baseStart_3917625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917638 : List Nat := [6, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4]
def baseStart_3917638 : Nat := 118140960795 + 3917638 * 2 ^ 59
def prefixEnd_3917638 : Nat := 4983230072969 + 3 ^ 40 * 3917638 * 2
def baseEnd_3917638 : Nat := 2011631324318848457008117

theorem tailTrace_3917638 : CollatzResearch.WordTrace tailWord_3917638 prefixEnd_3917638 2011631324318848457008117 := by
  unfold tailWord_3917638
  simp only [CollatzResearch.WordTrace]
  refine ⟨4465249893158565004605799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 95258664387382720098257045 4465249893158565004605799)
  ·
    refine ⟨6697874839737847506908699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4465249893158565004605799 6697874839737847506908699)
    ·
      refine ⟨10046812259606771260363049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6697874839737847506908699 10046812259606771260363049)
      ·
        refine ⟨7535109194705078445272287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10046812259606771260363049 7535109194705078445272287)
        ·
          refine ⟨11302663792057617667908431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7535109194705078445272287 11302663792057617667908431)
          ·
            refine ⟨16953995688086426501862647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11302663792057617667908431 16953995688086426501862647)
            ·
              refine ⟨25430993532129639752793971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16953995688086426501862647 25430993532129639752793971)
              ·
                refine ⟨38146490298194459629190957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25430993532129639752793971 38146490298194459629190957)
                ·
                  refine ⟨14304933861822922360946609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38146490298194459629190957 14304933861822922360946609)
                  ·
                    refine ⟨10728700396367191770709957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14304933861822922360946609 10728700396367191770709957)
                    ·
                      refine ⟨2011631324318848457008117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10728700396367191770709957 2011631324318848457008117)
                      ·
                        rfl

theorem cell23_3917638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_3917638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917638 prefixEnd_3917638 := by exact prefixLift 3917638
  have htrace : WordTrace (prefixWord ++ tailWord_3917638) baseStart_3917638 baseEnd_3917638 := by
    simpa [prefixWord, tailWord_3917638, baseEnd_3917638] using wordTrace_append hprefix tailTrace_3917638
  have hstable : (prefixWord ++ tailWord_3917638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917638).length < 2 ^ (prefixWord ++ tailWord_3917638).sum := by decide
  have hdescent : baseEnd_3917638 < baseStart_3917638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917658 : List Nat := [3, 1, 1, 2, 1, 3, 4, 2, 2, 1, 3]
def baseStart_3917658 : Nat := 118140960795 + 3917658 * 2 ^ 59
def prefixEnd_3917658 : Nat := 4983230072969 + 3 ^ 40 * 3917658 * 2
def baseEnd_3917658 : Nat := 2011641593931938378758025

theorem tailTrace_3917658 : CollatzResearch.WordTrace tailWord_3917658 prefixEnd_3917658 2011641593931938378758025 := by
  unfold tailWord_3917658
  simp only [CollatzResearch.WordTrace]
  refine ⟨35722181510250405890778407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95259150694001082375409085 35722181510250405890778407)
  ·
    refine ⟨53583272265375608836167611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35722181510250405890778407 53583272265375608836167611)
    ·
      refine ⟨80374908398063413254251417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53583272265375608836167611 80374908398063413254251417)
      ·
        refine ⟨60281181298547559940688563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80374908398063413254251417 60281181298547559940688563)
        ·
          refine ⟨90421771947821339911032845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60281181298547559940688563 90421771947821339911032845)
          ·
            refine ⟨33908164480433002466637317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90421771947821339911032845 33908164480433002466637317)
            ·
              refine ⟨6357780840081187962494497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33908164480433002466637317 6357780840081187962494497)
              ·
                refine ⟨4768335630060890971870873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6357780840081187962494497 4768335630060890971870873)
                ·
                  refine ⟨3576251722545668228903155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4768335630060890971870873 3576251722545668228903155)
                  ·
                    refine ⟨5364377583818502343354733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3576251722545668228903155 5364377583818502343354733)
                    ·
                      refine ⟨2011641593931938378758025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5364377583818502343354733 2011641593931938378758025)
                      ·
                        rfl

theorem cell23_3917658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 2, 1, 3].length) (baseStart_3917658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917658 prefixEnd_3917658 := by exact prefixLift 3917658
  have htrace : WordTrace (prefixWord ++ tailWord_3917658) baseStart_3917658 baseEnd_3917658 := by
    simpa [prefixWord, tailWord_3917658, baseEnd_3917658] using wordTrace_append hprefix tailTrace_3917658
  have hstable : (prefixWord ++ tailWord_3917658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917658).length < 2 ^ (prefixWord ++ tailWord_3917658).sum := by decide
  have hdescent : baseEnd_3917658 < baseStart_3917658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917664 : List Nat := [2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 4]
def baseStart_3917664 : Nat := 118140960795 + 3917664 * 2 ^ 59
def prefixEnd_3917664 : Nat := 4983230072969 + 3 ^ 40 * 3917664 * 2
def baseEnd_3917664 : Nat := 2011644674815865355282997

theorem tailTrace_3917664 : CollatzResearch.WordTrace tailWord_3917664 prefixEnd_3917664 2011644674815865355282997 := by
  unfold tailWord_3917664
  simp only [CollatzResearch.WordTrace]
  refine ⟨71444472439489943293916023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95259296585986591058554697 71444472439489943293916023)
  ·
    refine ⟨107166708659234914940874035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71444472439489943293916023 107166708659234914940874035)
    ·
      refine ⟨160750062988852372411311053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107166708659234914940874035 160750062988852372411311053)
      ·
        refine ⟨60281273620819639654241645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160750062988852372411311053 60281273620819639654241645)
        ·
          refine ⟨22605477607807364870340617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60281273620819639654241645 22605477607807364870340617)
          ·
            refine ⟨16954108205855523652755463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22605477607807364870340617 16954108205855523652755463)
            ·
              refine ⟨25431162308783285479133195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16954108205855523652755463 25431162308783285479133195)
              ·
                refine ⟨38146743463174928218699793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25431162308783285479133195 38146743463174928218699793)
                ·
                  refine ⟨28610057597381196164024845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38146743463174928218699793 28610057597381196164024845)
                  ·
                    refine ⟨10728771599017948561509317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28610057597381196164024845 10728771599017948561509317)
                    ·
                      refine ⟨2011644674815865355282997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10728771599017948561509317 2011644674815865355282997)
                      ·
                        rfl

theorem cell23_3917664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_3917664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917664 prefixEnd_3917664 := by exact prefixLift 3917664
  have htrace : WordTrace (prefixWord ++ tailWord_3917664) baseStart_3917664 baseEnd_3917664 := by
    simpa [prefixWord, tailWord_3917664, baseEnd_3917664] using wordTrace_append hprefix tailTrace_3917664
  have hstable : (prefixWord ++ tailWord_3917664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917664).length < 2 ^ (prefixWord ++ tailWord_3917664).sum := by decide
  have hdescent : baseEnd_3917664 < baseStart_3917664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917721 : List Nat := [1, 2, 1, 2, 1, 3, 4, 4, 5]
def baseStart_3917721 : Nat := 118140960795 + 3917721 * 2 ^ 59
def prefixEnd_3917721 : Nat := 4983230072969 + 3 ^ 40 * 3917721 * 2
def baseEnd_3917721 : Nat := 223519327023685736918915

theorem tailTrace_3917721 : CollatzResearch.WordTrace tailWord_3917721 prefixEnd_3917721 223519327023685736918915 := by
  unfold tailWord_3917721
  simp only [CollatzResearch.WordTrace]
  refine ⟨142891023839773385322657017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95260682559848923548438011 142891023839773385322657017)
  ·
    refine ⟨107168267879830038991992763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142891023839773385322657017 107168267879830038991992763)
    ·
      refine ⟨160752401819745058487989145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107168267879830038991992763 160752401819745058487989145)
      ·
        refine ⟨120564301364808793865991859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160752401819745058487989145 120564301364808793865991859)
        ·
          refine ⟨180846452047213190798987789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120564301364808793865991859 180846452047213190798987789)
          ·
            refine ⟨67817419517704946549620421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180846452047213190798987789 67817419517704946549620421)
            ·
              refine ⟨12715766159569677478053829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67817419517704946549620421 12715766159569677478053829)
              ·
                refine ⟨2384206154919314527135093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12715766159569677478053829 2384206154919314527135093)
                ·
                  refine ⟨223519327023685736918915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2384206154919314527135093 223519327023685736918915)
                  ·
                    rfl

theorem cell23_3917721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 4, 5].length) (baseStart_3917721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917721 prefixEnd_3917721 := by exact prefixLift 3917721
  have htrace : WordTrace (prefixWord ++ tailWord_3917721) baseStart_3917721 baseEnd_3917721 := by
    simpa [prefixWord, tailWord_3917721, baseEnd_3917721] using wordTrace_append hprefix tailTrace_3917721
  have hstable : (prefixWord ++ tailWord_3917721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917721).length < 2 ^ (prefixWord ++ tailWord_3917721).sum := by decide
  have hdescent : baseEnd_3917721 < baseStart_3917721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917732 : List Nat := [2, 3, 1, 2, 1, 4, 3, 1, 2, 2, 2]
def baseStart_3917732 : Nat := 118140960795 + 3917732 * 2 ^ 59
def prefixEnd_3917732 : Nat := 4983230072969 + 3 ^ 40 * 3917732 * 2
def baseEnd_3917732 : Nat := 2011679591500371089232685

theorem tailTrace_3917732 : CollatzResearch.WordTrace tailWord_3917732 prefixEnd_3917732 2011679591500371089232685 := by
  unfold tailWord_3917732
  simp only [CollatzResearch.WordTrace]
  refine ⟨71445712521366767100653725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95260950028489022800871633 71445712521366767100653725)
  ·
    refine ⟨26792142195512537662745147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71445712521366767100653725 26792142195512537662745147)
    ·
      refine ⟨40188213293268806494117721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26792142195512537662745147 40188213293268806494117721)
      ·
        refine ⟨30141159969951604870588291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40188213293268806494117721 30141159969951604870588291)
        ·
          refine ⟨45211739954927407305882437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30141159969951604870588291 45211739954927407305882437)
          ·
            refine ⟨8477201241548888869852957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45211739954927407305882437 8477201241548888869852957)
            ·
              refine ⟨3178950465580833326194859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8477201241548888869852957 3178950465580833326194859)
              ·
                refine ⟨4768425698371249989292289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3178950465580833326194859 4768425698371249989292289)
                ·
                  refine ⟨3576319273778437491969217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4768425698371249989292289 3576319273778437491969217)
                  ·
                    refine ⟨2682239455333828118976913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3576319273778437491969217 2682239455333828118976913)
                    ·
                      refine ⟨2011679591500371089232685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2682239455333828118976913 2011679591500371089232685)
                      ·
                        rfl

theorem cell23_3917732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_3917732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917732 prefixEnd_3917732 := by exact prefixLift 3917732
  have htrace : WordTrace (prefixWord ++ tailWord_3917732) baseStart_3917732 baseEnd_3917732 := by
    simpa [prefixWord, tailWord_3917732, baseEnd_3917732] using wordTrace_append hprefix tailTrace_3917732
  have hstable : (prefixWord ++ tailWord_3917732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917732).length < 2 ^ (prefixWord ++ tailWord_3917732).sum := by decide
  have hdescent : baseEnd_3917732 < baseStart_3917732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917771 : List Nat := [1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 4]
def baseStart_3917771 : Nat := 118140960795 + 3917771 * 2 ^ 59
def prefixEnd_3917771 : Nat := 4983230072969 + 3 ^ 40 * 3917771 * 2
def baseEnd_3917771 : Nat := 2011699617245896436645005

theorem tailTrace_3917771 : CollatzResearch.WordTrace tailWord_3917771 prefixEnd_3917771 2011699617245896436645005 := by
  unfold tailWord_3917771
  simp only [CollatzResearch.WordTrace]
  refine ⟨142892847489592243861977167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95261898326394829241318111 142892847489592243861977167)
  ·
    refine ⟨214339271234388365792965751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142892847489592243861977167 214339271234388365792965751)
    ·
      refine ⟨321508906851582548689448627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214339271234388365792965751 321508906851582548689448627)
      ·
        refine ⟨482263360277373823034172941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321508906851582548689448627 482263360277373823034172941)
        ·
          refine ⟨180848760104015183637814853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 482263360277373823034172941 180848760104015183637814853)
          ·
            refine ⟨33909142519502846932090285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180848760104015183637814853 33909142519502846932090285)
            ·
              refine ⟨12715928444813567599533857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33909142519502846932090285 12715928444813567599533857)
              ·
                refine ⟨9536946333610175699650393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12715928444813567599533857 9536946333610175699650393)
                ·
                  refine ⟨7152709750207631774737795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9536946333610175699650393 7152709750207631774737795)
                  ·
                    refine ⟨10729064625311447662106693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7152709750207631774737795 10729064625311447662106693)
                    ·
                      refine ⟨2011699617245896436645005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10729064625311447662106693 2011699617245896436645005)
                      ·
                        rfl

theorem cell23_3917771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 4].length) (baseStart_3917771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917771 prefixEnd_3917771 := by exact prefixLift 3917771
  have htrace : WordTrace (prefixWord ++ tailWord_3917771) baseStart_3917771 baseEnd_3917771 := by
    simpa [prefixWord, tailWord_3917771, baseEnd_3917771] using wordTrace_append hprefix tailTrace_3917771
  have hstable : (prefixWord ++ tailWord_3917771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917771).length < 2 ^ (prefixWord ++ tailWord_3917771).sum := by decide
  have hdescent : baseEnd_3917771 < baseStart_3917771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917778 : List Nat := [3, 2, 2, 3, 2, 1, 1, 1, 1, 2, 5]
def baseStart_3917778 : Nat := 118140960795 + 3917778 * 2 ^ 59
def prefixEnd_3917778 : Nat := 4983230072969 + 3 ^ 40 * 3917778 * 2
def baseEnd_3917778 : Nat := 2011703211610477909257473

theorem tailTrace_3917778 : CollatzResearch.WordTrace tailWord_3917778 prefixEnd_3917778 2011703211610477909257473 := by
  unfold tailWord_3917778
  simp only [CollatzResearch.WordTrace]
  refine ⟨35723275700141721014370497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95262068533711256038321325 35723275700141721014370497)
  ·
    refine ⟨26792456775106290760777873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35723275700141721014370497 26792456775106290760777873)
    ·
      refine ⟨20094342581329718070583405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26792456775106290760777873 20094342581329718070583405)
      ·
        refine ⟨7535378467998644276468777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20094342581329718070583405 7535378467998644276468777)
        ·
          refine ⟨5651533850998983207351583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7535378467998644276468777 5651533850998983207351583)
          ·
            refine ⟨8477300776498474811027375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5651533850998983207351583 8477300776498474811027375)
            ·
              refine ⟨12715951164747712216541063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8477300776498474811027375 12715951164747712216541063)
              ·
                refine ⟨19073926747121568324811595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12715951164747712216541063 19073926747121568324811595)
                ·
                  refine ⟨28610890120682352487217393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19073926747121568324811595 28610890120682352487217393)
                  ·
                    refine ⟨21458167590511764365413045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28610890120682352487217393 21458167590511764365413045)
                    ·
                      refine ⟨2011703211610477909257473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21458167590511764365413045 2011703211610477909257473)
                      ·
                        rfl

theorem cell23_3917778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_3917778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917778 prefixEnd_3917778 := by exact prefixLift 3917778
  have htrace : WordTrace (prefixWord ++ tailWord_3917778) baseStart_3917778 baseEnd_3917778 := by
    simpa [prefixWord, tailWord_3917778, baseEnd_3917778] using wordTrace_append hprefix tailTrace_3917778
  have hstable : (prefixWord ++ tailWord_3917778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917778).length < 2 ^ (prefixWord ++ tailWord_3917778).sum := by decide
  have hdescent : baseEnd_3917778 < baseStart_3917778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917848 : List Nat := [2, 1, 2, 3, 2, 1, 2, 2, 1, 5, 2]
def baseStart_3917848 : Nat := 118140960795 + 3917848 * 2 ^ 59
def prefixEnd_3917848 : Nat := 4983230072969 + 3 ^ 40 * 3917848 * 2
def baseEnd_3917848 : Nat := 2011739155256292635382151

theorem tailTrace_3917848 : CollatzResearch.WordTrace tailWord_3917848 prefixEnd_3917848 2011739155256292635382151 := by
  unfold tailWord_3917848
  simp only [CollatzResearch.WordTrace]
  refine ⟨71447827955156643006265099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95263770606875524008353465 71447827955156643006265099)
  ·
    refine ⟨107171741932734964509397649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71447827955156643006265099 107171741932734964509397649)
    ·
      refine ⟨80378806449551223382048237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107171741932734964509397649 80378806449551223382048237)
      ·
        refine ⟨30142052418581708768268089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80378806449551223382048237 30142052418581708768268089)
        ·
          refine ⟨22606539313936281576201067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30142052418581708768268089 22606539313936281576201067)
          ·
            refine ⟨33909808970904422364301601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22606539313936281576201067 33909808970904422364301601)
            ·
              refine ⟨25432356728178316773226201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33909808970904422364301601 25432356728178316773226201)
              ·
                refine ⟨19074267546133737579919651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25432356728178316773226201 19074267546133737579919651)
                ·
                  refine ⟨28611401319200606369879477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19074267546133737579919651 28611401319200606369879477)
                  ·
                    refine ⟨2682318873675056847176201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28611401319200606369879477 2682318873675056847176201)
                    ·
                      refine ⟨2011739155256292635382151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2682318873675056847176201 2011739155256292635382151)
                      ·
                        rfl

theorem cell23_3917848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_3917848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917848 prefixEnd_3917848 := by exact prefixLift 3917848
  have htrace : WordTrace (prefixWord ++ tailWord_3917848) baseStart_3917848 baseEnd_3917848 := by
    simpa [prefixWord, tailWord_3917848, baseEnd_3917848] using wordTrace_append hprefix tailTrace_3917848
  have hstable : (prefixWord ++ tailWord_3917848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917848).length < 2 ^ (prefixWord ++ tailWord_3917848).sum := by decide
  have hdescent : baseEnd_3917848 < baseStart_3917848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917858 : List Nat := [3, 3, 1, 1, 1, 2, 2, 4, 1, 5]
def baseStart_3917858 : Nat := 118140960795 + 3917858 * 2 ^ 59
def prefixEnd_3917858 : Nat := 4983230072969 + 3 ^ 40 * 3917858 * 2
def baseEnd_3917858 : Nat := 670581430020945865419035

theorem tailTrace_3917858 : CollatzResearch.WordTrace tailWord_3917858 prefixEnd_3917858 670581430020945865419035 := by
  unfold tailWord_3917858
  simp only [CollatzResearch.WordTrace]
  refine ⟨35724005160069264430098557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95264013760184705146929485 35724005160069264430098557)
  ·
    refine ⟨13396501935025974161286959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35724005160069264430098557 13396501935025974161286959)
    ·
      refine ⟨20094752902538961241930439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13396501935025974161286959 20094752902538961241930439)
      ·
        refine ⟨30142129353808441862895659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20094752902538961241930439 30142129353808441862895659)
        ·
          refine ⟨45213194030712662794343489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30142129353808441862895659 45213194030712662794343489)
          ·
            refine ⟨33909895523034497095757617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45213194030712662794343489 33909895523034497095757617)
            ·
              refine ⟨25432421642275872821818213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33909895523034497095757617 25432421642275872821818213)
              ·
                refine ⟨4768579057926726154090915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25432421642275872821818213 4768579057926726154090915)
                ·
                  refine ⟨7152868586890089231136373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4768579057926726154090915 7152868586890089231136373)
                  ·
                    refine ⟨670581430020945865419035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7152868586890089231136373 670581430020945865419035)
                    ·
                      rfl

theorem cell23_3917858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_3917858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917858 prefixEnd_3917858 := by exact prefixLift 3917858
  have htrace : WordTrace (prefixWord ++ tailWord_3917858) baseStart_3917858 baseEnd_3917858 := by
    simpa [prefixWord, tailWord_3917858, baseEnd_3917858] using wordTrace_append hprefix tailTrace_3917858
  have hstable : (prefixWord ++ tailWord_3917858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917858).length < 2 ^ (prefixWord ++ tailWord_3917858).sum := by decide
  have hdescent : baseEnd_3917858 < baseStart_3917858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917872 : List Nat := [2, 1, 1, 1, 2, 6, 2, 3, 1, 1, 3]
def baseStart_3917872 : Nat := 118140960795 + 3917872 * 2 ^ 59
def prefixEnd_3917872 : Nat := 4983230072969 + 3 ^ 40 * 3917872 * 2
def baseEnd_3917872 : Nat := 2011751478792000541482041

theorem tailTrace_3917872 : CollatzResearch.WordTrace tailWord_3917872 prefixEnd_3917872 2011751478792000541482041 := by
  unfold tailWord_3917872
  simp only [CollatzResearch.WordTrace]
  refine ⟨71448265631113169055701935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95264354174817558740935913 71448265631113169055701935)
  ·
    refine ⟨107172398446669753583552903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71448265631113169055701935 107172398446669753583552903)
    ·
      refine ⟨160758597670004630375329355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107172398446669753583552903 160758597670004630375329355)
      ·
        refine ⟨241137896505006945562994033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160758597670004630375329355 241137896505006945562994033)
        ·
          refine ⟨180853422378755209172245525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241137896505006945562994033 180853422378755209172245525)
          ·
            refine ⟨8477504174004150429949009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 180853422378755209172245525 8477504174004150429949009)
            ·
              refine ⟨6358128130503112822461757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8477504174004150429949009 6358128130503112822461757)
              ·
                refine ⟨2384298048938667308423159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6358128130503112822461757 2384298048938667308423159)
                ·
                  refine ⟨3576447073408000962634739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2384298048938667308423159 3576447073408000962634739)
                  ·
                    refine ⟨5364670610112001443952109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3576447073408000962634739 5364670610112001443952109)
                    ·
                      refine ⟨2011751478792000541482041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5364670610112001443952109 2011751478792000541482041)
                      ·
                        rfl

theorem cell23_3917872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 3, 1, 1, 3].length) (baseStart_3917872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917872 prefixEnd_3917872 := by exact prefixLift 3917872
  have htrace : WordTrace (prefixWord ++ tailWord_3917872) baseStart_3917872 baseEnd_3917872 := by
    simpa [prefixWord, tailWord_3917872, baseEnd_3917872] using wordTrace_append hprefix tailTrace_3917872
  have hstable : (prefixWord ++ tailWord_3917872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917872).length < 2 ^ (prefixWord ++ tailWord_3917872).sum := by decide
  have hdescent : baseEnd_3917872 < baseStart_3917872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917888 : List Nat := [2, 1, 1, 2, 2, 5, 1, 1, 4, 4]
def baseStart_3917888 : Nat := 118140960795 + 3917888 * 2 ^ 59
def prefixEnd_3917888 : Nat := 4983230072969 + 3 ^ 40 * 3917888 * 2
def baseEnd_3917888 : Nat := 670586564827490826293989

theorem tailTrace_3917888 : CollatzResearch.WordTrace tailWord_3917888 prefixEnd_3917888 670586564827490826293989 := by
  unfold tailWord_3917888
  simp only [CollatzResearch.WordTrace]
  refine ⟨71448557415084186421993159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95264743220112248562657545 71448557415084186421993159)
  ·
    refine ⟨107172836122626279632989739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71448557415084186421993159 107172836122626279632989739)
    ·
      refine ⟨160759254183939419449484609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107172836122626279632989739 160759254183939419449484609)
      ·
        refine ⟨120569440637954564587113457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160759254183939419449484609 120569440637954564587113457)
        ·
          refine ⟨90427080478465923440335093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120569440637954564587113457 90427080478465923440335093)
          ·
            refine ⟨8477538794856180322531415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90427080478465923440335093 8477538794856180322531415)
            ·
              refine ⟨12716308192284270483797123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8477538794856180322531415 12716308192284270483797123)
              ·
                refine ⟨19074462288426405725695685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12716308192284270483797123 19074462288426405725695685)
                ·
                  refine ⟨3576461679079951073567941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19074462288426405725695685 3576461679079951073567941)
                  ·
                    refine ⟨670586564827490826293989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3576461679079951073567941 670586564827490826293989)
                    ·
                      rfl

theorem cell23_3917888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 4, 4].length) (baseStart_3917888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917888 prefixEnd_3917888 := by exact prefixLift 3917888
  have htrace : WordTrace (prefixWord ++ tailWord_3917888) baseStart_3917888 baseEnd_3917888 := by
    simpa [prefixWord, tailWord_3917888, baseEnd_3917888] using wordTrace_append hprefix tailTrace_3917888
  have hstable : (prefixWord ++ tailWord_3917888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917888).length < 2 ^ (prefixWord ++ tailWord_3917888).sum := by decide
  have hdescent : baseEnd_3917888 < baseStart_3917888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917945 : List Nat := [1, 2, 1, 3, 4, 1, 2, 1, 4, 1, 3]
def baseStart_3917945 : Nat := 118140960795 + 3917945 * 2 ^ 59
def prefixEnd_3917945 : Nat := 4983230072969 + 3 ^ 40 * 3917945 * 2
def baseEnd_3917945 : Nat := 2011788962879778755869205

theorem tailTrace_3917945 : CollatzResearch.WordTrace tailWord_3917945 prefixEnd_3917945 2011788962879778755869205 := by
  unfold tailWord_3917945
  simp only [CollatzResearch.WordTrace]
  refine ⟨142899193790961871578811289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95266129193974581052540859 142899193790961871578811289)
  ·
    refine ⟨107174395343221403684108467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142899193790961871578811289 107174395343221403684108467)
    ·
      refine ⟨160761593014832105526162701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107174395343221403684108467 160761593014832105526162701)
      ·
        refine ⟨60285597380562039572311013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160761593014832105526162701 60285597380562039572311013)
        ·
          refine ⟨11303549508855382419808315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60285597380562039572311013 11303549508855382419808315)
          ·
            refine ⟨16955324263283073629712473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11303549508855382419808315 16955324263283073629712473)
            ·
              refine ⟨12716493197462305222284355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16955324263283073629712473 12716493197462305222284355)
              ·
                refine ⟨19074739796193457833426533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12716493197462305222284355 19074739796193457833426533)
                ·
                  refine ⟨3576513711786273343767475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19074739796193457833426533 3576513711786273343767475)
                  ·
                    refine ⟨5364770567679410015651213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3576513711786273343767475 5364770567679410015651213)
                    ·
                      refine ⟨2011788962879778755869205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5364770567679410015651213 2011788962879778755869205)
                      ·
                        rfl

theorem cell23_3917945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 4, 1, 3].length) (baseStart_3917945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917945 prefixEnd_3917945 := by exact prefixLift 3917945
  have htrace : WordTrace (prefixWord ++ tailWord_3917945) baseStart_3917945 baseEnd_3917945 := by
    simpa [prefixWord, tailWord_3917945, baseEnd_3917945] using wordTrace_append hprefix tailTrace_3917945
  have hstable : (prefixWord ++ tailWord_3917945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917945).length < 2 ^ (prefixWord ++ tailWord_3917945).sum := by decide
  have hdescent : baseEnd_3917945 < baseStart_3917945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917961 : List Nat := [1, 2, 1, 1, 4, 2, 2, 1, 1, 8]
def baseStart_3917961 : Nat := 118140960795 + 3917961 * 2 ^ 59
def prefixEnd_3917961 : Nat := 4983230072969 + 3 ^ 40 * 3917961 * 2
def baseEnd_3917961 : Nat := 670599059523416897756377

theorem tailTrace_3917961 : CollatzResearch.WordTrace tailWord_3917961 prefixEnd_3917961 670599059523416897756377 := by
  unfold tailWord_3917961
  simp only [CollatzResearch.WordTrace]
  refine ⟨142899777358903906311393737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95266518239269270874262491 142899777358903906311393737)
  ·
    refine ⟨107174833019177929733545303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142899777358903906311393737 107174833019177929733545303)
    ·
      refine ⟨160762249528766894600317955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107174833019177929733545303 160762249528766894600317955)
      ·
        refine ⟨241143374293150341900476933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160762249528766894600317955 241143374293150341900476933)
        ·
          refine ⟨45214382679965689106339425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 241143374293150341900476933 45214382679965689106339425)
          ·
            refine ⟨33910787009974266829754569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45214382679965689106339425 33910787009974266829754569)
            ·
              refine ⟨25433090257480700122315927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33910787009974266829754569 25433090257480700122315927)
              ·
                refine ⟨38149635386221050183473891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25433090257480700122315927 38149635386221050183473891)
                ·
                  refine ⟨57224453079331575275210837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38149635386221050183473891 57224453079331575275210837)
                  ·
                    refine ⟨670599059523416897756377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57224453079331575275210837 670599059523416897756377)
                    ·
                      rfl

theorem cell23_3917961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 8].length) (baseStart_3917961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917961 prefixEnd_3917961 := by exact prefixLift 3917961
  have htrace : WordTrace (prefixWord ++ tailWord_3917961) baseStart_3917961 baseEnd_3917961 := by
    simpa [prefixWord, tailWord_3917961, baseEnd_3917961] using wordTrace_append hprefix tailTrace_3917961
  have hstable : (prefixWord ++ tailWord_3917961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917961).length < 2 ^ (prefixWord ++ tailWord_3917961).sum := by decide
  have hdescent : baseEnd_3917961 < baseStart_3917961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917962 : List Nat := [3, 1, 2, 3, 1, 3, 1, 3, 2, 1, 3]
def baseStart_3917962 : Nat := 118140960795 + 3917962 * 2 ^ 59
def prefixEnd_3917962 : Nat := 4983230072969 + 3 ^ 40 * 3917962 * 2
def baseEnd_3917962 : Nat := 2011797692050905189356627

theorem tailTrace_3917962 : CollatzResearch.WordTrace tailWord_3917962 prefixEnd_3917962 2011797692050905189356627 := by
  unfold tailWord_3917962
  simp only [CollatzResearch.WordTrace]
  refine ⟨35724953457975070870545035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95266542554600188988120093 35724953457975070870545035)
  ·
    refine ⟨53587430186962606305817553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35724953457975070870545035 53587430186962606305817553)
    ·
      refine ⟨40190572640221954729363165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53587430186962606305817553 40190572640221954729363165)
      ·
        refine ⟨15071464740083233023511187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40190572640221954729363165 15071464740083233023511187)
        ·
          refine ⟨22607197110124849535266781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15071464740083233023511187 22607197110124849535266781)
          ·
            refine ⟨8477698916296818575725043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22607197110124849535266781 8477698916296818575725043)
            ·
              refine ⟨12716548374445227863587565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8477698916296818575725043 12716548374445227863587565)
              ·
                refine ⟨4768705640416960448845337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12716548374445227863587565 4768705640416960448845337)
                ·
                  refine ⟨3576529230312720336634003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4768705640416960448845337 3576529230312720336634003)
                  ·
                    refine ⟨5364793845469080504951005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3576529230312720336634003 5364793845469080504951005)
                    ·
                      refine ⟨2011797692050905189356627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5364793845469080504951005 2011797692050905189356627)
                      ·
                        rfl

theorem cell23_3917962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_3917962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917962 prefixEnd_3917962 := by exact prefixLift 3917962
  have htrace : WordTrace (prefixWord ++ tailWord_3917962) baseStart_3917962 baseEnd_3917962 := by
    simpa [prefixWord, tailWord_3917962, baseEnd_3917962] using wordTrace_append hprefix tailTrace_3917962
  have hstable : (prefixWord ++ tailWord_3917962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917962).length < 2 ^ (prefixWord ++ tailWord_3917962).sum := by decide
  have hdescent : baseEnd_3917962 < baseStart_3917962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917985 : List Nat := [1, 2, 3, 3, 1, 2, 1, 1, 3, 4, 2]
def baseStart_3917985 : Nat := 118140960795 + 3917985 * 2 ^ 59
def prefixEnd_3917985 : Nat := 4983230072969 + 3 ^ 40 * 3917985 * 2
def baseEnd_3917985 : Nat := 2011809502105958599369021

theorem tailTrace_3917985 : CollatzResearch.WordTrace tailWord_3917985 prefixEnd_3917985 2011809502105958599369021 := by
  unfold tailWord_3917985
  simp only [CollatzResearch.WordTrace]
  refine ⟨142900652710816958410267409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95267101807211305606844939 142900652710816958410267409)
  ·
    refine ⟨107175489533112718807700557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142900652710816958410267409 107175489533112718807700557)
    ·
      refine ⟨40190808574917269552887709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107175489533112718807700557 40190808574917269552887709)
      ·
        refine ⟨15071553215593976082332891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40190808574917269552887709 15071553215593976082332891)
        ·
          refine ⟨22607329823390964123499337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15071553215593976082332891 22607329823390964123499337)
          ·
            refine ⟨16955497367543223092624503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22607329823390964123499337 16955497367543223092624503)
            ·
              refine ⟨25433246051314834638936755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16955497367543223092624503 25433246051314834638936755)
              ·
                refine ⟨38149869076972251958405133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25433246051314834638936755 38149869076972251958405133)
                ·
                  refine ⟨14306200903864594484401925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38149869076972251958405133 14306200903864594484401925)
                  ·
                    refine ⟨2682412669474611465825361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14306200903864594484401925 2682412669474611465825361)
                    ·
                      refine ⟨2011809502105958599369021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2682412669474611465825361 2011809502105958599369021)
                      ·
                        rfl

theorem cell23_3917985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_3917985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3917985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3917985 prefixEnd_3917985 := by exact prefixLift 3917985
  have htrace : WordTrace (prefixWord ++ tailWord_3917985) baseStart_3917985 baseEnd_3917985 := by
    simpa [prefixWord, tailWord_3917985, baseEnd_3917985] using wordTrace_append hprefix tailTrace_3917985
  have hstable : (prefixWord ++ tailWord_3917985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917985).length < 2 ^ (prefixWord ++ tailWord_3917985).sum := by decide
  have hdescent : baseEnd_3917985 < baseStart_3917985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918112 : List Nat := [2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 3]
def baseStart_3918112 : Nat := 118140960795 + 3918112 * 2 ^ 59
def prefixEnd_3918112 : Nat := 4983230072969 + 3 ^ 40 * 3918112 * 2
def baseEnd_3918112 : Nat := 2011874714149079602480937

theorem tailTrace_3918112 : CollatzResearch.WordTrace tailWord_3918112 prefixEnd_3918112 2011874714149079602480937 := by
  unfold tailWord_3918112
  simp only [CollatzResearch.WordTrace]
  refine ⟨71452642390678429550070295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95270189854237906066760393 71452642390678429550070295)
  ·
    refine ⟨107178963586017644325105443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71452642390678429550070295 107178963586017644325105443)
    ·
      refine ⟨160768445379026466487658165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107178963586017644325105443 160768445379026466487658165)
      ·
        refine ⟨15072041754283731233217953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160768445379026466487658165 15072041754283731233217953)
        ·
          refine ⟨11304031315712798424913465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15072041754283731233217953 11304031315712798424913465)
          ·
            refine ⟨8478023486784598818685099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11304031315712798424913465 8478023486784598818685099)
            ·
              refine ⟨12717035230176898228027649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8478023486784598818685099 12717035230176898228027649)
              ·
                refine ⟨9537776422632673671020737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12717035230176898228027649 9537776422632673671020737)
                ·
                  refine ⟨7153332316974505253265553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9537776422632673671020737 7153332316974505253265553)
                  ·
                    refine ⟨5364999237730878939949165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7153332316974505253265553 5364999237730878939949165)
                    ·
                      refine ⟨2011874714149079602480937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5364999237730878939949165 2011874714149079602480937)
                      ·
                        rfl

theorem cell23_3918112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_3918112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3918112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3918112 prefixEnd_3918112 := by exact prefixLift 3918112
  have htrace : WordTrace (prefixWord ++ tailWord_3918112) baseStart_3918112 baseEnd_3918112 := by
    simpa [prefixWord, tailWord_3918112, baseEnd_3918112] using wordTrace_append hprefix tailTrace_3918112
  have hstable : (prefixWord ++ tailWord_3918112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918112).length < 2 ^ (prefixWord ++ tailWord_3918112).sum := by decide
  have hdescent : baseEnd_3918112 < baseStart_3918112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918132 : List Nat := [2, 5, 1, 1, 1, 3, 1, 3, 6]
def baseStart_3918132 : Nat := 118140960795 + 3918132 * 2 ^ 59
def prefixEnd_3918132 : Nat := 4983230072969 + 3 ^ 40 * 3918132 * 2
def baseEnd_3918132 : Nat := 223542775973574391581205

theorem tailTrace_3918132 : CollatzResearch.WordTrace tailWord_3918132 prefixEnd_3918132 223542775973574391581205 := by
  unfold tailWord_3918132
  simp only [CollatzResearch.WordTrace]
  refine ⟨71453007120642201257934325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95270676160856268343912433 71453007120642201257934325)
  ·
    refine ⟨6698719417560206367931343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71453007120642201257934325 6698719417560206367931343)
    ·
      refine ⟨10048079126340309551897015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6698719417560206367931343 10048079126340309551897015)
      ·
        refine ⟨15072118689510464327845523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10048079126340309551897015 15072118689510464327845523)
        ·
          refine ⟨22608178034265696491768285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15072118689510464327845523 22608178034265696491768285)
          ·
            refine ⟨8478066762849636184413107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22608178034265696491768285 8478066762849636184413107)
            ·
              refine ⟨12717100144274454276619661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8478066762849636184413107 12717100144274454276619661)
              ·
                refine ⟨4768912554102920353732373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12717100144274454276619661 4768912554102920353732373)
                ·
                  refine ⟨223542775973574391581205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4768912554102920353732373 223542775973574391581205)
                  ·
                    rfl

theorem cell23_3918132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_3918132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3918132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3918132 prefixEnd_3918132 := by exact prefixLift 3918132
  have htrace : WordTrace (prefixWord ++ tailWord_3918132) baseStart_3918132 baseEnd_3918132 := by
    simpa [prefixWord, tailWord_3918132, baseEnd_3918132] using wordTrace_append hprefix tailTrace_3918132
  have hstable : (prefixWord ++ tailWord_3918132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918132).length < 2 ^ (prefixWord ++ tailWord_3918132).sum := by decide
  have hdescent : baseEnd_3918132 < baseStart_3918132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918135 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 3, 5, 2]
def baseStart_3918135 : Nat := 118140960795 + 3918135 * 2 ^ 59
def prefixEnd_3918135 : Nat := 4983230072969 + 3 ^ 40 * 3918135 * 2
def baseEnd_3918135 : Nat := 2011886524204133012493331

theorem tailTrace_3918135 : CollatzResearch.WordTrace tailWord_3918135 prefixEnd_3918135 2011886524204133012493331 := by
  unfold tailWord_3918135
  simp only [CollatzResearch.WordTrace]
  refine ⟨142906123660273534028227859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95270749106849022685485239 142906123660273534028227859)
  ·
    refine ⟨214359185490410301042341789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142906123660273534028227859 214359185490410301042341789)
    ·
      refine ⟨80384694558903862890878171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214359185490410301042341789 80384694558903862890878171)
      ·
        refine ⟨120577041838355794336317257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80384694558903862890878171 120577041838355794336317257)
        ·
          refine ⟨90432781378766845752237943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120577041838355794336317257 90432781378766845752237943)
          ·
            refine ⟨135649172068150268628356915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90432781378766845752237943 135649172068150268628356915)
            ·
              refine ⟨203473758102225402942535373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135649172068150268628356915 203473758102225402942535373)
              ·
                refine ⟨76302659288334526103450765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203473758102225402942535373 76302659288334526103450765)
                ·
                  refine ⟨28613497233125447288794037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76302659288334526103450765 28613497233125447288794037)
                  ·
                    refine ⟨2682515365605510683324441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28613497233125447288794037 2682515365605510683324441)
                    ·
                      refine ⟨2011886524204133012493331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2682515365605510683324441 2011886524204133012493331)
                      ·
                        rfl

theorem cell23_3918135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 5, 2].length) (baseStart_3918135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3918135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3918135 prefixEnd_3918135 := by exact prefixLift 3918135
  have htrace : WordTrace (prefixWord ++ tailWord_3918135) baseStart_3918135 baseEnd_3918135 := by
    simpa [prefixWord, tailWord_3918135, baseEnd_3918135] using wordTrace_append hprefix tailTrace_3918135
  have hstable : (prefixWord ++ tailWord_3918135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918135).length < 2 ^ (prefixWord ++ tailWord_3918135).sum := by decide
  have hdescent : baseEnd_3918135 < baseStart_3918135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918152 : List Nat := [2, 1, 3, 1, 1, 2, 3, 3, 2, 3, 2]
def baseStart_3918152 : Nat := 118140960795 + 3918152 * 2 ^ 59
def prefixEnd_3918152 : Nat := 4983230072969 + 3 ^ 40 * 3918152 * 2
def baseEnd_3918152 : Nat := 2011895253375259445980753

theorem tailTrace_3918152 : CollatzResearch.WordTrace tailWord_3918152 prefixEnd_3918152 2011895253375259445980753 := by
  unfold tailWord_3918152
  simp only [CollatzResearch.WordTrace]
  refine ⟨71453371850605972965798355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95271162467474630621064473 71453371850605972965798355)
  ·
    refine ⟨107180057775908959448697533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71453371850605972965798355 107180057775908959448697533)
    ·
      refine ⟨40192521665965859793261575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107180057775908959448697533 40192521665965859793261575)
      ·
        refine ⟨60288782498948789689892363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40192521665965859793261575 60288782498948789689892363)
        ·
          refine ⟨90433173748423184534838545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60288782498948789689892363 90433173748423184534838545)
          ·
            refine ⟨67824880311317388401128909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90433173748423184534838545 67824880311317388401128909)
            ·
              refine ⟨25434330116744020650423341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67824880311317388401128909 25434330116744020650423341)
              ·
                refine ⟨9537873793779007743908753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25434330116744020650423341 9537873793779007743908753)
                ·
                  refine ⟨7153405345334255807931565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9537873793779007743908753 7153405345334255807931565)
                  ·
                    refine ⟨2682527004500345927974337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7153405345334255807931565 2682527004500345927974337)
                    ·
                      refine ⟨2011895253375259445980753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2682527004500345927974337 2011895253375259445980753)
                      ·
                        rfl

theorem cell23_3918152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 2, 3, 2].length) (baseStart_3918152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3918152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3918152 prefixEnd_3918152 := by exact prefixLift 3918152
  have htrace : WordTrace (prefixWord ++ tailWord_3918152) baseStart_3918152 baseEnd_3918152 := by
    simpa [prefixWord, tailWord_3918152, baseEnd_3918152] using wordTrace_append hprefix tailTrace_3918152
  have hstable : (prefixWord ++ tailWord_3918152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918152).length < 2 ^ (prefixWord ++ tailWord_3918152).sum := by decide
  have hdescent : baseEnd_3918152 < baseStart_3918152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918175 : List Nat := [1, 1, 2, 3, 1, 2, 2, 3, 4, 4]
def baseStart_3918175 : Nat := 118140960795 + 3918175 * 2 ^ 59
def prefixEnd_3918175 : Nat := 4983230072969 + 3 ^ 40 * 3918175 * 2
def baseEnd_3918175 : Nat := 670635687810104285331049

theorem tailTrace_3918175 : CollatzResearch.WordTrace tailWord_3918175 prefixEnd_3918175 670635687810104285331049 := by
  unfold tailWord_3918175
  simp only [CollatzResearch.WordTrace]
  refine ⟨142907582580128620859683979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95271721720085747239789319 142907582580128620859683979)
  ·
    refine ⟨214361373870192931289525969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142907582580128620859683979 214361373870192931289525969)
    ·
      refine ⟨160771030402644698467144477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214361373870192931289525969 160771030402644698467144477)
      ·
        refine ⟨60289136400991761925179179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160771030402644698467144477 60289136400991761925179179)
        ·
          refine ⟨90433704601487642887768769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60289136400991761925179179 90433704601487642887768769)
          ·
            refine ⟨67825278451115732165826577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90433704601487642887768769 67825278451115732165826577)
            ·
              refine ⟨50868958838336799124369933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67825278451115732165826577 50868958838336799124369933)
              ·
                refine ⟨19075859564376299671638725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50868958838336799124369933 19075859564376299671638725)
                ·
                  refine ⟨3576723668320556188432261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19075859564376299671638725 3576723668320556188432261)
                  ·
                    refine ⟨670635687810104285331049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3576723668320556188432261 670635687810104285331049)
                    ·
                      rfl

theorem cell23_3918175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 4, 4].length) (baseStart_3918175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3918175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3918175 prefixEnd_3918175 := by exact prefixLift 3918175
  have htrace : WordTrace (prefixWord ++ tailWord_3918175) baseStart_3918175 baseEnd_3918175 := by
    simpa [prefixWord, tailWord_3918175, baseEnd_3918175] using wordTrace_append hprefix tailTrace_3918175
  have hstable : (prefixWord ++ tailWord_3918175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918175).length < 2 ^ (prefixWord ++ tailWord_3918175).sum := by decide
  have hdescent : baseEnd_3918175 < baseStart_3918175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918176 : List Nat := [2, 1, 1, 3, 5, 1, 1, 4, 1, 1, 3]
def baseStart_3918176 : Nat := 118140960795 + 3918176 * 2 ^ 59
def prefixEnd_3918176 : Nat := 4983230072969 + 3 ^ 40 * 3918176 * 2
def baseEnd_3918176 : Nat := 2011907576910967352080643

theorem tailTrace_3918176 : CollatzResearch.WordTrace tailWord_3918176 prefixEnd_3918176 2011907576910967352080643 := by
  unfold tailWord_3918176
  simp only [CollatzResearch.WordTrace]
  refine ⟨71453809526562499015235191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95271746035416665353646921 71453809526562499015235191)
  ·
    refine ⟨107180714289843748522852787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71453809526562499015235191 107180714289843748522852787)
    ·
      refine ⟨160771071434765622784279181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107180714289843748522852787 160771071434765622784279181)
      ·
        refine ⟨60289151788037108544104693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160771071434765622784279181 60289151788037108544104693)
        ·
          refine ⟨5652107980128478926009815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60289151788037108544104693 5652107980128478926009815)
          ·
            refine ⟨8478161970192718389014723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5652107980128478926009815 8478161970192718389014723)
            ·
              refine ⟨12717242955289077583522085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8478161970192718389014723 12717242955289077583522085)
              ·
                refine ⟨2384483054116702046910391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12717242955289077583522085 2384483054116702046910391)
                ·
                  refine ⟨3576724581175053070365587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2384483054116702046910391 3576724581175053070365587)
                  ·
                    refine ⟨5365086871762579605548381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3576724581175053070365587 5365086871762579605548381)
                    ·
                      refine ⟨2011907576910967352080643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5365086871762579605548381 2011907576910967352080643)
                      ·
                        rfl

theorem cell23_3918176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 4, 1, 1, 3].length) (baseStart_3918176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3918176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3918176 prefixEnd_3918176 := by exact prefixLift 3918176
  have htrace : WordTrace (prefixWord ++ tailWord_3918176) baseStart_3918176 baseEnd_3918176 := by
    simpa [prefixWord, tailWord_3918176, baseEnd_3918176] using wordTrace_append hprefix tailTrace_3918176
  have hstable : (prefixWord ++ tailWord_3918176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918176).length < 2 ^ (prefixWord ++ tailWord_3918176).sum := by decide
  have hdescent : baseEnd_3918176 < baseStart_3918176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918185 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 5, 2, 3]
def baseStart_3918185 : Nat := 118140960795 + 3918185 * 2 ^ 59
def prefixEnd_3918185 : Nat := 4983230072969 + 3 ^ 40 * 3918185 * 2
def baseEnd_3918185 : Nat := 2011912198236857816868101

theorem tailTrace_3918185 : CollatzResearch.WordTrace tailWord_3918185 prefixEnd_3918185 2011912198236857816868101 := by
  unfold tailWord_3918185
  simp only [CollatzResearch.WordTrace]
  refine ⟨142907947310092392567548009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95271964873394928378365339 142907947310092392567548009)
  ·
    refine ⟨107180960482569294425661007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142907947310092392567548009 107180960482569294425661007)
    ·
      refine ⟨160771440723853941638491511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107180960482569294425661007 160771440723853941638491511)
      ·
        refine ⟨241157161085780912457737267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160771440723853941638491511 241157161085780912457737267)
        ·
          refine ⟨361735741628671368686605901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241157161085780912457737267 361735741628671368686605901)
          ·
            refine ⟨135650903110751763257477213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 361735741628671368686605901 135650903110751763257477213)
            ·
              refine ⟨50869088666531911221553955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135650903110751763257477213 50869088666531911221553955)
              ·
                refine ⟨76303632999797866832330933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50869088666531911221553955 76303632999797866832330933)
                ·
                  refine ⟨7153465593731050015531025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76303632999797866832330933 7153465593731050015531025)
                  ·
                    refine ⟨5365099195298287511648269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7153465593731050015531025 5365099195298287511648269)
                    ·
                      refine ⟨2011912198236857816868101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5365099195298287511648269 2011912198236857816868101)
                      ·
                        rfl

theorem cell23_3918185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 2, 3].length) (baseStart_3918185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3918185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3918185 prefixEnd_3918185 := by exact prefixLift 3918185
  have htrace : WordTrace (prefixWord ++ tailWord_3918185) baseStart_3918185 baseEnd_3918185 := by
    simpa [prefixWord, tailWord_3918185, baseEnd_3918185] using wordTrace_append hprefix tailTrace_3918185
  have hstable : (prefixWord ++ tailWord_3918185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918185).length < 2 ^ (prefixWord ++ tailWord_3918185).sum := by decide
  have hdescent : baseEnd_3918185 < baseStart_3918185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918192 : List Nat := [2, 1, 1, 1, 4, 3, 2, 3, 2, 4]
def baseStart_3918192 : Nat := 118140960795 + 3918192 * 2 ^ 59
def prefixEnd_3918192 : Nat := 4983230072969 + 3 ^ 40 * 3918192 * 2
def baseEnd_3918192 : Nat := 670638597533813096493523

theorem tailTrace_3918192 : CollatzResearch.WordTrace tailWord_3918192 prefixEnd_3918192 670638597533813096493523 := by
  unfold tailWord_3918192
  simp only [CollatzResearch.WordTrace]
  refine ⟨71454101310533516381526415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95272135080711355175368553 71454101310533516381526415)
  ·
    refine ⟨107181151965800274572289623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71454101310533516381526415 107181151965800274572289623)
    ·
      refine ⟨160771727948700411858434435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107181151965800274572289623 160771727948700411858434435)
      ·
        refine ⟨241157591923050617787651653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160771727948700411858434435 241157591923050617787651653)
        ·
          refine ⟨45217048485571990835184685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 241157591923050617787651653 45217048485571990835184685)
          ·
            refine ⟨16956393182089496563194257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45217048485571990835184685 16956393182089496563194257)
            ·
              refine ⟨12717294886567122422395693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16956393182089496563194257 12717294886567122422395693)
              ·
                refine ⟨4768985582462670908398385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12717294886567122422395693 4768985582462670908398385)
                ·
                  refine ⟨3576739186847003181298789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4768985582462670908398385 3576739186847003181298789)
                  ·
                    refine ⟨670638597533813096493523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3576739186847003181298789 670638597533813096493523)
                    ·
                      rfl

theorem cell23_3918192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 2, 4].length) (baseStart_3918192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3918192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3918192 prefixEnd_3918192 := by exact prefixLift 3918192
  have htrace : WordTrace (prefixWord ++ tailWord_3918192) baseStart_3918192 baseEnd_3918192 := by
    simpa [prefixWord, tailWord_3918192, baseEnd_3918192] using wordTrace_append hprefix tailTrace_3918192
  have hstable : (prefixWord ++ tailWord_3918192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918192).length < 2 ^ (prefixWord ++ tailWord_3918192).sum := by decide
  have hdescent : baseEnd_3918192 < baseStart_3918192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918210 : List Nat := [3, 4, 2, 1, 2, 1, 2, 3, 1, 1, 3]
def baseStart_3918210 : Nat := 118140960795 + 3918210 * 2 ^ 59
def prefixEnd_3918210 : Nat := 4983230072969 + 3 ^ 40 * 3918210 * 2
def baseEnd_3918210 : Nat := 2011925035253220219055487

theorem tailTrace_3918210 : CollatzResearch.WordTrace tailWord_3918210 prefixEnd_3918210 2011925035253220219055487 := by
  unfold tailWord_3918210
  simp only [CollatzResearch.WordTrace]
  refine ⟨35727214783750455459302021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95272572756667881224805389 35727214783750455459302021)
  ·
    refine ⟨6698852771953210398619129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35727214783750455459302021 6698852771953210398619129)
    ·
      refine ⟨5024139578964907798964347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6698852771953210398619129 5024139578964907798964347)
      ·
        refine ⟨7536209368447361698446521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5024139578964907798964347 7536209368447361698446521)
        ·
          refine ⟨5652157026335521273834891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7536209368447361698446521 5652157026335521273834891)
          ·
            refine ⟨8478235539503281910752337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5652157026335521273834891 8478235539503281910752337)
            ·
              refine ⟨6358676654627461433064253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8478235539503281910752337 6358676654627461433064253)
              ·
                refine ⟨2384503745485298037399095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6358676654627461433064253 2384503745485298037399095)
                ·
                  refine ⟨3576755618227947056098643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2384503745485298037399095 3576755618227947056098643)
                  ·
                    refine ⟨5365133427341920584147965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3576755618227947056098643 5365133427341920584147965)
                    ·
                      refine ⟨2011925035253220219055487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5365133427341920584147965 2011925035253220219055487)
                      ·
                        rfl

theorem cell23_3918210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_3918210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3918210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3918210 prefixEnd_3918210 := by exact prefixLift 3918210
  have htrace : WordTrace (prefixWord ++ tailWord_3918210) baseStart_3918210 baseEnd_3918210 := by
    simpa [prefixWord, tailWord_3918210, baseEnd_3918210] using wordTrace_append hprefix tailTrace_3918210
  have hstable : (prefixWord ++ tailWord_3918210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918210).length < 2 ^ (prefixWord ++ tailWord_3918210).sum := by decide
  have hdescent : baseEnd_3918210 < baseStart_3918210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918219 : List Nat := [1, 1, 1, 1, 4, 4, 4, 1, 1, 2, 3]
def baseStart_3918219 : Nat := 118140960795 + 3918219 * 2 ^ 59
def prefixEnd_3918219 : Nat := 4983230072969 + 3 ^ 40 * 3918219 * 2
def baseEnd_3918219 : Nat := 2011929656579110683842945

theorem tailTrace_3918219 : CollatzResearch.WordTrace tailWord_3918219 prefixEnd_3918219 2011929656579110683842945 := by
  unfold tailWord_3918219
  simp only [CollatzResearch.WordTrace]
  refine ⟨142909187391969216374285711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95272791594646144249523807 142909187391969216374285711)
  ·
    refine ⟨214363781087953824561428567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142909187391969216374285711 214363781087953824561428567)
    ·
      refine ⟨321545671631930736842142851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214363781087953824561428567 321545671631930736842142851)
      ·
        refine ⟨482318507447896105263214277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321545671631930736842142851 482318507447896105263214277)
        ·
          refine ⟨90434720146480519736852677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 482318507447896105263214277 90434720146480519736852677)
          ·
            refine ⟨16956510027465097450659877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90434720146480519736852677 16956510027465097450659877)
            ·
              refine ⟨3179345630149705771998727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16956510027465097450659877 3179345630149705771998727)
              ·
                refine ⟨4769018445224558657998091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3179345630149705771998727 4769018445224558657998091)
                ·
                  refine ⟨7153527667836837986997137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4769018445224558657998091 7153527667836837986997137)
                  ·
                    refine ⟨5365145750877628490247853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7153527667836837986997137 5365145750877628490247853)
                    ·
                      refine ⟨2011929656579110683842945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5365145750877628490247853 2011929656579110683842945)
                      ·
                        rfl

theorem cell23_3918219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 1, 2, 3].length) (baseStart_3918219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3918219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3918219 prefixEnd_3918219 := by exact prefixLift 3918219
  have htrace : WordTrace (prefixWord ++ tailWord_3918219) baseStart_3918219 baseEnd_3918219 := by
    simpa [prefixWord, tailWord_3918219, baseEnd_3918219] using wordTrace_append hprefix tailTrace_3918219
  have hstable : (prefixWord ++ tailWord_3918219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918219).length < 2 ^ (prefixWord ++ tailWord_3918219).sum := by decide
  have hdescent : baseEnd_3918219 < baseStart_3918219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918272 : List Nat := [2, 1, 1, 2, 3, 1, 1, 3, 3, 4, 2]
def baseStart_3918272 : Nat := 118140960795 + 3918272 * 2 ^ 59
def prefixEnd_3918272 : Nat := 4983230072969 + 3 ^ 40 * 3918272 * 2
def baseEnd_3918272 : Nat := 2011956871053798976480201

theorem tailTrace_3918272 : CollatzResearch.WordTrace tailWord_3918272 prefixEnd_3918272 2011956871053798976480201 := by
  unfold tailWord_3918272
  simp only [CollatzResearch.WordTrace]
  refine ⟨71455560230388603212982535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95274080307184804283976713 71455560230388603212982535)
  ·
    refine ⟨107183340345582904819473803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71455560230388603212982535 107183340345582904819473803)
    ·
      refine ⟨160775010518374357229210705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107183340345582904819473803 160775010518374357229210705)
      ·
        refine ⟨120581257888780767921908029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160775010518374357229210705 120581257888780767921908029)
        ·
          refine ⟨45217971708292787970715511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120581257888780767921908029 45217971708292787970715511)
          ·
            refine ⟨67826957562439181956073267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45217971708292787970715511 67826957562439181956073267)
            ·
              refine ⟨101740436343658772934109901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67826957562439181956073267 101740436343658772934109901)
              ·
                refine ⟨38152663628872039850291213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101740436343658772934109901 38152663628872039850291213)
                ·
                  refine ⟨14307248860827014943859205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38152663628872039850291213 14307248860827014943859205)
                  ·
                    refine ⟨2682609161405065301973601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14307248860827014943859205 2682609161405065301973601)
                    ·
                      refine ⟨2011956871053798976480201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2682609161405065301973601 2011956871053798976480201)
                      ·
                        rfl

theorem cell23_3918272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 3, 4, 2].length) (baseStart_3918272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3918272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3918272 prefixEnd_3918272 := by exact prefixLift 3918272
  have htrace : WordTrace (prefixWord ++ tailWord_3918272) baseStart_3918272 baseEnd_3918272 := by
    simpa [prefixWord, tailWord_3918272, baseEnd_3918272] using wordTrace_append hprefix tailTrace_3918272
  have hstable : (prefixWord ++ tailWord_3918272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918272).length < 2 ^ (prefixWord ++ tailWord_3918272).sum := by decide
  have hdescent : baseEnd_3918272 < baseStart_3918272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918275 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 1, 6, 3]
def baseStart_3918275 : Nat := 118140960795 + 3918275 * 2 ^ 59
def prefixEnd_3918275 : Nat := 4983230072969 + 3 ^ 40 * 3918275 * 2
def baseEnd_3918275 : Nat := 2011958411495762464742687

theorem tailTrace_3918275 : CollatzResearch.WordTrace tailWord_3918275 prefixEnd_3918275 2011958411495762464742687 := by
  unfold tailWord_3918275
  simp only [CollatzResearch.WordTrace]
  refine ⟨142911229879766337938324279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95274153253177558625549519 142911229879766337938324279)
  ·
    refine ⟨214366844819649506907486419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142911229879766337938324279 214366844819649506907486419)
    ·
      refine ⟨321550267229474260361229629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214366844819649506907486419 321550267229474260361229629)
      ·
        refine ⟨120581350211052847635461111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321550267229474260361229629 120581350211052847635461111)
        ·
          refine ⟨180872025316579271453191667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120581350211052847635461111 180872025316579271453191667)
          ·
            refine ⟨271308037974868907179787501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180872025316579271453191667 271308037974868907179787501)
            ·
              refine ⟨101740514240575840192420313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 271308037974868907179787501 101740514240575840192420313)
              ·
                refine ⟨76305385680431880144315235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101740514240575840192420313 76305385680431880144315235)
                ·
                  refine ⟨114458078520647820216472853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76305385680431880144315235 114458078520647820216472853)
                  ·
                    refine ⟨5365222430655366572647165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 114458078520647820216472853 5365222430655366572647165)
                    ·
                      refine ⟨2011958411495762464742687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5365222430655366572647165 2011958411495762464742687)
                      ·
                        rfl

theorem cell23_3918275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 6, 3].length) (baseStart_3918275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3918275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3918275 prefixEnd_3918275 := by exact prefixLift 3918275
  have htrace : WordTrace (prefixWord ++ tailWord_3918275) baseStart_3918275 baseEnd_3918275 := by
    simpa [prefixWord, tailWord_3918275, baseEnd_3918275] using wordTrace_append hprefix tailTrace_3918275
  have hstable : (prefixWord ++ tailWord_3918275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918275).length < 2 ^ (prefixWord ++ tailWord_3918275).sum := by decide
  have hdescent : baseEnd_3918275 < baseStart_3918275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918335 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 5]
def baseStart_3918335 : Nat := 118140960795 + 3918335 * 2 ^ 59
def prefixEnd_3918335 : Nat := 4983230072969 + 3 ^ 40 * 3918335 * 2
def baseEnd_3918335 : Nat := 2011989220335032229992411

theorem tailTrace_3918335 : CollatzResearch.WordTrace tailWord_3918335 prefixEnd_3918335 2011989220335032229992411 := by
  unfold tailWord_3918335
  simp only [CollatzResearch.WordTrace]
  refine ⟨142913418259548968185508459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95275612173032645457005639 142913418259548968185508459)
  ·
    refine ⟨214370127389323452278262689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142913418259548968185508459 214370127389323452278262689)
    ·
      refine ⟨160777595541992589208697017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214370127389323452278262689 160777595541992589208697017)
      ·
        refine ⟨120583196656494441906522763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160777595541992589208697017 120583196656494441906522763)
        ·
          refine ⟨180874794984741662859784145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120583196656494441906522763 180874794984741662859784145)
          ·
            refine ⟨135656096238556247144838109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180874794984741662859784145 135656096238556247144838109)
            ·
              refine ⟨50871036089458592679314291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135656096238556247144838109 50871036089458592679314291)
              ·
                refine ⟨76306554134187889018971437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50871036089458592679314291 76306554134187889018971437)
                ·
                  refine ⟨28614957800320458382114289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76306554134187889018971437 28614957800320458382114289)
                  ·
                    refine ⟨21461218350240343786585717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28614957800320458382114289 21461218350240343786585717)
                    ·
                      refine ⟨2011989220335032229992411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21461218350240343786585717 2011989220335032229992411)
                      ·
                        rfl

theorem cell23_3918335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_3918335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3918335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3918335 prefixEnd_3918335 := by exact prefixLift 3918335
  have htrace : WordTrace (prefixWord ++ tailWord_3918335) baseStart_3918335 baseEnd_3918335 := by
    simpa [prefixWord, tailWord_3918335, baseEnd_3918335] using wordTrace_append hprefix tailTrace_3918335
  have hstable : (prefixWord ++ tailWord_3918335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918335).length < 2 ^ (prefixWord ++ tailWord_3918335).sum := by decide
  have hdescent : baseEnd_3918335 < baseStart_3918335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918356 : List Nat := [2, 4, 3, 1, 1, 2, 1, 1, 2, 3, 3]
def baseStart_3918356 : Nat := 118140960795 + 3918356 * 2 ^ 59
def prefixEnd_3918356 : Nat := 4983230072969 + 3 ^ 40 * 3918356 * 2
def baseEnd_3918356 : Nat := 2012000003428776647829815

theorem tailTrace_3918356 : CollatzResearch.WordTrace tailWord_3918356 prefixEnd_3918356 2012000003428776647829815 := by
  unfold tailWord_3918356
  simp only [CollatzResearch.WordTrace]
  refine ⟨71457092096236444386011461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95276122794981925848015281 71457092096236444386011461)
  ·
    refine ⟨13398204768044333322377149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71457092096236444386011461 13398204768044333322377149)
    ·
      refine ⟨5024326788016624995891431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13398204768044333322377149 5024326788016624995891431)
      ·
        refine ⟨7536490182024937493837147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5024326788016624995891431 7536490182024937493837147)
        ·
          refine ⟨11304735273037406240755721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7536490182024937493837147 11304735273037406240755721)
          ·
            refine ⟨8478551454778054680566791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11304735273037406240755721 8478551454778054680566791)
            ·
              refine ⟨12717827182167082020850187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8478551454778054680566791 12717827182167082020850187)
              ·
                refine ⟨19076740773250623031275281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12717827182167082020850187 19076740773250623031275281)
                ·
                  refine ⟨14307555579937967273456461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19076740773250623031275281 14307555579937967273456461)
                  ·
                    refine ⟨5365333342476737727546173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14307555579937967273456461 5365333342476737727546173)
                    ·
                      refine ⟨2012000003428776647829815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5365333342476737727546173 2012000003428776647829815)
                      ·
                        rfl

theorem cell23_3918356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_3918356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3918356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3918356 prefixEnd_3918356 := by exact prefixLift 3918356
  have htrace : WordTrace (prefixWord ++ tailWord_3918356) baseStart_3918356 baseEnd_3918356 := by
    simpa [prefixWord, tailWord_3918356, baseEnd_3918356] using wordTrace_append hprefix tailTrace_3918356
  have hstable : (prefixWord ++ tailWord_3918356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918356).length < 2 ^ (prefixWord ++ tailWord_3918356).sum := by decide
  have hdescent : baseEnd_3918356 < baseStart_3918356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918362 : List Nat := [3, 1, 1, 3, 1, 1, 2, 2, 4, 1, 4]
def baseStart_3918362 : Nat := 118140960795 + 3918362 * 2 ^ 59
def prefixEnd_3918362 : Nat := 4983230072969 + 3 ^ 40 * 3918362 * 2
def baseEnd_3918362 : Nat := 2012003084312703624354787

theorem tailTrace_3918362 : CollatzResearch.WordTrace tailWord_3918362 prefixEnd_3918362 2012003084312703624354787 := by
  unfold tailWord_3918362
  simp only [CollatzResearch.WordTrace]
  refine ⟨35728600757612787949185335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95276268686967434531160893 35728600757612787949185335)
  ·
    refine ⟨53592901136419181923778003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35728600757612787949185335 53592901136419181923778003)
    ·
      refine ⟨80389351704628772885667005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53592901136419181923778003 80389351704628772885667005)
      ·
        refine ⟨30146006889235789832125127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80389351704628772885667005 30146006889235789832125127)
        ·
          refine ⟨45219010333853684748187691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30146006889235789832125127 45219010333853684748187691)
          ·
            refine ⟨67828515500780527122281537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45219010333853684748187691 67828515500780527122281537)
            ·
              refine ⟨50871386625585395341711153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67828515500780527122281537 50871386625585395341711153)
              ·
                refine ⟨38153539969189046506283365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50871386625585395341711153 38153539969189046506283365)
                ·
                  refine ⟨7153788744222946219928131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38153539969189046506283365 7153788744222946219928131)
                  ·
                    refine ⟨10730683116334419329892197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7153788744222946219928131 10730683116334419329892197)
                    ·
                      refine ⟨2012003084312703624354787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10730683116334419329892197 2012003084312703624354787)
                      ·
                        rfl

theorem cell23_3918362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_3918362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3918362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3918362 prefixEnd_3918362 := by exact prefixLift 3918362
  have htrace : WordTrace (prefixWord ++ tailWord_3918362) baseStart_3918362 baseEnd_3918362 := by
    simpa [prefixWord, tailWord_3918362, baseEnd_3918362] using wordTrace_append hprefix tailTrace_3918362
  have hstable : (prefixWord ++ tailWord_3918362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918362).length < 2 ^ (prefixWord ++ tailWord_3918362).sum := by decide
  have hdescent : baseEnd_3918362 < baseStart_3918362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918376 : List Nat := [2, 1, 5, 2, 1, 3, 1, 1, 2, 5]
def baseStart_3918376 : Nat := 118140960795 + 3918376 * 2 ^ 59
def prefixEnd_3918376 : Nat := 4983230072969 + 3 ^ 40 * 3918376 * 2
def baseEnd_3918376 : Nat := 670670091013955523193241

theorem tailTrace_3918376 : CollatzResearch.WordTrace tailWord_3918376 prefixEnd_3918376 670670091013955523193241 := by
  unfold tailWord_3918376
  simp only [CollatzResearch.WordTrace]
  refine ⟨71457456826200216093875491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95276609101600288125167321 71457456826200216093875491)
  ·
    refine ⟨107186185239300324140813237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71457456826200216093875491 107186185239300324140813237)
    ·
      refine ⟨10048704866184405388201241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107186185239300324140813237 10048704866184405388201241)
      ·
        refine ⟨7536528649638304041150931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10048704866184405388201241 7536528649638304041150931)
        ·
          refine ⟨11304792974457456061726397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7536528649638304041150931 11304792974457456061726397)
          ·
            refine ⟨4239297365421546023147399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11304792974457456061726397 4239297365421546023147399)
            ·
              refine ⟨6358946048132319034721099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4239297365421546023147399 6358946048132319034721099)
              ·
                refine ⟨9538419072198478552081649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6358946048132319034721099 9538419072198478552081649)
                ·
                  refine ⟨7153814304148858914061237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9538419072198478552081649 7153814304148858914061237)
                  ·
                    refine ⟨670670091013955523193241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7153814304148858914061237 670670091013955523193241)
                    ·
                      rfl

theorem cell23_3918376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_3918376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3918376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3918376 prefixEnd_3918376 := by exact prefixLift 3918376
  have htrace : WordTrace (prefixWord ++ tailWord_3918376) baseStart_3918376 baseEnd_3918376 := by
    simpa [prefixWord, tailWord_3918376, baseEnd_3918376] using wordTrace_append hprefix tailTrace_3918376
  have hstable : (prefixWord ++ tailWord_3918376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918376).length < 2 ^ (prefixWord ++ tailWord_3918376).sum := by decide
  have hdescent : baseEnd_3918376 < baseStart_3918376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918432 : List Nat := [2, 1, 1, 3, 2, 1, 2, 3, 3, 5]
def baseStart_3918432 : Nat := 118140960795 + 3918432 * 2 ^ 59
def prefixEnd_3918432 : Nat := 4983230072969 + 3 ^ 40 * 3918432 * 2
def baseEnd_3918432 : Nat := 670679675986172783493155

theorem tailTrace_3918432 : CollatzResearch.WordTrace tailWord_3918432 prefixEnd_3918432 670679675986172783493155 := by
  unfold tailWord_3918432
  simp only [CollatzResearch.WordTrace]
  refine ⟨71458478070098776875894775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95277970760131702501193033 71458478070098776875894775)
  ·
    refine ⟨107187717105148165313842163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71458478070098776875894775 107187717105148165313842163)
    ·
      refine ⟨160781575657722247970763245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107187717105148165313842163 160781575657722247970763245)
      ·
        refine ⟨60293090871645842989036217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160781575657722247970763245 60293090871645842989036217)
        ·
          refine ⟨45219818153734382241777163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60293090871645842989036217 45219818153734382241777163)
          ·
            refine ⟨67829727230601573362665745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45219818153734382241777163 67829727230601573362665745)
            ·
              refine ⟨50872295422951180021999309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67829727230601573362665745 50872295422951180021999309)
              ·
                refine ⟨19077110783606692508249741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50872295422951180021999309 19077110783606692508249741)
                ·
                  refine ⟨7153916543852509690593653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19077110783606692508249741 7153916543852509690593653)
                  ·
                    refine ⟨670679675986172783493155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7153916543852509690593653 670679675986172783493155)
                    ·
                      rfl

theorem cell23_3918432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 3, 5].length) (baseStart_3918432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3918432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3918432 prefixEnd_3918432 := by exact prefixLift 3918432
  have htrace : WordTrace (prefixWord ++ tailWord_3918432) baseStart_3918432 baseEnd_3918432 := by
    simpa [prefixWord, tailWord_3918432, baseEnd_3918432] using wordTrace_append hprefix tailTrace_3918432
  have hstable : (prefixWord ++ tailWord_3918432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918432).length < 2 ^ (prefixWord ++ tailWord_3918432).sum := by decide
  have hdescent : baseEnd_3918432 < baseStart_3918432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918440 : List Nat := [2, 1, 4, 3, 2, 2, 1, 3, 1, 4]
def baseStart_3918440 : Nat := 118140960795 + 3918440 * 2 ^ 59
def prefixEnd_3918440 : Nat := 4983230072969 + 3 ^ 40 * 3918440 * 2
def baseEnd_3918440 : Nat := 670681045267918106393143

theorem tailTrace_3918440 : CollatzResearch.WordTrace tailWord_3918440 prefixEnd_3918440 670681045267918106393143 := by
  unfold tailWord_3918440
  simp only [CollatzResearch.WordTrace]
  refine ⟨71458623962084285559040387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95278165282779047412053849 71458623962084285559040387)
  ·
    refine ⟨107187935943126428338560581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71458623962084285559040387 107187935943126428338560581)
    ·
      refine ⟨20097737989336205313480109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107187935943126428338560581 20097737989336205313480109)
      ·
        refine ⟨7536651746001076992555041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20097737989336205313480109 7536651746001076992555041)
        ·
          refine ⟨5652488809500807744416281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7536651746001076992555041 5652488809500807744416281)
          ·
            refine ⟨4239366607125605808312211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5652488809500807744416281 4239366607125605808312211)
            ·
              refine ⟨6359049910688408712468317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4239366607125605808312211 6359049910688408712468317)
              ·
                refine ⟨2384643716508153267175619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6359049910688408712468317 2384643716508153267175619)
                ·
                  refine ⟨3576965574762229900763429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2384643716508153267175619 3576965574762229900763429)
                  ·
                    refine ⟨670681045267918106393143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3576965574762229900763429 670681045267918106393143)
                    ·
                      rfl

theorem cell23_3918440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_3918440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3918440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3918440 prefixEnd_3918440 := by exact prefixLift 3918440
  have htrace : WordTrace (prefixWord ++ tailWord_3918440) baseStart_3918440 baseEnd_3918440 := by
    simpa [prefixWord, tailWord_3918440, baseEnd_3918440] using wordTrace_append hprefix tailTrace_3918440
  have hstable : (prefixWord ++ tailWord_3918440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918440).length < 2 ^ (prefixWord ++ tailWord_3918440).sum := by decide
  have hdescent : baseEnd_3918440 < baseStart_3918440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918479 : List Nat := [1, 1, 2, 1, 1, 1, 1, 9, 2, 4]
def baseStart_3918479 : Nat := 118140960795 + 3918479 * 2 ^ 59
def prefixEnd_3918479 : Nat := 4983230072969 + 3 ^ 40 * 3918479 * 2
def baseEnd_3918479 : Nat := 670687720516426555530583

theorem tailTrace_3918479 : CollatzResearch.WordTrace tailWord_3918479 prefixEnd_3918479 670687720516426555530583 := by
  unfold tailWord_3918479
  simp only [CollatzResearch.WordTrace]
  refine ⟨142918670371027280778750491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95279113580684853852500327 142918670371027280778750491)
  ·
    refine ⟨214378005556540921168125737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142918670371027280778750491 214378005556540921168125737)
    ·
      refine ⟨160783504167405690876094303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214378005556540921168125737 160783504167405690876094303)
      ·
        refine ⟨241175256251108536314141455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160783504167405690876094303 241175256251108536314141455)
        ·
          refine ⟨361762884376662804471212183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241175256251108536314141455 361762884376662804471212183)
          ·
            refine ⟨542644326564994206706818275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361762884376662804471212183 542644326564994206706818275)
            ·
              refine ⟨813966489847491310060227413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 542644326564994206706818275 813966489847491310060227413)
              ·
                refine ⟨4769334901450144394884145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 813966489847491310060227413 4769334901450144394884145)
                ·
                  refine ⟨3577001176087608296163109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4769334901450144394884145 3577001176087608296163109)
                  ·
                    refine ⟨670687720516426555530583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3577001176087608296163109 670687720516426555530583)
                    ·
                      rfl

theorem cell23_3918479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 2, 4].length) (baseStart_3918479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3918479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3918479 prefixEnd_3918479 := by exact prefixLift 3918479
  have htrace : WordTrace (prefixWord ++ tailWord_3918479) baseStart_3918479 baseEnd_3918479 := by
    simpa [prefixWord, tailWord_3918479, baseEnd_3918479] using wordTrace_append hprefix tailTrace_3918479
  have hstable : (prefixWord ++ tailWord_3918479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918479).length < 2 ^ (prefixWord ++ tailWord_3918479).sum := by decide
  have hdescent : baseEnd_3918479 < baseStart_3918479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918489 : List Nat := [1, 2, 1, 2, 1, 2, 5, 1, 3, 2, 3]
def baseStart_3918489 : Nat := 118140960795 + 3918489 * 2 ^ 59
def prefixEnd_3918489 : Nat := 4983230072969 + 3 ^ 40 * 3918489 * 2
def baseEnd_3918489 : Nat := 2012068296355824627466703

theorem tailTrace_3918489 : CollatzResearch.WordTrace tailWord_3918489 prefixEnd_3918489 2012068296355824627466703 := by
  unfold tailWord_3918489
  simp only [CollatzResearch.WordTrace]
  refine ⟨142919035100991052486614521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95279356733994034991076347 142919035100991052486614521)
  ·
    refine ⟨107189276325743289364960891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142919035100991052486614521 107189276325743289364960891)
    ·
      refine ⟨160783914488614934047441337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107189276325743289364960891 160783914488614934047441337)
      ·
        refine ⟨120587935866461200535581003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160783914488614934047441337 120587935866461200535581003)
        ·
          refine ⟨180881903799691800803371505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120587935866461200535581003 180881903799691800803371505)
          ·
            refine ⟨135661427849768850602528629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180881903799691800803371505 135661427849768850602528629)
            ·
              refine ⟨12718258860915829743987059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135661427849768850602528629 12718258860915829743987059)
              ·
                refine ⟨19077388291373744615980589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12718258860915829743987059 19077388291373744615980589)
                ·
                  refine ⟨7154020609265154230992721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19077388291373744615980589 7154020609265154230992721)
                  ·
                    refine ⟨5365515456948865673244541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7154020609265154230992721 5365515456948865673244541)
                    ·
                      refine ⟨2012068296355824627466703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5365515456948865673244541 2012068296355824627466703)
                      ·
                        rfl

theorem cell23_3918489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 2, 3].length) (baseStart_3918489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3918489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3918489 prefixEnd_3918489 := by exact prefixLift 3918489
  have htrace : WordTrace (prefixWord ++ tailWord_3918489) baseStart_3918489 baseEnd_3918489 := by
    simpa [prefixWord, tailWord_3918489, baseEnd_3918489] using wordTrace_append hprefix tailTrace_3918489
  have hstable : (prefixWord ++ tailWord_3918489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918489).length < 2 ^ (prefixWord ++ tailWord_3918489).sum := by decide
  have hdescent : baseEnd_3918489 < baseStart_3918489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918490 : List Nat := [3, 1, 1, 6, 1, 1, 2, 1, 2, 3, 2]
def baseStart_3918490 : Nat := 118140960795 + 3918490 * 2 ^ 59
def prefixEnd_3918490 : Nat := 4983230072969 + 3 ^ 40 * 3918490 * 2
def baseEnd_3918490 : Nat := 2012068809836479123554199

theorem tailTrace_3918490 : CollatzResearch.WordTrace tailWord_3918490 prefixEnd_3918490 2012068809836479123554199 := by
  unfold tailWord_3918490
  simp only [CollatzResearch.WordTrace]
  refine ⟨35729767893496857414350231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95279381049324953104933949 35729767893496857414350231)
  ·
    refine ⟨53594651840245286121525347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35729767893496857414350231 53594651840245286121525347)
    ·
      refine ⟨80391977760367929182288021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53594651840245286121525347 80391977760367929182288021)
      ·
        refine ⟨3768373957517246680419751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 80391977760367929182288021 3768373957517246680419751)
        ·
          refine ⟨5652560936275870020629627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3768373957517246680419751 5652560936275870020629627)
          ·
            refine ⟨8478841404413805030944441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5652560936275870020629627 8478841404413805030944441)
            ·
              refine ⟨6359131053310353773208331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8478841404413805030944441 6359131053310353773208331)
              ·
                refine ⟨9538696579965530659812497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6359131053310353773208331 9538696579965530659812497)
                ·
                  refine ⟨7154022434974147994859373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9538696579965530659812497 7154022434974147994859373)
                  ·
                    refine ⟨2682758413115305498072265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7154022434974147994859373 2682758413115305498072265)
                    ·
                      refine ⟨2012068809836479123554199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2682758413115305498072265 2012068809836479123554199)
                      ·
                        rfl

theorem cell23_3918490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_3918490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3918490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3918490 prefixEnd_3918490 := by exact prefixLift 3918490
  have htrace : WordTrace (prefixWord ++ tailWord_3918490) baseStart_3918490 baseEnd_3918490 := by
    simpa [prefixWord, tailWord_3918490, baseEnd_3918490] using wordTrace_append hprefix tailTrace_3918490
  have hstable : (prefixWord ++ tailWord_3918490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918490).length < 2 ^ (prefixWord ++ tailWord_3918490).sum := by decide
  have hdescent : baseEnd_3918490 < baseStart_3918490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918522 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 1, 9]
def baseStart_3918522 : Nat := 118140960795 + 3918522 * 2 ^ 59
def prefixEnd_3918522 : Nat := 4983230072969 + 3 ^ 40 * 3918522 * 2
def baseEnd_3918522 : Nat := 670695080405807666118017

theorem tailTrace_3918522 : CollatzResearch.WordTrace tailWord_3918522 prefixEnd_3918522 670695080405807666118017 := by
  unfold tailWord_3918522
  simp only [CollatzResearch.WordTrace]
  refine ⟨35730059677467874780641455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95280159139914332748377213 35730059677467874780641455)
  ·
    refine ⟨53595089516201812170962183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35730059677467874780641455 53595089516201812170962183)
    ·
      refine ⟨80392634274302718256443275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53595089516201812170962183 80392634274302718256443275)
      ·
        refine ⟨120588951411454077384664913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80392634274302718256443275 120588951411454077384664913)
        ·
          refine ⟨90441713558590558038498685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120588951411454077384664913 90441713558590558038498685)
          ·
            refine ⟨33915642584471459264437007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90441713558590558038498685 33915642584471459264437007)
            ·
              refine ⟨50873463876707188896655511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33915642584471459264437007 50873463876707188896655511)
              ·
                refine ⟨76310195815060783344983267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50873463876707188896655511 76310195815060783344983267)
                ·
                  refine ⟨114465293722591175017474901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76310195815060783344983267 114465293722591175017474901)
                  ·
                    refine ⟨670695080405807666118017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 114465293722591175017474901 670695080405807666118017)
                    ·
                      rfl

theorem cell23_3918522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 1, 9].length) (baseStart_3918522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3918522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3918522 prefixEnd_3918522 := by exact prefixLift 3918522
  have htrace : WordTrace (prefixWord ++ tailWord_3918522) baseStart_3918522 baseEnd_3918522 := by
    simpa [prefixWord, tailWord_3918522, baseEnd_3918522] using wordTrace_append hprefix tailTrace_3918522
  have hstable : (prefixWord ++ tailWord_3918522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918522).length < 2 ^ (prefixWord ++ tailWord_3918522).sum := by decide
  have hdescent : baseEnd_3918522 < baseStart_3918522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918536 : List Nat := [2, 1, 3, 1, 2, 4, 2, 1, 1, 3, 3]
def baseStart_3918536 : Nat := 118140960795 + 3918536 * 2 ^ 59
def prefixEnd_3918536 : Nat := 4983230072969 + 3 ^ 40 * 3918536 * 2
def baseEnd_3918536 : Nat := 2012092429946585943578987

theorem tailTrace_3918536 : CollatzResearch.WordTrace tailWord_3918536 prefixEnd_3918536 2012092429946585943578987 := by
  unfold tailWord_3918536
  simp only [CollatzResearch.WordTrace]
  refine ⟨71460374665910389756787731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95280499554547186342383641 71460374665910389756787731)
  ·
    refine ⟨107190561998865584635181597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71460374665910389756787731 107190561998865584635181597)
    ·
      refine ⟨40196460749574594238193099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107190561998865584635181597 40196460749574594238193099)
      ·
        refine ⟨60294691124361891357289649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40196460749574594238193099 60294691124361891357289649)
        ·
          refine ⟨45221018343271418517967237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60294691124361891357289649 45221018343271418517967237)
          ·
            refine ⟨8478940939363390972118857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45221018343271418517967237 8478940939363390972118857)
            ·
              refine ⟨6359205704522543229089143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8478940939363390972118857 6359205704522543229089143)
              ·
                refine ⟨9538808556783814843633715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6359205704522543229089143 9538808556783814843633715)
                ·
                  refine ⟨14308212835175722265450573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9538808556783814843633715 14308212835175722265450573)
                  ·
                    refine ⟨5365579813190895849543965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14308212835175722265450573 5365579813190895849543965)
                    ·
                      refine ⟨2012092429946585943578987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5365579813190895849543965 2012092429946585943578987)
                      ·
                        rfl

theorem cell23_3918536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 1, 3, 3].length) (baseStart_3918536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3918536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3918536 prefixEnd_3918536 := by exact prefixLift 3918536
  have htrace : WordTrace (prefixWord ++ tailWord_3918536) baseStart_3918536 baseEnd_3918536 := by
    simpa [prefixWord, tailWord_3918536, baseEnd_3918536] using wordTrace_append hprefix tailTrace_3918536
  have hstable : (prefixWord ++ tailWord_3918536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918536).length < 2 ^ (prefixWord ++ tailWord_3918536).sum := by decide
  have hdescent : baseEnd_3918536 < baseStart_3918536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918589 : List Nat := [1, 4, 1, 1, 1, 1, 3, 3, 2, 2, 4]
def baseStart_3918589 : Nat := 118140960795 + 3918589 * 2 ^ 59
def prefixEnd_3918589 : Nat := 4983230072969 + 3 ^ 40 * 3918589 * 2
def baseEnd_3918589 : Nat := 2012119644421274236216243

theorem tailTrace_3918589 : CollatzResearch.WordTrace tailWord_3918589 prefixEnd_3918589 2012119644421274236216243 := by
  unfold tailWord_3918589
  simp only [CollatzResearch.WordTrace]
  refine ⟨142922682400628769565254821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95281788267085846376836547 142922682400628769565254821)
  ·
    refine ⟨26798002950117894293485279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142922682400628769565254821 26798002950117894293485279)
    ·
      refine ⟨40197004425176841440227919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26798002950117894293485279 40197004425176841440227919)
      ·
        refine ⟨60295506637765262160341879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40197004425176841440227919 60295506637765262160341879)
        ·
          refine ⟨90443259956647893240512819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60295506637765262160341879 90443259956647893240512819)
          ·
            refine ⟨135664889934971839860769229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90443259956647893240512819 135664889934971839860769229)
            ·
              refine ⟨50874333725614439947788461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135664889934971839860769229 50874333725614439947788461)
              ·
                refine ⟨19077875147105414980420673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50874333725614439947788461 19077875147105414980420673)
                ·
                  refine ⟨14308406360329061235315505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19077875147105414980420673 14308406360329061235315505)
                  ·
                    refine ⟨10731304770246795926486629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14308406360329061235315505 10731304770246795926486629)
                    ·
                      refine ⟨2012119644421274236216243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10731304770246795926486629 2012119644421274236216243)
                      ·
                        rfl

theorem cell23_3918589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_3918589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3918589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3918589 prefixEnd_3918589 := by exact prefixLift 3918589
  have htrace : WordTrace (prefixWord ++ tailWord_3918589) baseStart_3918589 baseEnd_3918589 := by
    simpa [prefixWord, tailWord_3918589, baseEnd_3918589] using wordTrace_append hprefix tailTrace_3918589
  have hstable : (prefixWord ++ tailWord_3918589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918589).length < 2 ^ (prefixWord ++ tailWord_3918589).sum := by decide
  have hdescent : baseEnd_3918589 < baseStart_3918589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918609 : List Nat := [1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 3]
def baseStart_3918609 : Nat := 118140960795 + 3918609 * 2 ^ 59
def prefixEnd_3918609 : Nat := 4983230072969 + 3 ^ 40 * 3918609 * 2
def baseEnd_3918609 : Nat := 2012129914034364157966151

theorem tailTrace_3918609 : CollatzResearch.WordTrace tailWord_3918609 prefixEnd_3918609 2012129914034364157966151 := by
  unfold tailWord_3918609
  simp only [CollatzResearch.WordTrace]
  refine ⟨142923411860556312980982881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95282274573704208653988587 142923411860556312980982881)
  ·
    refine ⟨107192558895417234735737161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142923411860556312980982881 107192558895417234735737161)
    ·
      refine ⟨80394419171562926051802871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107192558895417234735737161 80394419171562926051802871)
      ·
        refine ⟨120591628757344389077704307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80394419171562926051802871 120591628757344389077704307)
        ·
          refine ⟨180887443136016583616556461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120591628757344389077704307 180887443136016583616556461)
          ·
            refine ⟨67832791176006218856208673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180887443136016583616556461 67832791176006218856208673)
            ·
              refine ⟨50874593382004664142156505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67832791176006218856208673 50874593382004664142156505)
              ·
                refine ⟨38155945036503498106617379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50874593382004664142156505 38155945036503498106617379)
                ·
                  refine ⟨57233917554755247159926069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38155945036503498106617379 57233917554755247159926069)
                  ·
                    refine ⟨5365679770758304421243069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57233917554755247159926069 5365679770758304421243069)
                    ·
                      refine ⟨2012129914034364157966151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5365679770758304421243069 2012129914034364157966151)
                      ·
                        rfl

theorem cell23_3918609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 3].length) (baseStart_3918609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3918609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3918609 prefixEnd_3918609 := by exact prefixLift 3918609
  have htrace : WordTrace (prefixWord ++ tailWord_3918609) baseStart_3918609 baseEnd_3918609 := by
    simpa [prefixWord, tailWord_3918609, baseEnd_3918609] using wordTrace_append hprefix tailTrace_3918609
  have hstable : (prefixWord ++ tailWord_3918609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918609).length < 2 ^ (prefixWord ++ tailWord_3918609).sum := by decide
  have hdescent : baseEnd_3918609 < baseStart_3918609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918636 : List Nat := [2, 2, 1, 1, 1, 4, 2, 1, 2, 5, 2]
def baseStart_3918636 : Nat := 118140960795 + 3918636 * 2 ^ 59
def prefixEnd_3918636 : Nat := 4983230072969 + 3 ^ 40 * 3918636 * 2
def baseEnd_3918636 : Nat := 2012143778012035552328527

theorem tailTrace_3918636 : CollatzResearch.WordTrace tailWord_3918636 prefixEnd_3918636 2012143778012035552328527 := by
  unfold tailWord_3918636
  simp only [CollatzResearch.WordTrace]
  refine ⟨71462198315729248296107881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95282931087638997728143841 71462198315729248296107881)
  ·
    refine ⟨53596648736796936222080911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71462198315729248296107881 53596648736796936222080911)
    ·
      refine ⟨80394973105195404333121367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53596648736796936222080911 80394973105195404333121367)
      ·
        refine ⟨120592459657793106499682051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80394973105195404333121367 120592459657793106499682051)
        ·
          refine ⟨180888689486689659749523077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120592459657793106499682051 180888689486689659749523077)
          ·
            refine ⟨33916629278754311203035577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180888689486689659749523077 33916629278754311203035577)
            ·
              refine ⟨25437471959065733402276683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33916629278754311203035577 25437471959065733402276683)
              ·
                refine ⟨38156207938598600103415025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25437471959065733402276683 38156207938598600103415025)
                ·
                  refine ⟨28617155953948950077561269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38156207938598600103415025 28617155953948950077561269)
                  ·
                    refine ⟨2682858370682714069771369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28617155953948950077561269 2682858370682714069771369)
                    ·
                      refine ⟨2012143778012035552328527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2682858370682714069771369 2012143778012035552328527)
                      ·
                        rfl

theorem cell23_3918636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 5, 2].length) (baseStart_3918636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3918636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3918636 prefixEnd_3918636 := by exact prefixLift 3918636
  have htrace : WordTrace (prefixWord ++ tailWord_3918636) baseStart_3918636 baseEnd_3918636 := by
    simpa [prefixWord, tailWord_3918636, baseEnd_3918636] using wordTrace_append hprefix tailTrace_3918636
  have hstable : (prefixWord ++ tailWord_3918636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918636).length < 2 ^ (prefixWord ++ tailWord_3918636).sum := by decide
  have hdescent : baseEnd_3918636 < baseStart_3918636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918666 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 3, 6, 2]
def baseStart_3918666 : Nat := 118140960795 + 3918666 * 2 ^ 59
def prefixEnd_3918666 : Nat := 4983230072969 + 3 ^ 40 * 3918666 * 2
def baseEnd_3918666 : Nat := 2012159182431670434953389

theorem tailTrace_3918666 : CollatzResearch.WordTrace tailWord_3918666 prefixEnd_3918666 2012159182431670434953389 := by
  unfold tailWord_3918666
  simp only [CollatzResearch.WordTrace]
  refine ⟨35731372705337452928951963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95283660547566541143871901 35731372705337452928951963)
  ·
    refine ⟨53597059058006179393427945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35731372705337452928951963 53597059058006179393427945)
    ·
      refine ⟨40197794293504634545070959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53597059058006179393427945 40197794293504634545070959)
      ·
        refine ⟨60296691440256951817606439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40197794293504634545070959 60296691440256951817606439)
        ·
          refine ⟨90445037160385427726409659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60296691440256951817606439 90445037160385427726409659)
          ·
            refine ⟨135667555740578141589614489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90445037160385427726409659 135667555740578141589614489)
            ·
              refine ⟨101750666805433606192210867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135667555740578141589614489 101750666805433606192210867)
              ·
                refine ⟨152626000208150409288316301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101750666805433606192210867 152626000208150409288316301)
                ·
                  refine ⟨57234750078056403483118613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152626000208150409288316301 57234750078056403483118613)
                  ·
                    refine ⟨2682878909908893913271185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 57234750078056403483118613 2682878909908893913271185)
                    ·
                      refine ⟨2012159182431670434953389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2682878909908893913271185 2012159182431670434953389)
                      ·
                        rfl

theorem cell23_3918666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 3, 6, 2].length) (baseStart_3918666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3918666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3918666 prefixEnd_3918666 := by exact prefixLift 3918666
  have htrace : WordTrace (prefixWord ++ tailWord_3918666) baseStart_3918666 baseEnd_3918666 := by
    simpa [prefixWord, tailWord_3918666, baseEnd_3918666] using wordTrace_append hprefix tailTrace_3918666
  have hstable : (prefixWord ++ tailWord_3918666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918666).length < 2 ^ (prefixWord ++ tailWord_3918666).sum := by decide
  have hdescent : baseEnd_3918666 < baseStart_3918666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918706 : List Nat := [3, 2, 1, 2, 1, 1, 4, 3, 6]
def baseStart_3918706 : Nat := 118140960795 + 3918706 * 2 ^ 59
def prefixEnd_3918706 : Nat := 4983230072969 + 3 ^ 40 * 3918706 * 2
def baseEnd_3918706 : Nat := 223575524628650030939245

theorem tailTrace_3918706 : CollatzResearch.WordTrace tailWord_3918706 prefixEnd_3918706 223575524628650030939245 := by
  unfold tailWord_3918706
  simp only [CollatzResearch.WordTrace]
  refine ⟨35731737435301224636815993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95284633160803265698175981 35731737435301224636815993)
  ·
    refine ⟨26798803076475918477611995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35731737435301224636815993 26798803076475918477611995)
    ·
      refine ⟨40198204614713877716417993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26798803076475918477611995 40198204614713877716417993)
      ·
        refine ⟨30148653461035408287313495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40198204614713877716417993 30148653461035408287313495)
        ·
          refine ⟨45222980191553112430970243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30148653461035408287313495 45222980191553112430970243)
          ·
            refine ⟨67834470287329668646455365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45222980191553112430970243 67834470287329668646455365)
            ·
              refine ⟨12718963178874312871210381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67834470287329668646455365 12718963178874312871210381)
              ·
                refine ⟨4769611192077867326703893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12718963178874312871210381 4769611192077867326703893)
                ·
                  refine ⟨223575524628650030939245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4769611192077867326703893 223575524628650030939245)
                  ·
                    rfl

theorem cell23_3918706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 6].length) (baseStart_3918706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3918706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3918706 prefixEnd_3918706 := by exact prefixLift 3918706
  have htrace : WordTrace (prefixWord ++ tailWord_3918706) baseStart_3918706 baseEnd_3918706 := by
    simpa [prefixWord, tailWord_3918706, baseEnd_3918706] using wordTrace_append hprefix tailTrace_3918706
  have hstable : (prefixWord ++ tailWord_3918706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918706).length < 2 ^ (prefixWord ++ tailWord_3918706).sum := by decide
  have hdescent : baseEnd_3918706 < baseStart_3918706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918710 : List Nat := [5, 1, 1, 3, 1, 2, 1, 2, 3, 4]
def baseStart_3918710 : Nat := 118140960795 + 3918710 * 2 ^ 59
def prefixEnd_3918710 : Nat := 4983230072969 + 3 ^ 40 * 3918710 * 2
def baseEnd_3918710 : Nat := 670727258526822754267729

theorem tailTrace_3918710 : CollatzResearch.WordTrace tailWord_3918710 prefixEnd_3918710 670727258526822754267729 := by
  unfold tailWord_3918710
  simp only [CollatzResearch.WordTrace]
  refine ⟨8932943477074400451900599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95284730422126938153606389 8932943477074400451900599)
  ·
    refine ⟨13399415215611600677850899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8932943477074400451900599 13399415215611600677850899)
    ·
      refine ⟨20099122823417401016776349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13399415215611600677850899 20099122823417401016776349)
      ·
        refine ⟨7537171058781525381291131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20099122823417401016776349 7537171058781525381291131)
        ·
          refine ⟨11305756588172288071936697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7537171058781525381291131 11305756588172288071936697)
          ·
            refine ⟨8479317441129216053952523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11305756588172288071936697 8479317441129216053952523)
            ·
              refine ⟨12718976161693824080928785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8479317441129216053952523 12718976161693824080928785)
              ·
                refine ⟨9539232121270368060696589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12718976161693824080928785 9539232121270368060696589)
                ·
                  refine ⟨3577212045476388022761221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9539232121270368060696589 3577212045476388022761221)
                  ·
                    refine ⟨670727258526822754267729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3577212045476388022761221 670727258526822754267729)
                    ·
                      rfl

theorem cell23_3918710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_3918710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3918710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3918710 prefixEnd_3918710 := by exact prefixLift 3918710
  have htrace : WordTrace (prefixWord ++ tailWord_3918710) baseStart_3918710 baseEnd_3918710 := by
    simpa [prefixWord, tailWord_3918710, baseEnd_3918710] using wordTrace_append hprefix tailTrace_3918710
  have hstable : (prefixWord ++ tailWord_3918710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918710).length < 2 ^ (prefixWord ++ tailWord_3918710).sum := by decide
  have hdescent : baseEnd_3918710 < baseStart_3918710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918743 : List Nat := [1, 1, 3, 3, 1, 2, 2, 1, 4, 3, 2]
def baseStart_3918743 : Nat := 118140960795 + 3918743 * 2 ^ 59
def prefixEnd_3918743 : Nat := 4983230072969 + 3 ^ 40 * 3918743 * 2
def baseEnd_3918743 : Nat := 2012198720442066633690535

theorem tailTrace_3918743 : CollatzResearch.WordTrace tailWord_3918743 prefixEnd_3918743 2012198720442066633690535 := by
  unfold tailWord_3918743
  simp only [CollatzResearch.WordTrace]
  refine ⟨142928299242070853866360883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95285532828047235910907255 142928299242070853866360883)
  ·
    refine ⟨214392448863106280799541325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142928299242070853866360883 214392448863106280799541325)
    ·
      refine ⟨80397168323664855299827997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214392448863106280799541325 80397168323664855299827997)
      ·
        refine ⟨30148938121374320737435499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80397168323664855299827997 30148938121374320737435499)
        ·
          refine ⟨45223407182061481106153249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30148938121374320737435499 45223407182061481106153249)
          ·
            refine ⟨33917555386546110829614937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45223407182061481106153249 33917555386546110829614937)
            ·
              refine ⟨25438166539909583122211203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33917555386546110829614937 25438166539909583122211203)
              ·
                refine ⟨38157249809864374683316805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25438166539909583122211203 38157249809864374683316805)
                ·
                  refine ⟨7154484339349570253121901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38157249809864374683316805 7154484339349570253121901)
                  ·
                    refine ⟨2682931627256088844920713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7154484339349570253121901 2682931627256088844920713)
                    ·
                      refine ⟨2012198720442066633690535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2682931627256088844920713 2012198720442066633690535)
                      ·
                        rfl

theorem cell23_3918743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_3918743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3918743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3918743 prefixEnd_3918743 := by exact prefixLift 3918743
  have htrace : WordTrace (prefixWord ++ tailWord_3918743) baseStart_3918743 baseEnd_3918743 := by
    simpa [prefixWord, tailWord_3918743, baseEnd_3918743] using wordTrace_append hprefix tailTrace_3918743
  have hstable : (prefixWord ++ tailWord_3918743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918743).length < 2 ^ (prefixWord ++ tailWord_3918743).sum := by decide
  have hdescent : baseEnd_3918743 < baseStart_3918743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918773 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 2, 6, 2]
def baseStart_3918773 : Nat := 118140960795 + 3918773 * 2 ^ 59
def prefixEnd_3918773 : Nat := 4983230072969 + 3 ^ 40 * 3918773 * 2
def baseEnd_3918773 : Nat := 2012214124861701516315397

theorem tailTrace_3918773 : CollatzResearch.WordTrace tailWord_3918773 prefixEnd_3918773 2012214124861701516315397 := by
  unfold tailWord_3918773
  simp only [CollatzResearch.WordTrace]
  refine ⟨142929393431962168989952973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95286262287974779326635315 142929393431962168989952973)
  ·
    refine ⟨53598522536985813371232365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142929393431962168989952973 53598522536985813371232365)
    ·
      refine ⟨20099445951369680014212137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53598522536985813371232365 20099445951369680014212137)
      ·
        refine ⟨15074584463527260010659103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20099445951369680014212137 15074584463527260010659103)
        ·
          refine ⟨22611876695290890015988655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15074584463527260010659103 22611876695290890015988655)
          ·
            refine ⟨33917815042936335023982983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22611876695290890015988655 33917815042936335023982983)
            ·
              refine ⟨50876722564404502535974475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33917815042936335023982983 50876722564404502535974475)
              ·
                refine ⟨76315083846606753803961713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50876722564404502535974475 76315083846606753803961713)
                ·
                  refine ⟨57236312884955065352971285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76315083846606753803961713 57236312884955065352971285)
                  ·
                    refine ⟨2682952166482268688420529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 57236312884955065352971285 2682952166482268688420529)
                    ·
                      refine ⟨2012214124861701516315397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2682952166482268688420529 2012214124861701516315397)
                      ·
                        rfl

theorem cell23_3918773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_3918773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3918773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3918773 prefixEnd_3918773 := by exact prefixLift 3918773
  have htrace : WordTrace (prefixWord ++ tailWord_3918773) baseStart_3918773 baseEnd_3918773 := by
    simpa [prefixWord, tailWord_3918773, baseEnd_3918773] using wordTrace_append hprefix tailTrace_3918773
  have hstable : (prefixWord ++ tailWord_3918773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918773).length < 2 ^ (prefixWord ++ tailWord_3918773).sum := by decide
  have hdescent : baseEnd_3918773 < baseStart_3918773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918813 : List Nat := [1, 4, 3, 1, 2, 2, 2, 8]
def baseStart_3918813 : Nat := 118140960795 + 3918813 * 2 ^ 59
def prefixEnd_3918813 : Nat := 4983230072969 + 3 ^ 40 * 3918813 * 2
def baseEnd_3918813 : Nat := 74527209781032642956119

theorem tailTrace_3918813 : CollatzResearch.WordTrace tailWord_3918813 prefixEnd_3918813 74527209781032642956119 := by
  unfold tailWord_3918813
  simp only [CollatzResearch.WordTrace]
  refine ⟨142930852351817255821409093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95287234901211503880939395 142930852351817255821409093)
  ·
    refine ⟨26799534815965735466514205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142930852351817255821409093 26799534815965735466514205)
    ·
      refine ⟨10049825555987150799942827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26799534815965735466514205 10049825555987150799942827)
      ·
        refine ⟨15074738333980726199914241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10049825555987150799942827 15074738333980726199914241)
        ·
          refine ⟨11306053750485544649935681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15074738333980726199914241 11306053750485544649935681)
          ·
            refine ⟨8479540312864158487451761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11306053750485544649935681 8479540312864158487451761)
            ·
              refine ⟨6359655234648118865588821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8479540312864158487451761 6359655234648118865588821)
              ·
                refine ⟨74527209781032642956119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6359655234648118865588821 74527209781032642956119)
                ·
                  rfl

theorem cell23_3918813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 8].length) (baseStart_3918813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3918813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3918813 prefixEnd_3918813 := by exact prefixLift 3918813
  have htrace : WordTrace (prefixWord ++ tailWord_3918813) baseStart_3918813 baseEnd_3918813 := by
    simpa [prefixWord, tailWord_3918813, baseEnd_3918813] using wordTrace_append hprefix tailTrace_3918813
  have hstable : (prefixWord ++ tailWord_3918813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918813).length < 2 ^ (prefixWord ++ tailWord_3918813).sum := by decide
  have hdescent : baseEnd_3918813 < baseStart_3918813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918837 : List Nat := [1, 3, 5, 2, 1, 1, 1, 2, 1, 2, 4]
def baseStart_3918837 : Nat := 118140960795 + 3918837 * 2 ^ 59
def prefixEnd_3918837 : Nat := 4983230072969 + 3 ^ 40 * 3918837 * 2
def baseEnd_3918837 : Nat := 2012246987623589265915103

theorem tailTrace_3918837 : CollatzResearch.WordTrace tailWord_3918837 prefixEnd_3918837 2012246987623589265915103 := by
  unfold tailWord_3918837
  simp only [CollatzResearch.WordTrace]
  refine ⟨142931727703730307920282765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95287818469153538613521843 142931727703730307920282765)
  ·
    refine ⟨53599397888898865470106037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142931727703730307920282765 53599397888898865470106037)
    ·
      refine ⟨5024943552084268637822441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53599397888898865470106037 5024943552084268637822441)
      ·
        refine ⟨3768707664063201478366831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5024943552084268637822441 3768707664063201478366831)
        ·
          refine ⟨5653061496094802217550247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3768707664063201478366831 5653061496094802217550247)
          ·
            refine ⟨8479592244142203326325371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5653061496094802217550247 8479592244142203326325371)
            ·
              refine ⟨12719388366213304989488057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8479592244142203326325371 12719388366213304989488057)
              ·
                refine ⟨9539541274659978742116043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12719388366213304989488057 9539541274659978742116043)
                ·
                  refine ⟨14309311911989968113174065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9539541274659978742116043 14309311911989968113174065)
                  ·
                    refine ⟨10731983933992476084880549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14309311911989968113174065 10731983933992476084880549)
                    ·
                      refine ⟨2012246987623589265915103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10731983933992476084880549 2012246987623589265915103)
                      ·
                        rfl

theorem cell23_3918837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_3918837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3918837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3918837 prefixEnd_3918837 := by exact prefixLift 3918837
  have htrace : WordTrace (prefixWord ++ tailWord_3918837) baseStart_3918837 baseEnd_3918837 := by
    simpa [prefixWord, tailWord_3918837, baseEnd_3918837] using wordTrace_append hprefix tailTrace_3918837
  have hstable : (prefixWord ++ tailWord_3918837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918837).length < 2 ^ (prefixWord ++ tailWord_3918837).sum := by decide
  have hdescent : baseEnd_3918837 < baseStart_3918837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918910 : List Nat := [4, 2, 1, 3, 1, 1, 1, 2, 2, 2, 4]
def baseStart_3918910 : Nat := 118140960795 + 3918910 * 2 ^ 59
def prefixEnd_3918910 : Nat := 4983230072969 + 3 ^ 40 * 3918910 * 2
def baseEnd_3918910 : Nat := 2012284471711367480302267

theorem tailTrace_3918910 : CollatzResearch.WordTrace tailWord_3918910 prefixEnd_3918910 2012284471711367480302267 := by
  unfold tailWord_3918910
  simp only [CollatzResearch.WordTrace]
  refine ⟨17866798779058230173461273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95289593488310560925126789 17866798779058230173461273)
  ·
    refine ⟨13400099084293672630095955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17866798779058230173461273 13400099084293672630095955)
    ·
      refine ⟨20100148626440508945143933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13400099084293672630095955 20100148626440508945143933)
      ·
        refine ⟨7537555734915190854428975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20100148626440508945143933 7537555734915190854428975)
        ·
          refine ⟨11306333602372786281643463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7537555734915190854428975 11306333602372786281643463)
          ·
            refine ⟨16959500403559179422465195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11306333602372786281643463 16959500403559179422465195)
            ·
              refine ⟨25439250605338769133697793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16959500403559179422465195 25439250605338769133697793)
              ·
                refine ⟨19079437954004076850273345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25439250605338769133697793 19079437954004076850273345)
                ·
                  refine ⟨14309578465503057637705009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19079437954004076850273345 14309578465503057637705009)
                  ·
                    refine ⟨10732183849127293228278757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14309578465503057637705009 10732183849127293228278757)
                    ·
                      refine ⟨2012284471711367480302267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10732183849127293228278757 2012284471711367480302267)
                      ·
                        rfl

theorem cell23_3918910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_3918910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3918910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3918910 prefixEnd_3918910 := by exact prefixLift 3918910
  have htrace : WordTrace (prefixWord ++ tailWord_3918910) baseStart_3918910 baseEnd_3918910 := by
    simpa [prefixWord, tailWord_3918910, baseEnd_3918910] using wordTrace_append hprefix tailTrace_3918910
  have hstable : (prefixWord ++ tailWord_3918910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918910).length < 2 ^ (prefixWord ++ tailWord_3918910).sum := by decide
  have hdescent : baseEnd_3918910 < baseStart_3918910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918930 : List Nat := [3, 2, 2, 1, 3, 1, 2, 1, 2, 3, 3]
def baseStart_3918930 : Nat := 118140960795 + 3918930 * 2 ^ 59
def prefixEnd_3918930 : Nat := 4983230072969 + 3 ^ 40 * 3918930 * 2
def baseEnd_3918930 : Nat := 2012294741324457402052175

theorem tailTrace_3918930 : CollatzResearch.WordTrace tailWord_3918930 prefixEnd_3918930 2012294741324457402052175 := by
  unfold tailWord_3918930
  simp only [CollatzResearch.WordTrace]
  refine ⟨35733779923098346200854561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95290079794928923202278829 35733779923098346200854561)
  ·
    refine ⟨26800334942323759650640921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35733779923098346200854561 26800334942323759650640921)
    ·
      refine ⟨20100251206742819737980691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26800334942323759650640921 20100251206742819737980691)
      ·
        refine ⟨30150376810114229606971037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20100251206742819737980691 30150376810114229606971037)
        ·
          refine ⟨11306391303792836102614139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30150376810114229606971037 11306391303792836102614139)
          ·
            refine ⟨16959586955689254153921209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11306391303792836102614139 16959586955689254153921209)
            ·
              refine ⟨12719690216766940615440907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16959586955689254153921209 12719690216766940615440907)
              ·
                refine ⟨19079535325150410923161361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12719690216766940615440907 19079535325150410923161361)
                ·
                  refine ⟨14309651493862808192371021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19079535325150410923161361 14309651493862808192371021)
                  ·
                    refine ⟨5366119310198553072139133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14309651493862808192371021 5366119310198553072139133)
                    ·
                      refine ⟨2012294741324457402052175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5366119310198553072139133 2012294741324457402052175)
                      ·
                        rfl

theorem cell23_3918930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_3918930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3918930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3918930 prefixEnd_3918930 := by exact prefixLift 3918930
  have htrace : WordTrace (prefixWord ++ tailWord_3918930) baseStart_3918930 baseEnd_3918930 := by
    simpa [prefixWord, tailWord_3918930, baseEnd_3918930] using wordTrace_append hprefix tailTrace_3918930
  have hstable : (prefixWord ++ tailWord_3918930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918930).length < 2 ^ (prefixWord ++ tailWord_3918930).sum := by decide
  have hdescent : baseEnd_3918930 < baseStart_3918930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918953 : List Nat := [1, 2, 1, 1, 1, 6, 2, 1, 1, 3, 4]
def baseStart_3918953 : Nat := 118140960795 + 3918953 * 2 ^ 59
def prefixEnd_3918953 : Nat := 4983230072969 + 3 ^ 40 * 3918953 * 2
def baseEnd_3918953 : Nat := 2012306551379510812064569

theorem tailTrace_3918953 : CollatzResearch.WordTrace tailWord_3918953 prefixEnd_3918953 2012306551379510812064569 := by
  unfold tailWord_3918953
  simp only [CollatzResearch.WordTrace]
  refine ⟨142935958571310059731505513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95290639047540039821003675 142935958571310059731505513)
  ·
    refine ⟨107201968928482544798629135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142935958571310059731505513 107201968928482544798629135)
    ·
      refine ⟨160802953392723817197943703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107201968928482544798629135 160802953392723817197943703)
      ·
        refine ⟨241204430089085725796915555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160802953392723817197943703 241204430089085725796915555)
        ·
          refine ⟨361806645133628588695373333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241204430089085725796915555 361806645133628588695373333)
          ·
            refine ⟨16959686490638840095095625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 361806645133628588695373333 16959686490638840095095625)
            ·
              refine ⟨12719764867979130071321719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16959686490638840095095625 12719764867979130071321719)
              ·
                refine ⟨19079647301968695106982579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12719764867979130071321719 19079647301968695106982579)
                ·
                  refine ⟨28619470952953042660473869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19079647301968695106982579 28619470952953042660473869)
                  ·
                    refine ⟨10732301607357390997677701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28619470952953042660473869 10732301607357390997677701)
                    ·
                      refine ⟨2012306551379510812064569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10732301607357390997677701 2012306551379510812064569)
                      ·
                        rfl

theorem cell23_3918953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 3, 4].length) (baseStart_3918953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3918953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3918953 prefixEnd_3918953 := by exact prefixLift 3918953
  have htrace : WordTrace (prefixWord ++ tailWord_3918953) baseStart_3918953 baseEnd_3918953 := by
    simpa [prefixWord, tailWord_3918953, baseEnd_3918953] using wordTrace_append hprefix tailTrace_3918953
  have hstable : (prefixWord ++ tailWord_3918953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918953).length < 2 ^ (prefixWord ++ tailWord_3918953).sum := by decide
  have hdescent : baseEnd_3918953 < baseStart_3918953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919020 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 3]
def baseStart_3919020 : Nat := 118140960795 + 3919020 * 2 ^ 59
def prefixEnd_3919020 : Nat := 4983230072969 + 3 ^ 40 * 3919020 * 2
def baseEnd_3919020 : Nat := 2012340954583362049926761

theorem tailTrace_3919020 : CollatzResearch.WordTrace tailWord_3919020 prefixEnd_3919020 2012340954583362049926761 := by
  unfold tailWord_3919020
  simp only [CollatzResearch.WordTrace]
  refine ⟨71469201131033665087097257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95292268174711553449463009 71469201131033665087097257)
  ·
    refine ⟨53601900848275248815322943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71469201131033665087097257 53601900848275248815322943)
    ·
      refine ⟨80402851272412873222984415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53601900848275248815322943 80402851272412873222984415)
      ·
        refine ⟨120604276908619309834476623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80402851272412873222984415 120604276908619309834476623)
        ·
          refine ⟨180906415362928964751714935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120604276908619309834476623 180906415362928964751714935)
          ·
            refine ⟨271359623044393447127572403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180906415362928964751714935 271359623044393447127572403)
            ·
              refine ⟨407039434566590170691358605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271359623044393447127572403 407039434566590170691358605)
              ·
                refine ⟨152639787962471314009259477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 407039434566590170691358605 152639787962471314009259477)
                ·
                  refine ⟨3577495030370421422092019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 152639787962471314009259477 3577495030370421422092019)
                  ·
                    refine ⟨5366242545555632133138029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3577495030370421422092019 5366242545555632133138029)
                    ·
                      refine ⟨2012340954583362049926761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5366242545555632133138029 2012340954583362049926761)
                      ·
                        rfl

theorem cell23_3919020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 3].length) (baseStart_3919020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919020 prefixEnd_3919020 := by exact prefixLift 3919020
  have htrace : WordTrace (prefixWord ++ tailWord_3919020) baseStart_3919020 baseEnd_3919020 := by
    simpa [prefixWord, tailWord_3919020, baseEnd_3919020] using wordTrace_append hprefix tailTrace_3919020
  have hstable : (prefixWord ++ tailWord_3919020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919020).length < 2 ^ (prefixWord ++ tailWord_3919020).sum := by decide
  have hdescent : baseEnd_3919020 < baseStart_3919020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919054 : List Nat := [4, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3]
def baseStart_3919054 : Nat := 118140960795 + 3919054 * 2 ^ 59
def prefixEnd_3919054 : Nat := 4983230072969 + 3 ^ 40 * 3919054 * 2
def baseEnd_3919054 : Nat := 2012358412925614916901605

theorem tailTrace_3919054 : CollatzResearch.WordTrace tailWord_3919054 prefixEnd_3919054 2012358412925614916901605 := by
  unfold tailWord_3919054
  simp only [CollatzResearch.WordTrace]
  refine ⟨17867455292993019247616527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95293094895962769320621477 17867455292993019247616527)
  ·
    refine ⟨26801182939489528871424791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17867455292993019247616527 26801182939489528871424791)
    ·
      refine ⟨40201774409234293307137187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26801182939489528871424791 40201774409234293307137187)
      ·
        refine ⟨60302661613851439960705781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40201774409234293307137187 60302661613851439960705781)
        ·
          refine ⟨5653374526298572496316167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60302661613851439960705781 5653374526298572496316167)
          ·
            refine ⟨8480061789447858744474251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5653374526298572496316167 8480061789447858744474251)
            ·
              refine ⟨12720092684171788116711377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8480061789447858744474251 12720092684171788116711377)
              ·
                refine ⟨9540069513128841087533533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12720092684171788116711377 9540069513128841087533533)
                ·
                  refine ⟨3577526067423315407825075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9540069513128841087533533 3577526067423315407825075)
                  ·
                    refine ⟨5366289101134973111737613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3577526067423315407825075 5366289101134973111737613)
                    ·
                      refine ⟨2012358412925614916901605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5366289101134973111737613 2012358412925614916901605)
                      ·
                        rfl

theorem cell23_3919054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3].length) (baseStart_3919054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919054 prefixEnd_3919054 := by exact prefixLift 3919054
  have htrace : WordTrace (prefixWord ++ tailWord_3919054) baseStart_3919054 baseEnd_3919054 := by
    simpa [prefixWord, tailWord_3919054, baseEnd_3919054] using wordTrace_append hprefix tailTrace_3919054
  have hstable : (prefixWord ++ tailWord_3919054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919054).length < 2 ^ (prefixWord ++ tailWord_3919054).sum := by decide
  have hdescent : baseEnd_3919054 < baseStart_3919054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919080 : List Nat := [2, 1, 4, 1, 2, 1, 2, 3, 1, 1, 5]
def baseStart_3919080 : Nat := 118140960795 + 3919080 * 2 ^ 59
def prefixEnd_3919080 : Nat := 4983230072969 + 3 ^ 40 * 3919080 * 2
def baseEnd_3919080 : Nat := 2012371763422631815176485

theorem tailTrace_3919080 : CollatzResearch.WordTrace tailWord_3919080 prefixEnd_3919080 2012371763422631815176485 := by
  unfold tailWord_3919080
  simp only [CollatzResearch.WordTrace]
  refine ⟨71470295320924980210689347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95293727094566640280919129 71470295320924980210689347)
  ·
    refine ⟨107205442981387470316034021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71470295320924980210689347 107205442981387470316034021)
    ·
      refine ⟨20101020559010150684256379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107205442981387470316034021 20101020559010150684256379)
      ·
        refine ⟨30151530838515226026384569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20101020559010150684256379 30151530838515226026384569)
        ·
          refine ⟨22613648128886419519788427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30151530838515226026384569 22613648128886419519788427)
          ·
            refine ⟨33920472193329629279682641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22613648128886419519788427 33920472193329629279682641)
            ·
              refine ⟨25440354144997221959761981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33920472193329629279682641 25440354144997221959761981)
              ·
                refine ⟨9540132804373958234910743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25440354144997221959761981 9540132804373958234910743)
                ·
                  refine ⟨14310199206560937352366115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9540132804373958234910743 14310199206560937352366115)
                  ·
                    refine ⟨21465298809841406028549173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14310199206560937352366115 21465298809841406028549173)
                    ·
                      refine ⟨2012371763422631815176485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21465298809841406028549173 2012371763422631815176485)
                      ·
                        rfl

theorem cell23_3919080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_3919080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919080 prefixEnd_3919080 := by exact prefixLift 3919080
  have htrace : WordTrace (prefixWord ++ tailWord_3919080) baseStart_3919080 baseEnd_3919080 := by
    simpa [prefixWord, tailWord_3919080, baseEnd_3919080] using wordTrace_append hprefix tailTrace_3919080
  have hstable : (prefixWord ++ tailWord_3919080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919080).length < 2 ^ (prefixWord ++ tailWord_3919080).sum := by decide
  have hdescent : baseEnd_3919080 < baseStart_3919080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919083 : List Nat := [1, 1, 1, 1, 2, 7, 10]
def baseStart_3919083 : Nat := 118140960795 + 3919083 * 2 ^ 59
def prefixEnd_3919083 : Nat := 4983230072969 + 3 ^ 40 * 3919083 * 2
def baseEnd_3919083 : Nat := 24844114862525867943691

theorem tailTrace_3919083 : CollatzResearch.WordTrace tailWord_3919083 prefixEnd_3919083 24844114862525867943691 := by
  unfold tailWord_3919083
  simp only [CollatzResearch.WordTrace]
  refine ⟨142940700060839091933737903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95293800040559394622491935 142940700060839091933737903)
  ·
    refine ⟨214411050091258637900606855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142940700060839091933737903 214411050091258637900606855)
    ·
      refine ⟨321616575136887956850910283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214411050091258637900606855 321616575136887956850910283)
      ·
        refine ⟨482424862705331935276365425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321616575136887956850910283 482424862705331935276365425)
        ·
          refine ⟨361818647028998951457274069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 482424862705331935276365425 361818647028998951457274069)
          ·
            refine ⟨8480124539742162924779861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 361818647028998951457274069 8480124539742162924779861)
            ·
              refine ⟨24844114862525867943691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8480124539742162924779861 24844114862525867943691)
              ·
                rfl

theorem cell23_3919083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 10].length) (baseStart_3919083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919083 prefixEnd_3919083 := by exact prefixLift 3919083
  have htrace : WordTrace (prefixWord ++ tailWord_3919083) baseStart_3919083 baseEnd_3919083 := by
    simpa [prefixWord, tailWord_3919083, baseEnd_3919083] using wordTrace_append hprefix tailTrace_3919083
  have hstable : (prefixWord ++ tailWord_3919083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919083).length < 2 ^ (prefixWord ++ tailWord_3919083).sum := by decide
  have hdescent : baseEnd_3919083 < baseStart_3919083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919087 : List Nat := [1, 1, 2, 1, 7, 1, 1, 1, 4, 4]
def baseStart_3919087 : Nat := 118140960795 + 3919087 * 2 ^ 59
def prefixEnd_3919087 : Nat := 4983230072969 + 3 ^ 40 * 3919087 * 2
def baseEnd_3919087 : Nat := 670791785929071095929651

theorem tailTrace_3919087 : CollatzResearch.WordTrace tailWord_3919087 prefixEnd_3919087 670791785929071095929651 := by
  unfold tailWord_3919087
  simp only [CollatzResearch.WordTrace]
  refine ⟨142940845952824600616883515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95293897301883067077922343 142940845952824600616883515)
  ·
    refine ⟨214411268929236900925325273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142940845952824600616883515 214411268929236900925325273)
    ·
      refine ⟨160808451696927675693993955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214411268929236900925325273 160808451696927675693993955)
      ·
        refine ⟨241212677545391513540990933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160808451696927675693993955 241212677545391513540990933)
        ·
          refine ⟨5653422129970113598616975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 241212677545391513540990933 5653422129970113598616975)
          ·
            refine ⟨8480133194955170397925463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5653422129970113598616975 8480133194955170397925463)
            ·
              refine ⟨12720199792432755596888195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8480133194955170397925463 12720199792432755596888195)
              ·
                refine ⟨19080299688649133395332293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12720199792432755596888195 19080299688649133395332293)
                ·
                  refine ⟨3577556191621712511624805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19080299688649133395332293 3577556191621712511624805)
                  ·
                    refine ⟨670791785929071095929651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3577556191621712511624805 670791785929071095929651)
                    ·
                      rfl

theorem cell23_3919087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 4, 4].length) (baseStart_3919087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919087 prefixEnd_3919087 := by exact prefixLift 3919087
  have htrace : WordTrace (prefixWord ++ tailWord_3919087) baseStart_3919087 baseEnd_3919087 := by
    simpa [prefixWord, tailWord_3919087, baseEnd_3919087] using wordTrace_append hprefix tailTrace_3919087
  have hstable : (prefixWord ++ tailWord_3919087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919087).length < 2 ^ (prefixWord ++ tailWord_3919087).sum := by decide
  have hdescent : baseEnd_3919087 < baseStart_3919087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919107 : List Nat := [1, 1, 1, 3, 2, 6, 1, 1, 1, 2, 4]
def baseStart_3919107 : Nat := 118140960795 + 3919107 * 2 ^ 59
def prefixEnd_3919107 : Nat := 4983230072969 + 3 ^ 40 * 3919107 * 2
def baseEnd_3919107 : Nat := 2012385627400303209538861

theorem tailTrace_3919107 : CollatzResearch.WordTrace tailWord_3919107 prefixEnd_3919107 2012385627400303209538861 := by
  unfold tailWord_3919107
  simp only [CollatzResearch.WordTrace]
  refine ⟨142941575412752144032611575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95294383608501429355074383 142941575412752144032611575)
  ·
    refine ⟨214412363119128216048917363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142941575412752144032611575 214412363119128216048917363)
    ·
      refine ⟨321618544678692324073376045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214412363119128216048917363 321618544678692324073376045)
      ·
        refine ⟨120606954254509621527516017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321618544678692324073376045 120606954254509621527516017)
        ·
          refine ⟨90455215690882216145637013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120606954254509621527516017 90455215690882216145637013)
          ·
            refine ⟨4240088235510103881826735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 90455215690882216145637013 4240088235510103881826735)
            ·
              refine ⟨6360132353265155822740103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4240088235510103881826735 6360132353265155822740103)
              ·
                refine ⟨9540198529897733734110155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6360132353265155822740103 9540198529897733734110155)
                ·
                  refine ⟨14310297794846600601165233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9540198529897733734110155 14310297794846600601165233)
                  ·
                    refine ⟨10732723346134950450873925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14310297794846600601165233 10732723346134950450873925)
                    ·
                      refine ⟨2012385627400303209538861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10732723346134950450873925 2012385627400303209538861)
                      ·
                        rfl

theorem cell23_3919107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 2, 4].length) (baseStart_3919107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919107 prefixEnd_3919107 := by exact prefixLift 3919107
  have htrace : WordTrace (prefixWord ++ tailWord_3919107) baseStart_3919107 baseEnd_3919107 := by
    simpa [prefixWord, tailWord_3919107, baseEnd_3919107] using wordTrace_append hprefix tailTrace_3919107
  have hstable : (prefixWord ++ tailWord_3919107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919107).length < 2 ^ (prefixWord ++ tailWord_3919107).sum := by decide
  have hdescent : baseEnd_3919107 < baseStart_3919107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919122 : List Nat := [3, 2, 4, 2, 2, 1, 1, 3, 1, 1, 3]
def baseStart_3919122 : Nat := 118140960795 + 3919122 * 2 ^ 59
def prefixEnd_3919122 : Nat := 4983230072969 + 3 ^ 40 * 3919122 * 2
def baseEnd_3919122 : Nat := 2012393329610120650851293

theorem tailTrace_3919122 : CollatzResearch.WordTrace tailWord_3919122 prefixEnd_3919122 2012393329610120650851293 := by
  unfold tailWord_3919122
  simp only [CollatzResearch.WordTrace]
  refine ⟨35735530626924450398601905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95294748338465201062938413 35735530626924450398601905)
  ·
    refine ⟨26801647970193337798951429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35735530626924450398601905 26801647970193337798951429)
    ·
      refine ⟨5025308994411250837303393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26801647970193337798951429 5025308994411250837303393)
      ·
        refine ⟨3768981745808438127977545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5025308994411250837303393 3768981745808438127977545)
        ·
          refine ⟨2826736309356328595983159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3768981745808438127977545 2826736309356328595983159)
          ·
            refine ⟨4240104464034492893974739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2826736309356328595983159 4240104464034492893974739)
            ·
              refine ⟨6360156696051739340962109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4240104464034492893974739 6360156696051739340962109)
              ·
                refine ⟨2385058761019402252860791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6360156696051739340962109 2385058761019402252860791)
                ·
                  refine ⟨3577588141529103379291187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2385058761019402252860791 3577588141529103379291187)
                  ·
                    refine ⟨5366382212293655068936781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3577588141529103379291187 5366382212293655068936781)
                    ·
                      refine ⟨2012393329610120650851293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5366382212293655068936781 2012393329610120650851293)
                      ·
                        rfl

theorem cell23_3919122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_3919122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919122 prefixEnd_3919122 := by exact prefixLift 3919122
  have htrace : WordTrace (prefixWord ++ tailWord_3919122) baseStart_3919122 baseEnd_3919122 := by
    simpa [prefixWord, tailWord_3919122, baseEnd_3919122] using wordTrace_append hprefix tailTrace_3919122
  have hstable : (prefixWord ++ tailWord_3919122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919122).length < 2 ^ (prefixWord ++ tailWord_3919122).sum := by decide
  have hdescent : baseEnd_3919122 < baseStart_3919122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919127 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 6, 1, 3]
def baseStart_3919127 : Nat := 118140960795 + 3919127 * 2 ^ 59
def prefixEnd_3919127 : Nat := 4983230072969 + 3 ^ 40 * 3919127 * 2
def baseEnd_3919127 : Nat := 2012395897013393131288769

theorem tailTrace_3919127 : CollatzResearch.WordTrace tailWord_3919127 prefixEnd_3919127 2012395897013393131288769 := by
  unfold tailWord_3919127
  simp only [CollatzResearch.WordTrace]
  refine ⟨142942304872679687448339635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95294869915119791632226423 142942304872679687448339635)
  ·
    refine ⟨214413457309019531172509453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142942304872679687448339635 214413457309019531172509453)
    ·
      refine ⟨80405046490882324189691045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214413457309019531172509453 80405046490882324189691045)
      ·
        refine ⟨15075946217040435785567071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80405046490882324189691045 15075946217040435785567071)
        ·
          refine ⟨22613919325560653678350607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15075946217040435785567071 22613919325560653678350607)
          ·
            refine ⟨33920878988340980517525911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22613919325560653678350607 33920878988340980517525911)
            ·
              refine ⟨50881318482511470776288867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33920878988340980517525911 50881318482511470776288867)
              ·
                refine ⟨76321977723767206164433301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50881318482511470776288867 76321977723767206164433301)
                ·
                  refine ⟨3577592705801587788957811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 76321977723767206164433301 3577592705801587788957811)
                  ·
                    refine ⟨5366389058702381683436717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3577592705801587788957811 5366389058702381683436717)
                    ·
                      refine ⟨2012395897013393131288769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5366389058702381683436717 2012395897013393131288769)
                      ·
                        rfl

theorem cell23_3919127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_3919127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919127 prefixEnd_3919127 := by exact prefixLift 3919127
  have htrace : WordTrace (prefixWord ++ tailWord_3919127) baseStart_3919127 baseEnd_3919127 := by
    simpa [prefixWord, tailWord_3919127, baseEnd_3919127] using wordTrace_append hprefix tailTrace_3919127
  have hstable : (prefixWord ++ tailWord_3919127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919127).length < 2 ^ (prefixWord ++ tailWord_3919127).sum := by decide
  have hdescent : baseEnd_3919127 < baseStart_3919127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919128 : List Nat := [2, 1, 2, 3, 1, 5, 1, 3, 1, 2, 2]
def baseStart_3919128 : Nat := 118140960795 + 3919128 * 2 ^ 59
def prefixEnd_3919128 : Nat := 4983230072969 + 3 ^ 40 * 3919128 * 2
def baseEnd_3919128 : Nat := 2012396410494047627376265

theorem tailTrace_3919128 : CollatzResearch.WordTrace tailWord_3919128 prefixEnd_3919128 2012396410494047627376265 := by
  unfold tailWord_3919128
  simp only [CollatzResearch.WordTrace]
  refine ⟨71471170672838032309563019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95294894230450709746084025 71471170672838032309563019)
  ·
    refine ⟨107206756009257048464344529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71471170672838032309563019 107206756009257048464344529)
    ·
      refine ⟨80405067006942786348258397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107206756009257048464344529 80405067006942786348258397)
      ·
        refine ⟨30151900127603544880596899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80405067006942786348258397 30151900127603544880596899)
        ·
          refine ⟨45227850191405317320895349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30151900127603544880596899 45227850191405317320895349)
          ·
            refine ⟨4240110955444248498833939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45227850191405317320895349 4240110955444248498833939)
            ·
              refine ⟨6360166433166372748250909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4240110955444248498833939 6360166433166372748250909)
              ·
                refine ⟨2385062412437389780594091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6360166433166372748250909 2385062412437389780594091)
                ·
                  refine ⟨3577593618656084670891137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2385062412437389780594091 3577593618656084670891137)
                  ·
                    refine ⟨2683195213992063503168353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3577593618656084670891137 2683195213992063503168353)
                    ·
                      refine ⟨2012396410494047627376265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2683195213992063503168353 2012396410494047627376265)
                      ·
                        rfl

theorem cell23_3919128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 3, 1, 2, 2].length) (baseStart_3919128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919128 prefixEnd_3919128 := by exact prefixLift 3919128
  have htrace : WordTrace (prefixWord ++ tailWord_3919128) baseStart_3919128 baseEnd_3919128 := by
    simpa [prefixWord, tailWord_3919128, baseEnd_3919128] using wordTrace_append hprefix tailTrace_3919128
  have hstable : (prefixWord ++ tailWord_3919128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919128).length < 2 ^ (prefixWord ++ tailWord_3919128).sum := by decide
  have hdescent : baseEnd_3919128 < baseStart_3919128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919134 : List Nat := [4, 3, 2, 1, 2, 2, 9]
def baseStart_3919134 : Nat := 118140960795 + 3919134 * 2 ^ 59
def prefixEnd_3919134 : Nat := 4983230072969 + 3 ^ 40 * 3919134 * 2
def baseEnd_3919134 : Nat := 24844438165160180295077

theorem tailTrace_3919134 : CollatzResearch.WordTrace tailWord_3919134 prefixEnd_3919134 24844438165160180295077 := by
  unfold tailWord_3919134
  simp only [CollatzResearch.WordTrace]
  refine ⟨17867820022956790955480557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95295040122436218429229637 17867820022956790955480557)
  ·
    refine ⟨6700432508608796608305209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17867820022956790955480557 6700432508608796608305209)
    ·
      refine ⟨5025324381456597456228907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6700432508608796608305209 5025324381456597456228907)
      ·
        refine ⟨7537986572184896184343361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5025324381456597456228907 7537986572184896184343361)
        ·
          refine ⟨5653489929138672138257521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7537986572184896184343361 5653489929138672138257521)
          ·
            refine ⟨4240117446854004103693141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5653489929138672138257521 4240117446854004103693141)
            ·
              refine ⟨24844438165160180295077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4240117446854004103693141 24844438165160180295077)
              ·
                rfl

theorem cell23_3919134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 9].length) (baseStart_3919134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919134 prefixEnd_3919134 := by exact prefixLift 3919134
  have htrace : WordTrace (prefixWord ++ tailWord_3919134) baseStart_3919134 baseEnd_3919134 := by
    simpa [prefixWord, tailWord_3919134, baseEnd_3919134] using wordTrace_append hprefix tailTrace_3919134
  have hstable : (prefixWord ++ tailWord_3919134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919134).length < 2 ^ (prefixWord ++ tailWord_3919134).sum := by decide
  have hdescent : baseEnd_3919134 < baseStart_3919134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919137 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 5, 3, 2]
def baseStart_3919137 : Nat := 118140960795 + 3919137 * 2 ^ 59
def prefixEnd_3919137 : Nat := 4983230072969 + 3 ^ 40 * 3919137 * 2
def baseEnd_3919137 : Nat := 2012401031819938092163723

theorem tailTrace_3919137 : CollatzResearch.WordTrace tailWord_3919137 prefixEnd_3919137 2012401031819938092163723 := by
  unfold tailWord_3919137
  simp only [CollatzResearch.WordTrace]
  refine ⟨142942669602643459156203665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95295113068428972770802443 142942669602643459156203665)
  ·
    refine ⟨107207002201982594367152749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142942669602643459156203665 107207002201982594367152749)
    ·
      refine ⟨40202625825743472887682281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107207002201982594367152749 40202625825743472887682281)
      ·
        refine ⟨30151969369307604665761711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40202625825743472887682281 30151969369307604665761711)
        ·
          refine ⟨45227954053961406998642567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30151969369307604665761711 45227954053961406998642567)
          ·
            refine ⟨67841931080942110497963851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45227954053961406998642567 67841931080942110497963851)
            ·
              refine ⟨101762896621413165746945777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67841931080942110497963851 101762896621413165746945777)
              ·
                refine ⟨76322172466059874310209333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101762896621413165746945777 76322172466059874310209333)
                ·
                  refine ⟨7155203668693113216582125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76322172466059874310209333 7155203668693113216582125)
                  ·
                    refine ⟨2683201375759917456218297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7155203668693113216582125 2683201375759917456218297)
                    ·
                      refine ⟨2012401031819938092163723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2683201375759917456218297 2012401031819938092163723)
                      ·
                        rfl

theorem cell23_3919137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_3919137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919137 prefixEnd_3919137 := by exact prefixLift 3919137
  have htrace : WordTrace (prefixWord ++ tailWord_3919137) baseStart_3919137 baseEnd_3919137 := by
    simpa [prefixWord, tailWord_3919137, baseEnd_3919137] using wordTrace_append hprefix tailTrace_3919137
  have hstable : (prefixWord ++ tailWord_3919137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919137).length < 2 ^ (prefixWord ++ tailWord_3919137).sum := by decide
  have hdescent : baseEnd_3919137 < baseStart_3919137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919140 : List Nat := [2, 3, 1, 3, 1, 1, 1, 2, 2, 2, 5]
def baseStart_3919140 : Nat := 118140960795 + 3919140 * 2 ^ 59
def prefixEnd_3919140 : Nat := 4983230072969 + 3 ^ 40 * 3919140 * 2
def baseEnd_3919140 : Nat := 2012402572261901580426209

theorem tailTrace_3919140 : CollatzResearch.WordTrace tailWord_3919140 prefixEnd_3919140 2012402572261901580426209 := by
  unfold tailWord_3919140
  simp only [CollatzResearch.WordTrace]
  refine ⟨71471389510816295334281437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95295186014421727112375249 71471389510816295334281437)
  ·
    refine ⟨26801771066556110750355539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71471389510816295334281437 26801771066556110750355539)
    ·
      refine ⟨40202656599834166125533309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26801771066556110750355539 40202656599834166125533309)
      ·
        refine ⟨15075996224937812297074991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40202656599834166125533309 15075996224937812297074991)
        ·
          refine ⟨22613994337406718445612487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15075996224937812297074991 22613994337406718445612487)
          ·
            refine ⟨33920991506110077668418731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22613994337406718445612487 33920991506110077668418731)
            ·
              refine ⟨50881487259165116502628097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33920991506110077668418731 50881487259165116502628097)
              ·
                refine ⟨38161115444373837376971073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50881487259165116502628097 38161115444373837376971073)
                ·
                  refine ⟨28620836583280378032728305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38161115444373837376971073 28620836583280378032728305)
                  ·
                    refine ⟨21465627437460283524546229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28620836583280378032728305 21465627437460283524546229)
                    ·
                      refine ⟨2012402572261901580426209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21465627437460283524546229 2012402572261901580426209)
                      ·
                        rfl

theorem cell23_3919140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_3919140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919140 prefixEnd_3919140 := by exact prefixLift 3919140
  have htrace : WordTrace (prefixWord ++ tailWord_3919140) baseStart_3919140 baseEnd_3919140 := by
    simpa [prefixWord, tailWord_3919140, baseEnd_3919140] using wordTrace_append hprefix tailTrace_3919140
  have hstable : (prefixWord ++ tailWord_3919140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919140).length < 2 ^ (prefixWord ++ tailWord_3919140).sum := by decide
  have hdescent : baseEnd_3919140 < baseStart_3919140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919144 : List Nat := [2, 1, 5, 1, 2, 1, 2, 1, 4, 1, 3]
def baseStart_3919144 : Nat := 118140960795 + 3919144 * 2 ^ 59
def prefixEnd_3919144 : Nat := 4983230072969 + 3 ^ 40 * 3919144 * 2
def baseEnd_3919144 : Nat := 2012404626184519564776191

theorem tailTrace_3919144 : CollatzResearch.WordTrace tailWord_3919144 prefixEnd_3919144 2012404626184519564776191 := by
  unfold tailWord_3919144
  simp only [CollatzResearch.WordTrace]
  refine ⟨71471462456809049675854243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95295283275745399567805657 71471462456809049675854243)
  ·
    refine ⟨107207193685213574513781365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71471462456809049675854243 107207193685213574513781365)
    ·
      refine ⟨10050674407988772610667003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107207193685213574513781365 10050674407988772610667003)
      ·
        refine ⟨15076011611983158916000505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10050674407988772610667003 15076011611983158916000505)
        ·
          refine ⟨11307008708987369187000379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15076011611983158916000505 11307008708987369187000379)
          ·
            refine ⟨16960513063481053780500569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11307008708987369187000379 16960513063481053780500569)
            ·
              refine ⟨12720384797610790335375427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16960513063481053780500569 12720384797610790335375427)
              ·
                refine ⟨19080577196416185503063141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12720384797610790335375427 19080577196416185503063141)
                ·
                  refine ⟨3577608224328034781824339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19080577196416185503063141 3577608224328034781824339)
                  ·
                    refine ⟨5366412336492052172736509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3577608224328034781824339 5366412336492052172736509)
                    ·
                      refine ⟨2012404626184519564776191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5366412336492052172736509 2012404626184519564776191)
                      ·
                        rfl

theorem cell23_3919144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_3919144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919144 prefixEnd_3919144 := by exact prefixLift 3919144
  have htrace : WordTrace (prefixWord ++ tailWord_3919144) baseStart_3919144 baseEnd_3919144 := by
    simpa [prefixWord, tailWord_3919144, baseEnd_3919144] using wordTrace_append hprefix tailTrace_3919144
  have hstable : (prefixWord ++ tailWord_3919144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919144).length < 2 ^ (prefixWord ++ tailWord_3919144).sum := by decide
  have hdescent : baseEnd_3919144 < baseStart_3919144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919161 : List Nat := [1, 2, 1, 6, 2, 1, 1, 3, 2, 1, 3]
def baseStart_3919161 : Nat := 118140960795 + 3919161 * 2 ^ 59
def prefixEnd_3919161 : Nat := 4983230072969 + 3 ^ 40 * 3919161 * 2
def baseEnd_3919161 : Nat := 2012413355355645998263613

theorem tailTrace_3919161 : CollatzResearch.WordTrace tailWord_3919161 prefixEnd_3919161 2012413355355645998263613 := by
  unfold tailWord_3919161
  simp only [CollatzResearch.WordTrace]
  refine ⟨142943544954556511255077337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95295696636371007503384891 142943544954556511255077337)
  ·
    refine ⟨107207658715917383441308003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142943544954556511255077337 107207658715917383441308003)
    ·
      refine ⟨160811488073876075161962005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107207658715917383441308003 160811488073876075161962005)
      ·
        refine ⟨7538038503462941023216969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 160811488073876075161962005 7538038503462941023216969)
        ·
          refine ⟨5653528877597205767412727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7538038503462941023216969 5653528877597205767412727)
          ·
            refine ⟨8480293316395808651119091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5653528877597205767412727 8480293316395808651119091)
            ·
              refine ⟨12720439974593712976678637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8480293316395808651119091 12720439974593712976678637)
              ·
                refine ⟨4770164990472642366254489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12720439974593712976678637 4770164990472642366254489)
                ·
                  refine ⟨3577623742854481774690867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4770164990472642366254489 3577623742854481774690867)
                  ·
                    refine ⟨5366435614281722662036301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3577623742854481774690867 5366435614281722662036301)
                    ·
                      refine ⟨2012413355355645998263613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5366435614281722662036301 2012413355355645998263613)
                      ·
                        rfl

theorem cell23_3919161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_3919161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919161 prefixEnd_3919161 := by exact prefixLift 3919161
  have htrace : WordTrace (prefixWord ++ tailWord_3919161) baseStart_3919161 baseEnd_3919161 := by
    simpa [prefixWord, tailWord_3919161, baseEnd_3919161] using wordTrace_append hprefix tailTrace_3919161
  have hstable : (prefixWord ++ tailWord_3919161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919161).length < 2 ^ (prefixWord ++ tailWord_3919161).sum := by decide
  have hdescent : baseEnd_3919161 < baseStart_3919161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919227 : List Nat := [1, 1, 1, 1, 1, 6, 1, 2, 2, 5, 2]
def baseStart_3919227 : Nat := 118140960795 + 3919227 * 2 ^ 59
def prefixEnd_3919227 : Nat := 4983230072969 + 3 ^ 40 * 3919227 * 2
def baseEnd_3919227 : Nat := 2012447245078842740038309

theorem tailTrace_3919227 : CollatzResearch.WordTrace tailWord_3919227 prefixEnd_3919227 2012447245078842740038309 := by
  unfold tailWord_3919227
  simp only [CollatzResearch.WordTrace]
  refine ⟨142945952172317404526979935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95297301448211603017986623 142945952172317404526979935)
  ·
    refine ⟨214418928258476106790469903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142945952172317404526979935 214418928258476106790469903)
    ·
      refine ⟨321628392387714160185704855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214418928258476106790469903 321628392387714160185704855)
      ·
        refine ⟨482442588581571240278557283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321628392387714160185704855 482442588581571240278557283)
        ·
          refine ⟨723663882872356860417835925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482442588581571240278557283 723663882872356860417835925)
          ·
            refine ⟨33921744509641727832086059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 723663882872356860417835925 33921744509641727832086059)
            ·
              refine ⟨50882616764462591748129089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33921744509641727832086059 50882616764462591748129089)
              ·
                refine ⟨38161962573346943811096817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50882616764462591748129089 38161962573346943811096817)
                ·
                  refine ⟨28621471930010207858322613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38161962573346943811096817 28621471930010207858322613)
                  ·
                    refine ⟨2683262993438456986717745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28621471930010207858322613 2683262993438456986717745)
                    ·
                      refine ⟨2012447245078842740038309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2683262993438456986717745 2012447245078842740038309)
                      ·
                        rfl

theorem cell23_3919227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 5, 2].length) (baseStart_3919227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919227 prefixEnd_3919227 := by exact prefixLift 3919227
  have htrace : WordTrace (prefixWord ++ tailWord_3919227) baseStart_3919227 baseEnd_3919227 := by
    simpa [prefixWord, tailWord_3919227, baseEnd_3919227] using wordTrace_append hprefix tailTrace_3919227
  have hstable : (prefixWord ++ tailWord_3919227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919227).length < 2 ^ (prefixWord ++ tailWord_3919227).sum := by decide
  have hdescent : baseEnd_3919227 < baseStart_3919227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919237 : List Nat := [1, 3, 1, 1, 3, 1, 5, 1, 2, 5]
def baseStart_3919237 : Nat := 118140960795 + 3919237 * 2 ^ 59
def prefixEnd_3919237 : Nat := 4983230072969 + 3 ^ 40 * 3919237 * 2
def baseEnd_3919237 : Nat := 670817459961795900304421

theorem tailTrace_3919237 : CollatzResearch.WordTrace tailWord_3919237 prefixEnd_3919237 670817459961795900304421 := by
  unfold tailWord_3919237
  simp only [CollatzResearch.WordTrace]
  refine ⟨142946316902281176234843965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95297544601520784156562643 142946316902281176234843965)
  ·
    refine ⟨53604868838355441088066487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142946316902281176234843965 53604868838355441088066487)
    ·
      refine ⟨80407303257533161632099731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53604868838355441088066487 80407303257533161632099731)
      ·
        refine ⟨120610954886299742448149597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80407303257533161632099731 120610954886299742448149597)
        ·
          refine ⟨45229108082362403418056099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120610954886299742448149597 45229108082362403418056099)
          ·
            refine ⟨67843662123543605127084149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45229108082362403418056099 67843662123543605127084149)
            ·
              refine ⟨6360343324082212980664139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67843662123543605127084149 6360343324082212980664139)
              ·
                refine ⟨9540514986123319470996209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6360343324082212980664139 9540514986123319470996209)
                ·
                  refine ⟨7155386239592489603247157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9540514986123319470996209 7155386239592489603247157)
                  ·
                    refine ⟨670817459961795900304421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7155386239592489603247157 670817459961795900304421)
                    ·
                      rfl

theorem cell23_3919237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 5].length) (baseStart_3919237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919237 prefixEnd_3919237 := by exact prefixLift 3919237
  have htrace : WordTrace (prefixWord ++ tailWord_3919237) baseStart_3919237 baseEnd_3919237 := by
    simpa [prefixWord, tailWord_3919237, baseEnd_3919237] using wordTrace_append hprefix tailTrace_3919237
  have hstable : (prefixWord ++ tailWord_3919237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919237).length < 2 ^ (prefixWord ++ tailWord_3919237).sum := by decide
  have hdescent : baseEnd_3919237 < baseStart_3919237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919290 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 2, 1, 9]
def baseStart_3919290 : Nat := 118140960795 + 3919290 * 2 ^ 59
def prefixEnd_3919290 : Nat := 4983230072969 + 3 ^ 40 * 3919290 * 2
def baseEnd_3919290 : Nat := 2012479594360075993550519

theorem tailTrace_3919290 : CollatzResearch.WordTrace tailWord_3919290 prefixEnd_3919290 2012479594360075993550519 := by
  unfold tailWord_3919290
  simp only [CollatzResearch.WordTrace]
  refine ⟨35737062492772291571630831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95298833314059444191015549 35737062492772291571630831)
  ·
    refine ⟨53605593739158437357446247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35737062492772291571630831 53605593739158437357446247)
    ·
      refine ⟨80408390608737656036169371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53605593739158437357446247 80408390608737656036169371)
      ·
        refine ⟨120612585913106484054254057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80408390608737656036169371 120612585913106484054254057)
        ·
          refine ⟨90459439434829863040690543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120612585913106484054254057 90459439434829863040690543)
          ·
            refine ⟨135689159152244794561035815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90459439434829863040690543 135689159152244794561035815)
            ·
              refine ⟨203533738728367191841553723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135689159152244794561035815 203533738728367191841553723)
              ·
                refine ⟨305300608092550787762330585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203533738728367191841553723 305300608092550787762330585)
                ·
                  refine ⟨228975456069413090821747939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 305300608092550787762330585 228975456069413090821747939)
                  ·
                    refine ⟨343463184104119636232621909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 228975456069413090821747939 343463184104119636232621909)
                    ·
                      refine ⟨2012479594360075993550519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 343463184104119636232621909 2012479594360075993550519)
                      ·
                        rfl

theorem cell23_3919290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_3919290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919290 prefixEnd_3919290 := by exact prefixLift 3919290
  have htrace : WordTrace (prefixWord ++ tailWord_3919290) baseStart_3919290 baseEnd_3919290 := by
    simpa [prefixWord, tailWord_3919290, baseEnd_3919290] using wordTrace_append hprefix tailTrace_3919290
  have hstable : (prefixWord ++ tailWord_3919290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919290).length < 2 ^ (prefixWord ++ tailWord_3919290).sum := by decide
  have hdescent : baseEnd_3919290 < baseStart_3919290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919294 : List Nat := [4, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3]
def baseStart_3919294 : Nat := 118140960795 + 3919294 * 2 ^ 59
def prefixEnd_3919294 : Nat := 4983230072969 + 3 ^ 40 * 3919294 * 2
def baseEnd_3919294 : Nat := 2012481648282693977900501

theorem tailTrace_3919294 : CollatzResearch.WordTrace tailWord_3919294 prefixEnd_3919294 2012481648282693977900501 := by
  unfold tailWord_3919294
  simp only [CollatzResearch.WordTrace]
  refine ⟨17868549482884334371208617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95298930575383116646445957 17868549482884334371208617)
  ·
    refine ⟨13401412112163250778406463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17868549482884334371208617 13401412112163250778406463)
    ·
      refine ⟨20102118168244876167609695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13401412112163250778406463 20102118168244876167609695)
      ·
        refine ⟨30153177252367314251414543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20102118168244876167609695 30153177252367314251414543)
        ·
          refine ⟨45229765878550971377121815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30153177252367314251414543 45229765878550971377121815)
          ·
            refine ⟨67844648817826457065682723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45229765878550971377121815 67844648817826457065682723)
            ·
              refine ⟨101766973226739685598524085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67844648817826457065682723 101766973226739685598524085)
              ·
                refine ⟨9540653740006845524861633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101766973226739685598524085 9540653740006845524861633)
                ·
                  refine ⟨7155490305005134143646225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9540653740006845524861633 7155490305005134143646225)
                  ·
                    refine ⟨5366617728753850607734669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7155490305005134143646225 5366617728753850607734669)
                    ·
                      refine ⟨2012481648282693977900501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5366617728753850607734669 2012481648282693977900501)
                      ·
                        rfl

theorem cell23_3919294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_3919294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919294 prefixEnd_3919294 := by exact prefixLift 3919294
  have htrace : WordTrace (prefixWord ++ tailWord_3919294) baseStart_3919294 baseEnd_3919294 := by
    simpa [prefixWord, tailWord_3919294, baseEnd_3919294] using wordTrace_append hprefix tailTrace_3919294
  have hstable : (prefixWord ++ tailWord_3919294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919294).length < 2 ^ (prefixWord ++ tailWord_3919294).sum := by decide
  have hdescent : baseEnd_3919294 < baseStart_3919294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919318 : List Nat := [5, 2, 1, 1, 1, 4, 1, 1, 3, 4]
def baseStart_3919318 : Nat := 118140960795 + 3919318 * 2 ^ 59
def prefixEnd_3919318 : Nat := 4983230072969 + 3 ^ 40 * 3919318 * 2
def baseEnd_3919318 : Nat := 670831323939467294666797

theorem tailTrace_3919318 : CollatzResearch.WordTrace tailWord_3919318 prefixEnd_3919318 670831323939467294666797 := by
  unfold tailWord_3919318
  simp only [CollatzResearch.WordTrace]
  refine ⟨8934329450936732941783913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95299514143325151379028405 8934329450936732941783913)
  ·
    refine ⟨6700747088202549706337935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8934329450936732941783913 6700747088202549706337935)
    ·
      refine ⟨10051120632303824559506903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6700747088202549706337935 10051120632303824559506903)
      ·
        refine ⟨15076680948455736839260355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10051120632303824559506903 15076680948455736839260355)
        ·
          refine ⟨22615021422683605258890533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15076680948455736839260355 22615021422683605258890533)
          ·
            refine ⟨4240316516753175986041975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22615021422683605258890533 4240316516753175986041975)
            ·
              refine ⟨6360474775129763979062963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4240316516753175986041975 6360474775129763979062963)
              ·
                refine ⟨9540712162694645968594445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6360474775129763979062963 9540712162694645968594445)
                ·
                  refine ⟨3577767061010492238222917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9540712162694645968594445 3577767061010492238222917)
                  ·
                    refine ⟨670831323939467294666797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3577767061010492238222917 670831323939467294666797)
                    ·
                      rfl

theorem cell23_3919318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_3919318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919318 prefixEnd_3919318 := by exact prefixLift 3919318
  have htrace : WordTrace (prefixWord ++ tailWord_3919318) baseStart_3919318 baseEnd_3919318 := by
    simpa [prefixWord, tailWord_3919318, baseEnd_3919318] using wordTrace_append hprefix tailTrace_3919318
  have hstable : (prefixWord ++ tailWord_3919318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919318).length < 2 ^ (prefixWord ++ tailWord_3919318).sum := by decide
  have hdescent : baseEnd_3919318 < baseStart_3919318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919327 : List Nat := [1, 1, 2, 3, 3, 1, 2, 2, 3, 5]
def baseStart_3919327 : Nat := 118140960795 + 3919327 * 2 ^ 59
def prefixEnd_3919327 : Nat := 4983230072969 + 3 ^ 40 * 3919327 * 2
def baseEnd_3919327 : Nat := 670832864381430782929283

theorem tailTrace_3919327 : CollatzResearch.WordTrace tailWord_3919327 prefixEnd_3919327 670832864381430782929283 := by
  unfold tailWord_3919327
  simp only [CollatzResearch.WordTrace]
  refine ⟨142949599471955121605620235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95299732981303414403746823 142949599471955121605620235)
  ·
    refine ⟨214424399207932682408430353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142949599471955121605620235 214424399207932682408430353)
    ·
      refine ⟨160818299405949511806322765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214424399207932682408430353 160818299405949511806322765)
      ·
        refine ⟨60306862277231066927371037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160818299405949511806322765 60306862277231066927371037)
        ·
          refine ⟨22615073353961650097764139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60306862277231066927371037 22615073353961650097764139)
          ·
            refine ⟨33922610030942475146646209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22615073353961650097764139 33922610030942475146646209)
            ·
              refine ⟨25441957523206856359984657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33922610030942475146646209 25441957523206856359984657)
              ·
                refine ⟨19081468142405142269988493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25441957523206856359984657 19081468142405142269988493)
                ·
                  refine ⟨7155550553401928351245685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19081468142405142269988493 7155550553401928351245685)
                  ·
                    refine ⟨670832864381430782929283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7155550553401928351245685 670832864381430782929283)
                    ·
                      rfl

theorem cell23_3919327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 5].length) (baseStart_3919327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919327 prefixEnd_3919327 := by exact prefixLift 3919327
  have htrace : WordTrace (prefixWord ++ tailWord_3919327) baseStart_3919327 baseEnd_3919327 := by
    simpa [prefixWord, tailWord_3919327, baseEnd_3919327] using wordTrace_append hprefix tailTrace_3919327
  have hstable : (prefixWord ++ tailWord_3919327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919327).length < 2 ^ (prefixWord ++ tailWord_3919327).sum := by decide
  have hdescent : baseEnd_3919327 < baseStart_3919327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919331 : List Nat := [1, 1, 1, 6, 2, 3, 2, 1, 6]
def baseStart_3919331 : Nat := 118140960795 + 3919331 * 2 ^ 59
def prefixEnd_3919331 : Nat := 4983230072969 + 3 ^ 40 * 3919331 * 2
def baseEnd_3919331 : Nat := 223611183007434481459759

theorem tailTrace_3919331 : CollatzResearch.WordTrace tailWord_3919331 prefixEnd_3919331 223611183007434481459759 := by
  unfold tailWord_3919331
  simp only [CollatzResearch.WordTrace]
  refine ⟨142949745363940630288765847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95299830242627086859177231 142949745363940630288765847)
  ·
    refine ⟨214424618045910945433148771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142949745363940630288765847 214424618045910945433148771)
    ·
      refine ⟨321636927068866418149723157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214424618045910945433148771 321636927068866418149723157)
      ·
        refine ⟨15076730956353113350768273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 321636927068866418149723157 15076730956353113350768273)
        ·
          refine ⟨11307548217264835013076205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15076730956353113350768273 11307548217264835013076205)
          ·
            refine ⟨4240330581474313129903577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11307548217264835013076205 4240330581474313129903577)
            ·
              refine ⟨3180247936105734847427683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4240330581474313129903577 3180247936105734847427683)
              ·
                refine ⟨4770371904158602271141525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3180247936105734847427683 4770371904158602271141525)
                ·
                  refine ⟨223611183007434481459759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4770371904158602271141525 223611183007434481459759)
                  ·
                    rfl

theorem cell23_3919331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 6].length) (baseStart_3919331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919331 prefixEnd_3919331 := by exact prefixLift 3919331
  have htrace : WordTrace (prefixWord ++ tailWord_3919331) baseStart_3919331 baseEnd_3919331 := by
    simpa [prefixWord, tailWord_3919331, baseEnd_3919331] using wordTrace_append hprefix tailTrace_3919331
  have hstable : (prefixWord ++ tailWord_3919331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919331).length < 2 ^ (prefixWord ++ tailWord_3919331).sum := by decide
  have hdescent : baseEnd_3919331 < baseStart_3919331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919344 : List Nat := [2, 1, 1, 1, 3, 4, 3, 2, 1, 5]
def baseStart_3919344 : Nat := 118140960795 + 3919344 * 2 ^ 59
def prefixEnd_3919344 : Nat := 4983230072969 + 3 ^ 40 * 3919344 * 2
def baseEnd_3919344 : Nat := 670835774105139594091757

theorem tailTrace_3919344 : CollatzResearch.WordTrace tailWord_3919344 prefixEnd_3919344 670835774105139594091757 := by
  unfold tailWord_3919344
  simp only [CollatzResearch.WordTrace]
  refine ⟨71475109756446766754494543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95300146341929022339326057 71475109756446766754494543)
  ·
    refine ⟨107212664634670150131741815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71475109756446766754494543 107212664634670150131741815)
    ·
      refine ⟨160818996952005225197612723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107212664634670150131741815 160818996952005225197612723)
      ·
        refine ⟨241228495428007837796419085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160818996952005225197612723 241228495428007837796419085)
        ·
          refine ⟨90460685785502939173657157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241228495428007837796419085 90460685785502939173657157)
          ·
            refine ⟨16961378584781801095060717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90460685785502939173657157 16961378584781801095060717)
            ·
              refine ⟨6360516969293175410647769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16961378584781801095060717 6360516969293175410647769)
              ·
                refine ⟨4770387726969881557985827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6360516969293175410647769 4770387726969881557985827)
                ·
                  refine ⟨7155581590454822336978741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4770387726969881557985827 7155581590454822336978741)
                  ·
                    refine ⟨670835774105139594091757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7155581590454822336978741 670835774105139594091757)
                    ·
                      rfl

theorem cell23_3919344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 1, 5].length) (baseStart_3919344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919344 prefixEnd_3919344 := by exact prefixLift 3919344
  have htrace : WordTrace (prefixWord ++ tailWord_3919344) baseStart_3919344 baseEnd_3919344 := by
    simpa [prefixWord, tailWord_3919344, baseEnd_3919344] using wordTrace_append hprefix tailTrace_3919344
  have hstable : (prefixWord ++ tailWord_3919344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919344).length < 2 ^ (prefixWord ++ tailWord_3919344).sum := by decide
  have hdescent : baseEnd_3919344 < baseStart_3919344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919357 : List Nat := [1, 4, 1, 1, 1, 4, 1, 1, 3, 6]
def baseStart_3919357 : Nat := 118140960795 + 3919357 * 2 ^ 59
def prefixEnd_3919357 : Nat := 4983230072969 + 3 ^ 40 * 3919357 * 2
def baseEnd_3919357 : Nat := 670837999187975743804237

theorem tailTrace_3919357 : CollatzResearch.WordTrace tailWord_3919357 prefixEnd_3919357 670837999187975743804237 := by
  unfold tailWord_3919357
  simp only [CollatzResearch.WordTrace]
  refine ⟨142950693661846436729212325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95300462441230957819474883 142950693661846436729212325)
  ·
    refine ⟨26803255061596206886727311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142950693661846436729212325 26803255061596206886727311)
    ·
      refine ⟨40204882592394310330090967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26803255061596206886727311 40204882592394310330090967)
      ·
        refine ⟨60307323888591465495136451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40204882592394310330090967 60307323888591465495136451)
        ·
          refine ⟨90460985832887198242704677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60307323888591465495136451 90460985832887198242704677)
          ·
            refine ⟨16961434843666349670507127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90460985832887198242704677 16961434843666349670507127)
            ·
              refine ⟨25442152265499524505760691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16961434843666349670507127 25442152265499524505760691)
              ·
                refine ⟨38163228398249286758641037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25442152265499524505760691 38163228398249286758641037)
                ·
                  refine ⟨14311210649343482534490389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38163228398249286758641037 14311210649343482534490389)
                  ·
                    refine ⟨670837999187975743804237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14311210649343482534490389 670837999187975743804237)
                    ·
                      rfl

theorem cell23_3919357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_3919357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919357 prefixEnd_3919357 := by exact prefixLift 3919357
  have htrace : WordTrace (prefixWord ++ tailWord_3919357) baseStart_3919357 baseEnd_3919357 := by
    simpa [prefixWord, tailWord_3919357, baseEnd_3919357] using wordTrace_append hprefix tailTrace_3919357
  have hstable : (prefixWord ++ tailWord_3919357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919357).length < 2 ^ (prefixWord ++ tailWord_3919357).sum := by decide
  have hdescent : baseEnd_3919357 < baseStart_3919357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919377 : List Nat := [1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 4]
def baseStart_3919377 : Nat := 118140960795 + 3919377 * 2 ^ 59
def prefixEnd_3919377 : Nat := 4983230072969 + 3 ^ 40 * 3919377 * 2
def baseEnd_3919377 : Nat := 2012524267177017153162619

theorem tailTrace_3919377 : CollatzResearch.WordTrace tailWord_3919377 prefixEnd_3919377 2012524267177017153162619 := by
  unfold tailWord_3919377
  simp only [CollatzResearch.WordTrace]
  refine ⟨142951423121773980144940385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95300948747849320096626923 142951423121773980144940385)
  ·
    refine ⟨107213567341330485108705289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142951423121773980144940385 107213567341330485108705289)
    ·
      refine ⟨80410175505997863831528967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107213567341330485108705289 80410175505997863831528967)
      ·
        refine ⟨120615263258996795747293451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80410175505997863831528967 120615263258996795747293451)
        ·
          refine ⟨180922894888495193620940177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120615263258996795747293451 180922894888495193620940177)
          ·
            refine ⟨135692171166371395215705133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180922894888495193620940177 135692171166371395215705133)
            ·
              refine ⟨50884564187389273205889425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135692171166371395215705133 50884564187389273205889425)
              ·
                refine ⟨38163423140541954904417069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50884564187389273205889425 38163423140541954904417069)
                ·
                  refine ⟨14311283677703233089156401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38163423140541954904417069 14311283677703233089156401)
                  ·
                    refine ⟨10733462758277424816867301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14311283677703233089156401 10733462758277424816867301)
                    ·
                      refine ⟨2012524267177017153162619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10733462758277424816867301 2012524267177017153162619)
                      ·
                        rfl

theorem cell23_3919377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 4].length) (baseStart_3919377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919377 prefixEnd_3919377 := by exact prefixLift 3919377
  have htrace : WordTrace (prefixWord ++ tailWord_3919377) baseStart_3919377 baseEnd_3919377 := by
    simpa [prefixWord, tailWord_3919377, baseEnd_3919377] using wordTrace_append hprefix tailTrace_3919377
  have hstable : (prefixWord ++ tailWord_3919377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919377).length < 2 ^ (prefixWord ++ tailWord_3919377).sum := by decide
  have hdescent : baseEnd_3919377 < baseStart_3919377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919394 : List Nat := [3, 3, 1, 1, 1, 1, 3, 3, 1, 2, 4]
def baseStart_3919394 : Nat := 118140960795 + 3919394 * 2 ^ 59
def prefixEnd_3919394 : Nat := 4983230072969 + 3 ^ 40 * 3919394 * 2
def baseEnd_3919394 : Nat := 2012532996348143586650041

theorem tailTrace_3919394 : CollatzResearch.WordTrace tailWord_3919394 prefixEnd_3919394 2012532996348143586650041 := by
  unfold tailWord_3919394
  simp only [CollatzResearch.WordTrace]
  refine ⟨35738010790678098012077309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95301362108474928032206157 35738010790678098012077309)
  ·
    refine ⟨13401754046504286754528991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35738010790678098012077309 13401754046504286754528991)
    ·
      refine ⟨20102631069756430131793487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13401754046504286754528991 20102631069756430131793487)
      ·
        refine ⟨30153946604634645197690231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20102631069756430131793487 30153946604634645197690231)
        ·
          refine ⟨45230919906951967796535347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30153946604634645197690231 45230919906951967796535347)
          ·
            refine ⟨67846379860427951694803021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45230919906951967796535347 67846379860427951694803021)
            ·
              refine ⟨25442392447660481885551133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67846379860427951694803021 25442392447660481885551133)
              ·
                refine ⟨9540897167872680707081675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25442392447660481885551133 9540897167872680707081675)
                ·
                  refine ⟨14311345751809021060622513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9540897167872680707081675 14311345751809021060622513)
                  ·
                    refine ⟨10733509313856765795466885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14311345751809021060622513 10733509313856765795466885)
                    ·
                      refine ⟨2012532996348143586650041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10733509313856765795466885 2012532996348143586650041)
                      ·
                        rfl

theorem cell23_3919394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_3919394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919394 prefixEnd_3919394 := by exact prefixLift 3919394
  have htrace : WordTrace (prefixWord ++ tailWord_3919394) baseStart_3919394 baseEnd_3919394 := by
    simpa [prefixWord, tailWord_3919394, baseEnd_3919394] using wordTrace_append hprefix tailTrace_3919394
  have hstable : (prefixWord ++ tailWord_3919394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919394).length < 2 ^ (prefixWord ++ tailWord_3919394).sum := by decide
  have hdescent : baseEnd_3919394 < baseStart_3919394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919415 : List Nat := [1, 1, 3, 1, 2, 5, 2, 3, 1, 2, 2]
def baseStart_3919415 : Nat := 118140960795 + 3919415 * 2 ^ 59
def prefixEnd_3919415 : Nat := 4983230072969 + 3 ^ 40 * 3919415 * 2
def baseEnd_3919415 : Nat := 2012543779441888004487445

theorem tailTrace_3919415 : CollatzResearch.WordTrace tailWord_3919415 prefixEnd_3919415 2012543779441888004487445 := by
  unfold tailWord_3919415
  simp only [CollatzResearch.WordTrace]
  refine ⟨142952809095636312634823699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95301872730424208423215799 142952809095636312634823699)
  ·
    refine ⟨214429213643454468952235549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142952809095636312634823699 214429213643454468952235549)
    ·
      refine ⟨80410955116295425857088331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214429213643454468952235549 80410955116295425857088331)
      ·
        refine ⟨120616432674443138785632497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80410955116295425857088331 120616432674443138785632497)
        ·
          refine ⟨90462324505832354089224373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120616432674443138785632497 90462324505832354089224373)
          ·
            refine ⟨8480842922421783195864785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90462324505832354089224373 8480842922421783195864785)
            ·
              refine ⟨6360632191816337396898589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8480842922421783195864785 6360632191816337396898589)
              ·
                refine ⟨2385237071931126523836971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6360632191816337396898589 2385237071931126523836971)
                ·
                  refine ⟨3577855607896689785755457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2385237071931126523836971 3577855607896689785755457)
                  ·
                    refine ⟨2683391705922517339316593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3577855607896689785755457 2683391705922517339316593)
                    ·
                      refine ⟨2012543779441888004487445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2683391705922517339316593 2012543779441888004487445)
                      ·
                        rfl

theorem cell23_3919415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 3, 1, 2, 2].length) (baseStart_3919415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919415 prefixEnd_3919415 := by exact prefixLift 3919415
  have htrace : WordTrace (prefixWord ++ tailWord_3919415) baseStart_3919415 baseEnd_3919415 := by
    simpa [prefixWord, tailWord_3919415, baseEnd_3919415] using wordTrace_append hprefix tailTrace_3919415
  have hstable : (prefixWord ++ tailWord_3919415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919415).length < 2 ^ (prefixWord ++ tailWord_3919415).sum := by decide
  have hdescent : baseEnd_3919415 < baseStart_3919415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919474 : List Nat := [3, 2, 1, 2, 3, 1, 1, 1, 1, 3, 5]
def baseStart_3919474 : Nat := 118140960795 + 3919474 * 2 ^ 59
def prefixEnd_3919474 : Nat := 4983230072969 + 3 ^ 40 * 3919474 * 2
def baseEnd_3919474 : Nat := 2012574074800503273649673

theorem tailTrace_3919474 : CollatzResearch.WordTrace tailWord_3919474 prefixEnd_3919474 2012574074800503273649673 := by
  unfold tailWord_3919474
  simp only [CollatzResearch.WordTrace]
  refine ⟨35738740250605641427805369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95303307334948377140814317 35738740250605641427805369)
  ·
    refine ⟨26804055187954231070854027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35738740250605641427805369 26804055187954231070854027)
    ·
      refine ⟨40206082781931346606281041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26804055187954231070854027 40206082781931346606281041)
      ·
        refine ⟨30154562086448509954710781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40206082781931346606281041 30154562086448509954710781)
        ·
          refine ⟨11307960782418191233016543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30154562086448509954710781 11307960782418191233016543)
          ·
            refine ⟨16961941173627286849524815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11307960782418191233016543 16961941173627286849524815)
            ·
              refine ⟨25442911760440930274287223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16961941173627286849524815 25442911760440930274287223)
              ·
                refine ⟨38164367640661395411430835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25442911760440930274287223 38164367640661395411430835)
                ·
                  refine ⟨57246551460992093117146253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38164367640661395411430835 57246551460992093117146253)
                  ·
                    refine ⟨21467456797872034918929845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57246551460992093117146253 21467456797872034918929845)
                    ·
                      refine ⟨2012574074800503273649673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21467456797872034918929845 2012574074800503273649673)
                      ·
                        rfl

theorem cell23_3919474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_3919474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919474 prefixEnd_3919474 := by exact prefixLift 3919474
  have htrace : WordTrace (prefixWord ++ tailWord_3919474) baseStart_3919474 baseEnd_3919474 := by
    simpa [prefixWord, tailWord_3919474, baseEnd_3919474] using wordTrace_append hprefix tailTrace_3919474
  have hstable : (prefixWord ++ tailWord_3919474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919474).length < 2 ^ (prefixWord ++ tailWord_3919474).sum := by decide
  have hdescent : baseEnd_3919474 < baseStart_3919474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919488 : List Nat := [2, 1, 1, 2, 1, 4, 2, 4, 2, 2, 2]
def baseStart_3919488 : Nat := 118140960795 + 3919488 * 2 ^ 59
def prefixEnd_3919488 : Nat := 4983230072969 + 3 ^ 40 * 3919488 * 2
def baseEnd_3919488 : Nat := 2012581263529666218874609

theorem tailTrace_3919488 : CollatzResearch.WordTrace tailWord_3919488 prefixEnd_3919488 2012581263529666218874609 := by
  unfold tailWord_3919488
  simp only [CollatzResearch.WordTrace]
  refine ⟨71477735812185923051115559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95303647749581230734820745 71477735812185923051115559)
  ·
    refine ⟨107216603718278884576673339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71477735812185923051115559 107216603718278884576673339)
    ·
      refine ⟨160824905577418326865010009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107216603718278884576673339 160824905577418326865010009)
      ·
        refine ⟨120618679183063745148757507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160824905577418326865010009 120618679183063745148757507)
        ·
          refine ⟨180928018774595617723136261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120618679183063745148757507 180928018774595617723136261)
          ·
            refine ⟨33924003520236678323088049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180928018774595617723136261 33924003520236678323088049)
            ·
              refine ⟨25443002640177508742316037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33924003520236678323088049 25443002640177508742316037)
              ·
                refine ⟨4770562995033282889184257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25443002640177508742316037 4770562995033282889184257)
                ·
                  refine ⟨3577922246274962166888193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4770562995033282889184257 3577922246274962166888193)
                  ·
                    refine ⟨2683441684706221625166145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3577922246274962166888193 2683441684706221625166145)
                    ·
                      refine ⟨2012581263529666218874609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2683441684706221625166145 2012581263529666218874609)
                      ·
                        rfl

theorem cell23_3919488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 2, 2, 2].length) (baseStart_3919488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919488 prefixEnd_3919488 := by exact prefixLift 3919488
  have htrace : WordTrace (prefixWord ++ tailWord_3919488) baseStart_3919488 baseEnd_3919488 := by
    simpa [prefixWord, tailWord_3919488, baseEnd_3919488] using wordTrace_append hprefix tailTrace_3919488
  have hstable : (prefixWord ++ tailWord_3919488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919488).length < 2 ^ (prefixWord ++ tailWord_3919488).sum := by decide
  have hdescent : baseEnd_3919488 < baseStart_3919488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919504 : List Nat := [2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 3]
def baseStart_3919504 : Nat := 118140960795 + 3919504 * 2 ^ 59
def prefixEnd_3919504 : Nat := 4983230072969 + 3 ^ 40 * 3919504 * 2
def baseEnd_3919504 : Nat := 2012589479220138156274535

theorem tailTrace_3919504 : CollatzResearch.WordTrace tailWord_3919504 prefixEnd_3919504 2012589479220138156274535 := by
  unfold tailWord_3919504
  simp only [CollatzResearch.WordTrace]
  refine ⟨71478027596156940417406783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95304036794875920556542377 71478027596156940417406783)
  ·
    refine ⟨107217041394235410626110175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71478027596156940417406783 107217041394235410626110175)
    ·
      refine ⟨160825562091353115939165263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107217041394235410626110175 160825562091353115939165263)
      ·
        refine ⟨241238343137029673908747895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160825562091353115939165263 241238343137029673908747895)
        ·
          refine ⟨361857514705544510863121843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241238343137029673908747895 361857514705544510863121843)
          ·
            refine ⟨542786272058316766294682765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361857514705544510863121843 542786272058316766294682765)
            ·
              refine ⟨203544852021868787360506037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 542786272058316766294682765 203544852021868787360506037)
              ·
                refine ⟨19082329877050198815047441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 203544852021868787360506037 19082329877050198815047441)
                ·
                  refine ⟨14311747407787649111285581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19082329877050198815047441 14311747407787649111285581)
                  ·
                    refine ⟨5366905277920368416732093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14311747407787649111285581 5366905277920368416732093)
                    ·
                      refine ⟨2012589479220138156274535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5366905277920368416732093 2012589479220138156274535)
                      ·
                        rfl

theorem cell23_3919504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 3].length) (baseStart_3919504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919504 prefixEnd_3919504 := by exact prefixLift 3919504
  have htrace : WordTrace (prefixWord ++ tailWord_3919504) baseStart_3919504 baseEnd_3919504 := by
    simpa [prefixWord, tailWord_3919504, baseEnd_3919504] using wordTrace_append hprefix tailTrace_3919504
  have hstable : (prefixWord ++ tailWord_3919504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919504).length < 2 ^ (prefixWord ++ tailWord_3919504).sum := by decide
  have hdescent : baseEnd_3919504 < baseStart_3919504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919578 : List Nat := [3, 1, 1, 2, 2, 5, 1, 1, 2, 1, 4]
def baseStart_3919578 : Nat := 118140960795 + 3919578 * 2 ^ 59
def prefixEnd_3919578 : Nat := 4983230072969 + 3 ^ 40 * 3919578 * 2
def baseEnd_3919578 : Nat := 2012627476788570866749195

theorem tailTrace_3919578 : CollatzResearch.WordTrace tailWord_3919578 prefixEnd_3919578 2012627476788570866749195 := by
  unfold tailWord_3919578
  simp only [CollatzResearch.WordTrace]
  refine ⟨35739688548511447868251847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95305836129363860982004925 35739688548511447868251847)
  ·
    refine ⟨53609532822767171802377771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35739688548511447868251847 53609532822767171802377771)
    ·
      refine ⟨80414299234150757703566657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53609532822767171802377771 80414299234150757703566657)
      ·
        refine ⟨60310724425613068277674993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80414299234150757703566657 60310724425613068277674993)
        ·
          refine ⟨45233043319209801208256245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60310724425613068277674993 45233043319209801208256245)
          ·
            refine ⟨4240597811175918863274023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45233043319209801208256245 4240597811175918863274023)
            ·
              refine ⟨6360896716763878294911035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4240597811175918863274023 6360896716763878294911035)
              ·
                refine ⟨9541345075145817442366553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6360896716763878294911035 9541345075145817442366553)
                ·
                  refine ⟨7156008806359363081774915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9541345075145817442366553 7156008806359363081774915)
                  ·
                    refine ⟨10734013209539044622662373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7156008806359363081774915 10734013209539044622662373)
                    ·
                      refine ⟨2012627476788570866749195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10734013209539044622662373 2012627476788570866749195)
                      ·
                        rfl

theorem cell23_3919578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 2, 1, 4].length) (baseStart_3919578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919578 prefixEnd_3919578 := by exact prefixLift 3919578
  have htrace : WordTrace (prefixWord ++ tailWord_3919578) baseStart_3919578 baseEnd_3919578 := by
    simpa [prefixWord, tailWord_3919578, baseEnd_3919578] using wordTrace_append hprefix tailTrace_3919578
  have hstable : (prefixWord ++ tailWord_3919578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919578).length < 2 ^ (prefixWord ++ tailWord_3919578).sum := by decide
  have hdescent : baseEnd_3919578 < baseStart_3919578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919601 : List Nat := [1, 2, 2, 2, 2, 3, 3, 2, 6]
def baseStart_3919601 : Nat := 118140960795 + 3919601 * 2 ^ 59
def prefixEnd_3919601 : Nat := 4983230072969 + 3 ^ 40 * 3919601 * 2
def baseEnd_3919601 : Nat := 223626587427069364084621

theorem tailTrace_3919601 : CollatzResearch.WordTrace tailWord_3919601 prefixEnd_3919601 223626587427069364084621 := by
  unfold tailWord_3919601
  simp only [CollatzResearch.WordTrace]
  refine ⟨142959593072962466401094657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95306395381974977600729771 142959593072962466401094657)
  ·
    refine ⟨107219694804721849800820993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142959593072962466401094657 107219694804721849800820993)
    ·
      refine ⟨80414771103541387350615745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107219694804721849800820993 80414771103541387350615745)
      ·
        refine ⟨60311078327656040512961809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80414771103541387350615745 60311078327656040512961809)
        ·
          refine ⟨45233308745742030384721357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60311078327656040512961809 45233308745742030384721357)
          ·
            refine ⟨16962490779653261394270509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45233308745742030384721357 16962490779653261394270509)
            ·
              refine ⟨6360934042369973022851441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16962490779653261394270509 6360934042369973022851441)
              ·
                refine ⟨4770700531777479767138581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6360934042369973022851441 4770700531777479767138581)
                ·
                  refine ⟨223626587427069364084621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4770700531777479767138581 223626587427069364084621)
                  ·
                    rfl

theorem cell23_3919601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 6].length) (baseStart_3919601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919601 prefixEnd_3919601 := by exact prefixLift 3919601
  have htrace : WordTrace (prefixWord ++ tailWord_3919601) baseStart_3919601 baseEnd_3919601 := by
    simpa [prefixWord, tailWord_3919601, baseEnd_3919601] using wordTrace_append hprefix tailTrace_3919601
  have hstable : (prefixWord ++ tailWord_3919601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919601).length < 2 ^ (prefixWord ++ tailWord_3919601).sum := by decide
  have hdescent : baseEnd_3919601 < baseStart_3919601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919628 : List Nat := [2, 2, 1, 2, 2, 1, 4, 2, 3, 1, 3]
def baseStart_3919628 : Nat := 118140960795 + 3919628 * 2 ^ 59
def prefixEnd_3919628 : Nat := 4983230072969 + 3 ^ 40 * 3919628 * 2
def baseEnd_3919628 : Nat := 2012653150821295671123965

theorem tailTrace_3919628 : CollatzResearch.WordTrace tailWord_3919628 prefixEnd_3919628 2012653150821295671123965 := by
  unfold tailWord_3919628
  simp only [CollatzResearch.WordTrace]
  refine ⟨71480288921932325006163769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95307051895909766674885025 71480288921932325006163769)
  ·
    refine ⟨53610216691449243754622827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71480288921932325006163769 53610216691449243754622827)
    ·
      refine ⟨80415325037173865631934241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53610216691449243754622827 80415325037173865631934241)
      ·
        refine ⟨60311493777880399223950681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80415325037173865631934241 60311493777880399223950681)
        ·
          refine ⟨45233620333410299417963011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60311493777880399223950681 45233620333410299417963011)
          ·
            refine ⟨67850430500115449126944517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45233620333410299417963011 67850430500115449126944517)
            ·
              refine ⟨12721955718771646711302097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67850430500115449126944517 12721955718771646711302097)
              ·
                refine ⟨9541466789078735033476573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12721955718771646711302097 9541466789078735033476573)
                ·
                  refine ⟨3578050045904525637553715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9541466789078735033476573 3578050045904525637553715)
                  ·
                    refine ⟨5367075068856788456330573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3578050045904525637553715 5367075068856788456330573)
                    ·
                      refine ⟨2012653150821295671123965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5367075068856788456330573 2012653150821295671123965)
                      ·
                        rfl

theorem cell23_3919628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 3, 1, 3].length) (baseStart_3919628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919628 prefixEnd_3919628 := by exact prefixLift 3919628
  have htrace : WordTrace (prefixWord ++ tailWord_3919628) baseStart_3919628 baseEnd_3919628 := by
    simpa [prefixWord, tailWord_3919628, baseEnd_3919628] using wordTrace_append hprefix tailTrace_3919628
  have hstable : (prefixWord ++ tailWord_3919628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919628).length < 2 ^ (prefixWord ++ tailWord_3919628).sum := by decide
  have hdescent : baseEnd_3919628 < baseStart_3919628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919688 : List Nat := [2, 1, 3, 1, 1, 5, 1, 1, 3, 2, 3]
def baseStart_3919688 : Nat := 118140960795 + 3919688 * 2 ^ 59
def prefixEnd_3919688 : Nat := 4983230072969 + 3 ^ 40 * 3919688 * 2
def baseEnd_3919688 : Nat := 2012683959660565436373689

theorem tailTrace_3919688 : CollatzResearch.WordTrace tailWord_3919688 prefixEnd_3919688 2012683959660565436373689 := by
  unfold tailWord_3919688
  simp only [CollatzResearch.WordTrace]
  refine ⟨71481383111823640129755859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95308510815764853506341145 71481383111823640129755859)
  ·
    refine ⟨107222074667735460194633789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71481383111823640129755859 107222074667735460194633789)
    ·
      refine ⟨40208278000400797572987671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107222074667735460194633789 40208278000400797572987671)
      ·
        refine ⟨60312417000601196359481507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40208278000400797572987671 60312417000601196359481507)
        ·
          refine ⟨90468625500901794539222261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60312417000601196359481507 90468625500901794539222261)
          ·
            refine ⟨8481433640709543238052087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90468625500901794539222261 8481433640709543238052087)
            ·
              refine ⟨12722150461064314857078131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8481433640709543238052087 12722150461064314857078131)
              ·
                refine ⟨19083225691596472285617197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12722150461064314857078131 19083225691596472285617197)
                ·
                  refine ⟨7156209634348677107106449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19083225691596472285617197 7156209634348677107106449)
                  ·
                    refine ⟨5367157225761507830329837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7156209634348677107106449 5367157225761507830329837)
                    ·
                      refine ⟨2012683959660565436373689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5367157225761507830329837 2012683959660565436373689)
                      ·
                        rfl

theorem cell23_3919688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 3, 2, 3].length) (baseStart_3919688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919688 prefixEnd_3919688 := by exact prefixLift 3919688
  have htrace : WordTrace (prefixWord ++ tailWord_3919688) baseStart_3919688 baseEnd_3919688 := by
    simpa [prefixWord, tailWord_3919688, baseEnd_3919688] using wordTrace_append hprefix tailTrace_3919688
  have hstable : (prefixWord ++ tailWord_3919688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919688).length < 2 ^ (prefixWord ++ tailWord_3919688).sum := by decide
  have hdescent : baseEnd_3919688 < baseStart_3919688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919698 : List Nat := [3, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4]
def baseStart_3919698 : Nat := 118140960795 + 3919698 * 2 ^ 59
def prefixEnd_3919698 : Nat := 4983230072969 + 3 ^ 40 * 3919698 * 2
def baseEnd_3919698 : Nat := 2012689094467110397248643

theorem tailTrace_3919698 : CollatzResearch.WordTrace tailWord_3919698 prefixEnd_3919698 2012689094467110397248643 := by
  unfold tailWord_3919698
  simp only [CollatzResearch.WordTrace]
  refine ⟨35740782738402762991843937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95308753969074034644917165 35740782738402762991843937)
  ·
    refine ⟨26805587053802072243882953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35740782738402762991843937 26805587053802072243882953)
    ·
      refine ⟨20104190290351554182912215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26805587053802072243882953 20104190290351554182912215)
      ·
        refine ⟨30156285435527331274368323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20104190290351554182912215 30156285435527331274368323)
        ·
          refine ⟨45234428153290996911552485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30156285435527331274368323 45234428153290996911552485)
          ·
            refine ⟨8481455278742061920916091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45234428153290996911552485 8481455278742061920916091)
            ·
              refine ⟨12722182918113092881374137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8481455278742061920916091 12722182918113092881374137)
              ·
                refine ⟨9541637188584819661030603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12722182918113092881374137 9541637188584819661030603)
                ·
                  refine ⟨14312455782877229491545905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9541637188584819661030603 14312455782877229491545905)
                  ·
                    refine ⟨10734341837157922118659429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14312455782877229491545905 10734341837157922118659429)
                    ·
                      refine ⟨2012689094467110397248643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10734341837157922118659429 2012689094467110397248643)
                      ·
                        rfl

theorem cell23_3919698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_3919698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919698 prefixEnd_3919698 := by exact prefixLift 3919698
  have htrace : WordTrace (prefixWord ++ tailWord_3919698) baseStart_3919698 baseEnd_3919698 := by
    simpa [prefixWord, tailWord_3919698, baseEnd_3919698] using wordTrace_append hprefix tailTrace_3919698
  have hstable : (prefixWord ++ tailWord_3919698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919698).length < 2 ^ (prefixWord ++ tailWord_3919698).sum := by decide
  have hdescent : baseEnd_3919698 < baseStart_3919698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919705 : List Nat := [1, 2, 1, 2, 2, 3, 5, 1, 1, 2, 3]
def baseStart_3919705 : Nat := 118140960795 + 3919705 * 2 ^ 59
def prefixEnd_3919705 : Nat := 4983230072969 + 3 ^ 40 * 3919705 * 2
def baseEnd_3919705 : Nat := 2012692688831691869861111

theorem tailTrace_3919705 : CollatzResearch.WordTrace tailWord_3919705 prefixEnd_3919705 2012692688831691869861111 := by
  unfold tailWord_3919705
  simp only [CollatzResearch.WordTrace]
  refine ⟨142963386264585692162880569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95308924176390461441920379 142963386264585692162880569)
  ·
    refine ⟨107222539698439269122160427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142963386264585692162880569 107222539698439269122160427)
    ·
      refine ⟨160833809547658903683240641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107222539698439269122160427 160833809547658903683240641)
      ·
        refine ⟨120625357160744177762430481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160833809547658903683240641 120625357160744177762430481)
        ·
          refine ⟨90469017870558133321822861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120625357160744177762430481 90469017870558133321822861)
          ·
            refine ⟨33925881701459299995683573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90469017870558133321822861 33925881701459299995683573)
            ·
              refine ⟨3180551409511809374595335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33925881701459299995683573 3180551409511809374595335)
              ·
                refine ⟨4770827114267714061893003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3180551409511809374595335 4770827114267714061893003)
                ·
                  refine ⟨7156240671401571092839505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4770827114267714061893003 7156240671401571092839505)
                  ·
                    refine ⟨5367180503551178319629629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7156240671401571092839505 5367180503551178319629629)
                    ·
                      refine ⟨2012692688831691869861111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5367180503551178319629629 2012692688831691869861111)
                      ·
                        rfl

theorem cell23_3919705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 1, 2, 3].length) (baseStart_3919705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919705 prefixEnd_3919705 := by exact prefixLift 3919705
  have htrace : WordTrace (prefixWord ++ tailWord_3919705) baseStart_3919705 baseEnd_3919705 := by
    simpa [prefixWord, tailWord_3919705, baseEnd_3919705] using wordTrace_append hprefix tailTrace_3919705
  have hstable : (prefixWord ++ tailWord_3919705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919705).length < 2 ^ (prefixWord ++ tailWord_3919705).sum := by decide
  have hdescent : baseEnd_3919705 < baseStart_3919705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919708 : List Nat := [2, 2, 4, 2, 3, 10]
def baseStart_3919708 : Nat := 118140960795 + 3919708 * 2 ^ 59
def prefixEnd_3919708 : Nat := 4983230072969 + 3 ^ 40 * 3919708 * 2
def baseEnd_3919708 : Nat := 8282692301537676370879

theorem tailTrace_3919708 : CollatzResearch.WordTrace tailWord_3919708 prefixEnd_3919708 8282692301537676370879 := by
  unfold tailWord_3919708
  simp only [CollatzResearch.WordTrace]
  refine ⟨71481747841787411837619889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95308997122383215783493185 71481747841787411837619889)
  ·
    refine ⟨53611310881340558878214917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71481747841787411837619889 53611310881340558878214917)
    ·
      refine ⟨10052120790251354789665297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53611310881340558878214917 10052120790251354789665297)
      ·
        refine ⟨7539090592688516092248973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10052120790251354789665297 7539090592688516092248973)
        ·
          refine ⟨2827158972258193534593365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7539090592688516092248973 2827158972258193534593365)
          ·
            refine ⟨8282692301537676370879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2827158972258193534593365 8282692301537676370879)
            ·
              rfl

theorem cell23_3919708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 10].length) (baseStart_3919708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919708 prefixEnd_3919708 := by exact prefixLift 3919708
  have htrace : WordTrace (prefixWord ++ tailWord_3919708) baseStart_3919708 baseEnd_3919708 := by
    simpa [prefixWord, tailWord_3919708, baseEnd_3919708] using wordTrace_append hprefix tailTrace_3919708
  have hstable : (prefixWord ++ tailWord_3919708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919708).length < 2 ^ (prefixWord ++ tailWord_3919708).sum := by decide
  have hdescent : baseEnd_3919708 < baseStart_3919708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919741 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 4, 3, 4]
def baseStart_3919741 : Nat := 118140960795 + 3919741 * 2 ^ 59
def prefixEnd_3919741 : Nat := 4983230072969 + 3 ^ 40 * 3919741 * 2
def baseEnd_3919741 : Nat := 2012711174135253729010945

theorem tailTrace_3919741 : CollatzResearch.WordTrace tailWord_3919741 prefixEnd_3919741 2012711174135253729010945 := by
  unfold tailWord_3919741
  simp only [CollatzResearch.WordTrace]
  refine ⟨142964699292455270311191077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95309799528303513540794051 142964699292455270311191077)
  ·
    refine ⟨26805881117335363183348327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142964699292455270311191077 26805881117335363183348327)
    ·
      refine ⟨40208821676003044775022491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26805881117335363183348327 40208821676003044775022491)
      ·
        refine ⟨60313232514004567162533737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40208821676003044775022491 60313232514004567162533737)
        ·
          refine ⟨45234924385503425371900303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60313232514004567162533737 45234924385503425371900303)
          ·
            refine ⟨67852386578255138057850455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45234924385503425371900303 67852386578255138057850455)
            ·
              refine ⟨101778579867382707086775683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67852386578255138057850455 101778579867382707086775683)
              ·
                refine ⟨152667869801074060630163525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101778579867382707086775683 152667869801074060630163525)
                ·
                  refine ⟨28625225587701386368155661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 152667869801074060630163525 28625225587701386368155661)
                  ·
                    refine ⟨10734459595388019888058373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28625225587701386368155661 10734459595388019888058373)
                    ·
                      refine ⟨2012711174135253729010945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10734459595388019888058373 2012711174135253729010945)
                      ·
                        rfl

theorem cell23_3919741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_3919741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919741 prefixEnd_3919741 := by exact prefixLift 3919741
  have htrace : WordTrace (prefixWord ++ tailWord_3919741) baseStart_3919741 baseEnd_3919741 := by
    simpa [prefixWord, tailWord_3919741, baseEnd_3919741] using wordTrace_append hprefix tailTrace_3919741
  have hstable : (prefixWord ++ tailWord_3919741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919741).length < 2 ^ (prefixWord ++ tailWord_3919741).sum := by decide
  have hdescent : baseEnd_3919741 < baseStart_3919741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
