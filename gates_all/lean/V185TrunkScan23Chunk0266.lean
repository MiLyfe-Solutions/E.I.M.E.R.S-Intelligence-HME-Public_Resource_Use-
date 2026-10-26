import V185TrunkScan23Chunk0265

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1573841 : List Nat := [1, 2, 2, 1, 2, 1, 5, 3, 1, 2, 3]
def baseStart_1573841 : Nat := 118140960795 + 1573841 * 2 ^ 59
def prefixEnd_1573841 : Nat := 4983230072969 + 3 ^ 40 * 1573841 * 2
def baseEnd_1573841 : Nat := 808136906752882073549543

theorem tailTrace_1573841 : CollatzResearch.WordTrace tailWord_1573841 prefixEnd_1573841 808136906752882073549543 := by
  unfold tailWord_1573841
  simp only [CollatzResearch.WordTrace]
  refine ⟨57402697091250322488393377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38268464727500214992262251 57402697091250322488393377)
  ·
    refine ⟨43052022818437741866295033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57402697091250322488393377 43052022818437741866295033)
    ·
      refine ⟨32289017113828306399721275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43052022818437741866295033 32289017113828306399721275)
      ·
        refine ⟨48433525670742459599581913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32289017113828306399721275 48433525670742459599581913)
        ·
          refine ⟨36325144253056844699686435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48433525670742459599581913 36325144253056844699686435)
          ·
            refine ⟨54487716379585267049529653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36325144253056844699686435 54487716379585267049529653)
            ·
              refine ⟨5108223410586118785893405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54487716379585267049529653 5108223410586118785893405)
              ·
                refine ⟨1915583778969794544710027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5108223410586118785893405 1915583778969794544710027)
                ·
                  refine ⟨2873375668454691817065041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1915583778969794544710027 2873375668454691817065041)
                  ·
                    refine ⟨2155031751341018862798781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2873375668454691817065041 2155031751341018862798781)
                    ·
                      refine ⟨808136906752882073549543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2155031751341018862798781 808136906752882073549543)
                      ·
                        rfl

theorem cell23_1573841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 2, 3].length) (baseStart_1573841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573841 prefixEnd_1573841 := by exact prefixLift 1573841
  have htrace : WordTrace (prefixWord ++ tailWord_1573841) baseStart_1573841 baseEnd_1573841 := by
    simpa [prefixWord, tailWord_1573841, baseEnd_1573841] using wordTrace_append hprefix tailTrace_1573841
  have hstable : (prefixWord ++ tailWord_1573841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573841).length < 2 ^ (prefixWord ++ tailWord_1573841).sum := by decide
  have hdescent : baseEnd_1573841 < baseStart_1573841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573844 : List Nat := [2, 4, 1, 2, 1, 3, 10]
def baseStart_1573844 : Nat := 118140960795 + 1573844 * 2 ^ 59
def prefixEnd_1573844 : Nat := 4983230072969 + 3 ^ 40 * 1573844 * 2
def baseEnd_1573844 : Nat := 9977017866603031627309

theorem tailTrace_1573844 : CollatzResearch.WordTrace tailWord_1573844 prefixEnd_1573844 9977017866603031627309 := by
  unfold tailWord_1573844
  simp only [CollatzResearch.WordTrace]
  refine ⟨28701403255119727000376293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38268537673492969333835057 28701403255119727000376293)
  ·
    refine ⟨5381513110334948812570555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28701403255119727000376293 5381513110334948812570555)
    ·
      refine ⟨8072269665502423218855833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5381513110334948812570555 8072269665502423218855833)
      ·
        refine ⟨6054202249126817414141875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8072269665502423218855833 6054202249126817414141875)
        ·
          refine ⟨9081303373690226121212813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6054202249126817414141875 9081303373690226121212813)
          ·
            refine ⟨3405488765133834795454805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9081303373690226121212813 3405488765133834795454805)
            ·
              refine ⟨9977017866603031627309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3405488765133834795454805 9977017866603031627309)
              ·
                rfl

theorem cell23_1573844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 10].length) (baseStart_1573844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573844 prefixEnd_1573844 := by exact prefixLift 1573844
  have htrace : WordTrace (prefixWord ++ tailWord_1573844) baseStart_1573844 baseEnd_1573844 := by
    simpa [prefixWord, tailWord_1573844, baseEnd_1573844] using wordTrace_append hprefix tailTrace_1573844
  have hstable : (prefixWord ++ tailWord_1573844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573844).length < 2 ^ (prefixWord ++ tailWord_1573844).sum := by decide
  have hdescent : baseEnd_1573844 < baseStart_1573844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573848 : List Nat := [2, 1, 2, 2, 2, 5, 1, 2, 2, 4]
def baseStart_1573848 : Nat := 118140960795 + 1573848 * 2 ^ 59
def prefixEnd_1573848 : Nat := 4983230072969 + 3 ^ 40 * 1573848 * 2
def baseEnd_1573848 : Nat := 269380167039154515387337

theorem tailTrace_1573848 : CollatzResearch.WordTrace tailWord_1573848 prefixEnd_1573848 269380167039154515387337 := by
  unfold tailWord_1573848
  simp only [CollatzResearch.WordTrace]
  refine ⟨28701476201112481341949099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38268634934816641789265465 28701476201112481341949099)
  ·
    refine ⟨43052214301668722012923649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28701476201112481341949099 43052214301668722012923649)
    ·
      refine ⟨32289160726251541509692737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43052214301668722012923649 32289160726251541509692737)
      ·
        refine ⟨24216870544688656132269553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32289160726251541509692737 24216870544688656132269553)
        ·
          refine ⟨18162652908516492099202165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24216870544688656132269553 18162652908516492099202165)
          ·
            refine ⟨1702748710173421134300203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18162652908516492099202165 1702748710173421134300203)
            ·
              refine ⟨2554123065260131701450305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1702748710173421134300203 2554123065260131701450305)
              ·
                refine ⟨1915592298945098776087729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2554123065260131701450305 1915592298945098776087729)
                ·
                  refine ⟨1436694224208824082065797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1915592298945098776087729 1436694224208824082065797)
                  ·
                    refine ⟨269380167039154515387337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1436694224208824082065797 269380167039154515387337)
                    ·
                      rfl

theorem cell23_1573848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 2, 4].length) (baseStart_1573848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573848 prefixEnd_1573848 := by exact prefixLift 1573848
  have htrace : WordTrace (prefixWord ++ tailWord_1573848) baseStart_1573848 baseEnd_1573848 := by
    simpa [prefixWord, tailWord_1573848, baseEnd_1573848] using wordTrace_append hprefix tailTrace_1573848
  have hstable : (prefixWord ++ tailWord_1573848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573848).length < 2 ^ (prefixWord ++ tailWord_1573848).sum := by decide
  have hdescent : baseEnd_1573848 < baseStart_1573848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573855 : List Nat := [1, 1, 2, 3, 5, 1, 2, 1, 3, 2, 2]
def baseStart_1573855 : Nat := 118140960795 + 1573855 * 2 ^ 59
def prefixEnd_1573855 : Nat := 4983230072969 + 3 ^ 40 * 1573855 * 2
def baseEnd_1573855 : Nat := 808144095482045018774479

theorem tailTrace_1573855 : CollatzResearch.WordTrace tailWord_1573855 prefixEnd_1573855 808144095482045018774479 := by
  unfold tailWord_1573855
  simp only [CollatzResearch.WordTrace]
  refine ⟨57403207713199602879403019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38268805142133068586268679 57403207713199602879403019)
  ·
    refine ⟨86104811569799404319104529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57403207713199602879403019 86104811569799404319104529)
    ·
      refine ⟨64578608677349553239328397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86104811569799404319104529 64578608677349553239328397)
      ·
        refine ⟨24216978254006082464748149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64578608677349553239328397 24216978254006082464748149)
        ·
          refine ⟨2270341711313070231070139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24216978254006082464748149 2270341711313070231070139)
          ·
            refine ⟨3405512566969605346605209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2270341711313070231070139 3405512566969605346605209)
            ·
              refine ⟨2554134425227204009953907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3405512566969605346605209 2554134425227204009953907)
              ·
                refine ⟨3831201637840806014930861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2554134425227204009953907 3831201637840806014930861)
                ·
                  refine ⟨1436700614190302255599073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3831201637840806014930861 1436700614190302255599073)
                  ·
                    refine ⟨1077525460642726691699305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1436700614190302255599073 1077525460642726691699305)
                    ·
                      refine ⟨808144095482045018774479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1077525460642726691699305 808144095482045018774479)
                      ·
                        rfl

theorem cell23_1573855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 3, 2, 2].length) (baseStart_1573855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573855 prefixEnd_1573855 := by exact prefixLift 1573855
  have htrace : WordTrace (prefixWord ++ tailWord_1573855) baseStart_1573855 baseEnd_1573855 := by
    simpa [prefixWord, tailWord_1573855, baseEnd_1573855] using wordTrace_append hprefix tailTrace_1573855
  have hstable : (prefixWord ++ tailWord_1573855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573855).length < 2 ^ (prefixWord ++ tailWord_1573855).sum := by decide
  have hdescent : baseEnd_1573855 < baseStart_1573855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573858 : List Nat := [3, 3, 3, 1, 1, 2, 1, 2, 1, 1, 5]
def baseStart_1573858 : Nat := 118140960795 + 1573858 * 2 ^ 59
def prefixEnd_1573858 : Nat := 4983230072969 + 3 ^ 40 * 1573858 * 2
def baseEnd_1573858 : Nat := 808145635924008507036965

theorem tailTrace_1573858 : CollatzResearch.WordTrace tailWord_1573858 prefixEnd_1573858 808145635924008507036965 := by
  unfold tailWord_1573858
  simp only [CollatzResearch.WordTrace]
  refine ⟨14350829283047183597940557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38268878088125822927841485 14350829283047183597940557)
  ·
    refine ⟨5381560981142693849227709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14350829283047183597940557 5381560981142693849227709)
    ·
      refine ⟨2018085367928510193460391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5381560981142693849227709 2018085367928510193460391)
      ·
        refine ⟨3027128051892765290190587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2018085367928510193460391 3027128051892765290190587)
        ·
          refine ⟨4540692077839147935285881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3027128051892765290190587 4540692077839147935285881)
          ·
            refine ⟨3405519058379360951464411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4540692077839147935285881 3405519058379360951464411)
            ·
              refine ⟨5108278587569041427196617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3405519058379360951464411 5108278587569041427196617)
              ·
                refine ⟨3831208940676781070397463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5108278587569041427196617 3831208940676781070397463)
                ·
                  refine ⟨5746813411015171605596195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3831208940676781070397463 5746813411015171605596195)
                  ·
                    refine ⟨8620220116522757408394293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5746813411015171605596195 8620220116522757408394293)
                    ·
                      refine ⟨808145635924008507036965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8620220116522757408394293 808145635924008507036965)
                      ·
                        rfl

theorem cell23_1573858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_1573858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573858 prefixEnd_1573858 := by exact prefixLift 1573858
  have htrace : WordTrace (prefixWord ++ tailWord_1573858) baseStart_1573858 baseEnd_1573858 := by
    simpa [prefixWord, tailWord_1573858, baseEnd_1573858] using wordTrace_append hprefix tailTrace_1573858
  have hstable : (prefixWord ++ tailWord_1573858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573858).length < 2 ^ (prefixWord ++ tailWord_1573858).sum := by decide
  have hdescent : baseEnd_1573858 < baseStart_1573858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573871 : List Nat := [1, 1, 2, 1, 4, 3, 3, 1, 1, 3, 3]
def baseStart_1573871 : Nat := 118140960795 + 1573871 * 2 ^ 59
def prefixEnd_1573871 : Nat := 4983230072969 + 3 ^ 40 * 1573871 * 2
def baseEnd_1573871 : Nat := 808152311172516956174405

theorem tailTrace_1573871 : CollatzResearch.WordTrace tailWord_1573871 prefixEnd_1573871 808152311172516956174405 := by
  unfold tailWord_1573871
  simp only [CollatzResearch.WordTrace]
  refine ⟨57403791281141637611985467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38269194187427758407990311 57403791281141637611985467)
  ·
    refine ⟨86105686921712456417978201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57403791281141637611985467 86105686921712456417978201)
    ·
      refine ⟨64579265191284342313483651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86105686921712456417978201 64579265191284342313483651)
      ·
        refine ⟨96868897786926513470225477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64579265191284342313483651 96868897786926513470225477)
        ·
          refine ⟨18162918335048721275667277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96868897786926513470225477 18162918335048721275667277)
          ·
            refine ⟨6811094375643270478375229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18162918335048721275667277 6811094375643270478375229)
            ·
              refine ⟨2554160390866226429390711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6811094375643270478375229 2554160390866226429390711)
              ·
                refine ⟨3831240586299339644086067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2554160390866226429390711 3831240586299339644086067)
                ·
                  refine ⟨5746860879449009466129101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3831240586299339644086067 5746860879449009466129101)
                  ·
                    refine ⟨2155072829793378549798413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5746860879449009466129101 2155072829793378549798413)
                    ·
                      refine ⟨808152311172516956174405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2155072829793378549798413 808152311172516956174405)
                      ·
                        rfl

theorem cell23_1573871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 3, 3].length) (baseStart_1573871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573871 prefixEnd_1573871 := by exact prefixLift 1573871
  have htrace : WordTrace (prefixWord ++ tailWord_1573871) baseStart_1573871 baseEnd_1573871 := by
    simpa [prefixWord, tailWord_1573871, baseEnd_1573871] using wordTrace_append hprefix tailTrace_1573871
  have hstable : (prefixWord ++ tailWord_1573871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573871).length < 2 ^ (prefixWord ++ tailWord_1573871).sum := by decide
  have hdescent : baseEnd_1573871 < baseStart_1573871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573878 : List Nat := [5, 1, 1, 1, 3, 3, 2, 7]
def baseStart_1573878 : Nat := 118140960795 + 1573878 * 2 ^ 59
def prefixEnd_1573878 : Nat := 4983230072969 + 3 ^ 40 * 1573878 * 2
def baseEnd_1573878 : Nat := 29931700205077719584699

theorem tailTrace_1573878 : CollatzResearch.WordTrace tailWord_1573878 prefixEnd_1573878 29931700205077719584699 := by
  unfold tailWord_1573878
  simp only [CollatzResearch.WordTrace]
  refine ⟨3587752912007267362968143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38269364394744185204993525 3587752912007267362968143)
  ·
    refine ⟨5381629368010901044452215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3587752912007267362968143 5381629368010901044452215)
    ·
      refine ⟨8072444052016351566678323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5381629368010901044452215 8072444052016351566678323)
      ·
        refine ⟨12108666078024527350017485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8072444052016351566678323 12108666078024527350017485)
        ·
          refine ⟨4540749779259197756256557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12108666078024527350017485 4540749779259197756256557)
          ·
            refine ⟨1702781167222199158596209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4540749779259197756256557 1702781167222199158596209)
            ·
              refine ⟨1277085875416649368947157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1702781167222199158596209 1277085875416649368947157)
              ·
                refine ⟨29931700205077719584699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1277085875416649368947157 29931700205077719584699)
                ·
                  rfl

theorem cell23_1573878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 7].length) (baseStart_1573878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573878 prefixEnd_1573878 := by exact prefixLift 1573878
  have htrace : WordTrace (prefixWord ++ tailWord_1573878) baseStart_1573878 baseEnd_1573878 := by
    simpa [prefixWord, tailWord_1573878, baseEnd_1573878] using wordTrace_append hprefix tailTrace_1573878
  have hstable : (prefixWord ++ tailWord_1573878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573878).length < 2 ^ (prefixWord ++ tailWord_1573878).sum := by decide
  have hdescent : baseEnd_1573878 < baseStart_1573878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573884 : List Nat := [2, 2, 2, 1, 2, 3, 1, 1, 2, 2, 5]
def baseStart_1573884 : Nat := 118140960795 + 1573884 * 2 ^ 59
def prefixEnd_1573884 : Nat := 4983230072969 + 3 ^ 40 * 1573884 * 2
def baseEnd_1573884 : Nat := 808158986421025405311845

theorem tailTrace_1573884 : CollatzResearch.WordTrace tailWord_1573884 prefixEnd_1573884 808158986421025405311845 := by
  unfold tailWord_1573884
  simp only [CollatzResearch.WordTrace]
  refine ⟨28702132715047270416104353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38269510286729693888139137 28702132715047270416104353)
  ·
    refine ⟨21526599536285452812078265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28702132715047270416104353 21526599536285452812078265)
    ·
      refine ⟨16144949652214089609058699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21526599536285452812078265 16144949652214089609058699)
      ·
        refine ⟨24217424478321134413588049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16144949652214089609058699 24217424478321134413588049)
        ·
          refine ⟨18163068358740850810191037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24217424478321134413588049 18163068358740850810191037)
          ·
            refine ⟨6811150634527819053821639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18163068358740850810191037 6811150634527819053821639)
            ·
              refine ⟨10216725951791728580732459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6811150634527819053821639 10216725951791728580732459)
              ·
                refine ⟨15325088927687592871098689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10216725951791728580732459 15325088927687592871098689)
                ·
                  refine ⟨11493816695765694653324017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15325088927687592871098689 11493816695765694653324017)
                  ·
                    refine ⟨8620362521824270989993013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11493816695765694653324017 8620362521824270989993013)
                    ·
                      refine ⟨808158986421025405311845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8620362521824270989993013 808158986421025405311845)
                      ·
                        rfl

theorem cell23_1573884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_1573884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573884 prefixEnd_1573884 := by exact prefixLift 1573884
  have htrace : WordTrace (prefixWord ++ tailWord_1573884) baseStart_1573884 baseEnd_1573884 := by
    simpa [prefixWord, tailWord_1573884, baseEnd_1573884] using wordTrace_append hprefix tailTrace_1573884
  have hstable : (prefixWord ++ tailWord_1573884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573884).length < 2 ^ (prefixWord ++ tailWord_1573884).sum := by decide
  have hdescent : baseEnd_1573884 < baseStart_1573884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573906 : List Nat := [3, 2, 5, 1, 1, 2, 1, 1, 3, 2, 2]
def baseStart_1573906 : Nat := 118140960795 + 1573906 * 2 ^ 59
def prefixEnd_1573906 : Nat := 4983230072969 + 3 ^ 40 * 1573906 * 2
def baseEnd_1573906 : Nat := 808170282995424319236745

theorem tailTrace_1573906 : CollatzResearch.WordTrace tailWord_1573906 prefixEnd_1573906 808170282995424319236745 := by
  unfold tailWord_1573906
  simp only [CollatzResearch.WordTrace]
  refine ⟨14351266959003709647377393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38270045224009892393006381 14351266959003709647377393)
  ·
    refine ⟨10763450219252782235533045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14351266959003709647377393 10763450219252782235533045)
    ·
      refine ⟨1009073458054948334581223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10763450219252782235533045 1009073458054948334581223)
      ·
        refine ⟨1513610187082422501871835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1009073458054948334581223 1513610187082422501871835)
        ·
          refine ⟨2270415280623633752807753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1513610187082422501871835 2270415280623633752807753)
          ·
            refine ⟨1702811460467725314605815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2270415280623633752807753 1702811460467725314605815)
            ·
              refine ⟨2554217190701587971908723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1702811460467725314605815 2554217190701587971908723)
              ·
                refine ⟨3831325786052381957863085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2554217190701587971908723 3831325786052381957863085)
                ·
                  refine ⟨1436747169769643234198657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3831325786052381957863085 1436747169769643234198657)
                  ·
                    refine ⟨1077560377327232425648993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1436747169769643234198657 1077560377327232425648993)
                    ·
                      refine ⟨808170282995424319236745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1077560377327232425648993 808170282995424319236745)
                      ·
                        rfl

theorem cell23_1573906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_1573906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573906 prefixEnd_1573906 := by exact prefixLift 1573906
  have htrace : WordTrace (prefixWord ++ tailWord_1573906) baseStart_1573906 baseEnd_1573906 := by
    simpa [prefixWord, tailWord_1573906, baseEnd_1573906] using wordTrace_append hprefix tailTrace_1573906
  have hstable : (prefixWord ++ tailWord_1573906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573906).length < 2 ^ (prefixWord ++ tailWord_1573906).sum := by decide
  have hdescent : baseEnd_1573906 < baseStart_1573906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573914 : List Nat := [3, 1, 1, 3, 1, 2, 1, 2, 1, 3, 5]
def baseStart_1573914 : Nat := 118140960795 + 1573914 * 2 ^ 59
def prefixEnd_1573914 : Nat := 4983230072969 + 3 ^ 40 * 1573914 * 2
def baseEnd_1573914 : Nat := 808174390840660287936707

theorem tailTrace_1573914 : CollatzResearch.WordTrace tailWord_1573914 prefixEnd_1573914 808174390840660287936707 := by
  unfold tailWord_1573914
  simp only [CollatzResearch.WordTrace]
  refine ⟨14351339904996463988950199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38270239746657237303867197 14351339904996463988950199)
  ·
    refine ⟨21527009857494695983425299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14351339904996463988950199 21527009857494695983425299)
    ·
      refine ⟨32290514786242043975137949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21527009857494695983425299 32290514786242043975137949)
      ·
        refine ⟨12108943044840766490676731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32290514786242043975137949 12108943044840766490676731)
        ·
          refine ⟨18163414567261149736015097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12108943044840766490676731 18163414567261149736015097)
          ·
            refine ⟨13622560925445862302011323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18163414567261149736015097 13622560925445862302011323)
            ·
              refine ⟨20433841388168793453016985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13622560925445862302011323 20433841388168793453016985)
              ·
                refine ⟨15325381041126595089762739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20433841388168793453016985 15325381041126595089762739)
                ·
                  refine ⟨22988071561689892634644109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15325381041126595089762739 22988071561689892634644109)
                  ·
                    refine ⟨8620526835633709737991541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22988071561689892634644109 8620526835633709737991541)
                    ·
                      refine ⟨808174390840660287936707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8620526835633709737991541 808174390840660287936707)
                      ·
                        rfl

theorem cell23_1573914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_1573914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573914 prefixEnd_1573914 := by exact prefixLift 1573914
  have htrace : WordTrace (prefixWord ++ tailWord_1573914) baseStart_1573914 baseEnd_1573914 := by
    simpa [prefixWord, tailWord_1573914, baseEnd_1573914] using wordTrace_append hprefix tailTrace_1573914
  have hstable : (prefixWord ++ tailWord_1573914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573914).length < 2 ^ (prefixWord ++ tailWord_1573914).sum := by decide
  have hdescent : baseEnd_1573914 < baseStart_1573914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573922 : List Nat := [3, 3, 1, 1, 1, 5, 2, 1, 2, 1, 3]
def baseStart_1573922 : Nat := 118140960795 + 1573922 * 2 ^ 59
def prefixEnd_1573922 : Nat := 4983230072969 + 3 ^ 40 * 1573922 * 2
def baseEnd_1573922 : Nat := 808178498685896256636671

theorem tailTrace_1573922 : CollatzResearch.WordTrace tailWord_1573922 prefixEnd_1573922 808178498685896256636671 := by
  unfold tailWord_1573922
  simp only [CollatzResearch.WordTrace]
  refine ⟨14351412850989218330523005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38270434269304582214728013 14351412850989218330523005)
  ·
    refine ⟨5381779819120956873946127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14351412850989218330523005 5381779819120956873946127)
    ·
      refine ⟨8072669728681435310919191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5381779819120956873946127 8072669728681435310919191)
      ·
        refine ⟨12109004593022152966378787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8072669728681435310919191 12109004593022152966378787)
        ·
          refine ⟨18163506889533229449568181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12109004593022152966378787 18163506889533229449568181)
          ·
            refine ⟨1702828770893740260897017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18163506889533229449568181 1702828770893740260897017)
            ·
              refine ⟨1277121578170305195672763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1702828770893740260897017 1277121578170305195672763)
              ·
                refine ⟨1915682367255457793509145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1277121578170305195672763 1915682367255457793509145)
                ·
                  refine ⟨1436761775441593345131859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1915682367255457793509145 1436761775441593345131859)
                  ·
                    refine ⟨2155142663162390017697789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1436761775441593345131859 2155142663162390017697789)
                    ·
                      refine ⟨808178498685896256636671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2155142663162390017697789 808178498685896256636671)
                      ·
                        rfl

theorem cell23_1573922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_1573922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573922 prefixEnd_1573922 := by exact prefixLift 1573922
  have htrace : WordTrace (prefixWord ++ tailWord_1573922) baseStart_1573922 baseEnd_1573922 := by
    simpa [prefixWord, tailWord_1573922, baseEnd_1573922] using wordTrace_append hprefix tailTrace_1573922
  have hstable : (prefixWord ++ tailWord_1573922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573922).length < 2 ^ (prefixWord ++ tailWord_1573922).sum := by decide
  have hdescent : baseEnd_1573922 < baseStart_1573922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573951 : List Nat := [1, 1, 2, 2, 3, 1, 1, 7, 5]
def baseStart_1573951 : Nat := 118140960795 + 1573951 * 2 ^ 59
def prefixEnd_1573951 : Nat := 4983230072969 + 3 ^ 40 * 1573951 * 2
def baseEnd_1573951 : Nat := 89799265513875182574893

theorem tailTrace_1573951 : CollatzResearch.WordTrace tailWord_1573951 prefixEnd_1573951 89799265513875182574893 := by
  unfold tailWord_1573951
  simp only [CollatzResearch.WordTrace]
  refine ⟨57406709120851811274897707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38271139413901207516598471 57406709120851811274897707)
  ·
    refine ⟨86110063681277716912346561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57406709120851811274897707 86110063681277716912346561)
    ·
      refine ⟨64582547760958287684259921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86110063681277716912346561 64582547760958287684259921)
      ·
        refine ⟨48436910820718715763194941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64582547760958287684259921 48436910820718715763194941)
        ·
          refine ⟨18163841557769518411198103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48436910820718715763194941 18163841557769518411198103)
          ·
            refine ⟨27245762336654277616797155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18163841557769518411198103 27245762336654277616797155)
            ·
              refine ⟨40868643504981416425195733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27245762336654277616797155 40868643504981416425195733)
              ·
                refine ⟨957858832148001947465525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 40868643504981416425195733 957858832148001947465525)
                ·
                  refine ⟨89799265513875182574893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 957858832148001947465525 89799265513875182574893)
                  ·
                    rfl

theorem cell23_1573951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 7, 5].length) (baseStart_1573951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573951 prefixEnd_1573951 := by exact prefixLift 1573951
  have htrace : WordTrace (prefixWord ++ tailWord_1573951) baseStart_1573951 baseEnd_1573951 := by
    simpa [prefixWord, tailWord_1573951, baseEnd_1573951] using wordTrace_append hprefix tailTrace_1573951
  have hstable : (prefixWord ++ tailWord_1573951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573951).length < 2 ^ (prefixWord ++ tailWord_1573951).sum := by decide
  have hdescent : baseEnd_1573951 < baseStart_1573951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573964 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 3, 7]
def baseStart_1573964 : Nat := 118140960795 + 1573964 * 2 ^ 59
def prefixEnd_1573964 : Nat := 4983230072969 + 3 ^ 40 * 1573964 * 2
def baseEnd_1573964 : Nat := 269400021624461697437159

theorem tailTrace_1573964 : CollatzResearch.WordTrace tailWord_1573964 prefixEnd_1573964 269400021624461697437159 := by
  unfold tailWord_1573964
  simp only [CollatzResearch.WordTrace]
  refine ⟨28703591634902357247560473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38271455513203142996747297 28703591634902357247560473)
  ·
    refine ⟨21527693726176767935670355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28703591634902357247560473 21527693726176767935670355)
    ·
      refine ⟨32291540589265151903505533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21527693726176767935670355 32291540589265151903505533)
      ·
        refine ⟨12109327720974431963814575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32291540589265151903505533 12109327720974431963814575)
        ·
          refine ⟨18163991581461647945721863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12109327720974431963814575 18163991581461647945721863)
          ·
            refine ⟨27245987372192471918582795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18163991581461647945721863 27245987372192471918582795)
            ·
              refine ⟨40868981058288707877874193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27245987372192471918582795 40868981058288707877874193)
              ·
                refine ⟨30651735793716530908405645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40868981058288707877874193 30651735793716530908405645)
                ·
                  refine ⟨11494400922643699090652117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30651735793716530908405645 11494400922643699090652117)
                  ·
                    refine ⟨269400021624461697437159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11494400922643699090652117 269400021624461697437159)
                    ·
                      rfl

theorem cell23_1573964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 3, 7].length) (baseStart_1573964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573964 prefixEnd_1573964 := by exact prefixLift 1573964
  have htrace : WordTrace (prefixWord ++ tailWord_1573964) baseStart_1573964 baseEnd_1573964 := by
    simpa [prefixWord, tailWord_1573964, baseEnd_1573964] using wordTrace_append hprefix tailTrace_1573964
  have hstable : (prefixWord ++ tailWord_1573964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573964).length < 2 ^ (prefixWord ++ tailWord_1573964).sum := by decide
  have hdescent : baseEnd_1573964 < baseStart_1573964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573971 : List Nat := [1, 1, 1, 2, 1, 1, 2, 5, 2, 5, 2]
def baseStart_1573971 : Nat := 118140960795 + 1573971 * 2 ^ 59
def prefixEnd_1573971 : Nat := 4983230072969 + 3 ^ 40 * 1573971 * 2
def baseEnd_1573971 : Nat := 808203659237966564923945

theorem tailTrace_1573971 : CollatzResearch.WordTrace tailWord_1573971 prefixEnd_1573971 808203659237966564923945 := by
  unfold tailWord_1573971
  simp only [CollatzResearch.WordTrace]
  refine ⟨57407438580779354690625767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38271625720519569793750511 57407438580779354690625767)
  ·
    refine ⟨86111157871169032035938651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57407438580779354690625767 86111157871169032035938651)
    ·
      refine ⟨129166736806753548053907977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86111157871169032035938651 129166736806753548053907977)
      ·
        refine ⟨96875052605065161040430983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129166736806753548053907977 96875052605065161040430983)
        ·
          refine ⟨145312578907597741560646475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96875052605065161040430983 145312578907597741560646475)
          ·
            refine ⟨217968868361396612340969713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145312578907597741560646475 217968868361396612340969713)
            ·
              refine ⟨163476651271047459255727285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217968868361396612340969713 163476651271047459255727285)
              ·
                refine ⟨15325936056660699305224433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 163476651271047459255727285 15325936056660699305224433)
                ·
                  refine ⟨11494452042495524478918325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15325936056660699305224433 11494452042495524478918325)
                  ·
                    refine ⟨1077604878983955419898593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11494452042495524478918325 1077604878983955419898593)
                    ·
                      refine ⟨808203659237966564923945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1077604878983955419898593 808203659237966564923945)
                      ·
                        rfl

theorem cell23_1573971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 5, 2].length) (baseStart_1573971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573971 prefixEnd_1573971 := by exact prefixLift 1573971
  have htrace : WordTrace (prefixWord ++ tailWord_1573971) baseStart_1573971 baseEnd_1573971 := by
    simpa [prefixWord, tailWord_1573971, baseEnd_1573971] using wordTrace_append hprefix tailTrace_1573971
  have hstable : (prefixWord ++ tailWord_1573971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573971).length < 2 ^ (prefixWord ++ tailWord_1573971).sum := by decide
  have hdescent : baseEnd_1573971 < baseStart_1573971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573998 : List Nat := [4, 1, 2, 2, 1, 2, 3, 1, 2, 5]
def baseStart_1573998 : Nat := 118140960795 + 1573998 * 2 ^ 59
def prefixEnd_1573998 : Nat := 4983230072969 + 3 ^ 40 * 1573998 * 2
def baseEnd_1573998 : Nat := 269405841071879319762107

theorem tailTrace_1573998 : CollatzResearch.WordTrace tailWord_1573998 prefixEnd_1573998 269405841071879319762107 := by
  unfold tailWord_1573998
  simp only [CollatzResearch.WordTrace]
  refine ⟨7176052918960192287732331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38272282234454358867905765 7176052918960192287732331)
  ·
    refine ⟨10764079378440288431598497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7176052918960192287732331 10764079378440288431598497)
    ·
      refine ⟨8073059533830216323698873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10764079378440288431598497 8073059533830216323698873)
      ·
        refine ⟨6054794650372662242774155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8073059533830216323698873 6054794650372662242774155)
        ·
          refine ⟨9082191975558993364161233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6054794650372662242774155 9082191975558993364161233)
          ·
            refine ⟨6811643981669245023120925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9082191975558993364161233 6811643981669245023120925)
            ·
              refine ⟨2554366493125966883670347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6811643981669245023120925 2554366493125966883670347)
              ·
                refine ⟨3831549739688950325505521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2554366493125966883670347 3831549739688950325505521)
                ·
                  refine ⟨2873662304766712744129141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3831549739688950325505521 2873662304766712744129141)
                  ·
                    refine ⟨269405841071879319762107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2873662304766712744129141 269405841071879319762107)
                    ·
                      rfl

theorem cell23_1573998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_1573998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573998 prefixEnd_1573998 := by exact prefixLift 1573998
  have htrace : WordTrace (prefixWord ++ tailWord_1573998) baseStart_1573998 baseEnd_1573998 := by
    simpa [prefixWord, tailWord_1573998, baseEnd_1573998] using wordTrace_append hprefix tailTrace_1573998
  have hstable : (prefixWord ++ tailWord_1573998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573998).length < 2 ^ (prefixWord ++ tailWord_1573998).sum := by decide
  have hdescent : baseEnd_1573998 < baseStart_1573998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574001 : List Nat := [1, 2, 2, 2, 1, 1, 2, 5, 2, 1, 4]
def baseStart_1574001 : Nat := 118140960795 + 1574001 * 2 ^ 59
def prefixEnd_1574001 : Nat := 4983230072969 + 3 ^ 40 * 1574001 * 2
def baseEnd_1574001 : Nat := 808219063657601447548807

theorem tailTrace_1574001 : CollatzResearch.WordTrace tailWord_1574001 prefixEnd_1574001 808219063657601447548807 := by
  unfold tailWord_1574001
  simp only [CollatzResearch.WordTrace]
  refine ⟨57408532770670669814217857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38272355180447113209478571 57408532770670669814217857)
  ·
    refine ⟨43056399578003002360663393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57408532770670669814217857 43056399578003002360663393)
    ·
      refine ⟨32292299683502251770497545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43056399578003002360663393 32292299683502251770497545)
      ·
        refine ⟨24219224762626688827873159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32292299683502251770497545 24219224762626688827873159)
        ·
          refine ⟨36328837143940033241809739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24219224762626688827873159 36328837143940033241809739)
          ·
            refine ⟨54493255715910049862714609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36328837143940033241809739 54493255715910049862714609)
            ·
              refine ⟨40869941786932537397035957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54493255715910049862714609 40869941786932537397035957)
              ·
                refine ⟨3831557042524925380972121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40869941786932537397035957 3831557042524925380972121)
                ·
                  refine ⟨2873667781893694035729091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3831557042524925380972121 2873667781893694035729091)
                  ·
                    refine ⟨4310501672840541053593637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2873667781893694035729091 4310501672840541053593637)
                    ·
                      refine ⟨808219063657601447548807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4310501672840541053593637 808219063657601447548807)
                      ·
                        rfl

theorem cell23_1574001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_1574001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574001 prefixEnd_1574001 := by exact prefixLift 1574001
  have htrace : WordTrace (prefixWord ++ tailWord_1574001) baseStart_1574001 baseEnd_1574001 := by
    simpa [prefixWord, tailWord_1574001, baseEnd_1574001] using wordTrace_append hprefix tailTrace_1574001
  have hstable : (prefixWord ++ tailWord_1574001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574001).length < 2 ^ (prefixWord ++ tailWord_1574001).sum := by decide
  have hdescent : baseEnd_1574001 < baseStart_1574001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574058 : List Nat := [3, 1, 5, 1, 1, 1, 1, 2, 8]
def baseStart_1574058 : Nat := 118140960795 + 1574058 * 2 ^ 59
def prefixEnd_1574058 : Nat := 4983230072969 + 3 ^ 40 * 1574058 * 2
def baseEnd_1574058 : Nat := 89805370228323080504005

theorem tailTrace_1574058 : CollatzResearch.WordTrace tailWord_1574058 prefixEnd_1574058 89805370228323080504005 := by
  unfold tailWord_1574058
  simp only [CollatzResearch.WordTrace]
  refine ⟨14352652932866042137260707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38273741154309445699361885 14352652932866042137260707)
  ·
    refine ⟨21528979399299063205891061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14352652932866042137260707 21528979399299063205891061)
    ·
      refine ⟨2018341818684287175552287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21528979399299063205891061 2018341818684287175552287)
      ·
        refine ⟨3027512728026430763328431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2018341818684287175552287 3027512728026430763328431)
        ·
          refine ⟨4541269092039646144992647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3027512728026430763328431 4541269092039646144992647)
          ·
            refine ⟨6811903638059469217488971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4541269092039646144992647 6811903638059469217488971)
            ·
              refine ⟨10217855457089203826233457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6811903638059469217488971 10217855457089203826233457)
              ·
                refine ⟨7663391592816902869675093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10217855457089203826233457 7663391592816902869675093)
                ·
                  refine ⟨89805370228323080504005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7663391592816902869675093 89805370228323080504005)
                  ·
                    rfl

theorem cell23_1574058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 8].length) (baseStart_1574058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574058 prefixEnd_1574058 := by exact prefixLift 1574058
  have htrace : WordTrace (prefixWord ++ tailWord_1574058) baseStart_1574058 baseEnd_1574058 := by
    simpa [prefixWord, tailWord_1574058, baseEnd_1574058] using wordTrace_append hprefix tailTrace_1574058
  have hstable : (prefixWord ++ tailWord_1574058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574058).length < 2 ^ (prefixWord ++ tailWord_1574058).sum := by decide
  have hdescent : baseEnd_1574058 < baseStart_1574058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574111 : List Nat := [1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 5]
def baseStart_1574111 : Nat := 118140960795 + 1574111 * 2 ^ 59
def prefixEnd_1574111 : Nat := 4983230072969 + 3 ^ 40 * 1574111 * 2
def baseEnd_1574111 : Nat := 808275546529596017173301

theorem tailTrace_1574111 : CollatzResearch.WordTrace tailWord_1574111 prefixEnd_1574111 808275546529596017173301 := by
  unfold tailWord_1574111
  simp only [CollatzResearch.WordTrace]
  refine ⟨57412544800272158600722187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38275029866848105733814791 57412544800272158600722187)
  ·
    refine ⟨86118817200408237901083281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57412544800272158600722187 86118817200408237901083281)
    ·
      refine ⟨64589112900306178425812461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86118817200408237901083281 64589112900306178425812461)
      ·
        refine ⟨24220917337614816909679673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64589112900306178425812461 24220917337614816909679673)
        ·
          refine ⟨18165688003211112682259755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24220917337614816909679673 18165688003211112682259755)
          ·
            refine ⟨27248532004816669023389633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18165688003211112682259755 27248532004816669023389633)
            ·
              refine ⟨20436399003612501767542225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27248532004816669023389633 20436399003612501767542225)
              ·
                refine ⟨15327299252709376325656669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20436399003612501767542225 15327299252709376325656669)
                ·
                  refine ⟨5747737219766016122121251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15327299252709376325656669 5747737219766016122121251)
                  ·
                    refine ⟨8621605829649024183181877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5747737219766016122121251 8621605829649024183181877)
                    ·
                      refine ⟨808275546529596017173301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8621605829649024183181877 808275546529596017173301)
                      ·
                        rfl

theorem cell23_1574111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_1574111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574111 prefixEnd_1574111 := by exact prefixLift 1574111
  have htrace : WordTrace (prefixWord ++ tailWord_1574111) baseStart_1574111 baseEnd_1574111 := by
    simpa [prefixWord, tailWord_1574111, baseEnd_1574111] using wordTrace_append hprefix tailTrace_1574111
  have hstable : (prefixWord ++ tailWord_1574111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574111).length < 2 ^ (prefixWord ++ tailWord_1574111).sum := by decide
  have hdescent : baseEnd_1574111 < baseStart_1574111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574148 : List Nat := [2, 3, 2, 2, 2, 1, 3, 8]
def baseStart_1574148 : Nat := 118140960795 + 1574148 * 2 ^ 59
def prefixEnd_1574148 : Nat := 4983230072969 + 3 ^ 40 * 1574148 * 2
def baseEnd_1574148 : Nat := 29936835011622680459653

theorem tailTrace_1574148 : CollatzResearch.WordTrace tailWord_1574148 prefixEnd_1574148 29936835011622680459653 := by
  unfold tailWord_1574148
  simp only [CollatzResearch.WordTrace]
  refine ⟨28706947150569056959909549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38275929534092075946546065 28706947150569056959909549)
  ·
    refine ⟨10765105181463396359966081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28706947150569056959909549 10765105181463396359966081)
    ·
      refine ⟨8073828886097547269974561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10765105181463396359966081 8073828886097547269974561)
      ·
        refine ⟨6055371664573160452480921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8073828886097547269974561 6055371664573160452480921)
        ·
          refine ⟨4541528748429870339360691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6055371664573160452480921 4541528748429870339360691)
          ·
            refine ⟨6812293122644805509041037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4541528748429870339360691 6812293122644805509041037)
            ·
              refine ⟨2554609920991802065890389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6812293122644805509041037 2554609920991802065890389)
              ·
                refine ⟨29936835011622680459653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2554609920991802065890389 29936835011622680459653)
                ·
                  rfl

theorem cell23_1574148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 8].length) (baseStart_1574148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574148 prefixEnd_1574148 := by exact prefixLift 1574148
  have htrace : WordTrace (prefixWord ++ tailWord_1574148) baseStart_1574148 baseEnd_1574148 := by
    simpa [prefixWord, tailWord_1574148, baseEnd_1574148] using wordTrace_append hprefix tailTrace_1574148
  have hstable : (prefixWord ++ tailWord_1574148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574148).length < 2 ^ (prefixWord ++ tailWord_1574148).sum := by decide
  have hdescent : baseEnd_1574148 < baseStart_1574148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574161 : List Nat := [1, 2, 2, 1, 1, 4, 1, 2, 2, 7]
def baseStart_1574161 : Nat := 118140960795 + 1574161 * 2 ^ 59
def prefixEnd_1574161 : Nat := 4983230072969 + 3 ^ 40 * 1574161 * 2
def baseEnd_1574161 : Nat := 269433740187440273849357

theorem tailTrace_1574161 : CollatzResearch.WordTrace tailWord_1574161 prefixEnd_1574161 269433740187440273849357 := by
  unfold tailWord_1574161
  simp only [CollatzResearch.WordTrace]
  refine ⟨57414368450091017140042337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38276245633394011426694891 57414368450091017140042337)
  ·
    refine ⟨43060776337568262855031753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57414368450091017140042337 43060776337568262855031753)
    ·
      refine ⟨32295582253176197141273815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43060776337568262855031753 32295582253176197141273815)
      ·
        refine ⟨48443373379764295711910723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32295582253176197141273815 48443373379764295711910723)
        ·
          refine ⟨72665060069646443567866085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48443373379764295711910723 72665060069646443567866085)
          ·
            refine ⟨13624698763058708168974891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72665060069646443567866085 13624698763058708168974891)
            ·
              refine ⟨20437048144588062253462337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13624698763058708168974891 20437048144588062253462337)
              ·
                refine ⟨15327786108441046690096753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20437048144588062253462337 15327786108441046690096753)
                ·
                  refine ⟨11495839581330785017572565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15327786108441046690096753 11495839581330785017572565)
                  ·
                    refine ⟨269433740187440273849357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11495839581330785017572565 269433740187440273849357)
                    ·
                      rfl

theorem cell23_1574161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 7].length) (baseStart_1574161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574161 prefixEnd_1574161 := by exact prefixLift 1574161
  have htrace : WordTrace (prefixWord ++ tailWord_1574161) baseStart_1574161 baseEnd_1574161 := by
    simpa [prefixWord, tailWord_1574161, baseEnd_1574161] using wordTrace_append hprefix tailTrace_1574161
  have hstable : (prefixWord ++ tailWord_1574161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574161).length < 2 ^ (prefixWord ++ tailWord_1574161).sum := by decide
  have hdescent : baseEnd_1574161 < baseStart_1574161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574171 : List Nat := [1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 5]
def baseStart_1574171 : Nat := 118140960795 + 1574171 * 2 ^ 59
def prefixEnd_1574171 : Nat := 4983230072969 + 3 ^ 40 * 1574171 * 2
def baseEnd_1574171 : Nat := 808306355368865782423025

theorem tailTrace_1574171 : CollatzResearch.WordTrace tailWord_1574171 prefixEnd_1574171 808306355368865782423025 := by
  unfold tailWord_1574171
  simp only [CollatzResearch.WordTrace]
  refine ⟨57414733180054788847906367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38276488786703192565270911 57414733180054788847906367)
  ·
    refine ⟨86122099770082183271859551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57414733180054788847906367 86122099770082183271859551)
    ·
      refine ⟨129183149655123274907789327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86122099770082183271859551 129183149655123274907789327)
      ·
        refine ⟨193774724482684912361683991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129183149655123274907789327 193774724482684912361683991)
        ·
          refine ⟨290662086724027368542525987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193774724482684912361683991 290662086724027368542525987)
          ·
            refine ⟨435993130086041052813788981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290662086724027368542525987 435993130086041052813788981)
            ·
              refine ⟨40874355945566348701292717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 435993130086041052813788981 40874355945566348701292717)
              ·
                refine ⟨15327883479587380762984769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40874355945566348701292717 15327883479587380762984769)
                ·
                  refine ⟨11495912609690535572238577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15327883479587380762984769 11495912609690535572238577)
                  ·
                    refine ⟨8621934457267901679178933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11495912609690535572238577 8621934457267901679178933)
                    ·
                      refine ⟨808306355368865782423025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8621934457267901679178933 808306355368865782423025)
                      ·
                        rfl

theorem cell23_1574171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 5].length) (baseStart_1574171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574171 prefixEnd_1574171 := by exact prefixLift 1574171
  have htrace : WordTrace (prefixWord ++ tailWord_1574171) baseStart_1574171 baseEnd_1574171 := by
    simpa [prefixWord, tailWord_1574171, baseEnd_1574171] using wordTrace_append hprefix tailTrace_1574171
  have hstable : (prefixWord ++ tailWord_1574171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574171).length < 2 ^ (prefixWord ++ tailWord_1574171).sum := by decide
  have hdescent : baseEnd_1574171 < baseStart_1574171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574176 : List Nat := [2, 1, 1, 5, 3, 1, 2, 3, 1, 2, 2]
def baseStart_1574176 : Nat := 118140960795 + 1574176 * 2 ^ 59
def prefixEnd_1574176 : Nat := 4983230072969 + 3 ^ 40 * 1574176 * 2
def baseEnd_1574176 : Nat := 808308922772138262860503

theorem tailTrace_1574176 : CollatzResearch.WordTrace tailWord_1574176 prefixEnd_1574176 808308922772138262860503 := by
  unfold tailWord_1574176
  simp only [CollatzResearch.WordTrace]
  refine ⟨28707457772518337350919191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38276610363357783134558921 28707457772518337350919191)
  ·
    refine ⟨43061186658777506026378787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28707457772518337350919191 43061186658777506026378787)
    ·
      refine ⟨64591779988166259039568181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43061186658777506026378787 64591779988166259039568181)
      ·
        refine ⟨6055479373890586784959517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64591779988166259039568181 6055479373890586784959517)
        ·
          refine ⟨2270804765208970044359819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6055479373890586784959517 2270804765208970044359819)
          ·
            refine ⟨3406207147813455066539729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2270804765208970044359819 3406207147813455066539729)
            ·
              refine ⟨2554655360860091299904797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3406207147813455066539729 2554655360860091299904797)
              ·
                refine ⟨957995760322534237464299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2554655360860091299904797 957995760322534237464299)
                ·
                  refine ⟨1436993640483801356196449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 957995760322534237464299 1436993640483801356196449)
                  ·
                    refine ⟨1077745230362851017147337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1436993640483801356196449 1077745230362851017147337)
                    ·
                      refine ⟨808308922772138262860503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1077745230362851017147337 808308922772138262860503)
                      ·
                        rfl

theorem cell23_1574176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_1574176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574176 prefixEnd_1574176 := by exact prefixLift 1574176
  have htrace : WordTrace (prefixWord ++ tailWord_1574176) baseStart_1574176 baseEnd_1574176 := by
    simpa [prefixWord, tailWord_1574176, baseEnd_1574176] using wordTrace_append hprefix tailTrace_1574176
  have hstable : (prefixWord ++ tailWord_1574176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574176).length < 2 ^ (prefixWord ++ tailWord_1574176).sum := by decide
  have hdescent : baseEnd_1574176 < baseStart_1574176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574218 : List Nat := [3, 1, 2, 1, 1, 1, 1, 4, 2, 4, 3]
def baseStart_1574218 : Nat := 118140960795 + 1574218 * 2 ^ 59
def prefixEnd_1574218 : Nat := 4983230072969 + 3 ^ 40 * 1574218 * 2
def baseEnd_1574218 : Nat := 808330488959627098535309

theorem tailTrace_1574218 : CollatzResearch.WordTrace tailWord_1574218 prefixEnd_1574218 808330488959627098535309 := by
  unfold tailWord_1574218
  simp only [CollatzResearch.WordTrace]
  refine ⟨14354111852721128968716827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38277631607256343916578205 14354111852721128968716827)
  ·
    refine ⟨21531167779081693453075241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14354111852721128968716827 21531167779081693453075241)
    ·
      refine ⟨16148375834311270089806431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21531167779081693453075241 16148375834311270089806431)
      ·
        refine ⟨24222563751466905134709647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16148375834311270089806431 24222563751466905134709647)
        ·
          refine ⟨36333845627200357702064471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24222563751466905134709647 36333845627200357702064471)
          ·
            refine ⟨54500768440800536553096707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36333845627200357702064471 54500768440800536553096707)
            ·
              refine ⟨81751152661200804829645061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54500768440800536553096707 81751152661200804829645061)
              ·
                refine ⟨15328341123975150905558449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81751152661200804829645061 15328341123975150905558449)
                ·
                  refine ⟨11496255842981363179168837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15328341123975150905558449 11496255842981363179168837)
                  ·
                    refine ⟨2155547970559005596094157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11496255842981363179168837 2155547970559005596094157)
                    ·
                      refine ⟨808330488959627098535309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2155547970559005596094157 808330488959627098535309)
                      ·
                        rfl

theorem cell23_1574218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 2, 4, 3].length) (baseStart_1574218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574218 prefixEnd_1574218 := by exact prefixLift 1574218
  have htrace : WordTrace (prefixWord ++ tailWord_1574218) baseStart_1574218 baseEnd_1574218 := by
    simpa [prefixWord, tailWord_1574218, baseEnd_1574218] using wordTrace_append hprefix tailTrace_1574218
  have hstable : (prefixWord ++ tailWord_1574218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574218).length < 2 ^ (prefixWord ++ tailWord_1574218).sum := by decide
  have hdescent : baseEnd_1574218 < baseStart_1574218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574268 : List Nat := [2, 2, 2, 1, 1, 1, 3, 2, 4, 5]
def baseStart_1574268 : Nat := 118140960795 + 1574268 * 2 ^ 59
def prefixEnd_1574268 : Nat := 4983230072969 + 3 ^ 40 * 1574268 * 2
def baseEnd_1574268 : Nat := 269452054330783967636693

theorem tailTrace_1574268 : CollatzResearch.WordTrace tailWord_1574268 prefixEnd_1574268 269452054330783967636693 := by
  unfold tailWord_1574268
  simp only [CollatzResearch.WordTrace]
  refine ⟨28709135530351687207093729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38278847373802249609458305 28709135530351687207093729)
  ·
    refine ⟨21531851647763765405320297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28709135530351687207093729 21531851647763765405320297)
    ·
      refine ⟨16148888735822824053990223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21531851647763765405320297 16148888735822824053990223)
      ·
        refine ⟨24223333103734236080985335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16148888735822824053990223 24223333103734236080985335)
        ·
          refine ⟨36334999655601354121478003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24223333103734236080985335 36334999655601354121478003)
          ·
            refine ⟨54502499483402031182217005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36334999655601354121478003 54502499483402031182217005)
            ·
              refine ⟨20438437306275761693331377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54502499483402031182217005 20438437306275761693331377)
              ·
                refine ⟨15328827979706821269998533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20438437306275761693331377 15328827979706821269998533)
                ·
                  refine ⟨2874155246195028988124725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15328827979706821269998533 2874155246195028988124725)
                  ·
                    refine ⟨269452054330783967636693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2874155246195028988124725 269452054330783967636693)
                    ·
                      rfl

theorem cell23_1574268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_1574268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574268 prefixEnd_1574268 := by exact prefixLift 1574268
  have htrace : WordTrace (prefixWord ++ tailWord_1574268) baseStart_1574268 baseEnd_1574268 := by
    simpa [prefixWord, tailWord_1574268, baseEnd_1574268] using wordTrace_append hprefix tailTrace_1574268
  have hstable : (prefixWord ++ tailWord_1574268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574268).length < 2 ^ (prefixWord ++ tailWord_1574268).sum := by decide
  have hdescent : baseEnd_1574268 < baseStart_1574268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574270 : List Nat := [4, 2, 3, 2, 2, 1, 1, 2, 1, 3, 2]
def baseStart_1574270 : Nat := 118140960795 + 1574270 * 2 ^ 59
def prefixEnd_1574270 : Nat := 4983230072969 + 3 ^ 40 * 1574270 * 2
def baseEnd_1574270 : Nat := 808357189953660895085071

theorem tailTrace_1574270 : CollatzResearch.WordTrace tailWord_1574270 prefixEnd_1574270 808357189953660895085071 := by
  unfold tailWord_1574270
  simp only [CollatzResearch.WordTrace]
  refine ⟨7177293000837016094470033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38278896004464085837173509 7177293000837016094470033)
  ·
    refine ⟨5382969750627762070852525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7177293000837016094470033 5382969750627762070852525)
    ·
      refine ⟨2018613656485410776569697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5382969750627762070852525 2018613656485410776569697)
      ·
        refine ⟨1513960242364058082427273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2018613656485410776569697 1513960242364058082427273)
        ·
          refine ⟨1135470181773043561820455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1513960242364058082427273 1135470181773043561820455)
          ·
            refine ⟨1703205272659565342730683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1135470181773043561820455 1703205272659565342730683)
            ·
              refine ⟨2554807908989348014096025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1703205272659565342730683 2554807908989348014096025)
              ·
                refine ⟨1916105931742011010572019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2554807908989348014096025 1916105931742011010572019)
                ·
                  refine ⟨2874158897613016515858029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1916105931742011010572019 2874158897613016515858029)
                  ·
                    refine ⟨1077809586604881193446761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2874158897613016515858029 1077809586604881193446761)
                    ·
                      refine ⟨808357189953660895085071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1077809586604881193446761 808357189953660895085071)
                      ·
                        rfl

theorem cell23_1574270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_1574270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574270 prefixEnd_1574270 := by exact prefixLift 1574270
  have htrace : WordTrace (prefixWord ++ tailWord_1574270) baseStart_1574270 baseEnd_1574270 := by
    simpa [prefixWord, tailWord_1574270, baseEnd_1574270] using wordTrace_append hprefix tailTrace_1574270
  have hstable : (prefixWord ++ tailWord_1574270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574270).length < 2 ^ (prefixWord ++ tailWord_1574270).sum := by decide
  have hdescent : baseEnd_1574270 < baseStart_1574270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574308 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 1, 5, 5]
def baseStart_1574308 : Nat := 118140960795 + 1574308 * 2 ^ 59
def prefixEnd_1574308 : Nat := 4983230072969 + 3 ^ 40 * 1574308 * 2
def baseEnd_1574308 : Nat := 808376702218531746409895

theorem tailTrace_1574308 : CollatzResearch.WordTrace tailWord_1574308 prefixEnd_1574308 808376702218531746409895 := by
  unfold tailWord_1574308
  simp only [CollatzResearch.WordTrace]
  refine ⟨28709864990279230622821789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38279819987038974163762385 28709864990279230622821789)
  ·
    refine ⟨10766199371354711483558171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28709864990279230622821789 10766199371354711483558171)
    ·
      refine ⟨16149299057032067225337257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10766199371354711483558171 16149299057032067225337257)
      ·
        refine ⟨12111974292774050419002943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16149299057032067225337257 12111974292774050419002943)
        ·
          refine ⟨18167961439161075628504415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12111974292774050419002943 18167961439161075628504415)
          ·
            refine ⟨27251942158741613442756623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18167961439161075628504415 27251942158741613442756623)
            ·
              refine ⟨40877913238112420164134935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27251942158741613442756623 40877913238112420164134935)
              ·
                refine ⟨61316869857168630246202403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40877913238112420164134935 61316869857168630246202403)
                ·
                  refine ⟨91975304785752945369303605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61316869857168630246202403 91975304785752945369303605)
                  ·
                    refine ⟨8622684823664338628372213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 91975304785752945369303605 8622684823664338628372213)
                    ·
                      refine ⟨808376702218531746409895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8622684823664338628372213 808376702218531746409895)
                      ·
                        rfl

theorem cell23_1574308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_1574308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574308 prefixEnd_1574308 := by exact prefixLift 1574308
  have htrace : WordTrace (prefixWord ++ tailWord_1574308) baseStart_1574308 baseEnd_1574308 := by
    simpa [prefixWord, tailWord_1574308, baseEnd_1574308] using wordTrace_append hprefix tailTrace_1574308
  have hstable : (prefixWord ++ tailWord_1574308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574308).length < 2 ^ (prefixWord ++ tailWord_1574308).sum := by decide
  have hdescent : baseEnd_1574308 < baseStart_1574308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574362 : List Nat := [3, 1, 1, 2, 3, 4, 1, 2, 6]
def baseStart_1574362 : Nat := 118140960795 + 1574362 * 2 ^ 59
def prefixEnd_1574362 : Nat := 4983230072969 + 3 ^ 40 * 1574362 * 2
def baseEnd_1574362 : Nat := 89822714463763837237183

theorem tailTrace_1574362 : CollatzResearch.WordTrace tailWord_1574362 prefixEnd_1574362 89822714463763837237183 := by
  unfold tailWord_1574362
  simp only [CollatzResearch.WordTrace]
  refine ⟨14355424880590707117027335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38281133014908552312072893 14355424880590707117027335)
  ·
    refine ⟨21533137320886060675541003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14355424880590707117027335 21533137320886060675541003)
    ·
      refine ⟨32299705981329091013311505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21533137320886060675541003 32299705981329091013311505)
      ·
        refine ⟨24224779485996818259983629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32299705981329091013311505 24224779485996818259983629)
        ·
          refine ⟨9084292307248806847493861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24224779485996818259983629 9084292307248806847493861)
          ·
            refine ⟨1703304807609151283905099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9084292307248806847493861 1703304807609151283905099)
            ·
              refine ⟨2554957211413726925857649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1703304807609151283905099 2554957211413726925857649)
              ·
                refine ⟨1916217908560295194393237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2554957211413726925857649 1916217908560295194393237)
                ·
                  refine ⟨89822714463763837237183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1916217908560295194393237 89822714463763837237183)
                  ·
                    rfl

theorem cell23_1574362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 6].length) (baseStart_1574362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574362 prefixEnd_1574362 := by exact prefixLift 1574362
  have htrace : WordTrace (prefixWord ++ tailWord_1574362) baseStart_1574362 baseEnd_1574362 := by
    simpa [prefixWord, tailWord_1574362, baseEnd_1574362] using wordTrace_append hprefix tailTrace_1574362
  have hstable : (prefixWord ++ tailWord_1574362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574362).length < 2 ^ (prefixWord ++ tailWord_1574362).sum := by decide
  have hdescent : baseEnd_1574362 < baseStart_1574362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574365 : List Nat := [1, 4, 3, 1, 1, 2, 1, 1, 1, 2, 6]
def baseStart_1574365 : Nat := 118140960795 + 1574365 * 2 ^ 59
def prefixEnd_1574365 : Nat := 4983230072969 + 3 ^ 40 * 1574365 * 2
def baseEnd_1574365 : Nat := 808405970615838023397133

theorem tailTrace_1574365 : CollatzResearch.WordTrace tailWord_1574365 prefixEnd_1574365 808405970615838023397133 := by
  unfold tailWord_1574365
  simp only [CollatzResearch.WordTrace]
  refine ⟨57421808941351959980468549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38281205960901306653645699 57421808941351959980468549)
  ·
    refine ⟨10766589176503492496337853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57421808941351959980468549 10766589176503492496337853)
    ·
      refine ⟨4037470941188809686126695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10766589176503492496337853 4037470941188809686126695)
      ·
        refine ⟨6056206411783214529190043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4037470941188809686126695 6056206411783214529190043)
        ·
          refine ⟨9084309617674821793785065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6056206411783214529190043 9084309617674821793785065)
          ·
            refine ⟨6813232213256116345338799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9084309617674821793785065 6813232213256116345338799)
            ·
              refine ⟨10219848319884174518008199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6813232213256116345338799 10219848319884174518008199)
              ·
                refine ⟨15329772479826261777012299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10219848319884174518008199 15329772479826261777012299)
                ·
                  refine ⟨22994658719739392665518449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15329772479826261777012299 22994658719739392665518449)
                  ·
                    refine ⟨17245994039804544499138837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22994658719739392665518449 17245994039804544499138837)
                    ·
                      refine ⟨808405970615838023397133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17245994039804544499138837 808405970615838023397133)
                      ·
                        rfl

theorem cell23_1574365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_1574365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574365 prefixEnd_1574365 := by exact prefixLift 1574365
  have htrace : WordTrace (prefixWord ++ tailWord_1574365) baseStart_1574365 baseEnd_1574365 := by
    simpa [prefixWord, tailWord_1574365, baseEnd_1574365] using wordTrace_append hprefix tailTrace_1574365
  have hstable : (prefixWord ++ tailWord_1574365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574365).length < 2 ^ (prefixWord ++ tailWord_1574365).sum := by decide
  have hdescent : baseEnd_1574365 < baseStart_1574365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574368 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 7]
def baseStart_1574368 : Nat := 118140960795 + 1574368 * 2 ^ 59
def prefixEnd_1574368 : Nat := 4983230072969 + 3 ^ 40 * 1574368 * 2
def baseEnd_1574368 : Nat := 808407511057801511659619

theorem tailTrace_1574368 : CollatzResearch.WordTrace tailWord_1574368 prefixEnd_1574368 808407511057801511659619 := by
  unfold tailWord_1574368
  simp only [CollatzResearch.WordTrace]
  refine ⟨28710959180170545746413879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38281278906894060995218505 28710959180170545746413879)
  ·
    refine ⟨43066438770255818619620819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28710959180170545746413879 43066438770255818619620819)
    ·
      refine ⟨64599658155383727929431229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43066438770255818619620819 64599658155383727929431229)
      ·
        refine ⟨24224871808268897973536711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64599658155383727929431229 24224871808268897973536711)
        ·
          refine ⟨36337307712403346960305067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24224871808268897973536711 36337307712403346960305067)
          ·
            refine ⟨54505961568605020440457601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36337307712403346960305067 54505961568605020440457601)
            ·
              refine ⟨40879471176453765330343201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54505961568605020440457601 40879471176453765330343201)
              ·
                refine ⟨30659603382340323997757401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40879471176453765330343201 30659603382340323997757401)
                ·
                  refine ⟨22994702536755242998318051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30659603382340323997757401 22994702536755242998318051)
                  ·
                    refine ⟨34492053805132864497477077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22994702536755242998318051 34492053805132864497477077)
                    ·
                      refine ⟨808407511057801511659619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 34492053805132864497477077 808407511057801511659619)
                      ·
                        rfl

theorem cell23_1574368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_1574368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574368 prefixEnd_1574368 := by exact prefixLift 1574368
  have htrace : WordTrace (prefixWord ++ tailWord_1574368) baseStart_1574368 baseEnd_1574368 := by
    simpa [prefixWord, tailWord_1574368, baseEnd_1574368] using wordTrace_append hprefix tailTrace_1574368
  have hstable : (prefixWord ++ tailWord_1574368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574368).length < 2 ^ (prefixWord ++ tailWord_1574368).sum := by decide
  have hdescent : baseEnd_1574368 < baseStart_1574368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574382 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 3, 5, 2]
def baseStart_1574382 : Nat := 118140960795 + 1574382 * 2 ^ 59
def prefixEnd_1574382 : Nat := 4983230072969 + 3 ^ 40 * 1574382 * 2
def baseEnd_1574382 : Nat := 808414699786964456884555

theorem tailTrace_1574382 : CollatzResearch.WordTrace tailWord_1574382 prefixEnd_1574382 808414699786964456884555 := by
  unfold tailWord_1574382
  simp only [CollatzResearch.WordTrace]
  refine ⟨7177803622786296485479675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38281619321526914589224933 7177803622786296485479675)
  ·
    refine ⟨10766705434179444728219513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7177803622786296485479675 10766705434179444728219513)
    ·
      refine ⟨8075029075634583546164635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10766705434179444728219513 8075029075634583546164635)
      ·
        refine ⟨12112543613451875319246953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8075029075634583546164635 12112543613451875319246953)
        ·
          refine ⟨9084407710088906489435215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12112543613451875319246953 9084407710088906489435215)
          ·
            refine ⟨13626611565133359734152823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9084407710088906489435215 13626611565133359734152823)
            ·
              refine ⟨20439917347700039601229235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13626611565133359734152823 20439917347700039601229235)
              ·
                refine ⟨30659876021550059401843853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20439917347700039601229235 30659876021550059401843853)
                ·
                  refine ⟨11497453508081272275691445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30659876021550059401843853 11497453508081272275691445)
                  ·
                    refine ⟨1077886266382619275846073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11497453508081272275691445 1077886266382619275846073)
                    ·
                      refine ⟨808414699786964456884555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1077886266382619275846073 808414699786964456884555)
                      ·
                        rfl

theorem cell23_1574382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_1574382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574382 prefixEnd_1574382 := by exact prefixLift 1574382
  have htrace : WordTrace (prefixWord ++ tailWord_1574382) baseStart_1574382 baseEnd_1574382 := by
    simpa [prefixWord, tailWord_1574382, baseEnd_1574382] using wordTrace_append hprefix tailTrace_1574382
  have hstable : (prefixWord ++ tailWord_1574382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574382).length < 2 ^ (prefixWord ++ tailWord_1574382).sum := by decide
  have hdescent : baseEnd_1574382 < baseStart_1574382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574392 : List Nat := [2, 1, 2, 1, 1, 6, 2, 2, 1, 5]
def baseStart_1574392 : Nat := 118140960795 + 1574392 * 2 ^ 59
def prefixEnd_1574392 : Nat := 4983230072969 + 3 ^ 40 * 1574392 * 2
def baseEnd_1574392 : Nat := 269473278197836472586503

theorem tailTrace_1574392 : CollatzResearch.WordTrace tailWord_1574392 prefixEnd_1574392 269473278197836472586503 := by
  unfold tailWord_1574392
  simp only [CollatzResearch.WordTrace]
  refine ⟨28711396856127071795850715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38281862474836095727800953 28711396856127071795850715)
  ·
    refine ⟨43067095284190607693776073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28711396856127071795850715 43067095284190607693776073)
    ·
      refine ⟨32300321463142955770332055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43067095284190607693776073 32300321463142955770332055)
      ·
        refine ⟨48450482194714433655498083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32300321463142955770332055 48450482194714433655498083)
        ·
          refine ⟨72675723292071650483247125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48450482194714433655498083 72675723292071650483247125)
          ·
            refine ⟨3406674529315858616402209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 72675723292071650483247125 3406674529315858616402209)
            ·
              refine ⟨2555005896986893962301657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3406674529315858616402209 2555005896986893962301657)
              ·
                refine ⟨1916254422740170471726243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2555005896986893962301657 1916254422740170471726243)
                ·
                  refine ⟨2874381634110255707589365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1916254422740170471726243 2874381634110255707589365)
                  ·
                    refine ⟨269473278197836472586503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2874381634110255707589365 269473278197836472586503)
                    ·
                      rfl

theorem cell23_1574392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 1, 5].length) (baseStart_1574392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574392 prefixEnd_1574392 := by exact prefixLift 1574392
  have htrace : WordTrace (prefixWord ++ tailWord_1574392) baseStart_1574392 baseEnd_1574392 := by
    simpa [prefixWord, tailWord_1574392, baseEnd_1574392] using wordTrace_append hprefix tailTrace_1574392
  have hstable : (prefixWord ++ tailWord_1574392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574392).length < 2 ^ (prefixWord ++ tailWord_1574392).sum := by decide
  have hdescent : baseEnd_1574392 < baseStart_1574392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574430 : List Nat := [4, 3, 3, 1, 1, 2, 2, 1, 6]
def baseStart_1574430 : Nat := 118140960795 + 1574430 * 2 ^ 59
def prefixEnd_1574430 : Nat := 4983230072969 + 3 ^ 40 * 1574430 * 2
def baseEnd_1574430 : Nat := 89826594095375585453815

theorem tailTrace_1574430 : CollatzResearch.WordTrace tailWord_1574430 prefixEnd_1574430 89826594095375585453815 := by
  unfold tailWord_1574430
  simp only [CollatzResearch.WordTrace]
  refine ⟨7178022460764559510198093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38282786457410984054389829 7178022460764559510198093)
  ·
    refine ⟨2691758422786709816324285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7178022460764559510198093 2691758422786709816324285)
    ·
      refine ⟨1009409408545016181121607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2691758422786709816324285 1009409408545016181121607)
      ·
        refine ⟨1514114112817524271682411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1009409408545016181121607 1514114112817524271682411)
        ·
          refine ⟨2271171169226286407523617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1514114112817524271682411 2271171169226286407523617)
          ·
            refine ⟨1703378376919714805642713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2271171169226286407523617 1703378376919714805642713)
            ·
              refine ⟨1277533782689786104232035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1703378376919714805642713 1277533782689786104232035)
              ·
                refine ⟨1916300674034679156348053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1277533782689786104232035 1916300674034679156348053)
                ·
                  refine ⟨89826594095375585453815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1916300674034679156348053 89826594095375585453815)
                  ·
                    rfl

theorem cell23_1574430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_1574430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574430 prefixEnd_1574430 := by exact prefixLift 1574430
  have htrace : WordTrace (prefixWord ++ tailWord_1574430) baseStart_1574430 baseEnd_1574430 := by
    simpa [prefixWord, tailWord_1574430, baseEnd_1574430] using wordTrace_append hprefix tailTrace_1574430
  have hstable : (prefixWord ++ tailWord_1574430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574430).length < 2 ^ (prefixWord ++ tailWord_1574430).sum := by decide
  have hdescent : baseEnd_1574430 < baseStart_1574430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574432 : List Nat := [2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 5]
def baseStart_1574432 : Nat := 118140960795 + 1574432 * 2 ^ 59
def prefixEnd_1574432 : Nat := 4983230072969 + 3 ^ 40 * 1574432 * 2
def baseEnd_1574432 : Nat := 808440373819689261259325

theorem tailTrace_1574432 : CollatzResearch.WordTrace tailWord_1574432 prefixEnd_1574432 808440373819689261259325 := by
  unfold tailWord_1574432
  simp only [CollatzResearch.WordTrace]
  refine ⟨28712126316054615211578775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38282835088072820282105033 28712126316054615211578775)
  ·
    refine ⟨43068189474081922817368163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28712126316054615211578775 43068189474081922817368163)
    ·
      refine ⟨64602284211122884226052245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43068189474081922817368163 64602284211122884226052245)
      ·
        refine ⟨3028232072396385198096199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 64602284211122884226052245 3028232072396385198096199)
        ·
          refine ⟨4542348108594577797144299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3028232072396385198096199 4542348108594577797144299)
          ·
            refine ⟨6813522162891866695716449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4542348108594577797144299 6813522162891866695716449)
            ·
              refine ⟨5110141622168900021787337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6813522162891866695716449 5110141622168900021787337)
              ·
                refine ⟨3832606216626675016340503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5110141622168900021787337 3832606216626675016340503)
                ·
                  refine ⟨5748909324940012524510755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3832606216626675016340503 5748909324940012524510755)
                  ·
                    refine ⟨8623363987410018786766133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5748909324940012524510755 8623363987410018786766133)
                    ·
                      refine ⟨808440373819689261259325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8623363987410018786766133 808440373819689261259325)
                      ·
                        rfl

theorem cell23_1574432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_1574432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574432 prefixEnd_1574432 := by exact prefixLift 1574432
  have htrace : WordTrace (prefixWord ++ tailWord_1574432) baseStart_1574432 baseEnd_1574432 := by
    simpa [prefixWord, tailWord_1574432, baseEnd_1574432] using wordTrace_append hprefix tailTrace_1574432
  have hstable : (prefixWord ++ tailWord_1574432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574432).length < 2 ^ (prefixWord ++ tailWord_1574432).sum := by decide
  have hdescent : baseEnd_1574432 < baseStart_1574432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574442 : List Nat := [3, 1, 4, 1, 1, 1, 2, 3, 1, 2, 4]
def baseStart_1574442 : Nat := 118140960795 + 1574442 * 2 ^ 59
def prefixEnd_1574442 : Nat := 4983230072969 + 3 ^ 40 * 1574442 * 2
def baseEnd_1574442 : Nat := 808445508626234222134279

theorem tailTrace_1574442 : CollatzResearch.WordTrace tailWord_1574442 prefixEnd_1574442 808445508626234222134279 := by
  unfold tailWord_1574442
  simp only [CollatzResearch.WordTrace]
  refine ⟨14356154340518250532755395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38283078241382001420681053 14356154340518250532755395)
  ·
    refine ⟨21534231510777375799133093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14356154340518250532755395 21534231510777375799133093)
    ·
      refine ⟨4037668408270757962337455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21534231510777375799133093 4037668408270757962337455)
      ·
        refine ⟨6056502612406136943506183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4037668408270757962337455 6056502612406136943506183)
        ·
          refine ⟨9084753918609205415259275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6056502612406136943506183 9084753918609205415259275)
          ·
            refine ⟨13627130877913808122888913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9084753918609205415259275 13627130877913808122888913)
            ·
              refine ⟨10220348158435356092166685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13627130877913808122888913 10220348158435356092166685)
              ·
                refine ⟨3832630559413258534562507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10220348158435356092166685 3832630559413258534562507)
                ·
                  refine ⟨5748945839119887801843761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3832630559413258534562507 5748945839119887801843761)
                  ·
                    refine ⟨4311709379339915851382821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5748945839119887801843761 4311709379339915851382821)
                    ·
                      refine ⟨808445508626234222134279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4311709379339915851382821 808445508626234222134279)
                      ·
                        rfl

theorem cell23_1574442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_1574442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574442 prefixEnd_1574442 := by exact prefixLift 1574442
  have htrace : WordTrace (prefixWord ++ tailWord_1574442) baseStart_1574442 baseEnd_1574442 := by
    simpa [prefixWord, tailWord_1574442, baseEnd_1574442] using wordTrace_append hprefix tailTrace_1574442
  have hstable : (prefixWord ++ tailWord_1574442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574442).length < 2 ^ (prefixWord ++ tailWord_1574442).sum := by decide
  have hdescent : baseEnd_1574442 < baseStart_1574442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574446 : List Nat := [4, 1, 3, 1, 2, 3, 1, 2, 1, 1, 4]
def baseStart_1574446 : Nat := 118140960795 + 1574446 * 2 ^ 59
def prefixEnd_1574446 : Nat := 4983230072969 + 3 ^ 40 * 1574446 * 2
def baseEnd_1574446 : Nat := 808447562548852206484261

theorem tailTrace_1574446 : CollatzResearch.WordTrace tailWord_1574446 prefixEnd_1574446 808447562548852206484261 := by
  unfold tailWord_1574446
  simp only [CollatzResearch.WordTrace]
  refine ⟨7178095406757313851770899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38283175502705673876111461 7178095406757313851770899)
  ·
    refine ⟨10767143110135970777656349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7178095406757313851770899 10767143110135970777656349)
    ·
      refine ⟨4037678666300989041621131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10767143110135970777656349 4037678666300989041621131)
      ·
        refine ⟨6056517999451483562431697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4037678666300989041621131 6056517999451483562431697)
        ·
          refine ⟨4542388499588612671823773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6056517999451483562431697 4542388499588612671823773)
          ·
            refine ⟨1703395687345729751933915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4542388499588612671823773 1703395687345729751933915)
            ·
              refine ⟨2555093531018594627900873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1703395687345729751933915 2555093531018594627900873)
              ·
                refine ⟨1916320148263945970925655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2555093531018594627900873 1916320148263945970925655)
                ·
                  refine ⟨2874480222395918956388483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1916320148263945970925655 2874480222395918956388483)
                  ·
                    refine ⟨4311720333593878434582725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2874480222395918956388483 4311720333593878434582725)
                    ·
                      refine ⟨808447562548852206484261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4311720333593878434582725 808447562548852206484261)
                      ·
                        rfl

theorem cell23_1574446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_1574446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574446 prefixEnd_1574446 := by exact prefixLift 1574446
  have htrace : WordTrace (prefixWord ++ tailWord_1574446) baseStart_1574446 baseEnd_1574446 := by
    simpa [prefixWord, tailWord_1574446, baseEnd_1574446] using wordTrace_append hprefix tailTrace_1574446
  have hstable : (prefixWord ++ tailWord_1574446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574446).length < 2 ^ (prefixWord ++ tailWord_1574446).sum := by decide
  have hdescent : baseEnd_1574446 < baseStart_1574446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574505 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 4, 1, 5]
def baseStart_1574505 : Nat := 118140960795 + 1574505 * 2 ^ 59
def prefixEnd_1574505 : Nat := 4983230072969 + 3 ^ 40 * 1574505 * 2
def baseEnd_1574505 : Nat := 808477857907467475646489

theorem tailTrace_1574505 : CollatzResearch.WordTrace tailWord_1574505 prefixEnd_1574505 808477857907467475646489 := by
  unfold tailWord_1574505
  simp only [CollatzResearch.WordTrace]
  refine ⟨57426915160844763890564969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38284610107229842593709979 57426915160844763890564969)
  ·
    refine ⟨43070186370633572917923727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57426915160844763890564969 43070186370633572917923727)
    ·
      refine ⟨64605279555950359376885591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43070186370633572917923727 64605279555950359376885591)
      ·
        refine ⟨96907919333925539065328387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64605279555950359376885591 96907919333925539065328387)
        ·
          refine ⟨145361879000888308597992581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96907919333925539065328387 145361879000888308597992581)
          ·
            refine ⟨27255352312666557862123609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145361879000888308597992581 27255352312666557862123609)
            ·
              refine ⟨20441514234499918396592707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27255352312666557862123609 20441514234499918396592707)
              ·
                refine ⟨30662271351749877594889061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20441514234499918396592707 30662271351749877594889061)
                ·
                  refine ⟨5749175878453102049041699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30662271351749877594889061 5749175878453102049041699)
                  ·
                    refine ⟨8623763817679653073562549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5749175878453102049041699 8623763817679653073562549)
                    ·
                      refine ⟨808477857907467475646489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8623763817679653073562549 808477857907467475646489)
                      ·
                        rfl

theorem cell23_1574505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 1, 5].length) (baseStart_1574505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574505 prefixEnd_1574505 := by exact prefixLift 1574505
  have htrace : WordTrace (prefixWord ++ tailWord_1574505) baseStart_1574505 baseEnd_1574505 := by
    simpa [prefixWord, tailWord_1574505, baseEnd_1574505] using wordTrace_append hprefix tailTrace_1574505
  have hstable : (prefixWord ++ tailWord_1574505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574505).length < 2 ^ (prefixWord ++ tailWord_1574505).sum := by decide
  have hdescent : baseEnd_1574505 < baseStart_1574505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574519 : List Nat := [1, 1, 3, 1, 1, 3, 1, 4, 4, 2, 2]
def baseStart_1574519 : Nat := 118140960795 + 1574519 * 2 ^ 59
def prefixEnd_1574519 : Nat := 4983230072969 + 3 ^ 40 * 1574519 * 2
def baseEnd_1574519 : Nat := 808485046636630420871425

theorem tailTrace_1574519 : CollatzResearch.WordTrace tailWord_1574519 prefixEnd_1574519 808485046636630420871425 := by
  unfold tailWord_1574519
  simp only [CollatzResearch.WordTrace]
  refine ⟨57427425782794044281574611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38284950521862696187716407 57427425782794044281574611)
  ·
    refine ⟨86141138674191066422361917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57427425782794044281574611 86141138674191066422361917)
    ·
      refine ⟨32302927002821649908385719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86141138674191066422361917 32302927002821649908385719)
      ·
        refine ⟨48454390504232474862578579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32302927002821649908385719 48454390504232474862578579)
        ·
          refine ⟨72681585756348712293867869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48454390504232474862578579 72681585756348712293867869)
          ·
            refine ⟨27255594658630767110200451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72681585756348712293867869 27255594658630767110200451)
            ·
              refine ⟨40883391987946150665300677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27255594658630767110200451 40883391987946150665300677)
              ·
                refine ⟨7665635997739903249743877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40883391987946150665300677 7665635997739903249743877)
                ·
                  refine ⟨1437306749576231859326977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7665635997739903249743877 1437306749576231859326977)
                  ·
                    refine ⟨1077980062182173894495233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1437306749576231859326977 1077980062182173894495233)
                    ·
                      refine ⟨808485046636630420871425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1077980062182173894495233 808485046636630420871425)
                      ·
                        rfl

theorem cell23_1574519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 4, 2, 2].length) (baseStart_1574519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574519 prefixEnd_1574519 := by exact prefixLift 1574519
  have htrace : WordTrace (prefixWord ++ tailWord_1574519) baseStart_1574519 baseEnd_1574519 := by
    simpa [prefixWord, tailWord_1574519, baseEnd_1574519] using wordTrace_append hprefix tailTrace_1574519
  have hstable : (prefixWord ++ tailWord_1574519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574519).length < 2 ^ (prefixWord ++ tailWord_1574519).sum := by decide
  have hdescent : baseEnd_1574519 < baseStart_1574519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574542 : List Nat := [4, 1, 1, 3, 1, 2, 1, 3, 7]
def baseStart_1574542 : Nat := 118140960795 + 1574542 * 2 ^ 59
def prefixEnd_1574542 : Nat := 4983230072969 + 3 ^ 40 * 1574542 * 2
def baseEnd_1574542 : Nat := 89832984076853758987091

theorem tailTrace_1574542 : CollatzResearch.WordTrace tailWord_1574542 prefixEnd_1574542 89832984076853758987091 := by
  unfold tailWord_1574542
  simp only [CollatzResearch.WordTrace]
  refine ⟨7178533082713839901207735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38285509774473812806441253 7178533082713839901207735)
  ·
    refine ⟨10767799624070759851811603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7178533082713839901207735 10767799624070759851811603)
    ·
      refine ⟨16151699436106139777717405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10767799624070759851811603 16151699436106139777717405)
      ·
        refine ⟨6056887288539802416644027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16151699436106139777717405 6056887288539802416644027)
        ·
          refine ⟨9085330932809703624966041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6056887288539802416644027 9085330932809703624966041)
          ·
            refine ⟨6813998199607277718724531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9085330932809703624966041 6813998199607277718724531)
            ·
              refine ⟨10220997299410916578086797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6813998199607277718724531 10220997299410916578086797)
              ·
                refine ⟨3832873987279093716782549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10220997299410916578086797 3832873987279093716782549)
                ·
                  refine ⟨89832984076853758987091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3832873987279093716782549 89832984076853758987091)
                  ·
                    rfl

theorem cell23_1574542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 7].length) (baseStart_1574542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574542 prefixEnd_1574542 := by exact prefixLift 1574542
  have htrace : WordTrace (prefixWord ++ tailWord_1574542) baseStart_1574542 baseEnd_1574542 := by
    simpa [prefixWord, tailWord_1574542, baseEnd_1574542] using wordTrace_append hprefix tailTrace_1574542
  have hstable : (prefixWord ++ tailWord_1574542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574542).length < 2 ^ (prefixWord ++ tailWord_1574542).sum := by decide
  have hdescent : baseEnd_1574542 < baseStart_1574542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574646 : List Nat := [5, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3]
def baseStart_1574646 : Nat := 118140960795 + 1574646 * 2 ^ 59
def prefixEnd_1574646 : Nat := 4983230072969 + 3 ^ 40 * 1574646 * 2
def baseEnd_1574646 : Nat := 808550258679751423983341

theorem tailTrace_1574646 : CollatzResearch.WordTrace tailWord_1574646 prefixEnd_1574646 808550258679751423983341 := by
  unfold tailWord_1574646
  simp only [CollatzResearch.WordTrace]
  refine ⟨3589503615833371560715487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38288038568889296647631861 3589503615833371560715487)
  ·
    refine ⟨5384255423750057341073231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3589503615833371560715487 5384255423750057341073231)
    ·
      refine ⟨8076383135625086011609847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5384255423750057341073231 8076383135625086011609847)
      ·
        refine ⟨12114574703437629017414771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8076383135625086011609847 12114574703437629017414771)
        ·
          refine ⟨18171862055156443526122157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12114574703437629017414771 18171862055156443526122157)
          ·
            refine ⟨6814448270683666322295809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18171862055156443526122157 6814448270683666322295809)
            ·
              refine ⟨5110836203012749741721857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6814448270683666322295809 5110836203012749741721857)
              ·
                refine ⟨3833127152259562306291393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5110836203012749741721857 3833127152259562306291393)
                ·
                  refine ⟨2874845364194671729718545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3833127152259562306291393 2874845364194671729718545)
                  ·
                    refine ⟨2156134023146003797288909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2874845364194671729718545 2156134023146003797288909)
                    ·
                      refine ⟨808550258679751423983341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2156134023146003797288909 808550258679751423983341)
                      ·
                        rfl

theorem cell23_1574646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_1574646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574646 prefixEnd_1574646 := by exact prefixLift 1574646
  have htrace : WordTrace (prefixWord ++ tailWord_1574646) baseStart_1574646 baseEnd_1574646 := by
    simpa [prefixWord, tailWord_1574646, baseEnd_1574646] using wordTrace_append hprefix tailTrace_1574646
  have hstable : (prefixWord ++ tailWord_1574646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574646).length < 2 ^ (prefixWord ++ tailWord_1574646).sum := by decide
  have hdescent : baseEnd_1574646 < baseStart_1574646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574652 : List Nat := [2, 2, 2, 1, 3, 1, 2, 1, 1, 2, 6]
def baseStart_1574652 : Nat := 118140960795 + 1574652 * 2 ^ 59
def prefixEnd_1574652 : Nat := 4983230072969 + 3 ^ 40 * 1574652 * 2
def baseEnd_1574652 : Nat := 808553339563678400508313

theorem tailTrace_1574652 : CollatzResearch.WordTrace tailWord_1574652 prefixEnd_1574652 808553339563678400508313 := by
  unfold tailWord_1574652
  simp only [CollatzResearch.WordTrace]
  refine ⟨28716138345656103998083105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38288184460874805330777473 28716138345656103998083105)
  ·
    refine ⟨21537103759242077998562329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28716138345656103998083105 21537103759242077998562329)
    ·
      refine ⟨16152827819431558498921747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21537103759242077998562329 16152827819431558498921747)
      ·
        refine ⟨24229241729147337748382621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16152827819431558498921747 24229241729147337748382621)
        ·
          refine ⟨9085965648430251655643483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24229241729147337748382621 9085965648430251655643483)
          ·
            refine ⟨13628948472645377483465225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9085965648430251655643483 13628948472645377483465225)
            ·
              refine ⟨10221711354484033112598919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13628948472645377483465225 10221711354484033112598919)
              ·
                refine ⟨15332567031726049668898379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10221711354484033112598919 15332567031726049668898379)
                ·
                  refine ⟨22998850547589074503347569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15332567031726049668898379 22998850547589074503347569)
                  ·
                    refine ⟨17249137910691805877510677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22998850547589074503347569 17249137910691805877510677)
                    ·
                      refine ⟨808553339563678400508313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17249137910691805877510677 808553339563678400508313)
                      ·
                        rfl

theorem cell23_1574652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_1574652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574652 prefixEnd_1574652 := by exact prefixLift 1574652
  have htrace : WordTrace (prefixWord ++ tailWord_1574652) baseStart_1574652 baseEnd_1574652 := by
    simpa [prefixWord, tailWord_1574652, baseEnd_1574652] using wordTrace_append hprefix tailTrace_1574652
  have hstable : (prefixWord ++ tailWord_1574652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574652).length < 2 ^ (prefixWord ++ tailWord_1574652).sum := by decide
  have hdescent : baseEnd_1574652 < baseStart_1574652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574679 : List Nat := [1, 1, 3, 4, 2, 1, 2, 1, 3, 5]
def baseStart_1574679 : Nat := 118140960795 + 1574679 * 2 ^ 59
def prefixEnd_1574679 : Nat := 4983230072969 + 3 ^ 40 * 1574679 * 2
def baseEnd_1574679 : Nat := 269522401180449931623563

theorem tailTrace_1574679 : CollatzResearch.WordTrace tailWord_1574679 prefixEnd_1574679 269522401180449931623563 := by
  unfold tailWord_1574679
  simp only [CollatzResearch.WordTrace]
  refine ⟨57433261462214391607399091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38288840974809594404932727 57433261462214391607399091)
  ·
    refine ⟨86149892193321587411098637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57433261462214391607399091 86149892193321587411098637)
    ·
      refine ⟨32306209572495595279161989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86149892193321587411098637 32306209572495595279161989)
      ·
        refine ⟨6057414294842924114842873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32306209572495595279161989 6057414294842924114842873)
        ·
          refine ⟨4543060721132193086132155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6057414294842924114842873 4543060721132193086132155)
          ·
            refine ⟨6814591081698289629198233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4543060721132193086132155 6814591081698289629198233)
            ·
              refine ⟨5110943311273717221898675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6814591081698289629198233 5110943311273717221898675)
              ·
                refine ⟨7666414966910575832848013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5110943311273717221898675 7666414966910575832848013)
                ·
                  refine ⟨2874905612591465937318005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7666414966910575832848013 2874905612591465937318005)
                  ·
                    refine ⟨269522401180449931623563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2874905612591465937318005 269522401180449931623563)
                    ·
                      rfl

theorem cell23_1574679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 5].length) (baseStart_1574679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574679 prefixEnd_1574679 := by exact prefixLift 1574679
  have htrace : WordTrace (prefixWord ++ tailWord_1574679) baseStart_1574679 baseEnd_1574679 := by
    simpa [prefixWord, tailWord_1574679, baseEnd_1574679] using wordTrace_append hprefix tailTrace_1574679
  have hstable : (prefixWord ++ tailWord_1574679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574679).length < 2 ^ (prefixWord ++ tailWord_1574679).sum := by decide
  have hdescent : baseEnd_1574679 < baseStart_1574679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574693 : List Nat := [1, 3, 1, 2, 3, 2, 1, 5, 1, 1, 3]
def baseStart_1574693 : Nat := 118140960795 + 1574693 * 2 ^ 59
def prefixEnd_1574693 : Nat := 4983230072969 + 3 ^ 40 * 1574693 * 2
def baseEnd_1574693 : Nat := 808574392270512740095625

theorem tailTrace_1574693 : CollatzResearch.WordTrace tailWord_1574693 prefixEnd_1574693 808574392270512740095625 := by
  unfold tailWord_1574693
  simp only [CollatzResearch.WordTrace]
  refine ⟨57433772084163671998408733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38289181389442447998939155 57433772084163671998408733)
  ·
    refine ⟨21537664531561376999403275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57433772084163671998408733 21537664531561376999403275)
    ·
      refine ⟨32306496797342065499104913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21537664531561376999403275 32306496797342065499104913)
      ·
        refine ⟨24229872598006549124328685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32306496797342065499104913 24229872598006549124328685)
        ·
          refine ⟨9086202224252455921623257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24229872598006549124328685 9086202224252455921623257)
          ·
            refine ⟨6814651668189341941217443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9086202224252455921623257 6814651668189341941217443)
            ·
              refine ⟨10221977502284012911826165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6814651668189341941217443 10221977502284012911826165)
              ·
                refine ⟨958310390839126210483703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10221977502284012911826165 958310390839126210483703)
                ·
                  refine ⟨1437465586258689315725555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 958310390839126210483703 1437465586258689315725555)
                  ·
                    refine ⟨2156198379388033973588333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1437465586258689315725555 2156198379388033973588333)
                    ·
                      refine ⟨808574392270512740095625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2156198379388033973588333 808574392270512740095625)
                      ·
                        rfl

theorem cell23_1574693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 5, 1, 1, 3].length) (baseStart_1574693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574693 prefixEnd_1574693 := by exact prefixLift 1574693
  have htrace : WordTrace (prefixWord ++ tailWord_1574693) baseStart_1574693 baseEnd_1574693 := by
    simpa [prefixWord, tailWord_1574693, baseEnd_1574693] using wordTrace_append hprefix tailTrace_1574693
  have hstable : (prefixWord ++ tailWord_1574693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574693).length < 2 ^ (prefixWord ++ tailWord_1574693).sum := by decide
  have hdescent : baseEnd_1574693 < baseStart_1574693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574696 : List Nat := [2, 1, 5, 1, 1, 3, 1, 3, 1, 5]
def baseStart_1574696 : Nat := 118140960795 + 1574696 * 2 ^ 59
def prefixEnd_1574696 : Nat := 4983230072969 + 3 ^ 40 * 1574696 * 2
def baseEnd_1574696 : Nat := 269525310904158742786037

theorem tailTrace_1574696 : CollatzResearch.WordTrace tailWord_1574696 prefixEnd_1574696 269525310904158742786037 := by
  unfold tailWord_1574696
  simp only [CollatzResearch.WordTrace]
  refine ⟨28716940751576401755383971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38289254335435202340511961 28716940751576401755383971)
  ·
    refine ⟨43075411127364602633075957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28716940751576401755383971 43075411127364602633075957)
    ·
      refine ⟨4038319793190431496850871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43075411127364602633075957 4038319793190431496850871)
      ·
        refine ⟨6057479689785647245276307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4038319793190431496850871 6057479689785647245276307)
        ·
          refine ⟨9086219534678470867914461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6057479689785647245276307 9086219534678470867914461)
          ·
            refine ⟨3407332325504426575467923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9086219534678470867914461 3407332325504426575467923)
            ·
              refine ⟨5110998488256639863201885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3407332325504426575467923 5110998488256639863201885)
              ·
                refine ⟨1916624433096239948700707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5110998488256639863201885 1916624433096239948700707)
                ·
                  refine ⟨2874936649644359923051061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1916624433096239948700707 2874936649644359923051061)
                  ·
                    refine ⟨269525310904158742786037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2874936649644359923051061 269525310904158742786037)
                    ·
                      rfl

theorem cell23_1574696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_1574696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574696 prefixEnd_1574696 := by exact prefixLift 1574696
  have htrace : WordTrace (prefixWord ++ tailWord_1574696) baseStart_1574696 baseEnd_1574696 := by
    simpa [prefixWord, tailWord_1574696, baseEnd_1574696] using wordTrace_append hprefix tailTrace_1574696
  have hstable : (prefixWord ++ tailWord_1574696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574696).length < 2 ^ (prefixWord ++ tailWord_1574696).sum := by decide
  have hdescent : baseEnd_1574696 < baseStart_1574696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574710 : List Nat := [5, 1, 2, 2, 1, 2, 2, 1, 3, 1, 3]
def baseStart_1574710 : Nat := 118140960795 + 1574710 * 2 ^ 59
def prefixEnd_1574710 : Nat := 4983230072969 + 3 ^ 40 * 1574710 * 2
def baseEnd_1574710 : Nat := 808583121441639173583047

theorem tailTrace_1574710 : CollatzResearch.WordTrace tailWord_1574710 prefixEnd_1574710 808583121441639173583047 := by
  unfold tailWord_1574710
  simp only [CollatzResearch.WordTrace]
  refine ⟨3589649507818880243861099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38289594750068055934518389 3589649507818880243861099)
  ·
    refine ⟨5384474261728320365791649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3589649507818880243861099 5384474261728320365791649)
    ·
      refine ⟨4038355696296240274343737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5384474261728320365791649 4038355696296240274343737)
      ·
        refine ⟨3028766772222180205757803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4038355696296240274343737 3028766772222180205757803)
        ·
          refine ⟨4543150158333270308636705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3028766772222180205757803 4543150158333270308636705)
          ·
            refine ⟨3407362618749952731477529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4543150158333270308636705 3407362618749952731477529)
            ·
              refine ⟨2555521964062464548608147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3407362618749952731477529 2555521964062464548608147)
              ·
                refine ⟨3833282946093696822912221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2555521964062464548608147 3833282946093696822912221)
                ·
                  refine ⟨1437481104785136308592083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3833282946093696822912221 1437481104785136308592083)
                  ·
                    refine ⟨2156221657177704462888125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1437481104785136308592083 2156221657177704462888125)
                    ·
                      refine ⟨808583121441639173583047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2156221657177704462888125 808583121441639173583047)
                      ·
                        rfl

theorem cell23_1574710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_1574710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574710 prefixEnd_1574710 := by exact prefixLift 1574710
  have htrace : WordTrace (prefixWord ++ tailWord_1574710) baseStart_1574710 baseEnd_1574710 := by
    simpa [prefixWord, tailWord_1574710, baseEnd_1574710] using wordTrace_append hprefix tailTrace_1574710
  have hstable : (prefixWord ++ tailWord_1574710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574710).length < 2 ^ (prefixWord ++ tailWord_1574710).sum := by decide
  have hdescent : baseEnd_1574710 < baseStart_1574710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574733 : List Nat := [1, 6, 1, 2, 1, 1, 1, 4, 1, 1, 4]
def baseStart_1574733 : Nat := 118140960795 + 1574733 * 2 ^ 59
def prefixEnd_1574733 : Nat := 4983230072969 + 3 ^ 40 * 1574733 * 2
def baseEnd_1574733 : Nat := 808594931496692583595441

theorem tailTrace_1574733 : CollatzResearch.WordTrace tailWord_1574733 prefixEnd_1574733 808594931496692583595441 := by
  unfold tailWord_1574733
  simp only [CollatzResearch.WordTrace]
  refine ⟨57435231004018758829864853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38290154002679172553243235 57435231004018758829864853)
  ·
    refine ⟨2692276453313379320149915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 57435231004018758829864853 2692276453313379320149915)
    ·
      refine ⟨4038414679970068980224873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2692276453313379320149915 4038414679970068980224873)
      ·
        refine ⟨3028811009977551735168655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4038414679970068980224873 3028811009977551735168655)
        ·
          refine ⟨4543216514966327602752983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3028811009977551735168655 4543216514966327602752983)
          ·
            refine ⟨6814824772449491404129475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4543216514966327602752983 6814824772449491404129475)
            ·
              refine ⟨10222237158674237106194213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6814824772449491404129475 10222237158674237106194213)
              ·
                refine ⟨1916669467251419457411415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10222237158674237106194213 1916669467251419457411415)
                ·
                  refine ⟨2875004200877129186117123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1916669467251419457411415 2875004200877129186117123)
                  ·
                    refine ⟨4312506301315693779175685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2875004200877129186117123 4312506301315693779175685)
                    ·
                      refine ⟨808594931496692583595441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4312506301315693779175685 808594931496692583595441)
                      ·
                        rfl

theorem cell23_1574733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_1574733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574733 prefixEnd_1574733 := by exact prefixLift 1574733
  have htrace : WordTrace (prefixWord ++ tailWord_1574733) baseStart_1574733 baseEnd_1574733 := by
    simpa [prefixWord, tailWord_1574733, baseEnd_1574733] using wordTrace_append hprefix tailTrace_1574733
  have hstable : (prefixWord ++ tailWord_1574733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574733).length < 2 ^ (prefixWord ++ tailWord_1574733).sum := by decide
  have hdescent : baseEnd_1574733 < baseStart_1574733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574756 : List Nat := [2, 3, 1, 1, 6, 1, 9]
def baseStart_1574756 : Nat := 118140960795 + 1574756 * 2 ^ 59
def prefixEnd_1574756 : Nat := 4983230072969 + 3 ^ 40 * 1574756 * 2
def baseEnd_1574756 : Nat := 9982799278416617205035

theorem tailTrace_1574756 : CollatzResearch.WordTrace tailWord_1574756 prefixEnd_1574756 9982799278416617205035 := by
  unfold tailWord_1574756
  simp only [CollatzResearch.WordTrace]
  refine ⟨28718034941467716878976061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38290713255290289171968081 28718034941467716878976061)
  ·
    refine ⟨10769263103050393829616023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28718034941467716878976061 10769263103050393829616023)
    ·
      refine ⟨16153894654575590744424035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10769263103050393829616023 16153894654575590744424035)
      ·
        refine ⟨24230841981863386116636053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16153894654575590744424035 24230841981863386116636053)
        ·
          refine ⟨1135820717899846224217315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24230841981863386116636053 1135820717899846224217315)
          ·
            refine ⟨1703731076849769336325973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1135820717899846224217315 1703731076849769336325973)
            ·
              refine ⟨9982799278416617205035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1703731076849769336325973 9982799278416617205035)
              ·
                rfl

theorem cell23_1574756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 9].length) (baseStart_1574756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574756 prefixEnd_1574756 := by exact prefixLift 1574756
  have htrace : WordTrace (prefixWord ++ tailWord_1574756) baseStart_1574756 baseEnd_1574756 := by
    simpa [prefixWord, tailWord_1574756, baseEnd_1574756] using wordTrace_append hprefix tailTrace_1574756
  have hstable : (prefixWord ++ tailWord_1574756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574756).length < 2 ^ (prefixWord ++ tailWord_1574756).sum := by decide
  have hdescent : baseEnd_1574756 < baseStart_1574756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574809 : List Nat := [1, 2, 1, 2, 1, 3, 4, 1, 2, 1, 5]
def baseStart_1574809 : Nat := 118140960795 + 1574809 * 2 ^ 59
def prefixEnd_1574809 : Nat := 4983230072969 + 3 ^ 40 * 1574809 * 2
def baseEnd_1574809 : Nat := 808633956026434286245091

theorem tailTrace_1574809 : CollatzResearch.WordTrace tailWord_1574809 prefixEnd_1574809 808633956026434286245091 := by
  unfold tailWord_1574809
  simp only [CollatzResearch.WordTrace]
  refine ⟨57438002951743423809631481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38292001967828949206420987 57438002951743423809631481)
  ·
    refine ⟨43078502213807567857223611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57438002951743423809631481 43078502213807567857223611)
    ·
      refine ⟨64617753320711351785835417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43078502213807567857223611 64617753320711351785835417)
      ·
        refine ⟨48463314990533513839376563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64617753320711351785835417 48463314990533513839376563)
        ·
          refine ⟨72694972485800270759064845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48463314990533513839376563 72694972485800270759064845)
          ·
            refine ⟨27260614682175101534649317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72694972485800270759064845 27260614682175101534649317)
            ·
              refine ⟨5111365252907831537746747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27260614682175101534649317 5111365252907831537746747)
              ·
                refine ⟨7667047879361747306620121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5111365252907831537746747 7667047879361747306620121)
                ·
                  refine ⟨5750285909521310479965091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7667047879361747306620121 5750285909521310479965091)
                  ·
                    refine ⟨8625428864281965719947637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5750285909521310479965091 8625428864281965719947637)
                    ·
                      refine ⟨808633956026434286245091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8625428864281965719947637 808633956026434286245091)
                      ·
                        rfl

theorem cell23_1574809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 1, 5].length) (baseStart_1574809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574809 prefixEnd_1574809 := by exact prefixLift 1574809
  have htrace : WordTrace (prefixWord ++ tailWord_1574809) baseStart_1574809 baseEnd_1574809 := by
    simpa [prefixWord, tailWord_1574809, baseEnd_1574809] using wordTrace_append hprefix tailTrace_1574809
  have hstable : (prefixWord ++ tailWord_1574809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574809).length < 2 ^ (prefixWord ++ tailWord_1574809).sum := by decide
  have hdescent : baseEnd_1574809 < baseStart_1574809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574819 : List Nat := [1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 4]
def baseStart_1574819 : Nat := 118140960795 + 1574819 * 2 ^ 59
def prefixEnd_1574819 : Nat := 4983230072969 + 3 ^ 40 * 1574819 * 2
def baseEnd_1574819 : Nat := 808639090832979247120045

theorem tailTrace_1574819 : CollatzResearch.WordTrace tailWord_1574819 prefixEnd_1574819 808639090832979247120045 := by
  unfold tailWord_1574819
  simp only [CollatzResearch.WordTrace]
  refine ⟨57438367681707195517495511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38292245121138130344997007 57438367681707195517495511)
  ·
    refine ⟨86157551522560793276243267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57438367681707195517495511 86157551522560793276243267)
    ·
      refine ⟨129236327283841189914364901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86157551522560793276243267 129236327283841189914364901)
      ·
        refine ⟨24231811365720223108943419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129236327283841189914364901 24231811365720223108943419)
        ·
          refine ⟨36347717048580334663415129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24231811365720223108943419 36347717048580334663415129)
          ·
            refine ⟨27260787786435250997561347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36347717048580334663415129 27260787786435250997561347)
            ·
              refine ⟨40891181679652876496342021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27260787786435250997561347 40891181679652876496342021)
              ·
                refine ⟨7667096564934914343064129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40891181679652876496342021 7667096564934914343064129)
                ·
                  refine ⟨5750322423701185757298097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7667096564934914343064129 5750322423701185757298097)
                  ·
                    refine ⟨4312741817775889317973573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5750322423701185757298097 4312741817775889317973573)
                    ·
                      refine ⟨808639090832979247120045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4312741817775889317973573 808639090832979247120045)
                      ·
                        rfl

theorem cell23_1574819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_1574819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574819 prefixEnd_1574819 := by exact prefixLift 1574819
  have htrace : WordTrace (prefixWord ++ tailWord_1574819) baseStart_1574819 baseEnd_1574819 := by
    simpa [prefixWord, tailWord_1574819, baseEnd_1574819] using wordTrace_append hprefix tailTrace_1574819
  have hstable : (prefixWord ++ tailWord_1574819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574819).length < 2 ^ (prefixWord ++ tailWord_1574819).sum := by decide
  have hdescent : baseEnd_1574819 < baseStart_1574819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574846 : List Nat := [4, 2, 1, 1, 1, 4, 1, 2, 7]
def baseStart_1574846 : Nat := 118140960795 + 1574846 * 2 ^ 59
def prefixEnd_1574846 : Nat := 4983230072969 + 3 ^ 40 * 1574846 * 2
def baseEnd_1574846 : Nat := 89850328312294515720269

theorem tailTrace_1574846 : CollatzResearch.WordTrace tailWord_1574846 prefixEnd_1574846 89850328312294515720269 := by
  unfold tailWord_1574846
  simp only [CollatzResearch.WordTrace]
  refine ⟨7179919056576172391091049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38292901635072919419152261 7179919056576172391091049)
  ·
    refine ⟨5384939292432129293318287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7179919056576172391091049 5384939292432129293318287)
    ·
      refine ⟨8077408938648193939977431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5384939292432129293318287 8077408938648193939977431)
      ·
        refine ⟨12116113407972290909966147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8077408938648193939977431 12116113407972290909966147)
        ·
          refine ⟨18174170111958436364949221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12116113407972290909966147 18174170111958436364949221)
          ·
            refine ⟨3407656895992206818427979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18174170111958436364949221 3407656895992206818427979)
            ·
              refine ⟨5111485343988310227641969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3407656895992206818427979 5111485343988310227641969)
              ·
                refine ⟨3833614007991232670731477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5111485343988310227641969 3833614007991232670731477)
                ·
                  refine ⟨89850328312294515720269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3833614007991232670731477 89850328312294515720269)
                  ·
                    rfl

theorem cell23_1574846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_1574846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574846 prefixEnd_1574846 := by exact prefixLift 1574846
  have htrace : WordTrace (prefixWord ++ tailWord_1574846) baseStart_1574846 baseEnd_1574846 := by
    simpa [prefixWord, tailWord_1574846, baseEnd_1574846] using wordTrace_append hprefix tailTrace_1574846
  have hstable : (prefixWord ++ tailWord_1574846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574846).length < 2 ^ (prefixWord ++ tailWord_1574846).sum := by decide
  have hdescent : baseEnd_1574846 < baseStart_1574846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574859 : List Nat := [1, 1, 1, 1, 3, 4, 3, 1, 1, 7]
def baseStart_1574859 : Nat := 118140960795 + 1574859 * 2 ^ 59
def prefixEnd_1574859 : Nat := 4983230072969 + 3 ^ 40 * 1574859 * 2
def baseEnd_1574859 : Nat := 269553210019719696873287

theorem tailTrace_1574859 : CollatzResearch.WordTrace tailWord_1574859 prefixEnd_1574859 269553210019719696873287 := by
  unfold tailWord_1574859
  simp only [CollatzResearch.WordTrace]
  refine ⟨57439826601562282348951631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38293217734374854899301087 57439826601562282348951631)
  ·
    refine ⟨86159739902343423523427447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57439826601562282348951631 86159739902343423523427447)
    ·
      refine ⟨129239609853515135285141171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86159739902343423523427447 129239609853515135285141171)
      ·
        refine ⟨193859414780272702927711757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129239609853515135285141171 193859414780272702927711757)
        ·
          refine ⟨72697280542602263597891909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193859414780272702927711757 72697280542602263597891909)
          ·
            refine ⟨13630740101737924424604733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72697280542602263597891909 13630740101737924424604733)
            ·
              refine ⟨5111527538151721659226775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13630740101737924424604733 5111527538151721659226775)
              ·
                refine ⟨7667291307227582488840163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5111527538151721659226775 7667291307227582488840163)
                ·
                  refine ⟨11500936960841373733260245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7667291307227582488840163 11500936960841373733260245)
                  ·
                    refine ⟨269553210019719696873287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11500936960841373733260245 269553210019719696873287)
                    ·
                      rfl

theorem cell23_1574859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 7].length) (baseStart_1574859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574859 prefixEnd_1574859 := by exact prefixLift 1574859
  have htrace : WordTrace (prefixWord ++ tailWord_1574859) baseStart_1574859 baseEnd_1574859 := by
    simpa [prefixWord, tailWord_1574859, baseEnd_1574859] using wordTrace_append hprefix tailTrace_1574859
  have hstable : (prefixWord ++ tailWord_1574859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574859).length < 2 ^ (prefixWord ++ tailWord_1574859).sum := by decide
  have hdescent : baseEnd_1574859 < baseStart_1574859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574874 : List Nat := [3, 1, 1, 2, 6, 1, 1, 2, 2, 2, 2]
def baseStart_1574874 : Nat := 118140960795 + 1574874 * 2 ^ 59
def prefixEnd_1574874 : Nat := 4983230072969 + 3 ^ 40 * 1574874 * 2
def baseEnd_1574874 : Nat := 808667332268976531932293

theorem tailTrace_1574874 : CollatzResearch.WordTrace tailWord_1574874 prefixEnd_1574874 808667332268976531932293 := by
  unfold tailWord_1574874
  simp only [CollatzResearch.WordTrace]
  refine ⟨14360093424126984977686919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38293582464338626607165117 14360093424126984977686919)
  ·
    refine ⟨21540140136190477466530379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14360093424126984977686919 21540140136190477466530379)
    ·
      refine ⟨32310210204285716199795569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21540140136190477466530379 32310210204285716199795569)
      ·
        refine ⟨24232657653214287149846677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32310210204285716199795569 24232657653214287149846677)
        ·
          refine ⟨1135905827494419710149063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24232657653214287149846677 1135905827494419710149063)
          ·
            refine ⟨1703858741241629565223595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1135905827494419710149063 1703858741241629565223595)
            ·
              refine ⟨2555788111862444347835393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1703858741241629565223595 2555788111862444347835393)
              ·
                refine ⟨1916841083896833260876545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2555788111862444347835393 1916841083896833260876545)
                ·
                  refine ⟨1437630812922624945657409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1916841083896833260876545 1437630812922624945657409)
                  ·
                    refine ⟨1078223109691968709243057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1437630812922624945657409 1078223109691968709243057)
                    ·
                      refine ⟨808667332268976531932293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1078223109691968709243057 808667332268976531932293)
                      ·
                        rfl

theorem cell23_1574874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 2, 2, 2].length) (baseStart_1574874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574874 prefixEnd_1574874 := by exact prefixLift 1574874
  have htrace : WordTrace (prefixWord ++ tailWord_1574874) baseStart_1574874 baseEnd_1574874 := by
    simpa [prefixWord, tailWord_1574874, baseEnd_1574874] using wordTrace_append hprefix tailTrace_1574874
  have hstable : (prefixWord ++ tailWord_1574874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574874).length < 2 ^ (prefixWord ++ tailWord_1574874).sum := by decide
  have hdescent : baseEnd_1574874 < baseStart_1574874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574936 : List Nat := [2, 1, 2, 3, 2, 1, 2, 4, 6]
def baseStart_1574936 : Nat := 118140960795 + 1574936 * 2 ^ 59
def prefixEnd_1574936 : Nat := 4983230072969 + 3 ^ 40 * 1574936 * 2
def baseEnd_1574936 : Nat := 89855463118839476595223

theorem tailTrace_1574936 : CollatzResearch.WordTrace tailWord_1574936 prefixEnd_1574936 89855463118839476595223 := by
  unfold tailWord_1574936
  simp only [CollatzResearch.WordTrace]
  refine ⟨28721317511141662249752331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38295090014855549666336441 28721317511141662249752331)
  ·
    refine ⟨43081976266712493374628497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28721317511141662249752331 43081976266712493374628497)
    ·
      refine ⟨32311482200034370030971373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43081976266712493374628497 32311482200034370030971373)
      ·
        refine ⟨12116805825012888761614265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32311482200034370030971373 12116805825012888761614265)
        ·
          refine ⟨9087604368759666571210699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12116805825012888761614265 9087604368759666571210699)
          ·
            refine ⟨13631406553139499856816049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9087604368759666571210699 13631406553139499856816049)
            ·
              refine ⟨10223554914854624892612037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13631406553139499856816049 10223554914854624892612037)
              ·
                refine ⟨1916916546535242167364757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10223554914854624892612037 1916916546535242167364757)
                ·
                  refine ⟨89855463118839476595223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1916916546535242167364757 89855463118839476595223)
                  ·
                    rfl

theorem cell23_1574936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 6].length) (baseStart_1574936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574936 prefixEnd_1574936 := by exact prefixLift 1574936
  have htrace : WordTrace (prefixWord ++ tailWord_1574936) baseStart_1574936 baseEnd_1574936 := by
    simpa [prefixWord, tailWord_1574936, baseEnd_1574936] using wordTrace_append hprefix tailTrace_1574936
  have hstable : (prefixWord ++ tailWord_1574936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574936).length < 2 ^ (prefixWord ++ tailWord_1574936).sum := by decide
  have hdescent : baseEnd_1574936 < baseStart_1574936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574939 : List Nat := [1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 6]
def baseStart_1574939 : Nat := 118140960795 + 1574939 * 2 ^ 59
def prefixEnd_1574939 : Nat := 4983230072969 + 3 ^ 40 * 1574939 * 2
def baseEnd_1574939 : Nat := 808700708511518777619493

theorem tailTrace_1574939 : CollatzResearch.WordTrace tailWord_1574939 prefixEnd_1574939 808700708511518777619493 := by
  unfold tailWord_1574939
  simp only [CollatzResearch.WordTrace]
  refine ⟨57442744441272456011863871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38295162960848304007909247 57442744441272456011863871)
  ·
    refine ⟨86164116661908684017795807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57442744441272456011863871 86164116661908684017795807)
    ·
      refine ⟨129246174992863026026693711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86164116661908684017795807 129246174992863026026693711)
      ·
        refine ⟨193869262489294539040040567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129246174992863026026693711 193869262489294539040040567)
        ·
          refine ⟨290803893733941808560060851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193869262489294539040040567 290803893733941808560060851)
          ·
            refine ⟨436205840600912712840091277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290803893733941808560060851 436205840600912712840091277)
            ·
              refine ⟨163577190225342267315034229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 436205840600912712840091277 163577190225342267315034229)
              ·
                refine ⟨15335361583625837560784459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 163577190225342267315034229 15335361583625837560784459)
                ·
                  refine ⟨23003042375438756341176689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15335361583625837560784459 23003042375438756341176689)
                  ·
                    refine ⟨17252281781579067255882517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23003042375438756341176689 17252281781579067255882517)
                    ·
                      refine ⟨808700708511518777619493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17252281781579067255882517 808700708511518777619493)
                      ·
                        rfl

theorem cell23_1574939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 6].length) (baseStart_1574939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574939 prefixEnd_1574939 := by exact prefixLift 1574939
  have htrace : WordTrace (prefixWord ++ tailWord_1574939) baseStart_1574939 baseEnd_1574939 := by
    simpa [prefixWord, tailWord_1574939, baseEnd_1574939] using wordTrace_append hprefix tailTrace_1574939
  have hstable : (prefixWord ++ tailWord_1574939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574939).length < 2 ^ (prefixWord ++ tailWord_1574939).sum := by decide
  have hdescent : baseEnd_1574939 < baseStart_1574939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574940 : List Nat := [2, 2, 3, 1, 3, 3, 1, 1, 3, 4]
def baseStart_1574940 : Nat := 118140960795 + 1574940 * 2 ^ 59
def prefixEnd_1574940 : Nat := 4983230072969 + 3 ^ 40 * 1574940 * 2
def baseEnd_1574940 : Nat := 269567073997391091235663

theorem tailTrace_1574940 : CollatzResearch.WordTrace tailWord_1574940 prefixEnd_1574940 269567073997391091235663 := by
  unfold tailWord_1574940
  simp only [CollatzResearch.WordTrace]
  refine ⟨28721390457134416591325137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38295187276179222121766849 28721390457134416591325137)
  ·
    refine ⟨21541042842850812443493853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28721390457134416591325137 21541042842850812443493853)
    ·
      refine ⟨8077891066069054666310195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21541042842850812443493853 8077891066069054666310195)
      ·
        refine ⟨12116836599103581999465293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8077891066069054666310195 12116836599103581999465293)
        ·
          refine ⟨4543813724663843249799485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12116836599103581999465293 4543813724663843249799485)
          ·
            refine ⟨1703930146748941218674807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4543813724663843249799485 1703930146748941218674807)
            ·
              refine ⟨2555895220123411828012211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1703930146748941218674807 2555895220123411828012211)
              ·
                refine ⟨3833842830185117742018317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2555895220123411828012211 3833842830185117742018317)
                ·
                  refine ⟨1437691061319419153256869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3833842830185117742018317 1437691061319419153256869)
                  ·
                    refine ⟨269567073997391091235663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1437691061319419153256869 269567073997391091235663)
                    ·
                      rfl

theorem cell23_1574940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_1574940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574940 prefixEnd_1574940 := by exact prefixLift 1574940
  have htrace : WordTrace (prefixWord ++ tailWord_1574940) baseStart_1574940 baseEnd_1574940 := by
    simpa [prefixWord, tailWord_1574940, baseEnd_1574940] using wordTrace_append hprefix tailTrace_1574940
  have hstable : (prefixWord ++ tailWord_1574940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574940).length < 2 ^ (prefixWord ++ tailWord_1574940).sum := by decide
  have hdescent : baseEnd_1574940 < baseStart_1574940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574959 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 7]
def baseStart_1574959 : Nat := 118140960795 + 1574959 * 2 ^ 59
def prefixEnd_1574959 : Nat := 4983230072969 + 3 ^ 40 * 1574959 * 2
def baseEnd_1574959 : Nat := 808710978124608699369401

theorem tailTrace_1574959 : CollatzResearch.WordTrace tailWord_1574959 prefixEnd_1574959 808710978124608699369401 := by
  unfold tailWord_1574959
  simp only [CollatzResearch.WordTrace]
  refine ⟨57443473901199999427591931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38295649267466666285061287 57443473901199999427591931)
  ·
    refine ⟨86165210851799999141387897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57443473901199999427591931 86165210851799999141387897)
    ·
      refine ⟨64623908138849999356040923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86165210851799999141387897 64623908138849999356040923)
      ·
        refine ⟨96935862208274999034061385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64623908138849999356040923 96935862208274999034061385)
        ·
          refine ⟨72701896656206249275546039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96935862208274999034061385 72701896656206249275546039)
          ·
            refine ⟨109052844984309373913319059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72701896656206249275546039 109052844984309373913319059)
            ·
              refine ⟨163579267476464060869978589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109052844984309373913319059 163579267476464060869978589)
              ·
                refine ⟨61342225303674022826241971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163579267476464060869978589 61342225303674022826241971)
                ·
                  refine ⟨92013337955511034239362957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61342225303674022826241971 92013337955511034239362957)
                  ·
                    refine ⟨34505001733316637839761109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92013337955511034239362957 34505001733316637839761109)
                    ·
                      refine ⟨808710978124608699369401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 34505001733316637839761109 808710978124608699369401)
                      ·
                        rfl

theorem cell23_1574959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 7].length) (baseStart_1574959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574959 prefixEnd_1574959 := by exact prefixLift 1574959
  have htrace : WordTrace (prefixWord ++ tailWord_1574959) baseStart_1574959 baseEnd_1574959 := by
    simpa [prefixWord, tailWord_1574959, baseEnd_1574959] using wordTrace_append hprefix tailTrace_1574959
  have hstable : (prefixWord ++ tailWord_1574959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574959).length < 2 ^ (prefixWord ++ tailWord_1574959).sum := by decide
  have hdescent : baseEnd_1574959 < baseStart_1574959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574963 : List Nat := [1, 1, 1, 2, 4, 1, 2, 4, 3, 1, 3]
def baseStart_1574963 : Nat := 118140960795 + 1574963 * 2 ^ 59
def prefixEnd_1574963 : Nat := 4983230072969 + 3 ^ 40 * 1574963 * 2
def baseEnd_1574963 : Nat := 808713032047226683719383

theorem tailTrace_1574963 : CollatzResearch.WordTrace tailWord_1574963 prefixEnd_1574963 808713032047226683719383 := by
  unfold tailWord_1574963
  simp only [CollatzResearch.WordTrace]
  refine ⟨57443619793185508110737543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38295746528790338740491695 57443619793185508110737543)
  ·
    refine ⟨86165429689778262166106315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57443619793185508110737543 86165429689778262166106315)
    ·
      refine ⟨129248144534667393249159473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86165429689778262166106315 129248144534667393249159473)
      ·
        refine ⟨96936108401000544936869605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129248144534667393249159473 96936108401000544936869605)
        ·
          refine ⟨18175520325187602175663051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96936108401000544936869605 18175520325187602175663051)
          ·
            refine ⟨27263280487781403263494577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18175520325187602175663051 27263280487781403263494577)
            ·
              refine ⟨20447460365836052447620933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27263280487781403263494577 20447460365836052447620933)
              ·
                refine ⟨3833898818594259833928925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20447460365836052447620933 3833898818594259833928925)
                ·
                  refine ⟨1437712056972847437723347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3833898818594259833928925 1437712056972847437723347)
                  ·
                    refine ⟨2156568085459271156585021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1437712056972847437723347 2156568085459271156585021)
                    ·
                      refine ⟨808713032047226683719383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2156568085459271156585021 808713032047226683719383)
                      ·
                        rfl

theorem cell23_1574963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 3, 1, 3].length) (baseStart_1574963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574963 prefixEnd_1574963 := by exact prefixLift 1574963
  have htrace : WordTrace (prefixWord ++ tailWord_1574963) baseStart_1574963 baseEnd_1574963 := by
    simpa [prefixWord, tailWord_1574963, baseEnd_1574963] using wordTrace_append hprefix tailTrace_1574963
  have hstable : (prefixWord ++ tailWord_1574963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574963).length < 2 ^ (prefixWord ++ tailWord_1574963).sum := by decide
  have hdescent : baseEnd_1574963 < baseStart_1574963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574990 : List Nat := [4, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2]
def baseStart_1574990 : Nat := 118140960795 + 1574990 * 2 ^ 59
def prefixEnd_1574990 : Nat := 4983230072969 + 3 ^ 40 * 1574990 * 2
def baseEnd_1574990 : Nat := 808726896024898078081759

theorem tailTrace_1574990 : CollatzResearch.WordTrace tailWord_1574990 prefixEnd_1574990 808726896024898078081759 := by
  unfold tailWord_1574990
  simp only [CollatzResearch.WordTrace]
  refine ⟨7180575570510961465246303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38296403042725127814646949 7180575570510961465246303)
  ·
    refine ⟨10770863355766442197869455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7180575570510961465246303 10770863355766442197869455)
    ·
      refine ⟨16156295033649663296804183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10770863355766442197869455 16156295033649663296804183)
      ·
        refine ⟨24234442550474494945206275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16156295033649663296804183 24234442550474494945206275)
        ·
          refine ⟨36351663825711742417809413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24234442550474494945206275 36351663825711742417809413)
          ·
            refine ⟨6815936967320951703339265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36351663825711742417809413 6815936967320951703339265)
            ·
              refine ⟨5111952725490713777504449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6815936967320951703339265 5111952725490713777504449)
              ·
                refine ⟨3833964544118035333128337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5111952725490713777504449 3833964544118035333128337)
                ·
                  refine ⟨2875473408088526499846253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3833964544118035333128337 2875473408088526499846253)
                  ·
                    refine ⟨1078302528033197437442345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2875473408088526499846253 1078302528033197437442345)
                    ·
                      refine ⟨808726896024898078081759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1078302528033197437442345 808726896024898078081759)
                      ·
                        rfl

theorem cell23_1574990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2].length) (baseStart_1574990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574990 prefixEnd_1574990 := by exact prefixLift 1574990
  have htrace : WordTrace (prefixWord ++ tailWord_1574990) baseStart_1574990 baseEnd_1574990 := by
    simpa [prefixWord, tailWord_1574990, baseEnd_1574990] using wordTrace_append hprefix tailTrace_1574990
  have hstable : (prefixWord ++ tailWord_1574990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574990).length < 2 ^ (prefixWord ++ tailWord_1574990).sum := by decide
  have hdescent : baseEnd_1574990 < baseStart_1574990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574996 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 5, 6]
def baseStart_1574996 : Nat := 118140960795 + 1574996 * 2 ^ 59
def prefixEnd_1574996 : Nat := 4983230072969 + 3 ^ 40 * 1574996 * 2
def baseEnd_1574996 : Nat := 269576658969608351535577

theorem tailTrace_1574996 : CollatzResearch.WordTrace tailWord_1574996 prefixEnd_1574996 269576658969608351535577 := by
  unfold tailWord_1574996
  simp only [CollatzResearch.WordTrace]
  refine ⟨28722411701032977373344421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38296548934710636497792561 28722411701032977373344421)
  ·
    refine ⟨5385452193943683257502079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28722411701032977373344421 5385452193943683257502079)
    ·
      refine ⟨8078178290915524886253119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5385452193943683257502079 8078178290915524886253119)
      ·
        refine ⟨12117267436373287329379679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8078178290915524886253119 12117267436373287329379679)
        ·
          refine ⟨18175901154559930994069519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12117267436373287329379679 18175901154559930994069519)
          ·
            refine ⟨27263851731839896491104279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18175901154559930994069519 27263851731839896491104279)
            ·
              refine ⟨40895777597759844736656419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27263851731839896491104279 40895777597759844736656419)
              ·
                refine ⟨61343666396639767104984629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40895777597759844736656419 61343666396639767104984629)
                ·
                  refine ⟨5750968724684978166092309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61343666396639767104984629 5750968724684978166092309)
                  ·
                    refine ⟨269576658969608351535577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5750968724684978166092309 269576658969608351535577)
                    ·
                      rfl

theorem cell23_1574996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_1574996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574996 prefixEnd_1574996 := by exact prefixLift 1574996
  have htrace : WordTrace (prefixWord ++ tailWord_1574996) baseStart_1574996 baseEnd_1574996 := by
    simpa [prefixWord, tailWord_1574996, baseEnd_1574996] using wordTrace_append hprefix tailTrace_1574996
  have hstable : (prefixWord ++ tailWord_1574996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574996).length < 2 ^ (prefixWord ++ tailWord_1574996).sum := by decide
  have hdescent : baseEnd_1574996 < baseStart_1574996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574997 : List Nat := [1, 3, 2, 2, 1, 4, 1, 4, 1, 1, 3]
def baseStart_1574997 : Nat := 118140960795 + 1574997 * 2 ^ 59
def prefixEnd_1574997 : Nat := 4983230072969 + 3 ^ 40 * 1574997 * 2
def baseEnd_1574997 : Nat := 808730490389479550694227

theorem tailTrace_1574997 : CollatzResearch.WordTrace tailWord_1574997 prefixEnd_1574997 808730490389479550694227 := by
  unfold tailWord_1574997
  simp only [CollatzResearch.WordTrace]
  refine ⟨57444859875062331917475245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38296573250041554611650163 57444859875062331917475245)
  ·
    refine ⟨21541822453148374469053217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57444859875062331917475245 21541822453148374469053217)
    ·
      refine ⟨16156366839861280851789913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21541822453148374469053217 16156366839861280851789913)
      ·
        refine ⟨12117275129895960638842435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16156366839861280851789913 12117275129895960638842435)
        ·
          refine ⟨18175912694843940958263653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12117275129895960638842435 18175912694843940958263653)
          ·
            refine ⟨3407983630283238929674435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18175912694843940958263653 3407983630283238929674435)
            ·
              refine ⟨5111975445424858394511653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3407983630283238929674435 5111975445424858394511653)
              ·
                refine ⟨958495396017160948970935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5111975445424858394511653 958495396017160948970935)
                ·
                  refine ⟨1437743094025741423456403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 958495396017160948970935 1437743094025741423456403)
                  ·
                    refine ⟨2156614641038612135184605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1437743094025741423456403 2156614641038612135184605)
                    ·
                      refine ⟨808730490389479550694227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2156614641038612135184605 808730490389479550694227)
                      ·
                        rfl

theorem cell23_1574997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 4, 1, 1, 3].length) (baseStart_1574997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1574997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1574997 prefixEnd_1574997 := by exact prefixLift 1574997
  have htrace : WordTrace (prefixWord ++ tailWord_1574997) baseStart_1574997 baseEnd_1574997 := by
    simpa [prefixWord, tailWord_1574997, baseEnd_1574997] using wordTrace_append hprefix tailTrace_1574997
  have hstable : (prefixWord ++ tailWord_1574997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574997).length < 2 ^ (prefixWord ++ tailWord_1574997).sum := by decide
  have hdescent : baseEnd_1574997 < baseStart_1574997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575013 : List Nat := [1, 3, 1, 3, 2, 3, 2, 1, 1, 6]
def baseStart_1575013 : Nat := 118140960795 + 1575013 * 2 ^ 59
def prefixEnd_1575013 : Nat := 4983230072969 + 3 ^ 40 * 1575013 * 2
def baseEnd_1575013 : Nat := 269579568693317162698051

theorem tailTrace_1575013 : CollatzResearch.WordTrace tailWord_1575013 prefixEnd_1575013 269579568693317162698051 := by
  unfold tailWord_1575013
  simp only [CollatzResearch.WordTrace]
  refine ⟨57445443443004366650057693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38296962295336244433371795 57445443443004366650057693)
  ·
    refine ⟨21542041291126637493771635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57445443443004366650057693 21542041291126637493771635)
    ·
      refine ⟨32313061936689956240657453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21542041291126637493771635 32313061936689956240657453)
      ·
        refine ⟨12117398226258733590246545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32313061936689956240657453 12117398226258733590246545)
        ·
          refine ⟨9088048669694050192684909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12117398226258733590246545 9088048669694050192684909)
          ·
            refine ⟨3408018251135268822256841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9088048669694050192684909 3408018251135268822256841)
            ·
              refine ⟨2556013688351451616692631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3408018251135268822256841 2556013688351451616692631)
              ·
                refine ⟨3834020532527177425038947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2556013688351451616692631 3834020532527177425038947)
                ·
                  refine ⟨5751030798790766137558421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3834020532527177425038947 5751030798790766137558421)
                  ·
                    refine ⟨269579568693317162698051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5751030798790766137558421 269579568693317162698051)
                    ·
                      rfl

theorem cell23_1575013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 6].length) (baseStart_1575013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575013 prefixEnd_1575013 := by exact prefixLift 1575013
  have htrace : WordTrace (prefixWord ++ tailWord_1575013) baseStart_1575013 baseEnd_1575013 := by
    simpa [prefixWord, tailWord_1575013, baseEnd_1575013] using wordTrace_append hprefix tailTrace_1575013
  have hstable : (prefixWord ++ tailWord_1575013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575013).length < 2 ^ (prefixWord ++ tailWord_1575013).sum := by decide
  have hdescent : baseEnd_1575013 < baseStart_1575013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575020 : List Nat := [2, 2, 1, 1, 3, 3, 1, 1, 5, 2, 2]
def baseStart_1575020 : Nat := 118140960795 + 1575020 * 2 ^ 59
def prefixEnd_1575020 : Nat := 4983230072969 + 3 ^ 40 * 1575020 * 2
def baseEnd_1575020 : Nat := 808742300444532960706621

theorem tailTrace_1575020 : CollatzResearch.WordTrace tailWord_1575020 prefixEnd_1575020 808742300444532960706621 := by
  unfold tailWord_1575020
  simp only [CollatzResearch.WordTrace]
  refine ⟨28722849376989503422781257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38297132502652671230375009 28722849376989503422781257)
  ·
    refine ⟨21542137032742127567085943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28722849376989503422781257 21542137032742127567085943)
    ·
      refine ⟨32313205549113191350628915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21542137032742127567085943 32313205549113191350628915)
      ·
        refine ⟨48469808323669787025943373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32313205549113191350628915 48469808323669787025943373)
        ·
          refine ⟨18176178121376170134728765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48469808323669787025943373 18176178121376170134728765)
          ·
            refine ⟨6816066795516063800523287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18176178121376170134728765 6816066795516063800523287)
            ·
              refine ⟨10224100193274095700784931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6816066795516063800523287 10224100193274095700784931)
              ·
                refine ⟨15336150289911143551177397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10224100193274095700784931 15336150289911143551177397)
                ·
                  refine ⟨1437764089679169707922881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15336150289911143551177397 1437764089679169707922881)
                  ·
                    refine ⟨1078323067259377280942161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1437764089679169707922881 1078323067259377280942161)
                    ·
                      refine ⟨808742300444532960706621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1078323067259377280942161 808742300444532960706621)
                      ·
                        rfl

theorem cell23_1575020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 2, 2].length) (baseStart_1575020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575020 prefixEnd_1575020 := by exact prefixLift 1575020
  have htrace : WordTrace (prefixWord ++ tailWord_1575020) baseStart_1575020 baseEnd_1575020 := by
    simpa [prefixWord, tailWord_1575020, baseEnd_1575020] using wordTrace_append hprefix tailTrace_1575020
  have hstable : (prefixWord ++ tailWord_1575020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575020).length < 2 ^ (prefixWord ++ tailWord_1575020).sum := by decide
  have hdescent : baseEnd_1575020 < baseStart_1575020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575023 : List Nat := [1, 1, 2, 1, 3, 4, 2, 1, 3, 2, 3]
def baseStart_1575023 : Nat := 118140960795 + 1575023 * 2 ^ 59
def prefixEnd_1575023 : Nat := 4983230072969 + 3 ^ 40 * 1575023 * 2
def baseEnd_1575023 : Nat := 808743840886496448969107

theorem tailTrace_1575023 : CollatzResearch.WordTrace tailWord_1575023 prefixEnd_1575023 808743840886496448969107 := by
  unfold tailWord_1575023
  simp only [CollatzResearch.WordTrace]
  refine ⟨57445808172968138357921723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38297205448645425571947815 57445808172968138357921723)
  ·
    refine ⟨86168712259452207536882585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57445808172968138357921723 86168712259452207536882585)
    ·
      refine ⟨64626534194589155652661939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86168712259452207536882585 64626534194589155652661939)
      ·
        refine ⟨96939801291883733478992909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64626534194589155652661939 96939801291883733478992909)
        ·
          refine ⟨36352425484456400054622341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96939801291883733478992909 36352425484456400054622341)
          ·
            refine ⟨6816079778335575010241689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36352425484456400054622341 6816079778335575010241689)
            ·
              refine ⟨5112059833751681257681267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6816079778335575010241689 5112059833751681257681267)
              ·
                refine ⟨7668089750627521886521901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5112059833751681257681267 7668089750627521886521901)
                ·
                  refine ⟨2875533656485320707445713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7668089750627521886521901 2875533656485320707445713)
                  ·
                    refine ⟨2156650242363990530584285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2875533656485320707445713 2156650242363990530584285)
                    ·
                      refine ⟨808743840886496448969107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2156650242363990530584285 808743840886496448969107)
                      ·
                        rfl

theorem cell23_1575023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 2, 3].length) (baseStart_1575023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575023 prefixEnd_1575023 := by exact prefixLift 1575023
  have htrace : WordTrace (prefixWord ++ tailWord_1575023) baseStart_1575023 baseEnd_1575023 := by
    simpa [prefixWord, tailWord_1575023, baseEnd_1575023] using wordTrace_append hprefix tailTrace_1575023
  have hstable : (prefixWord ++ tailWord_1575023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575023).length < 2 ^ (prefixWord ++ tailWord_1575023).sum := by decide
  have hdescent : baseEnd_1575023 < baseStart_1575023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575033 : List Nat := [1, 2, 1, 3, 4, 1, 2, 2, 1, 2, 4]
def baseStart_1575033 : Nat := 118140960795 + 1575033 * 2 ^ 59
def prefixEnd_1575033 : Nat := 4983230072969 + 3 ^ 40 * 1575033 * 2
def baseEnd_1575033 : Nat := 808748975693041409844061

theorem tailTrace_1575033 : CollatzResearch.WordTrace tailWord_1575033 prefixEnd_1575033 808748975693041409844061 := by
  unfold tailWord_1575033
  simp only [CollatzResearch.WordTrace]
  refine ⟨57446172902931910065785753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38297448601954606710523835 57446172902931910065785753)
  ·
    refine ⟨43084629677198932549339315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57446172902931910065785753 43084629677198932549339315)
    ·
      refine ⟨64626944515798398824008973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43084629677198932549339315 64626944515798398824008973)
      ·
        refine ⟨24235104193424399559003365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64626944515798398824008973 24235104193424399559003365)
        ·
          refine ⟨4544082036267074917313131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24235104193424399559003365 4544082036267074917313131)
          ·
            refine ⟨6816123054400612375969697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4544082036267074917313131 6816123054400612375969697)
            ·
              refine ⟨5112092290800459281977273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6816123054400612375969697 5112092290800459281977273)
              ·
                refine ⟨3834069218100344461482955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5112092290800459281977273 3834069218100344461482955)
                ·
                  refine ⟨5751103827150516692224433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3834069218100344461482955 5751103827150516692224433)
                  ·
                    refine ⟨4313327870362887519168325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5751103827150516692224433 4313327870362887519168325)
                    ·
                      refine ⟨808748975693041409844061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4313327870362887519168325 808748975693041409844061)
                      ·
                        rfl

theorem cell23_1575033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_1575033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575033 prefixEnd_1575033 := by exact prefixLift 1575033
  have htrace : WordTrace (prefixWord ++ tailWord_1575033) baseStart_1575033 baseEnd_1575033 := by
    simpa [prefixWord, tailWord_1575033, baseEnd_1575033] using wordTrace_append hprefix tailTrace_1575033
  have hstable : (prefixWord ++ tailWord_1575033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575033).length < 2 ^ (prefixWord ++ tailWord_1575033).sum := by decide
  have hdescent : baseEnd_1575033 < baseStart_1575033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575037 : List Nat := [1, 4, 1, 1, 3, 4, 2, 1, 1, 1, 4]
def baseStart_1575037 : Nat := 118140960795 + 1575037 * 2 ^ 59
def prefixEnd_1575037 : Nat := 4983230072969 + 3 ^ 40 * 1575037 * 2
def baseEnd_1575037 : Nat := 808751029615659394194043

theorem tailTrace_1575037 : CollatzResearch.WordTrace tailWord_1575037 prefixEnd_1575037 808751029615659394194043 := by
  unfold tailWord_1575037
  simp only [CollatzResearch.WordTrace]
  refine ⟨57446318794917418748931365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38297545863278279165954243 57446318794917418748931365)
  ·
    refine ⟨10771184774047016015424631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57446318794917418748931365 10771184774047016015424631)
    ·
      refine ⟨16156777161070524023136947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10771184774047016015424631 16156777161070524023136947)
      ·
        refine ⟨24235165741605786034705421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16156777161070524023136947 24235165741605786034705421)
        ·
          refine ⟨9088187153102169763014533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24235165741605786034705421 9088187153102169763014533)
          ·
            refine ⟨1704035091206656830565225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9088187153102169763014533 1704035091206656830565225)
            ·
              refine ⟨1278026318404992622923919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1704035091206656830565225 1278026318404992622923919)
              ·
                refine ⟨1917039477607488934385879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1278026318404992622923919 1917039477607488934385879)
                ·
                  refine ⟨2875559216411233401578819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1917039477607488934385879 2875559216411233401578819)
                  ·
                    refine ⟨4313338824616850102368229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2875559216411233401578819 4313338824616850102368229)
                    ·
                      refine ⟨808751029615659394194043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4313338824616850102368229 808751029615659394194043)
                      ·
                        rfl

theorem cell23_1575037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 1, 1, 4].length) (baseStart_1575037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575037 prefixEnd_1575037 := by exact prefixLift 1575037
  have htrace : WordTrace (prefixWord ++ tailWord_1575037) baseStart_1575037 baseEnd_1575037 := by
    simpa [prefixWord, tailWord_1575037, baseEnd_1575037] using wordTrace_append hprefix tailTrace_1575037
  have hstable : (prefixWord ++ tailWord_1575037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575037).length < 2 ^ (prefixWord ++ tailWord_1575037).sum := by decide
  have hdescent : baseEnd_1575037 < baseStart_1575037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575054 : List Nat := [4, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2]
def baseStart_1575054 : Nat := 118140960795 + 1575054 * 2 ^ 59
def prefixEnd_1575054 : Nat := 4983230072969 + 3 ^ 40 * 1575054 * 2
def baseEnd_1575054 : Nat := 808759758786785827681465

theorem tailTrace_1575054 : CollatzResearch.WordTrace tailWord_1575054 prefixEnd_1575054 808759758786785827681465 := by
  unfold tailWord_1575054
  simp only [CollatzResearch.WordTrace]
  refine ⟨7180867354481978831537527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38297959223903887101533477 7180867354481978831537527)
  ·
    refine ⟨10771301031722968247306291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7180867354481978831537527 10771301031722968247306291)
    ·
      refine ⟨16156951547584452370959437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10771301031722968247306291 16156951547584452370959437)
      ·
        refine ⟨6058856830344169639109789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16156951547584452370959437 6058856830344169639109789)
        ·
          refine ⟨2272071311379063614666171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6058856830344169639109789 2272071311379063614666171)
          ·
            refine ⟨3408106967068595421999257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2272071311379063614666171 3408106967068595421999257)
            ·
              refine ⟨2556080225301446566499443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3408106967068595421999257 2556080225301446566499443)
              ·
                refine ⟨3834120337952169849749165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2556080225301446566499443 3834120337952169849749165)
                ·
                  refine ⟨1437795126732063693655937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3834120337952169849749165 1437795126732063693655937)
                  ·
                    refine ⟨1078346345049047770241953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1437795126732063693655937 1078346345049047770241953)
                    ·
                      refine ⟨808759758786785827681465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1078346345049047770241953 808759758786785827681465)
                      ·
                        rfl

theorem cell23_1575054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_1575054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575054 prefixEnd_1575054 := by exact prefixLift 1575054
  have htrace : WordTrace (prefixWord ++ tailWord_1575054) baseStart_1575054 baseEnd_1575054 := by
    simpa [prefixWord, tailWord_1575054, baseEnd_1575054] using wordTrace_append hprefix tailTrace_1575054
  have hstable : (prefixWord ++ tailWord_1575054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575054).length < 2 ^ (prefixWord ++ tailWord_1575054).sum := by decide
  have hdescent : baseEnd_1575054 < baseStart_1575054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575150 : List Nat := [4, 1, 2, 1, 1, 1, 1, 7, 5]
def baseStart_1575150 : Nat := 118140960795 + 1575150 * 2 ^ 59
def prefixEnd_1575150 : Nat := 4983230072969 + 3 ^ 40 * 1575150 * 2
def baseEnd_1575150 : Nat := 89867672547735272453447

theorem tailTrace_1575150 : CollatzResearch.WordTrace tailWord_1575150 prefixEnd_1575150 89867672547735272453447 := by
  unfold tailWord_1575150
  simp only [CollatzResearch.WordTrace]
  refine ⟨7181305030438504880974363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38300293495672026031863269 7181305030438504880974363)
  ·
    refine ⟨10771957545657757321461545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7181305030438504880974363 10771957545657757321461545)
    ·
      refine ⟨8078968159243317991096159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10771957545657757321461545 8078968159243317991096159)
      ·
        refine ⟨12118452238864976986644239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8078968159243317991096159 12118452238864976986644239)
        ·
          refine ⟨18177678358297465479966359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12118452238864976986644239 18177678358297465479966359)
          ·
            refine ⟨27266517537446198219949539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18177678358297465479966359 27266517537446198219949539)
            ·
              refine ⟨40899776306169297329924309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27266517537446198219949539 40899776306169297329924309)
              ·
                refine ⟨958588507175842906170101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 40899776306169297329924309 958588507175842906170101)
                ·
                  refine ⟨89867672547735272453447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 958588507175842906170101 89867672547735272453447)
                  ·
                    rfl

theorem cell23_1575150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 7, 5].length) (baseStart_1575150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575150 prefixEnd_1575150 := by exact prefixLift 1575150
  have htrace : WordTrace (prefixWord ++ tailWord_1575150) baseStart_1575150 baseEnd_1575150 := by
    simpa [prefixWord, tailWord_1575150, baseEnd_1575150] using wordTrace_append hprefix tailTrace_1575150
  have hstable : (prefixWord ++ tailWord_1575150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575150).length < 2 ^ (prefixWord ++ tailWord_1575150).sum := by decide
  have hdescent : baseEnd_1575150 < baseStart_1575150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575183 : List Nat := [1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 4]
def baseStart_1575183 : Nat := 118140960795 + 1575183 * 2 ^ 59
def prefixEnd_1575183 : Nat := 4983230072969 + 3 ^ 40 * 1575183 * 2
def baseEnd_1575183 : Nat := 808825997791215822968371

theorem tailTrace_1575183 : CollatzResearch.WordTrace tailWord_1575183 prefixEnd_1575183 808825997791215822968371 := by
  unfold tailWord_1575183
  simp only [CollatzResearch.WordTrace]
  refine ⟨57451643852388485683746203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38301095901592323789164135 57451643852388485683746203)
  ·
    refine ⟨86177465778582728525619305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57451643852388485683746203 86177465778582728525619305)
    ·
      refine ⟨64633099333937046394214479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86177465778582728525619305 64633099333937046394214479)
      ·
        refine ⟨96949649000905569591321719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64633099333937046394214479 96949649000905569591321719)
        ·
          refine ⟨145424473501358354386982579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96949649000905569591321719 145424473501358354386982579)
          ·
            refine ⟨218136710252037531580473869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145424473501358354386982579 218136710252037531580473869)
            ·
              refine ⟨81801266344514074342677701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 218136710252037531580473869 81801266344514074342677701)
              ·
                refine ⟨15337737439596388939252069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81801266344514074342677701 15337737439596388939252069)
                ·
                  refine ⟨2875825769924322926109763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15337737439596388939252069 2875825769924322926109763)
                  ·
                    refine ⟨4313738654886484389164645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2875825769924322926109763 4313738654886484389164645)
                    ·
                      refine ⟨808825997791215822968371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4313738654886484389164645 808825997791215822968371)
                      ·
                        rfl

theorem cell23_1575183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 4].length) (baseStart_1575183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575183 prefixEnd_1575183 := by exact prefixLift 1575183
  have htrace : WordTrace (prefixWord ++ tailWord_1575183) baseStart_1575183 baseEnd_1575183 := by
    simpa [prefixWord, tailWord_1575183, baseEnd_1575183] using wordTrace_append hprefix tailTrace_1575183
  have hstable : (prefixWord ++ tailWord_1575183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575183).length < 2 ^ (prefixWord ++ tailWord_1575183).sum := by decide
  have hdescent : baseEnd_1575183 < baseStart_1575183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575200 : List Nat := [2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 4]
def baseStart_1575200 : Nat := 118140960795 + 1575200 * 2 ^ 59
def prefixEnd_1575200 : Nat := 4983230072969 + 3 ^ 40 * 1575200 * 2
def baseEnd_1575200 : Nat := 808834726962342256455793

theorem tailTrace_1575200 : CollatzResearch.WordTrace tailWord_1575200 prefixEnd_1575200 808834726962342256455793 := by
  unfold tailWord_1575200
  simp only [CollatzResearch.WordTrace]
  refine ⟨28726131946663448793557527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38301509262217931724743369 28726131946663448793557527)
  ·
    refine ⟨43089197919995173190336291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28726131946663448793557527 43089197919995173190336291)
    ·
      refine ⟨64633796879992759785504437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43089197919995173190336291 64633796879992759785504437)
      ·
        refine ⟨6059418457499321229891041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64633796879992759785504437 6059418457499321229891041)
        ·
          refine ⟨4544563843124490922418281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6059418457499321229891041 4544563843124490922418281)
          ·
            refine ⟨3408422882343368191813711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4544563843124490922418281 3408422882343368191813711)
            ·
              refine ⟨5112634323515052287720567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3408422882343368191813711 5112634323515052287720567)
              ·
                refine ⟨7668951485272578431580851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5112634323515052287720567 7668951485272578431580851)
                ·
                  refine ⟨11503427227908867647371277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7668951485272578431580851 11503427227908867647371277)
                  ·
                    refine ⟨4313785210465825367764229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11503427227908867647371277 4313785210465825367764229)
                    ·
                      refine ⟨808834726962342256455793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4313785210465825367764229 808834726962342256455793)
                      ·
                        rfl

theorem cell23_1575200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_1575200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575200 prefixEnd_1575200 := by exact prefixLift 1575200
  have htrace : WordTrace (prefixWord ++ tailWord_1575200) baseStart_1575200 baseEnd_1575200 := by
    simpa [prefixWord, tailWord_1575200, baseEnd_1575200] using wordTrace_append hprefix tailTrace_1575200
  have hstable : (prefixWord ++ tailWord_1575200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575200).length < 2 ^ (prefixWord ++ tailWord_1575200).sum := by decide
  have hdescent : baseEnd_1575200 < baseStart_1575200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575283 : List Nat := [1, 1, 1, 2, 2, 1, 2, 4, 3, 6]
def baseStart_1575283 : Nat := 118140960795 + 1575283 * 2 ^ 59
def prefixEnd_1575283 : Nat := 4983230072969 + 3 ^ 40 * 1575283 * 2
def baseEnd_1575283 : Nat := 269625781952221810572637

theorem tailTrace_1575283 : CollatzResearch.WordTrace tailWord_1575283 prefixEnd_1575283 269625781952221810572637 := by
  unfold tailWord_1575283
  simp only [CollatzResearch.WordTrace]
  refine ⟨57455291152026202762386503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38303527434684135174924335 57455291152026202762386503)
  ·
    refine ⟨86182936728039304143579755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57455291152026202762386503 86182936728039304143579755)
    ·
      refine ⟨129274405092058956215369633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86182936728039304143579755 129274405092058956215369633)
      ·
        refine ⟨96955803819044217161527225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129274405092058956215369633 96955803819044217161527225)
        ·
          refine ⟨72716852864283162871145419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96955803819044217161527225 72716852864283162871145419)
          ·
            refine ⟨109075279296424744306718129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72716852864283162871145419 109075279296424744306718129)
            ·
              refine ⟨81806459472318558230038597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109075279296424744306718129 81806459472318558230038597)
              ·
                refine ⟨15338711151059729668132237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81806459472318558230038597 15338711151059729668132237)
                ·
                  refine ⟨5752016681647398625549589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15338711151059729668132237 5752016681647398625549589)
                  ·
                    refine ⟨269625781952221810572637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5752016681647398625549589 269625781952221810572637)
                    ·
                      rfl

theorem cell23_1575283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 6].length) (baseStart_1575283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575283 prefixEnd_1575283 := by exact prefixLift 1575283
  have htrace : WordTrace (prefixWord ++ tailWord_1575283) baseStart_1575283 baseEnd_1575283 := by
    simpa [prefixWord, tailWord_1575283, baseEnd_1575283] using wordTrace_append hprefix tailTrace_1575283
  have hstable : (prefixWord ++ tailWord_1575283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575283).length < 2 ^ (prefixWord ++ tailWord_1575283).sum := by decide
  have hdescent : baseEnd_1575283 < baseStart_1575283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575300 : List Nat := [2, 3, 2, 1, 1, 2, 2, 3, 1, 6]
def baseStart_1575300 : Nat := 118140960795 + 1575300 * 2 ^ 59
def prefixEnd_1575300 : Nat := 4983230072969 + 3 ^ 40 * 1575300 * 2
def baseEnd_1575300 : Nat := 269628691675930621735111

theorem tailTrace_1575300 : CollatzResearch.WordTrace tailWord_1575300 prefixEnd_1575300 269628691675930621735111 := by
  unfold tailWord_1575300
  simp only [CollatzResearch.WordTrace]
  refine ⟨28727955596482307332877677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38303940795309743110503569 28727955596482307332877677)
  ·
    refine ⟨10772983348680865249829129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28727955596482307332877677 10772983348680865249829129)
    ·
      refine ⟨8079737511510648937371847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10772983348680865249829129 8079737511510648937371847)
      ·
        refine ⟨12119606267265973406057771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8079737511510648937371847 12119606267265973406057771)
        ·
          refine ⟨18179409400898960109086657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12119606267265973406057771 18179409400898960109086657)
          ·
            refine ⟨13634557050674220081814993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18179409400898960109086657 13634557050674220081814993)
            ·
              refine ⟨10225917788005665061361245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13634557050674220081814993 10225917788005665061361245)
              ·
                refine ⟨3834719170502124398010467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10225917788005665061361245 3834719170502124398010467)
                ·
                  refine ⟨5752078755753186597015701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3834719170502124398010467 5752078755753186597015701)
                  ·
                    refine ⟨269628691675930621735111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5752078755753186597015701 269628691675930621735111)
                    ·
                      rfl

theorem cell23_1575300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_1575300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575300 prefixEnd_1575300 := by exact prefixLift 1575300
  have htrace : WordTrace (prefixWord ++ tailWord_1575300) baseStart_1575300 baseEnd_1575300 := by
    simpa [prefixWord, tailWord_1575300, baseEnd_1575300] using wordTrace_append hprefix tailTrace_1575300
  have hstable : (prefixWord ++ tailWord_1575300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575300).length < 2 ^ (prefixWord ++ tailWord_1575300).sum := by decide
  have hdescent : baseEnd_1575300 < baseStart_1575300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575307 : List Nat := [1, 1, 1, 1, 4, 4, 3, 2, 1, 1, 4]
def baseStart_1575307 : Nat := 118140960795 + 1575307 * 2 ^ 59
def prefixEnd_1575307 : Nat := 4983230072969 + 3 ^ 40 * 1575307 * 2
def baseEnd_1575307 : Nat := 808889669392373337817801

theorem tailTrace_1575307 : CollatzResearch.WordTrace tailWord_1575307 prefixEnd_1575307 808889669392373337817801 := by
  unfold tailWord_1575307
  simp only [CollatzResearch.WordTrace]
  refine ⟨57456166503939254861260175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38304111002626169907506783 57456166503939254861260175)
  ·
    refine ⟨86184249755908882291890263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57456166503939254861260175 86184249755908882291890263)
    ·
      refine ⟨129276374633863323437835395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86184249755908882291890263 129276374633863323437835395)
      ·
        refine ⟨193914561950794985156753093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129276374633863323437835395 193914561950794985156753093)
        ·
          refine ⟨36358980365774059716891205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193914561950794985156753093 36358980365774059716891205)
          ·
            refine ⟨6817308818582636196917101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36358980365774059716891205 6817308818582636196917101)
            ·
              refine ⟨2556490806968488573843913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6817308818582636196917101 2556490806968488573843913)
              ·
                refine ⟨1917368105226366430382935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2556490806968488573843913 1917368105226366430382935)
                ·
                  refine ⟨2876052157839549645574403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1917368105226366430382935 2876052157839549645574403)
                  ·
                    refine ⟨4314078236759324468361605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2876052157839549645574403 4314078236759324468361605)
                    ·
                      refine ⟨808889669392373337817801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4314078236759324468361605 808889669392373337817801)
                      ·
                        rfl

theorem cell23_1575307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 1, 4].length) (baseStart_1575307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575307 prefixEnd_1575307 := by exact prefixLift 1575307
  have htrace : WordTrace (prefixWord ++ tailWord_1575307) baseStart_1575307 baseEnd_1575307 := by
    simpa [prefixWord, tailWord_1575307, baseEnd_1575307] using wordTrace_append hprefix tailTrace_1575307
  have hstable : (prefixWord ++ tailWord_1575307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575307).length < 2 ^ (prefixWord ++ tailWord_1575307).sum := by decide
  have hdescent : baseEnd_1575307 < baseStart_1575307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575340 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 3]
def baseStart_1575340 : Nat := 118140960795 + 1575340 * 2 ^ 59
def prefixEnd_1575340 : Nat := 4983230072969 + 3 ^ 40 * 1575340 * 2
def baseEnd_1575340 : Nat := 808906614253971708705149

theorem tailTrace_1575340 : CollatzResearch.WordTrace tailWord_1575340 prefixEnd_1575340 808906614253971708705149 := by
  unfold tailWord_1575340
  simp only [CollatzResearch.WordTrace]
  refine ⟨28728685056409850748605737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38304913408546467664807649 28728685056409850748605737)
  ·
    refine ⟨21546513792307388061454303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28728685056409850748605737 21546513792307388061454303)
    ·
      refine ⟨32319770688461082092181455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21546513792307388061454303 32319770688461082092181455)
      ·
        refine ⟨48479656032691623138272183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32319770688461082092181455 48479656032691623138272183)
        ·
          refine ⟨72719484049037434707408275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48479656032691623138272183 72719484049037434707408275)
          ·
            refine ⟨109079226073556152061112413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72719484049037434707408275 109079226073556152061112413)
            ·
              refine ⟨40904709777583557022917155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109079226073556152061112413 40904709777583557022917155)
              ·
                refine ⟨61357064666375335534375733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40904709777583557022917155 61357064666375335534375733)
                ·
                  refine ⟨5752224812472687706347725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61357064666375335534375733 5752224812472687706347725)
                  ·
                    refine ⟨2157084304677257889880397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5752224812472687706347725 2157084304677257889880397)
                    ·
                      refine ⟨808906614253971708705149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2157084304677257889880397 808906614253971708705149)
                      ·
                        rfl

theorem cell23_1575340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 3].length) (baseStart_1575340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575340 prefixEnd_1575340 := by exact prefixLift 1575340
  have htrace : WordTrace (prefixWord ++ tailWord_1575340) baseStart_1575340 baseEnd_1575340 := by
    simpa [prefixWord, tailWord_1575340, baseEnd_1575340] using wordTrace_append hprefix tailTrace_1575340
  have hstable : (prefixWord ++ tailWord_1575340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575340).length < 2 ^ (prefixWord ++ tailWord_1575340).sum := by decide
  have hdescent : baseEnd_1575340 < baseStart_1575340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575357 : List Nat := [1, 4, 1, 2, 2, 2, 1, 3, 1, 3, 3]
def baseStart_1575357 : Nat := 118140960795 + 1575357 * 2 ^ 59
def prefixEnd_1575357 : Nat := 4983230072969 + 3 ^ 40 * 1575357 * 2
def baseEnd_1575357 : Nat := 808915343425098142192571

theorem tailTrace_1575357 : CollatzResearch.WordTrace tailWord_1575357 prefixEnd_1575357 808915343425098142192571 := by
  unfold tailWord_1575357
  simp only [CollatzResearch.WordTrace]
  refine ⟨57457990153758113400580325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38305326769172075600386883 57457990153758113400580325)
  ·
    refine ⟨10773373153829646262608811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57457990153758113400580325 10773373153829646262608811)
    ·
      refine ⟨16160059730744469393913217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10773373153829646262608811 16160059730744469393913217)
      ·
        refine ⟨12120044798058352045434913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16160059730744469393913217 12120044798058352045434913)
        ·
          refine ⟨9090033598543764034076185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12120044798058352045434913 9090033598543764034076185)
          ·
            refine ⟨6817525198907823025557139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9090033598543764034076185 6817525198907823025557139)
            ·
              refine ⟨10226287798361734538335709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6817525198907823025557139 10226287798361734538335709)
              ·
                refine ⟨3834857924385650451875891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10226287798361734538335709 3834857924385650451875891)
                ·
                  refine ⟨5752286886578475677813837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3834857924385650451875891 5752286886578475677813837)
                  ·
                    refine ⟨2157107582466928379180189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5752286886578475677813837 2157107582466928379180189)
                    ·
                      refine ⟨808915343425098142192571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2157107582466928379180189 808915343425098142192571)
                      ·
                        rfl

theorem cell23_1575357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_1575357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575357 prefixEnd_1575357 := by exact prefixLift 1575357
  have htrace : WordTrace (prefixWord ++ tailWord_1575357) baseStart_1575357 baseEnd_1575357 := by
    simpa [prefixWord, tailWord_1575357, baseEnd_1575357] using wordTrace_append hprefix tailTrace_1575357
  have hstable : (prefixWord ++ tailWord_1575357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575357).length < 2 ^ (prefixWord ++ tailWord_1575357).sum := by decide
  have hdescent : baseEnd_1575357 < baseStart_1575357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575364 : List Nat := [2, 3, 3, 2, 2, 1, 3, 7]
def baseStart_1575364 : Nat := 118140960795 + 1575364 * 2 ^ 59
def prefixEnd_1575364 : Nat := 4983230072969 + 3 ^ 40 * 1575364 * 2
def baseEnd_1575364 : Nat := 29959960658877022770557

theorem tailTrace_1575364 : CollatzResearch.WordTrace tailWord_1575364 prefixEnd_1575364 29959960658877022770557 := by
  unfold tailWord_1575364
  simp only [CollatzResearch.WordTrace]
  refine ⟨28729122732366376798042573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38305496976488502397390097 28729122732366376798042573)
  ·
    refine ⟨10773421024637391299265965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28729122732366376798042573 10773421024637391299265965)
    ·
      refine ⟨4040032884239021737224737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10773421024637391299265965 4040032884239021737224737)
      ·
        refine ⟨3030024663179266302918553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4040032884239021737224737 3030024663179266302918553)
        ·
          refine ⟨2272518497384449727188915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3030024663179266302918553 2272518497384449727188915)
          ·
            refine ⟨3408777746076674590783373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2272518497384449727188915 3408777746076674590783373)
            ·
              refine ⟨1278291654778752971543765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3408777746076674590783373 1278291654778752971543765)
              ·
                refine ⟨29959960658877022770557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1278291654778752971543765 29959960658877022770557)
                ·
                  rfl

theorem cell23_1575364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 7].length) (baseStart_1575364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575364 prefixEnd_1575364 := by exact prefixLift 1575364
  have htrace : WordTrace (prefixWord ++ tailWord_1575364) baseStart_1575364 baseEnd_1575364 := by
    simpa [prefixWord, tailWord_1575364, baseEnd_1575364] using wordTrace_append hprefix tailTrace_1575364
  have hstable : (prefixWord ++ tailWord_1575364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575364).length < 2 ^ (prefixWord ++ tailWord_1575364).sum := by decide
  have hdescent : baseEnd_1575364 < baseStart_1575364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575370 : List Nat := [3, 1, 2, 1, 2, 2, 2, 1, 2, 2, 5]
def baseStart_1575370 : Nat := 118140960795 + 1575370 * 2 ^ 59
def prefixEnd_1575370 : Nat := 4983230072969 + 3 ^ 40 * 1575370 * 2
def baseEnd_1575370 : Nat := 808922018673606591330011

theorem tailTrace_1575370 : CollatzResearch.WordTrace tailWord_1575370 prefixEnd_1575370 808922018673606591330011 := by
  unfold tailWord_1575370
  simp only [CollatzResearch.WordTrace]
  refine ⟨14364616075677754155200891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38305642868474011080535709 14364616075677754155200891)
  ·
    refine ⟨21546924113516631232801337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14364616075677754155200891 21546924113516631232801337)
    ·
      refine ⟨16160193085137473424601003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21546924113516631232801337 16160193085137473424601003)
      ·
        refine ⟨24240289627706210136901505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16160193085137473424601003 24240289627706210136901505)
        ·
          refine ⟨18180217220779657602676129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24240289627706210136901505 18180217220779657602676129)
          ·
            refine ⟨13635162915584743202007097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18180217220779657602676129 13635162915584743202007097)
            ·
              refine ⟨10226372186688557401505323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13635162915584743202007097 10226372186688557401505323)
              ·
                refine ⟨15339558280032836102257985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10226372186688557401505323 15339558280032836102257985)
                ·
                  refine ⟨11504668710024627076693489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15339558280032836102257985 11504668710024627076693489)
                  ·
                    refine ⟨8628501532518470307520117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11504668710024627076693489 8628501532518470307520117)
                    ·
                      refine ⟨808922018673606591330011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8628501532518470307520117 808922018673606591330011)
                      ·
                        rfl

theorem cell23_1575370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_1575370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575370 prefixEnd_1575370 := by exact prefixLift 1575370
  have htrace : WordTrace (prefixWord ++ tailWord_1575370) baseStart_1575370 baseEnd_1575370 := by
    simpa [prefixWord, tailWord_1575370, baseEnd_1575370] using wordTrace_append hprefix tailTrace_1575370
  have hstable : (prefixWord ++ tailWord_1575370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575370).length < 2 ^ (prefixWord ++ tailWord_1575370).sum := by decide
  have hdescent : baseEnd_1575370 < baseStart_1575370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575391 : List Nat := [1, 1, 2, 3, 3, 4, 1, 2, 2, 1, 3]
def baseStart_1575391 : Nat := 118140960795 + 1575391 * 2 ^ 59
def prefixEnd_1575391 : Nat := 4983230072969 + 3 ^ 40 * 1575391 * 2
def baseEnd_1575391 : Nat := 808932801767351009167415

theorem tailTrace_1575391 : CollatzResearch.WordTrace tailWord_1575391 prefixEnd_1575391 808932801767351009167415 := by
  unfold tailWord_1575391
  simp only [CollatzResearch.WordTrace]
  refine ⟨57459230235634937207318027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38306153490423291471545351 57459230235634937207318027)
  ·
    refine ⟨86188845353452405810977041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57459230235634937207318027 86188845353452405810977041)
    ·
      refine ⟨64641634015089304358232781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86188845353452405810977041 64641634015089304358232781)
      ·
        refine ⟨24240612755658489134337293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64641634015089304358232781 24240612755658489134337293)
        ·
          refine ⟨9090229783371933425376485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24240612755658489134337293 9090229783371933425376485)
          ·
            refine ⟨1704418084382237517258091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9090229783371933425376485 1704418084382237517258091)
            ·
              refine ⟨2556627126573356275887137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1704418084382237517258091 2556627126573356275887137)
              ·
                refine ⟨1917470344930017206915353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2556627126573356275887137 1917470344930017206915353)
                ·
                  refine ⟨1438102758697512905186515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1917470344930017206915353 1438102758697512905186515)
                  ·
                    refine ⟨2157154138046269357779773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1438102758697512905186515 2157154138046269357779773)
                    ·
                      refine ⟨808932801767351009167415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2157154138046269357779773 808932801767351009167415)
                      ·
                        rfl

theorem cell23_1575391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 2, 1, 3].length) (baseStart_1575391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575391 prefixEnd_1575391 := by exact prefixLift 1575391
  have htrace : WordTrace (prefixWord ++ tailWord_1575391) baseStart_1575391 baseEnd_1575391 := by
    simpa [prefixWord, tailWord_1575391, baseEnd_1575391] using wordTrace_append hprefix tailTrace_1575391
  have hstable : (prefixWord ++ tailWord_1575391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575391).length < 2 ^ (prefixWord ++ tailWord_1575391).sum := by decide
  have hdescent : baseEnd_1575391 < baseStart_1575391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575469 : List Nat := [1, 5, 4, 1, 2, 1, 1, 2, 1, 3, 2]
def baseStart_1575469 : Nat := 118140960795 + 1575469 * 2 ^ 59
def prefixEnd_1575469 : Nat := 4983230072969 + 3 ^ 40 * 1575469 * 2
def baseEnd_1575469 : Nat := 808972853258401703992057

theorem tailTrace_1575469 : CollatzResearch.WordTrace tailWord_1575469 prefixEnd_1575469 808972853258401703992057 := by
  unfold tailWord_1575469
  simp only [CollatzResearch.WordTrace]
  refine ⟨57462075129352356528657461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38308050086234904352438307 57462075129352356528657461)
  ·
    refine ⟨5387069543376783424561637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57462075129352356528657461 5387069543376783424561637)
    ·
      refine ⟨1010075539383146892105307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5387069543376783424561637 1010075539383146892105307)
      ·
        refine ⟨1515113309074720338157961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1010075539383146892105307 1515113309074720338157961)
        ·
          refine ⟨1136334981806040253618471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1515113309074720338157961 1136334981806040253618471)
          ·
            refine ⟨1704502472709060380427707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1136334981806040253618471 1704502472709060380427707)
            ·
              refine ⟨2556753709063590570641561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1704502472709060380427707 2556753709063590570641561)
              ·
                refine ⟨1917565281797692927981171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2556753709063590570641561 1917565281797692927981171)
                ·
                  refine ⟨2876347922696539391971757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1917565281797692927981171 2876347922696539391971757)
                  ·
                    refine ⟨1078630471011202271989409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2876347922696539391971757 1078630471011202271989409)
                    ·
                      refine ⟨808972853258401703992057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1078630471011202271989409 808972853258401703992057)
                      ·
                        rfl

theorem cell23_1575469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_1575469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575469 prefixEnd_1575469 := by exact prefixLift 1575469
  have htrace : WordTrace (prefixWord ++ tailWord_1575469) baseStart_1575469 baseEnd_1575469 := by
    simpa [prefixWord, tailWord_1575469, baseEnd_1575469] using wordTrace_append hprefix tailTrace_1575469
  have hstable : (prefixWord ++ tailWord_1575469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575469).length < 2 ^ (prefixWord ++ tailWord_1575469).sum := by decide
  have hdescent : baseEnd_1575469 < baseStart_1575469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575484 : List Nat := [2, 2, 2, 2, 3, 2, 2, 1, 2, 5]
def baseStart_1575484 : Nat := 118140960795 + 1575484 * 2 ^ 59
def prefixEnd_1575484 : Nat := 4983230072969 + 3 ^ 40 * 1575484 * 2
def baseEnd_1575484 : Nat := 269660185156073048434829

theorem tailTrace_1575484 : CollatzResearch.WordTrace tailWord_1575484 prefixEnd_1575484 269660185156073048434829 := by
  unfold tailWord_1575484
  simp only [CollatzResearch.WordTrace]
  refine ⟨28731311112149007045226753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38308414816198676060302337 28731311112149007045226753)
  ·
    refine ⟨21548483334111755283920065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28731311112149007045226753 21548483334111755283920065)
    ·
      refine ⟨16161362500583816462940049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21548483334111755283920065 16161362500583816462940049)
      ·
        refine ⟨12121021875437862347205037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16161362500583816462940049 12121021875437862347205037)
        ·
          refine ⟨4545383203289198380201889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12121021875437862347205037 4545383203289198380201889)
          ·
            refine ⟨3409037402466898785151417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4545383203289198380201889 3409037402466898785151417)
            ·
              refine ⟨2556778051850174088863563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3409037402466898785151417 2556778051850174088863563)
              ·
                refine ⟨3835167077775261133295345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2556778051850174088863563 3835167077775261133295345)
                ·
                  refine ⟨2876375308331445849971509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3835167077775261133295345 2876375308331445849971509)
                  ·
                    refine ⟨269660185156073048434829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2876375308331445849971509 269660185156073048434829)
                    ·
                      rfl

theorem cell23_1575484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 2, 5].length) (baseStart_1575484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575484 prefixEnd_1575484 := by exact prefixLift 1575484
  have htrace : WordTrace (prefixWord ++ tailWord_1575484) baseStart_1575484 baseEnd_1575484 := by
    simpa [prefixWord, tailWord_1575484, baseEnd_1575484] using wordTrace_append hprefix tailTrace_1575484
  have hstable : (prefixWord ++ tailWord_1575484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575484).length < 2 ^ (prefixWord ++ tailWord_1575484).sum := by decide
  have hdescent : baseEnd_1575484 < baseStart_1575484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575538 : List Nat := [3, 2, 1, 2, 5, 1, 1, 1, 2, 1, 4]
def baseStart_1575538 : Nat := 118140960795 + 1575538 * 2 ^ 59
def prefixEnd_1575538 : Nat := 4983230072969 + 3 ^ 40 * 1575538 * 2
def baseEnd_1575538 : Nat := 809008283423561934029239

theorem tailTrace_1575538 : CollatzResearch.WordTrace tailWord_1575538 prefixEnd_1575538 809008283423561934029239 := by
  unfold tailWord_1575538
  simp only [CollatzResearch.WordTrace]
  refine ⟨14366147941525595328229817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38309727844068254208612845 14366147941525595328229817)
  ·
    refine ⟨10774610956144196496172363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14366147941525595328229817 10774610956144196496172363)
    ·
      refine ⟨16161916434216294744258545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10774610956144196496172363 16161916434216294744258545)
      ·
        refine ⟨12121437325662221058193909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16161916434216294744258545 12121437325662221058193909)
        ·
          refine ⟨1136384749280833224205679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12121437325662221058193909 1136384749280833224205679)
          ·
            refine ⟨1704577123921249836308519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1136384749280833224205679 1704577123921249836308519)
            ·
              refine ⟨2556865685881874754462779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1704577123921249836308519 2556865685881874754462779)
              ·
                refine ⟨3835298528822812131694169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2556865685881874754462779 3835298528822812131694169)
                ·
                  refine ⟨2876473896617109098770627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3835298528822812131694169 2876473896617109098770627)
                  ·
                    refine ⟨4314710844925663648155941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2876473896617109098770627 4314710844925663648155941)
                    ·
                      refine ⟨809008283423561934029239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4314710844925663648155941 809008283423561934029239)
                      ·
                        rfl

theorem cell23_1575538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_1575538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575538 prefixEnd_1575538 := by exact prefixLift 1575538
  have htrace : WordTrace (prefixWord ++ tailWord_1575538) baseStart_1575538 baseEnd_1575538 := by
    simpa [prefixWord, tailWord_1575538, baseEnd_1575538] using wordTrace_append hprefix tailTrace_1575538
  have hstable : (prefixWord ++ tailWord_1575538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575538).length < 2 ^ (prefixWord ++ tailWord_1575538).sum := by decide
  have hdescent : baseEnd_1575538 < baseStart_1575538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575541 : List Nat := [1, 3, 4, 2, 2, 1, 1, 1, 1, 4, 3]
def baseStart_1575541 : Nat := 118140960795 + 1575541 * 2 ^ 59
def prefixEnd_1575541 : Nat := 4983230072969 + 3 ^ 40 * 1575541 * 2
def baseEnd_1575541 : Nat := 809009823865525422291725

theorem tailTrace_1575541 : CollatzResearch.WordTrace tailWord_1575541 prefixEnd_1575541 809009823865525422291725 := by
  unfold tailWord_1575541
  simp only [CollatzResearch.WordTrace]
  refine ⟨57464701185091512825278477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38309800790061008550185651 57464701185091512825278477)
  ·
    refine ⟨21549262944409317309479429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57464701185091512825278477 21549262944409317309479429)
    ·
      refine ⟨4040486802076746995527393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21549262944409317309479429 4040486802076746995527393)
      ·
        refine ⟨3030365101557560246645545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4040486802076746995527393 3030365101557560246645545)
        ·
          refine ⟨2272773826168170184984159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3030365101557560246645545 2272773826168170184984159)
          ·
            refine ⟨3409160739252255277476239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2272773826168170184984159 3409160739252255277476239)
            ·
              refine ⟨5113741108878382916214359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3409160739252255277476239 5113741108878382916214359)
              ·
                refine ⟨7670611663317574374321539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5113741108878382916214359 7670611663317574374321539)
                ·
                  refine ⟨11505917494976361561482309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7670611663317574374321539 11505917494976361561482309)
                  ·
                    refine ⟨2157359530308067792777933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11505917494976361561482309 2157359530308067792777933)
                    ·
                      refine ⟨809009823865525422291725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2157359530308067792777933 809009823865525422291725)
                      ·
                        rfl

theorem cell23_1575541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_1575541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575541 prefixEnd_1575541 := by exact prefixLift 1575541
  have htrace : WordTrace (prefixWord ++ tailWord_1575541) baseStart_1575541 baseEnd_1575541 := by
    simpa [prefixWord, tailWord_1575541, baseEnd_1575541] using wordTrace_append hprefix tailTrace_1575541
  have hstable : (prefixWord ++ tailWord_1575541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575541).length < 2 ^ (prefixWord ++ tailWord_1575541).sum := by decide
  have hdescent : baseEnd_1575541 < baseStart_1575541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575578 : List Nat := [3, 1, 1, 6, 1, 1, 3, 1, 6]
def baseStart_1575578 : Nat := 118140960795 + 1575578 * 2 ^ 59
def prefixEnd_1575578 : Nat := 4983230072969 + 3 ^ 40 * 1575578 * 2
def baseEnd_1575578 : Nat := 89892091405526864169895

theorem tailTrace_1575578 : CollatzResearch.WordTrace tailWord_1575578 prefixEnd_1575578 89892091405526864169895 := by
  unfold tailWord_1575578
  simp only [CollatzResearch.WordTrace]
  refine ⟨14366512671489367036093847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38310700457304978762916925 14366512671489367036093847)
  ·
    refine ⟨21549769007234050554140771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14366512671489367036093847 21549769007234050554140771)
    ·
      refine ⟨32324653510851075831211157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21549769007234050554140771 32324653510851075831211157)
      ·
        refine ⟨1515218133321144179588023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32324653510851075831211157 1515218133321144179588023)
        ·
          refine ⟨2272827199981716269382035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1515218133321144179588023 2272827199981716269382035)
          ·
            refine ⟨3409240799972574404073053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2272827199981716269382035 3409240799972574404073053)
            ·
              refine ⟨1278465299989715401527395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3409240799972574404073053 1278465299989715401527395)
              ·
                refine ⟨1917697949984573102291093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1278465299989715401527395 1917697949984573102291093)
                ·
                  refine ⟨89892091405526864169895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1917697949984573102291093 89892091405526864169895)
                  ·
                    rfl

theorem cell23_1575578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 6].length) (baseStart_1575578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575578 prefixEnd_1575578 := by exact prefixLift 1575578
  have htrace : WordTrace (prefixWord ++ tailWord_1575578) baseStart_1575578 baseEnd_1575578 := by
    simpa [prefixWord, tailWord_1575578, baseEnd_1575578] using wordTrace_append hprefix tailTrace_1575578
  have hstable : (prefixWord ++ tailWord_1575578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575578).length < 2 ^ (prefixWord ++ tailWord_1575578).sum := by decide
  have hdescent : baseEnd_1575578 < baseStart_1575578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575587 : List Nat := [1, 1, 1, 4, 1, 1, 2, 5, 1, 6]
def baseStart_1575587 : Nat := 118140960795 + 1575587 * 2 ^ 59
def prefixEnd_1575587 : Nat := 4983230072969 + 3 ^ 40 * 1575587 * 2
def baseEnd_1575587 : Nat := 269677814658544080772171

theorem tailTrace_1575587 : CollatzResearch.WordTrace tailWord_1575587 prefixEnd_1575587 269677814658544080772171 := by
  unfold tailWord_1575587
  simp only [CollatzResearch.WordTrace]
  refine ⟨57466378942924862681453015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38310919295283241787635343 57466378942924862681453015)
  ·
    refine ⟨86199568414387294022179523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57466378942924862681453015 86199568414387294022179523)
    ·
      refine ⟨129299352621580941033269285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86199568414387294022179523 129299352621580941033269285)
      ·
        refine ⟨24243628616546426443737991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129299352621580941033269285 24243628616546426443737991)
        ·
          refine ⟨36365442924819639665606987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24243628616546426443737991 36365442924819639665606987)
          ·
            refine ⟨54548164387229459498410481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36365442924819639665606987 54548164387229459498410481)
            ·
              refine ⟨40911123290422094623807861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54548164387229459498410481 40911123290422094623807861)
              ·
                refine ⟨3835417808477071370981987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40911123290422094623807861 3835417808477071370981987)
                ·
                  refine ⟨5753126712715607056472981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3835417808477071370981987 5753126712715607056472981)
                  ·
                    refine ⟨269677814658544080772171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5753126712715607056472981 269677814658544080772171)
                    ·
                      rfl

theorem cell23_1575587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 6].length) (baseStart_1575587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575587 prefixEnd_1575587 := by exact prefixLift 1575587
  have htrace : WordTrace (prefixWord ++ tailWord_1575587) baseStart_1575587 baseEnd_1575587 := by
    simpa [prefixWord, tailWord_1575587, baseEnd_1575587] using wordTrace_append hprefix tailTrace_1575587
  have hstable : (prefixWord ++ tailWord_1575587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575587).length < 2 ^ (prefixWord ++ tailWord_1575587).sum := by decide
  have hdescent : baseEnd_1575587 < baseStart_1575587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575598 : List Nat := [4, 1, 4, 1, 1, 1, 2, 1, 1, 5, 2]
def baseStart_1575598 : Nat := 118140960795 + 1575598 * 2 ^ 59
def prefixEnd_1575598 : Nat := 4983230072969 + 3 ^ 40 * 1575598 * 2
def baseEnd_1575598 : Nat := 809039092262831699278963

theorem tailTrace_1575598 : CollatzResearch.WordTrace tailWord_1575598 prefixEnd_1575598 809039092262831699278963 := by
  unfold tailWord_1575598
  simp only [CollatzResearch.WordTrace]
  refine ⟨7183347518235626445012931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38311186763923341040068965 7183347518235626445012931)
  ·
    refine ⟨10775021277353439667519397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7183347518235626445012931 10775021277353439667519397)
    ·
      refine ⟨2020316489503769937659887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10775021277353439667519397 2020316489503769937659887)
      ·
        refine ⟨3030474734255654906489831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2020316489503769937659887 3030474734255654906489831)
        ·
          refine ⟨4545712101383482359734747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3030474734255654906489831 4545712101383482359734747)
          ·
            refine ⟨6818568152075223539602121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4545712101383482359734747 6818568152075223539602121)
            ·
              refine ⟨5113926114056417654701591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6818568152075223539602121 5113926114056417654701591)
              ·
                refine ⟨7670889171084626482052387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5113926114056417654701591 7670889171084626482052387)
                ·
                  refine ⟨11506333756626939723078581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7670889171084626482052387 11506333756626939723078581)
                  ·
                    refine ⟨1078718789683775599038617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11506333756626939723078581 1078718789683775599038617)
                    ·
                      refine ⟨809039092262831699278963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1078718789683775599038617 809039092262831699278963)
                      ·
                        rfl

theorem cell23_1575598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_1575598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575598 prefixEnd_1575598 := by exact prefixLift 1575598
  have htrace : WordTrace (prefixWord ++ tailWord_1575598) baseStart_1575598 baseEnd_1575598 := by
    simpa [prefixWord, tailWord_1575598, baseEnd_1575598] using wordTrace_append hprefix tailTrace_1575598
  have hstable : (prefixWord ++ tailWord_1575598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575598).length < 2 ^ (prefixWord ++ tailWord_1575598).sum := by decide
  have hdescent : baseEnd_1575598 < baseStart_1575598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575605 : List Nat := [1, 3, 3, 3, 1, 1, 3, 3, 1, 1, 3]
def baseStart_1575605 : Nat := 118140960795 + 1575605 * 2 ^ 59
def prefixEnd_1575605 : Nat := 4983230072969 + 3 ^ 40 * 1575605 * 2
def baseEnd_1575605 : Nat := 809042686627413171891431

theorem tailTrace_1575605 : CollatzResearch.WordTrace tailWord_1575605 prefixEnd_1575605 809042686627413171891431 := by
  unfold tailWord_1575605
  simp only [CollatzResearch.WordTrace]
  refine ⟨57467035456859651755608269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38311356971239767837072179 57467035456859651755608269)
  ·
    refine ⟨21550138296322369408353101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57467035456859651755608269 21550138296322369408353101)
    ·
      refine ⟨8081301861120888528132413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21550138296322369408353101 8081301861120888528132413)
      ·
        refine ⟨3030488197920333198049655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8081301861120888528132413 3030488197920333198049655)
        ·
          refine ⟨4545732296880499797074483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3030488197920333198049655 4545732296880499797074483)
          ·
            refine ⟨6818598445320749695611725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4545732296880499797074483 6818598445320749695611725)
            ·
              refine ⟨2556974416995281135854397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6818598445320749695611725 2556974416995281135854397)
              ·
                refine ⟨958865406373230425945399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2556974416995281135854397 958865406373230425945399)
                ·
                  refine ⟨1438298109559845638918099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 958865406373230425945399 1438298109559845638918099)
                  ·
                    refine ⟨2157447164339768458377149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1438298109559845638918099 2157447164339768458377149)
                    ·
                      refine ⟨809042686627413171891431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2157447164339768458377149 809042686627413171891431)
                      ·
                        rfl

theorem cell23_1575605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_1575605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575605 prefixEnd_1575605 := by exact prefixLift 1575605
  have htrace : WordTrace (prefixWord ++ tailWord_1575605) baseStart_1575605 baseEnd_1575605 := by
    simpa [prefixWord, tailWord_1575605, baseEnd_1575605] using wordTrace_append hprefix tailTrace_1575605
  have hstable : (prefixWord ++ tailWord_1575605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575605).length < 2 ^ (prefixWord ++ tailWord_1575605).sum := by decide
  have hdescent : baseEnd_1575605 < baseStart_1575605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575657 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 1, 4, 5]
def baseStart_1575657 : Nat := 118140960795 + 1575657 * 2 ^ 59
def prefixEnd_1575657 : Nat := 4983230072969 + 3 ^ 40 * 1575657 * 2
def baseEnd_1575657 : Nat := 809069387621446968441191

theorem tailTrace_1575657 : CollatzResearch.WordTrace tailWord_1575657 prefixEnd_1575657 809069387621446968441191 := by
  unfold tailWord_1575657
  simp only [CollatzResearch.WordTrace]
  refine ⟨57468932052671264636501225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38312621368447509757667483 57468932052671264636501225)
  ·
    refine ⟨43101699039503448477375919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57468932052671264636501225 43101699039503448477375919)
    ·
      refine ⟨64652548559255172716063879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43101699039503448477375919 64652548559255172716063879)
      ·
        refine ⟨96978822838882759074095819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64652548559255172716063879 96978822838882759074095819)
        ·
          refine ⟨145468234258324138611143729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96978822838882759074095819 145468234258324138611143729)
          ·
            refine ⟨109101175693743103958357797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145468234258324138611143729 109101175693743103958357797)
            ·
              refine ⟨20456470442576831992192087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109101175693743103958357797 20456470442576831992192087)
              ·
                refine ⟨30684705663865247988288131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20456470442576831992192087 30684705663865247988288131)
                ·
                  refine ⟨46027058495797871982432197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30684705663865247988288131 46027058495797871982432197)
                  ·
                    refine ⟨8630073467962100996706037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46027058495797871982432197 8630073467962100996706037)
                    ·
                      refine ⟨809069387621446968441191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8630073467962100996706037 809069387621446968441191)
                      ·
                        rfl

theorem cell23_1575657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 4, 5].length) (baseStart_1575657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575657 prefixEnd_1575657 := by exact prefixLift 1575657
  have htrace : WordTrace (prefixWord ++ tailWord_1575657) baseStart_1575657 baseEnd_1575657 := by
    simpa [prefixWord, tailWord_1575657, baseEnd_1575657] using wordTrace_append hprefix tailTrace_1575657
  have hstable : (prefixWord ++ tailWord_1575657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575657).length < 2 ^ (prefixWord ++ tailWord_1575657).sum := by decide
  have hdescent : baseEnd_1575657 < baseStart_1575657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575661 : List Nat := [1, 5, 1, 2, 1, 1, 3, 2, 1, 3, 3]
def baseStart_1575661 : Nat := 118140960795 + 1575661 * 2 ^ 59
def prefixEnd_1575661 : Nat := 4983230072969 + 3 ^ 40 * 1575661 * 2
def baseEnd_1575661 : Nat := 809071441544064952791173

theorem tailTrace_1575661 : CollatzResearch.WordTrace tailWord_1575661 prefixEnd_1575661 809071441544064952791173 := by
  unfold tailWord_1575661
  simp only [CollatzResearch.WordTrace]
  refine ⟨57469077944656773319646837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38312718629771182213097891 57469077944656773319646837)
  ·
    refine ⟨5387726057311572498716891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57469077944656773319646837 5387726057311572498716891)
    ·
      refine ⟨8081589085967358748075337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5387726057311572498716891 8081589085967358748075337)
      ·
        refine ⟨6061191814475519061056503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8081589085967358748075337 6061191814475519061056503)
        ·
          refine ⟨9091787721713278591584755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6061191814475519061056503 9091787721713278591584755)
          ·
            refine ⟨13637681582569917887377133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9091787721713278591584755 13637681582569917887377133)
            ·
              refine ⟨5114130593463719207766425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13637681582569917887377133 5114130593463719207766425)
              ·
                refine ⟨3835597945097789405824819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5114130593463719207766425 3835597945097789405824819)
                ·
                  refine ⟨5753396917646684108737229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3835597945097789405824819 5753396917646684108737229)
                  ·
                    refine ⟨2157523844117506540776461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5753396917646684108737229 2157523844117506540776461)
                    ·
                      refine ⟨809071441544064952791173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2157523844117506540776461 809071441544064952791173)
                      ·
                        rfl

theorem cell23_1575661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_1575661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575661 prefixEnd_1575661 := by exact prefixLift 1575661
  have htrace : WordTrace (prefixWord ++ tailWord_1575661) baseStart_1575661 baseEnd_1575661 := by
    simpa [prefixWord, tailWord_1575661, baseEnd_1575661] using wordTrace_append hprefix tailTrace_1575661
  have hstable : (prefixWord ++ tailWord_1575661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575661).length < 2 ^ (prefixWord ++ tailWord_1575661).sum := by decide
  have hdescent : baseEnd_1575661 < baseStart_1575661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575668 : List Nat := [2, 6, 1, 1, 3, 10]
def baseStart_1575668 : Nat := 118140960795 + 1575668 * 2 ^ 59
def prefixEnd_1575668 : Nat := 4983230072969 + 3 ^ 40 * 1575668 * 2
def baseEnd_1575668 : Nat := 3329526896743400927587

theorem tailTrace_1575668 : CollatzResearch.WordTrace tailWord_1575668 prefixEnd_1575668 3329526896743400927587 := by
  unfold tailWord_1575668
  simp only [CollatzResearch.WordTrace]
  refine ⟨28734666627815706757575829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38312888837087609010101105 28734666627815706757575829)
  ·
    refine ⟨1346937498178861254261367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28734666627815706757575829 1346937498178861254261367)
    ·
      refine ⟨2020406247268291881392051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1346937498178861254261367 2020406247268291881392051)
      ·
        refine ⟨3030609370902437822088077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2020406247268291881392051 3030609370902437822088077)
        ·
          refine ⟨1136478514088414183283029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3030609370902437822088077 1136478514088414183283029)
          ·
            refine ⟨3329526896743400927587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1136478514088414183283029 3329526896743400927587)
            ·
              rfl

theorem cell23_1575668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 10].length) (baseStart_1575668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575668 prefixEnd_1575668 := by exact prefixLift 1575668
  have htrace : WordTrace (prefixWord ++ tailWord_1575668) baseStart_1575668 baseEnd_1575668 := by
    simpa [prefixWord, tailWord_1575668, baseEnd_1575668] using wordTrace_append hprefix tailTrace_1575668
  have hstable : (prefixWord ++ tailWord_1575668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575668).length < 2 ^ (prefixWord ++ tailWord_1575668).sum := by decide
  have hdescent : baseEnd_1575668 < baseStart_1575668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575684 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 1, 5, 4]
def baseStart_1575684 : Nat := 118140960795 + 1575684 * 2 ^ 59
def prefixEnd_1575684 : Nat := 4983230072969 + 3 ^ 40 * 1575684 * 2
def baseEnd_1575684 : Nat := 809083251599118362803567

theorem tailTrace_1575684 : CollatzResearch.WordTrace tailWord_1575684 prefixEnd_1575684 809083251599118362803567 := by
  unfold tailWord_1575684
  simp only [CollatzResearch.WordTrace]
  refine ⟨28734958411786724123867053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38313277882382298831822737 28734958411786724123867053)
  ·
    refine ⟨10775609404420021546450145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28734958411786724123867053 10775609404420021546450145)
    ·
      refine ⟨8081707053315016159837609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10775609404420021546450145 8081707053315016159837609)
      ·
        refine ⟨6061280289986262119878207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8081707053315016159837609 6061280289986262119878207)
        ·
          refine ⟨9091920434979393179817311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6061280289986262119878207 9091920434979393179817311)
          ·
            refine ⟨13637880652469089769725967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9091920434979393179817311 13637880652469089769725967)
            ·
              refine ⟨20456820978703634654588951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13637880652469089769725967 20456820978703634654588951)
              ·
                refine ⟨30685231468055451981883427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20456820978703634654588951 30685231468055451981883427)
                ·
                  refine ⟨46027847202083177972825141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30685231468055451981883427 46027847202083177972825141)
                  ·
                    refine ⟨4315110675195297934952357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46027847202083177972825141 4315110675195297934952357)
                    ·
                      refine ⟨809083251599118362803567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4315110675195297934952357 809083251599118362803567)
                      ·
                        rfl

theorem cell23_1575684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_1575684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575684 prefixEnd_1575684 := by exact prefixLift 1575684
  have htrace : WordTrace (prefixWord ++ tailWord_1575684) baseStart_1575684 baseEnd_1575684 := by
    simpa [prefixWord, tailWord_1575684, baseEnd_1575684] using wordTrace_append hprefix tailTrace_1575684
  have hstable : (prefixWord ++ tailWord_1575684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575684).length < 2 ^ (prefixWord ++ tailWord_1575684).sum := by decide
  have hdescent : baseEnd_1575684 < baseStart_1575684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575704 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 4, 4, 3]
def baseStart_1575704 : Nat := 118140960795 + 1575704 * 2 ^ 59
def prefixEnd_1575704 : Nat := 4983230072969 + 3 ^ 40 * 1575704 * 2
def baseEnd_1575704 : Nat := 809093521212208284553475

theorem tailTrace_1575704 : CollatzResearch.WordTrace tailWord_1575704 prefixEnd_1575704 809093521212208284553475 := by
  unfold tailWord_1575704
  simp only [CollatzResearch.WordTrace]
  refine ⟨28735323141750495831731083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38313764189000661108974777 28735323141750495831731083)
  ·
    refine ⟨43102984712625743747596625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28735323141750495831731083 43102984712625743747596625)
    ·
      refine ⟨32327238534469307810697469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43102984712625743747596625 32327238534469307810697469)
      ·
        refine ⟨12122714450425990429011551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32327238534469307810697469 12122714450425990429011551)
        ·
          refine ⟨18184071675638985643517327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12122714450425990429011551 18184071675638985643517327)
          ·
            refine ⟨27276107513458478465275991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18184071675638985643517327 27276107513458478465275991)
            ·
              refine ⟨40914161270187717697913987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27276107513458478465275991 40914161270187717697913987)
              ·
                refine ⟨61371241905281576546870981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40914161270187717697913987 61371241905281576546870981)
                ·
                  refine ⟨11507107857240295602538309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61371241905281576546870981 11507107857240295602538309)
                  ·
                    refine ⟨2157582723232555425475933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11507107857240295602538309 2157582723232555425475933)
                    ·
                      refine ⟨809093521212208284553475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2157582723232555425475933 809093521212208284553475)
                      ·
                        rfl

theorem cell23_1575704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_1575704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575704 prefixEnd_1575704 := by exact prefixLift 1575704
  have htrace : WordTrace (prefixWord ++ tailWord_1575704) baseStart_1575704 baseEnd_1575704 := by
    simpa [prefixWord, tailWord_1575704, baseEnd_1575704] using wordTrace_append hprefix tailTrace_1575704
  have hstable : (prefixWord ++ tailWord_1575704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575704).length < 2 ^ (prefixWord ++ tailWord_1575704).sum := by decide
  have hdescent : baseEnd_1575704 < baseStart_1575704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575722 : List Nat := [3, 1, 4, 3, 1, 1, 1, 3, 1, 3, 2]
def baseStart_1575722 : Nat := 118140960795 + 1575722 * 2 ^ 59
def prefixEnd_1575722 : Nat := 4983230072969 + 3 ^ 40 * 1575722 * 2
def baseEnd_1575722 : Nat := 809102763863989214128393

theorem tailTrace_1575722 : CollatzResearch.WordTrace tailWord_1575722 prefixEnd_1575722 809102763863989214128393 := by
  unfold tailWord_1575722
  simp only [CollatzResearch.WordTrace]
  refine ⟨14367825699358945184404355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38314201864957187158411613 14367825699358945184404355)
  ·
    refine ⟨21551738549038417776606533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14367825699358945184404355 21551738549038417776606533)
    ·
      refine ⟨4040950977944703333113725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21551738549038417776606533 4040950977944703333113725)
      ·
        refine ⟨1515356616729263749917647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4040950977944703333113725 1515356616729263749917647)
        ·
          refine ⟨2273034925093895624876471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1515356616729263749917647 2273034925093895624876471)
          ·
            refine ⟨3409552387640843437314707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2273034925093895624876471 3409552387640843437314707)
            ·
              refine ⟨5114328581461265155972061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3409552387640843437314707 5114328581461265155972061)
              ·
                refine ⟨1917873218047974433489523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5114328581461265155972061 1917873218047974433489523)
                ·
                  refine ⟨2876809827071961650234285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1917873218047974433489523 2876809827071961650234285)
                  ·
                    refine ⟨1078803685151985618837857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2876809827071961650234285 1078803685151985618837857)
                    ·
                      refine ⟨809102763863989214128393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1078803685151985618837857 809102763863989214128393)
                      ·
                        rfl

theorem cell23_1575722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_1575722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575722 prefixEnd_1575722 := by exact prefixLift 1575722
  have htrace : WordTrace (prefixWord ++ tailWord_1575722) baseStart_1575722 baseEnd_1575722 := by
    simpa [prefixWord, tailWord_1575722, baseEnd_1575722] using wordTrace_append hprefix tailTrace_1575722
  have hstable : (prefixWord ++ tailWord_1575722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575722).length < 2 ^ (prefixWord ++ tailWord_1575722).sum := by decide
  have hdescent : baseEnd_1575722 < baseStart_1575722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575754 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 6, 5]
def baseStart_1575754 : Nat := 118140960795 + 1575754 * 2 ^ 59
def prefixEnd_1575754 : Nat := 4983230072969 + 3 ^ 40 * 1575754 * 2
def baseEnd_1575754 : Nat := 269706398414977696309415

theorem tailTrace_1575754 : CollatzResearch.WordTrace tailWord_1575754 prefixEnd_1575754 269706398414977696309415 := by
  unfold tailWord_1575754
  simp only [CollatzResearch.WordTrace]
  refine ⟨14368117483329962550695579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38314979955546566801854877 14368117483329962550695579)
  ·
    refine ⟨21552176224994943826043369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14368117483329962550695579 21552176224994943826043369)
    ·
      refine ⟨16164132168746207869532527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21552176224994943826043369 16164132168746207869532527)
      ·
        refine ⟨24246198253119311804298791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16164132168746207869532527 24246198253119311804298791)
        ·
          refine ⟨36369297379678967706448187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24246198253119311804298791 36369297379678967706448187)
          ·
            refine ⟨54553946069518451559672281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36369297379678967706448187 54553946069518451559672281)
            ·
              refine ⟨40915459552138838669754211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54553946069518451559672281 40915459552138838669754211)
              ·
                refine ⟨61373189328208258004631317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40915459552138838669754211 61373189328208258004631317)
                ·
                  refine ⟨2876868249759762093967093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 61373189328208258004631317 2876868249759762093967093)
                  ·
                    refine ⟨269706398414977696309415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2876868249759762093967093 269706398414977696309415)
                    ·
                      rfl

theorem cell23_1575754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_1575754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575754 prefixEnd_1575754 := by exact prefixLift 1575754
  have htrace : WordTrace (prefixWord ++ tailWord_1575754) baseStart_1575754 baseEnd_1575754 := by
    simpa [prefixWord, tailWord_1575754, baseEnd_1575754] using wordTrace_append hprefix tailTrace_1575754
  have hstable : (prefixWord ++ tailWord_1575754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575754).length < 2 ^ (prefixWord ++ tailWord_1575754).sum := by decide
  have hdescent : baseEnd_1575754 < baseStart_1575754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575791 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 4, 4, 2]
def baseStart_1575791 : Nat := 118140960795 + 1575791 * 2 ^ 59
def prefixEnd_1575791 : Nat := 4983230072969 + 3 ^ 40 * 1575791 * 2
def baseEnd_1575791 : Nat := 809138194029149444165575

theorem tailTrace_1575791 : CollatzResearch.WordTrace tailWord_1575791 prefixEnd_1575791 809138194029149444165575 := by
  unfold tailWord_1575791
  simp only [CollatzResearch.WordTrace]
  refine ⟨57473819434185805521879227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38315879622790537014586151 57473819434185805521879227)
  ·
    refine ⟨86210729151278708282818841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57473819434185805521879227 86210729151278708282818841)
    ·
      refine ⟨64658046863459031212114131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86210729151278708282818841 64658046863459031212114131)
      ·
        refine ⟨96987070295188546818171197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64658046863459031212114131 96987070295188546818171197)
        ·
          refine ⟨36370151360695705056814199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96987070295188546818171197 36370151360695705056814199)
          ·
            refine ⟨54555227041043557585221299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36370151360695705056814199 54555227041043557585221299)
            ·
              refine ⟨81832840561565336377831949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54555227041043557585221299 81832840561565336377831949)
              ·
                refine ⟨30687315210587001141686981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81832840561565336377831949 30687315210587001141686981)
                ·
                  refine ⟨5753871601985062714066309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30687315210587001141686981 5753871601985062714066309)
                  ·
                    refine ⟨1078850925372199258887433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5753871601985062714066309 1078850925372199258887433)
                    ·
                      refine ⟨809138194029149444165575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1078850925372199258887433 809138194029149444165575)
                      ·
                        rfl

theorem cell23_1575791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 4, 2].length) (baseStart_1575791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575791 prefixEnd_1575791 := by exact prefixLift 1575791
  have htrace : WordTrace (prefixWord ++ tailWord_1575791) baseStart_1575791 baseEnd_1575791 := by
    simpa [prefixWord, tailWord_1575791, baseEnd_1575791] using wordTrace_append hprefix tailTrace_1575791
  have hstable : (prefixWord ++ tailWord_1575791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575791).length < 2 ^ (prefixWord ++ tailWord_1575791).sum := by decide
  have hdescent : baseEnd_1575791 < baseStart_1575791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575798 : List Nat := [5, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5]
def baseStart_1575798 : Nat := 118140960795 + 1575798 * 2 ^ 59
def prefixEnd_1575798 : Nat := 4983230072969 + 3 ^ 40 * 1575798 * 2
def baseEnd_1575798 : Nat := 809141788393730916778043

theorem tailTrace_1575798 : CollatzResearch.WordTrace tailWord_1575798 prefixEnd_1575798 809141788393730916778043 := by
  unfold tailWord_1575798
  simp only [CollatzResearch.WordTrace]
  refine ⟨3592129671572527857336503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38316049830106963811589365 3592129671572527857336503)
  ·
    refine ⟨5388194507358791786004755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3592129671572527857336503 5388194507358791786004755)
    ·
      refine ⟨8082291761038187679007133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5388194507358791786004755 8082291761038187679007133)
      ·
        refine ⟨3030859410389320379627675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8082291761038187679007133 3030859410389320379627675)
        ·
          refine ⟨4546289115583980569441513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3030859410389320379627675 4546289115583980569441513)
          ·
            refine ⟨3409716836687985427081135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4546289115583980569441513 3409716836687985427081135)
            ·
              refine ⟨5114575255031978140621703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3409716836687985427081135 5114575255031978140621703)
              ·
                refine ⟨7671862882547967210932555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5114575255031978140621703 7671862882547967210932555)
                ·
                  refine ⟨11507794323821950816398833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7671862882547967210932555 11507794323821950816398833)
                  ·
                    refine ⟨8630845742866463112299125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11507794323821950816398833 8630845742866463112299125)
                    ·
                      refine ⟨809141788393730916778043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8630845742866463112299125 809141788393730916778043)
                      ·
                        rfl

theorem cell23_1575798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_1575798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575798 prefixEnd_1575798 := by exact prefixLift 1575798
  have htrace : WordTrace (prefixWord ++ tailWord_1575798) baseStart_1575798 baseEnd_1575798 := by
    simpa [prefixWord, tailWord_1575798, baseEnd_1575798] using wordTrace_append hprefix tailTrace_1575798
  have hstable : (prefixWord ++ tailWord_1575798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575798).length < 2 ^ (prefixWord ++ tailWord_1575798).sum := by decide
  have hdescent : baseEnd_1575798 < baseStart_1575798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575804 : List Nat := [2, 2, 2, 1, 1, 1, 1, 4, 2, 1, 6]
def baseStart_1575804 : Nat := 118140960795 + 1575804 * 2 ^ 59
def prefixEnd_1575804 : Nat := 4983230072969 + 3 ^ 40 * 1575804 * 2
def baseEnd_1575804 : Nat := 809144869277657893303015

theorem tailTrace_1575804 : CollatzResearch.WordTrace tailWord_1575804 prefixEnd_1575804 809144869277657893303015 := by
  unfold tailWord_1575804
  simp only [CollatzResearch.WordTrace]
  refine ⟨28737146791569354371051233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38316195722092472494734977 28737146791569354371051233)
  ·
    refine ⟨21552860093677015778288425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28737146791569354371051233 21552860093677015778288425)
    ·
      refine ⟨16164645070257761833716319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21552860093677015778288425 16164645070257761833716319)
      ·
        refine ⟨24246967605386642750574479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16164645070257761833716319 24246967605386642750574479)
        ·
          refine ⟨36370451408079964125861719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24246967605386642750574479 36370451408079964125861719)
          ·
            refine ⟨54555677112119946188792579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36370451408079964125861719 54555677112119946188792579)
            ·
              refine ⟨81833515668179919283188869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54555677112119946188792579 81833515668179919283188869)
              ·
                refine ⟨15343784187783734865597913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81833515668179919283188869 15343784187783734865597913)
                ·
                  refine ⟨11507838140837801149198435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15343784187783734865597913 11507838140837801149198435)
                  ·
                    refine ⟨17261757211256701723797653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11507838140837801149198435 17261757211256701723797653)
                    ·
                      refine ⟨809144869277657893303015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17261757211256701723797653 809144869277657893303015)
                      ·
                        rfl

theorem cell23_1575804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_1575804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575804 prefixEnd_1575804 := by exact prefixLift 1575804
  have htrace : WordTrace (prefixWord ++ tailWord_1575804) baseStart_1575804 baseEnd_1575804 := by
    simpa [prefixWord, tailWord_1575804, baseEnd_1575804] using wordTrace_append hprefix tailTrace_1575804
  have hstable : (prefixWord ++ tailWord_1575804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575804).length < 2 ^ (prefixWord ++ tailWord_1575804).sum := by decide
  have hdescent : baseEnd_1575804 < baseStart_1575804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575811 : List Nat := [1, 1, 1, 3, 4, 1, 1, 2, 4, 2, 3]
def baseStart_1575811 : Nat := 118140960795 + 1575811 * 2 ^ 59
def prefixEnd_1575811 : Nat := 4983230072969 + 3 ^ 40 * 1575811 * 2
def baseEnd_1575811 : Nat := 809148463642239365915483

theorem tailTrace_1575811 : CollatzResearch.WordTrace tailWord_1575811 prefixEnd_1575811 809148463642239365915483 := by
  unfold tailWord_1575811
  simp only [CollatzResearch.WordTrace]
  refine ⟨57474548894113348937607287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38316365929408899291738191 57474548894113348937607287)
  ·
    refine ⟨86211823341170023406410931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57474548894113348937607287 86211823341170023406410931)
    ·
      refine ⟨129317735011755035109616397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86211823341170023406410931 129317735011755035109616397)
      ·
        refine ⟨48494150629408138166106149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129317735011755035109616397 48494150629408138166106149)
        ·
          refine ⟨9092653243014025906144903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48494150629408138166106149 9092653243014025906144903)
          ·
            refine ⟨13638979864521038859217355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9092653243014025906144903 13638979864521038859217355)
            ·
              refine ⟨20458469796781558288826033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13638979864521038859217355 20458469796781558288826033)
              ·
                refine ⟨15343852347586168716619525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20458469796781558288826033 15343852347586168716619525)
                ·
                  refine ⟨2876972315172406634366161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15343852347586168716619525 2876972315172406634366161)
                  ·
                    refine ⟨2157729236379304975774621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2876972315172406634366161 2157729236379304975774621)
                    ·
                      refine ⟨809148463642239365915483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2157729236379304975774621 809148463642239365915483)
                      ·
                        rfl

theorem cell23_1575811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 2, 3].length) (baseStart_1575811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575811 prefixEnd_1575811 := by exact prefixLift 1575811
  have htrace : WordTrace (prefixWord ++ tailWord_1575811) baseStart_1575811 baseEnd_1575811 := by
    simpa [prefixWord, tailWord_1575811, baseEnd_1575811] using wordTrace_append hprefix tailTrace_1575811
  have hstable : (prefixWord ++ tailWord_1575811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575811).length < 2 ^ (prefixWord ++ tailWord_1575811).sum := by decide
  have hdescent : baseEnd_1575811 < baseStart_1575811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575861 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 5, 5]
def baseStart_1575861 : Nat := 118140960795 + 1575861 * 2 ^ 59
def prefixEnd_1575861 : Nat := 4983230072969 + 3 ^ 40 * 1575861 * 2
def baseEnd_1575861 : Nat := 269724712558321390096751

theorem tailTrace_1575861 : CollatzResearch.WordTrace tailWord_1575861 prefixEnd_1575861 269724712558321390096751 := by
  unfold tailWord_1575861
  simp only [CollatzResearch.WordTrace]
  refine ⟨57476372543932207476927437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38317581695954804984618291 57476372543932207476927437)
  ·
    refine ⟨21553639703974577803847789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57476372543932207476927437 21553639703974577803847789)
    ·
      refine ⟨8082614888990466676442921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21553639703974577803847789 8082614888990466676442921)
      ·
        refine ⟨6061961166742850007332191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8082614888990466676442921 6061961166742850007332191)
        ·
          refine ⟨9092941750114275010998287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6061961166742850007332191 9092941750114275010998287)
          ·
            refine ⟨13639412625171412516497431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9092941750114275010998287 13639412625171412516497431)
            ·
              refine ⟨20459118937757118774746147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13639412625171412516497431 20459118937757118774746147)
              ·
                refine ⟨30688678406635678162119221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20459118937757118774746147 30688678406635678162119221)
                ·
                  refine ⟨2877063600622094827698677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30688678406635678162119221 2877063600622094827698677)
                  ·
                    refine ⟨269724712558321390096751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2877063600622094827698677 269724712558321390096751)
                    ·
                      rfl

theorem cell23_1575861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_1575861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575861 prefixEnd_1575861 := by exact prefixLift 1575861
  have htrace : WordTrace (prefixWord ++ tailWord_1575861) baseStart_1575861 baseEnd_1575861 := by
    simpa [prefixWord, tailWord_1575861, baseEnd_1575861] using wordTrace_append hprefix tailTrace_1575861
  have hstable : (prefixWord ++ tailWord_1575861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575861).length < 2 ^ (prefixWord ++ tailWord_1575861).sum := by decide
  have hdescent : baseEnd_1575861 < baseStart_1575861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575892 : List Nat := [2, 4, 1, 2, 1, 2, 1, 5, 1, 1, 3]
def baseStart_1575892 : Nat := 118140960795 + 1575892 * 2 ^ 59
def prefixEnd_1575892 : Nat := 4983230072969 + 3 ^ 40 * 1575892 * 2
def baseEnd_1575892 : Nat := 809190055575253549002611

theorem tailTrace_1575892 : CollatzResearch.WordTrace tailWord_1575892 prefixEnd_1575892 809190055575253549002611 := by
  unfold tailWord_1575892
  simp only [CollatzResearch.WordTrace]
  refine ⟨28738751603409949885652965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38318335471213266514203953 28738751603409949885652965)
  ·
    refine ⟨5388515925639365603559931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28738751603409949885652965 5388515925639365603559931)
    ·
      refine ⟨8082773888459048405339897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5388515925639365603559931 8082773888459048405339897)
      ·
        refine ⟨6062080416344286304004923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8082773888459048405339897 6062080416344286304004923)
        ·
          refine ⟨9093120624516429456007385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6062080416344286304004923 9093120624516429456007385)
          ·
            refine ⟨6819840468387322092005539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9093120624516429456007385 6819840468387322092005539)
            ·
              refine ⟨10229760702580983138008309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6819840468387322092005539 10229760702580983138008309)
              ·
                refine ⟨959040065866967169188279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10229760702580983138008309 959040065866967169188279)
                ·
                  refine ⟨1438560098800450753782419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 959040065866967169188279 1438560098800450753782419)
                  ·
                    refine ⟨2157840148200676130673629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1438560098800450753782419 2157840148200676130673629)
                    ·
                      refine ⟨809190055575253549002611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2157840148200676130673629 809190055575253549002611)
                      ·
                        rfl

theorem cell23_1575892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_1575892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575892 prefixEnd_1575892 := by exact prefixLift 1575892
  have htrace : WordTrace (prefixWord ++ tailWord_1575892) baseStart_1575892 baseEnd_1575892 := by
    simpa [prefixWord, tailWord_1575892, baseEnd_1575892] using wordTrace_append hprefix tailTrace_1575892
  have hstable : (prefixWord ++ tailWord_1575892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575892).length < 2 ^ (prefixWord ++ tailWord_1575892).sum := by decide
  have hdescent : baseEnd_1575892 < baseStart_1575892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575908 : List Nat := [2, 3, 1, 1, 1, 1, 2, 6, 2, 4]
def baseStart_1575908 : Nat := 118140960795 + 1575908 * 2 ^ 59
def prefixEnd_1575908 : Nat := 4983230072969 + 3 ^ 40 * 1575908 * 2
def baseEnd_1575908 : Nat := 269732757088575162134179

theorem tailTrace_1575908 : CollatzResearch.WordTrace tailWord_1575908 prefixEnd_1575908 269732757088575162134179 := by
  unfold tailWord_1575908
  simp only [CollatzResearch.WordTrace]
  refine ⟨28739043387380967251944189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38318724516507956335925585 28739043387380967251944189)
  ·
    refine ⟨10777141270267862719479071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28739043387380967251944189 10777141270267862719479071)
    ·
      refine ⟨16165711905401794079218607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10777141270267862719479071 16165711905401794079218607)
      ·
        refine ⟨24248567858102691118827911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16165711905401794079218607 24248567858102691118827911)
        ·
          refine ⟨36372851787154036678241867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24248567858102691118827911 36372851787154036678241867)
          ·
            refine ⟨54559277680731055017362801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36372851787154036678241867 54559277680731055017362801)
            ·
              refine ⟨40919458260548291263022101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54559277680731055017362801 40919458260548291263022101)
              ·
                refine ⟨1918099605963201152954161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40919458260548291263022101 1918099605963201152954161)
                ·
                  refine ⟨1438574704472400864715621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1918099605963201152954161 1438574704472400864715621)
                  ·
                    refine ⟨269732757088575162134179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1438574704472400864715621 269732757088575162134179)
                    ·
                      rfl

theorem cell23_1575908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 2, 4].length) (baseStart_1575908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575908 prefixEnd_1575908 := by exact prefixLift 1575908
  have htrace : WordTrace (prefixWord ++ tailWord_1575908) baseStart_1575908 baseEnd_1575908 := by
    simpa [prefixWord, tailWord_1575908, baseEnd_1575908] using wordTrace_append hprefix tailTrace_1575908
  have hstable : (prefixWord ++ tailWord_1575908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575908).length < 2 ^ (prefixWord ++ tailWord_1575908).sum := by decide
  have hdescent : baseEnd_1575908 < baseStart_1575908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575982 : List Nat := [4, 1, 3, 1, 1, 1, 3, 3, 2, 1, 3]
def baseStart_1575982 : Nat := 118140960795 + 1575982 * 2 ^ 59
def prefixEnd_1575982 : Nat := 4983230072969 + 3 ^ 40 * 1575982 * 2
def baseEnd_1575982 : Nat := 809236268834158196877197

theorem tailTrace_1575982 : CollatzResearch.WordTrace tailWord_1575982 prefixEnd_1575982 809236268834158196877197 := by
  unfold tailWord_1575982
  simp only [CollatzResearch.WordTrace]
  refine ⟨7185098222061730642760275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38320523850995896761388133 7185098222061730642760275)
  ·
    refine ⟨10777647333092595964140413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7185098222061730642760275 10777647333092595964140413)
    ·
      refine ⟨4041617749909723486552655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10777647333092595964140413 4041617749909723486552655)
      ·
        refine ⟨6062426624864585229828983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4041617749909723486552655 6062426624864585229828983)
        ·
          refine ⟨9093639937296877844743475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6062426624864585229828983 9093639937296877844743475)
          ·
            refine ⟨13640459905945316767115213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9093639937296877844743475 13640459905945316767115213)
            ·
              refine ⟨5115172464729493787668205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13640459905945316767115213 5115172464729493787668205)
              ·
                refine ⟨1918189674273560170375577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5115172464729493787668205 1918189674273560170375577)
                ·
                  refine ⟨1438642255705170127781683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1918189674273560170375577 1438642255705170127781683)
                  ·
                    refine ⟨2157963383557755191672525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1438642255705170127781683 2157963383557755191672525)
                    ·
                      refine ⟨809236268834158196877197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2157963383557755191672525 809236268834158196877197)
                      ·
                        rfl

theorem cell23_1575982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_1575982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575982 prefixEnd_1575982 := by exact prefixLift 1575982
  have htrace : WordTrace (prefixWord ++ tailWord_1575982) baseStart_1575982 baseEnd_1575982 := by
    simpa [prefixWord, tailWord_1575982, baseEnd_1575982] using wordTrace_append hprefix tailTrace_1575982
  have hstable : (prefixWord ++ tailWord_1575982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575982).length < 2 ^ (prefixWord ++ tailWord_1575982).sum := by decide
  have hdescent : baseEnd_1575982 < baseStart_1575982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575992 : List Nat := [2, 1, 2, 1, 5, 1, 3, 2, 1, 3, 2]
def baseStart_1575992 : Nat := 118140960795 + 1575992 * 2 ^ 59
def prefixEnd_1575992 : Nat := 4983230072969 + 3 ^ 40 * 1575992 * 2
def baseEnd_1575992 : Nat := 809241403640703157752151

theorem tailTrace_1575992 : CollatzResearch.WordTrace tailWord_1575992 prefixEnd_1575992 809241403640703157752151 := by
  unfold tailWord_1575992
  simp only [CollatzResearch.WordTrace]
  refine ⟨28740575253228808424973115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38320767004305077899964153 28740575253228808424973115)
  ·
    refine ⟨43110862879843212637459673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28740575253228808424973115 43110862879843212637459673)
    ·
      refine ⟨32333147159882409478094755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43110862879843212637459673 32333147159882409478094755)
      ·
        refine ⟨48499720739823614217142133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32333147159882409478094755 48499720739823614217142133)
        ·
          refine ⟨4546848819358463832857075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48499720739823614217142133 4546848819358463832857075)
          ·
            refine ⟨6820273229037695749285613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4546848819358463832857075 6820273229037695749285613)
            ·
              refine ⟨2557602460889135905982105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6820273229037695749285613 2557602460889135905982105)
              ·
                refine ⟨1918201845666851929486579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2557602460889135905982105 1918201845666851929486579)
                ·
                  refine ⟨2877302768500277894229869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1918201845666851929486579 2877302768500277894229869)
                  ·
                    refine ⟨1078988538187604210336201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2877302768500277894229869 1078988538187604210336201)
                    ·
                      refine ⟨809241403640703157752151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1078988538187604210336201 809241403640703157752151)
                      ·
                        rfl

theorem cell23_1575992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 1, 3, 2].length) (baseStart_1575992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1575992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1575992 prefixEnd_1575992 := by exact prefixLift 1575992
  have htrace : WordTrace (prefixWord ++ tailWord_1575992) baseStart_1575992 baseEnd_1575992 := by
    simpa [prefixWord, tailWord_1575992, baseEnd_1575992] using wordTrace_append hprefix tailTrace_1575992
  have hstable : (prefixWord ++ tailWord_1575992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575992).length < 2 ^ (prefixWord ++ tailWord_1575992).sum := by decide
  have hdescent : baseEnd_1575992 < baseStart_1575992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576005 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 6, 2, 2]
def baseStart_1576005 : Nat := 118140960795 + 1576005 * 2 ^ 59
def prefixEnd_1576005 : Nat := 4983230072969 + 3 ^ 40 * 1576005 * 2
def baseEnd_1576005 : Nat := 809248078889211606889591

theorem tailTrace_1576005 : CollatzResearch.WordTrace tailWord_1576005 prefixEnd_1576005 809248078889211606889591 := by
  unfold tailWord_1576005
  simp only [CollatzResearch.WordTrace]
  refine ⟨57481624655410520070169469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38321083103607013380112979 57481624655410520070169469)
  ·
    refine ⟨21555609245778945026313551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57481624655410520070169469 21555609245778945026313551)
    ·
      refine ⟨32333413868668417539470327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21555609245778945026313551 32333413868668417539470327)
      ·
        refine ⟨48500120803002626309205491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32333413868668417539470327 48500120803002626309205491)
        ·
          refine ⟨72750181204503939463808237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48500120803002626309205491 72750181204503939463808237)
          ·
            refine ⟨27281317951688977298928089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72750181204503939463808237 27281317951688977298928089)
            ·
              refine ⟨20460988463766732974196067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27281317951688977298928089 20460988463766732974196067)
              ·
                refine ⟨30691482695650099461294101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20460988463766732974196067 30691482695650099461294101)
                ·
                  refine ⟨1438663251358598412248161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 30691482695650099461294101 1438663251358598412248161)
                  ·
                    refine ⟨1078997438518948809186121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1438663251358598412248161 1078997438518948809186121)
                    ·
                      refine ⟨809248078889211606889591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1078997438518948809186121 809248078889211606889591)
                      ·
                        rfl

theorem cell23_1576005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 6, 2, 2].length) (baseStart_1576005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576005 prefixEnd_1576005 := by exact prefixLift 1576005
  have htrace : WordTrace (prefixWord ++ tailWord_1576005) baseStart_1576005 baseEnd_1576005 := by
    simpa [prefixWord, tailWord_1576005, baseEnd_1576005] using wordTrace_append hprefix tailTrace_1576005
  have hstable : (prefixWord ++ tailWord_1576005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576005).length < 2 ^ (prefixWord ++ tailWord_1576005).sum := by decide
  have hdescent : baseEnd_1576005 < baseStart_1576005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576028 : List Nat := [2, 2, 4, 1, 1, 1, 2, 3, 7]
def baseStart_1576028 : Nat := 118140960795 + 1576028 * 2 ^ 59
def prefixEnd_1576028 : Nat := 4983230072969 + 3 ^ 40 * 1576028 * 2
def baseEnd_1576028 : Nat := 89917765438251668544665

theorem tailTrace_1576028 : CollatzResearch.WordTrace tailWord_1576028 prefixEnd_1576028 89917765438251668544665 := by
  unfold tailWord_1576028
  simp only [CollatzResearch.WordTrace]
  refine ⟨28741231767163597499128369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38321642356218129998837825 28741231767163597499128369)
  ·
    refine ⟨21555923825372698124346277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28741231767163597499128369 21555923825372698124346277)
    ·
      refine ⟨4041735717257380898314927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21555923825372698124346277 4041735717257380898314927)
      ·
        refine ⟨6062603575886071347472391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4041735717257380898314927 6062603575886071347472391)
        ·
          refine ⟨9093905363829107021208587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6062603575886071347472391 9093905363829107021208587)
          ·
            refine ⟨13640858045743660531812881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9093905363829107021208587 13640858045743660531812881)
            ·
              refine ⟨10230643534307745398859661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13640858045743660531812881 10230643534307745398859661)
              ·
                refine ⟨3836491325365404524572373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10230643534307745398859661 3836491325365404524572373)
                ·
                  refine ⟨89917765438251668544665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3836491325365404524572373 89917765438251668544665)
                  ·
                    rfl

theorem cell23_1576028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 7].length) (baseStart_1576028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576028 prefixEnd_1576028 := by exact prefixLift 1576028
  have htrace : WordTrace (prefixWord ++ tailWord_1576028) baseStart_1576028 baseEnd_1576028 := by
    simpa [prefixWord, tailWord_1576028, baseEnd_1576028] using wordTrace_append hprefix tailTrace_1576028
  have hstable : (prefixWord ++ tailWord_1576028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576028).length < 2 ^ (prefixWord ++ tailWord_1576028).sum := by decide
  have hdescent : baseEnd_1576028 < baseStart_1576028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576051 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 5]
def baseStart_1576051 : Nat := 118140960795 + 1576051 * 2 ^ 59
def prefixEnd_1576051 : Nat := 4983230072969 + 3 ^ 40 * 1576051 * 2
def baseEnd_1576051 : Nat := 809271698999318426914379

theorem tailTrace_1576051 : CollatzResearch.WordTrace tailWord_1576051 prefixEnd_1576051 809271698999318426914379 := by
  unfold tailWord_1576051
  simp only [CollatzResearch.WordTrace]
  refine ⟨57483302413243869926344007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38322201608829246617562671 57483302413243869926344007)
  ·
    refine ⟨86224953619865804889516011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57483302413243869926344007 86224953619865804889516011)
    ·
      refine ⟨129337430429798707334274017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86224953619865804889516011 129337430429798707334274017)
      ·
        refine ⟨97003072822349030500705513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129337430429798707334274017 97003072822349030500705513)
        ·
          refine ⟨72752304616761772875529135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97003072822349030500705513 72752304616761772875529135)
          ·
            refine ⟨109128456925142659313293703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72752304616761772875529135 109128456925142659313293703)
            ·
              refine ⟨163692685387713988969940555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109128456925142659313293703 163692685387713988969940555)
              ·
                refine ⟨245539028081570983454910833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163692685387713988969940555 245539028081570983454910833)
                ·
                  refine ⟨184154271061178237591183125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 245539028081570983454910833 184154271061178237591183125)
                  ·
                    refine ⟨8632231455992729887086709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 184154271061178237591183125 8632231455992729887086709)
                    ·
                      refine ⟨809271698999318426914379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8632231455992729887086709 809271698999318426914379)
                      ·
                        rfl

theorem cell23_1576051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 5].length) (baseStart_1576051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576051 prefixEnd_1576051 := by exact prefixLift 1576051
  have htrace : WordTrace (prefixWord ++ tailWord_1576051) baseStart_1576051 baseEnd_1576051 := by
    simpa [prefixWord, tailWord_1576051, baseEnd_1576051] using wordTrace_append hprefix tailTrace_1576051
  have hstable : (prefixWord ++ tailWord_1576051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576051).length < 2 ^ (prefixWord ++ tailWord_1576051).sum := by decide
  have hdescent : baseEnd_1576051 < baseStart_1576051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576172 : List Nat := [2, 2, 1, 1, 2, 4, 1, 3, 2, 3, 2]
def baseStart_1576172 : Nat := 118140960795 + 1576172 * 2 ^ 59
def prefixEnd_1576172 : Nat := 4983230072969 + 3 ^ 40 * 1576172 * 2
def baseEnd_1576172 : Nat := 809333830158512453501323

theorem tailTrace_1576172 : CollatzResearch.WordTrace tailWord_1576172 prefixEnd_1576172 809333830158512453501323 := by
  unfold tailWord_1576172
  simp only [CollatzResearch.WordTrace]
  refine ⟨28743857822902753795749385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38325143763870338394332513 28743857822902753795749385)
  ·
    refine ⟨21557893367177065346812039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28743857822902753795749385 21557893367177065346812039)
    ·
      refine ⟨32336840050765598020218059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21557893367177065346812039 32336840050765598020218059)
      ·
        refine ⟨48505260076148397030327089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32336840050765598020218059 48505260076148397030327089)
        ·
          refine ⟨36378945057111297772745317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48505260076148397030327089 36378945057111297772745317)
          ·
            refine ⟨6821052198208368332389747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36378945057111297772745317 6821052198208368332389747)
            ·
              refine ⟨10231578297312552498584621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6821052198208368332389747 10231578297312552498584621)
              ·
                refine ⟨3836841861492207186969233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10231578297312552498584621 3836841861492207186969233)
                ·
                  refine ⟨2877631396119155390226925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3836841861492207186969233 2877631396119155390226925)
                  ·
                    refine ⟨1079111773544683271335097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2877631396119155390226925 1079111773544683271335097)
                    ·
                      refine ⟨809333830158512453501323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1079111773544683271335097 809333830158512453501323)
                      ·
                        rfl

theorem cell23_1576172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 3, 2].length) (baseStart_1576172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576172 prefixEnd_1576172 := by exact prefixLift 1576172
  have htrace : WordTrace (prefixWord ++ tailWord_1576172) baseStart_1576172 baseEnd_1576172 := by
    simpa [prefixWord, tailWord_1576172, baseEnd_1576172] using wordTrace_append hprefix tailTrace_1576172
  have hstable : (prefixWord ++ tailWord_1576172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576172).length < 2 ^ (prefixWord ++ tailWord_1576172).sum := by decide
  have hdescent : baseEnd_1576172 < baseStart_1576172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576196 : List Nat := [2, 3, 2, 2, 2, 2, 1, 4, 1, 1, 3]
def baseStart_1576196 : Nat := 118140960795 + 1576196 * 2 ^ 59
def prefixEnd_1576196 : Nat := 4983230072969 + 3 ^ 40 * 1576196 * 2
def baseEnd_1576196 : Nat := 809346153694220359601213

theorem tailTrace_1576196 : CollatzResearch.WordTrace tailWord_1576196 prefixEnd_1576196 809346153694220359601213 := by
  unfold tailWord_1576196
  simp only [CollatzResearch.WordTrace]
  refine ⟨28744295498859279845186221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38325727331812373126914961 28744295498859279845186221)
  ·
    refine ⟨10779110812072229941944833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28744295498859279845186221 10779110812072229941944833)
    ·
      refine ⟨8084333109054172456458625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10779110812072229941944833 8084333109054172456458625)
      ·
        refine ⟨6063249831790629342343969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8084333109054172456458625 6063249831790629342343969)
        ·
          refine ⟨4547437373842972006757977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6063249831790629342343969 4547437373842972006757977)
          ·
            refine ⟨3410578030382229005068483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4547437373842972006757977 3410578030382229005068483)
            ·
              refine ⟨5115867045573343507602725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3410578030382229005068483 5115867045573343507602725)
              ·
                refine ⟨959225071045001907675511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5115867045573343507602725 959225071045001907675511)
                ·
                  refine ⟨1438837606567502861513267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 959225071045001907675511 1438837606567502861513267)
                  ·
                    refine ⟨2158256409851254292269901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1438837606567502861513267 2158256409851254292269901)
                    ·
                      refine ⟨809346153694220359601213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2158256409851254292269901 809346153694220359601213)
                      ·
                        rfl

theorem cell23_1576196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_1576196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576196 prefixEnd_1576196 := by exact prefixLift 1576196
  have htrace : WordTrace (prefixWord ++ tailWord_1576196) baseStart_1576196 baseEnd_1576196 := by
    simpa [prefixWord, tailWord_1576196, baseEnd_1576196] using wordTrace_append hprefix tailTrace_1576196
  have hstable : (prefixWord ++ tailWord_1576196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576196).length < 2 ^ (prefixWord ++ tailWord_1576196).sum := by decide
  have hdescent : baseEnd_1576196 < baseStart_1576196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576232 : List Nat := [2, 1, 5, 1, 2, 1, 2, 2, 1, 2, 4]
def baseStart_1576232 : Nat := 118140960795 + 1576232 * 2 ^ 59
def prefixEnd_1576232 : Nat := 4983230072969 + 3 ^ 40 * 1576232 * 2
def baseEnd_1576232 : Nat := 809364638997782218751047

theorem tailTrace_1576232 : CollatzResearch.WordTrace tailWord_1576232 prefixEnd_1576232 809364638997782218751047 := by
  unfold tailWord_1576232
  simp only [CollatzResearch.WordTrace]
  refine ⟨28744952012794068919341475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38326602683725425225788633 28744952012794068919341475)
  ·
    refine ⟨43117428019191103379012213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28744952012794068919341475 43117428019191103379012213)
    ·
      refine ⟨4042258876799165941782395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43117428019191103379012213 4042258876799165941782395)
      ·
        refine ⟨6063388315198748912673593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4042258876799165941782395 6063388315198748912673593)
        ·
          refine ⟨4547541236399061684505195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6063388315198748912673593 4547541236399061684505195)
          ·
            refine ⟨6821311854598592526757793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4547541236399061684505195 6821311854598592526757793)
            ·
              refine ⟨5115983890948944395068345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6821311854598592526757793 5115983890948944395068345)
              ·
                refine ⟨3836987918211708296301259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5115983890948944395068345 3836987918211708296301259)
                ·
                  refine ⟨5755481877317562444451889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3836987918211708296301259 5755481877317562444451889)
                  ·
                    refine ⟨4316611407988171833338917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5755481877317562444451889 4316611407988171833338917)
                    ·
                      refine ⟨809364638997782218751047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4316611407988171833338917 809364638997782218751047)
                      ·
                        rfl

theorem cell23_1576232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_1576232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576232 prefixEnd_1576232 := by exact prefixLift 1576232
  have htrace : WordTrace (prefixWord ++ tailWord_1576232) baseStart_1576232 baseEnd_1576232 := by
    simpa [prefixWord, tailWord_1576232, baseEnd_1576232] using wordTrace_append hprefix tailTrace_1576232
  have hstable : (prefixWord ++ tailWord_1576232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576232).length < 2 ^ (prefixWord ++ tailWord_1576232).sum := by decide
  have hdescent : baseEnd_1576232 < baseStart_1576232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576246 : List Nat := [5, 1, 2, 3, 1, 1, 1, 1, 4, 4]
def baseStart_1576246 : Nat := 118140960795 + 1576246 * 2 ^ 59
def prefixEnd_1576246 : Nat := 4983230072969 + 3 ^ 40 * 1576246 * 2
def baseEnd_1576246 : Nat := 269790609242315054658661

theorem tailTrace_1576246 : CollatzResearch.WordTrace tailWord_1576246 prefixEnd_1576246 269790609242315054658661 := by
  unfold tailWord_1576246
  simp only [CollatzResearch.WordTrace]
  refine ⟨3593150915471088639355787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38326943098358278819795061 3593150915471088639355787)
  ·
    refine ⟨5389726373206632959033681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3593150915471088639355787 5389726373206632959033681)
    ·
      refine ⟨4042294779904974719275261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5389726373206632959033681 4042294779904974719275261)
      ·
        refine ⟨1515860542464365519728223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4042294779904974719275261 1515860542464365519728223)
        ·
          refine ⟨2273790813696548279592335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1515860542464365519728223 2273790813696548279592335)
          ·
            refine ⟨3410686220544822419388503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2273790813696548279592335 3410686220544822419388503)
            ·
              refine ⟨5116029330817233629082755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3410686220544822419388503 5116029330817233629082755)
              ·
                refine ⟨7674043996225850443624133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5116029330817233629082755 7674043996225850443624133)
                ·
                  refine ⟨1438883249292346958179525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7674043996225850443624133 1438883249292346958179525)
                  ·
                    refine ⟨269790609242315054658661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1438883249292346958179525 269790609242315054658661)
                    ·
                      rfl

theorem cell23_1576246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_1576246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576246 prefixEnd_1576246 := by exact prefixLift 1576246
  have htrace : WordTrace (prefixWord ++ tailWord_1576246) baseStart_1576246 baseEnd_1576246 := by
    simpa [prefixWord, tailWord_1576246, baseEnd_1576246] using wordTrace_append hprefix tailTrace_1576246
  have hstable : (prefixWord ++ tailWord_1576246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576246).length < 2 ^ (prefixWord ++ tailWord_1576246).sum := by decide
  have hdescent : baseEnd_1576246 < baseStart_1576246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576253 : List Nat := [1, 4, 1, 5, 1, 1, 2, 1, 3, 2, 2]
def baseStart_1576253 : Nat := 118140960795 + 1576253 * 2 ^ 59
def prefixEnd_1576253 : Nat := 4983230072969 + 3 ^ 40 * 1576253 * 2
def baseEnd_1576253 : Nat := 809375422091526636588451

theorem tailTrace_1576253 : CollatzResearch.WordTrace tailWord_1576253 prefixEnd_1576253 809375422091526636588451 := by
  unfold tailWord_1576253
  simp only [CollatzResearch.WordTrace]
  refine ⟨57490669958512058425197413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38327113305674705616798275 57490669958512058425197413)
  ·
    refine ⟨10779500617221010954724515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57490669958512058425197413 10779500617221010954724515)
    ·
      refine ⟨16169250925831516432086773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10779500617221010954724515 16169250925831516432086773)
      ·
        refine ⟨1515867274296704665508135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16169250925831516432086773 1515867274296704665508135)
        ·
          refine ⟨2273800911445056998262203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1515867274296704665508135 2273800911445056998262203)
          ·
            refine ⟨3410701367167585497393305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2273800911445056998262203 3410701367167585497393305)
            ·
              refine ⟨2558026025375689123044979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3410701367167585497393305 2558026025375689123044979)
              ·
                refine ⟨3837039038063533684567469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2558026025375689123044979 3837039038063533684567469)
                ·
                  refine ⟨1438889639273825131712801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3837039038063533684567469 1438889639273825131712801)
                  ·
                    refine ⟨1079167229455368848784601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1438889639273825131712801 1079167229455368848784601)
                    ·
                      refine ⟨809375422091526636588451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1079167229455368848784601 809375422091526636588451)
                      ·
                        rfl

theorem cell23_1576253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_1576253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576253 prefixEnd_1576253 := by exact prefixLift 1576253
  have htrace : WordTrace (prefixWord ++ tailWord_1576253) baseStart_1576253 baseEnd_1576253 := by
    simpa [prefixWord, tailWord_1576253, baseEnd_1576253] using wordTrace_append hprefix tailTrace_1576253
  have hstable : (prefixWord ++ tailWord_1576253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576253).length < 2 ^ (prefixWord ++ tailWord_1576253).sum := by decide
  have hdescent : baseEnd_1576253 < baseStart_1576253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576279 : List Nat := [1, 1, 3, 2, 3, 2, 1, 4, 1, 3, 2]
def baseStart_1576279 : Nat := 118140960795 + 1576279 * 2 ^ 59
def prefixEnd_1576279 : Nat := 4983230072969 + 3 ^ 40 * 1576279 * 2
def baseEnd_1576279 : Nat := 809388772588543534863331

theorem tailTrace_1576279 : CollatzResearch.WordTrace tailWord_1576279 prefixEnd_1576279 809388772588543534863331 := by
  unfold tailWord_1576279
  simp only [CollatzResearch.WordTrace]
  refine ⟨57491618256417864865643891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38327745504278576577095927 57491618256417864865643891)
  ·
    refine ⟨86237427384626797298465837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57491618256417864865643891 86237427384626797298465837)
    ·
      refine ⟨32339035269235048986924689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86237427384626797298465837 32339035269235048986924689)
      ·
        refine ⟨24254276451926286740193517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32339035269235048986924689 24254276451926286740193517)
        ·
          refine ⟨9095353669472357527572569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24254276451926286740193517 9095353669472357527572569)
          ·
            refine ⟨6821515252104268145679427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9095353669472357527572569 6821515252104268145679427)
            ·
              refine ⟨10232272878156402218519141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6821515252104268145679427 10232272878156402218519141)
              ·
                refine ⟨1918551164654325415972339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10232272878156402218519141 1918551164654325415972339)
                ·
                  refine ⟨2877826746981488123958509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1918551164654325415972339 2877826746981488123958509)
                  ·
                    refine ⟨1079185030118058046484441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2877826746981488123958509 1079185030118058046484441)
                    ·
                      refine ⟨809388772588543534863331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1079185030118058046484441 809388772588543534863331)
                      ·
                        rfl

theorem cell23_1576279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 3, 2].length) (baseStart_1576279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576279 prefixEnd_1576279 := by exact prefixLift 1576279
  have htrace : WordTrace (prefixWord ++ tailWord_1576279) baseStart_1576279 baseEnd_1576279 := by
    simpa [prefixWord, tailWord_1576279, baseEnd_1576279] using wordTrace_append hprefix tailTrace_1576279
  have hstable : (prefixWord ++ tailWord_1576279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576279).length < 2 ^ (prefixWord ++ tailWord_1576279).sum := by decide
  have hdescent : baseEnd_1576279 < baseStart_1576279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576305 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 4, 2, 4]
def baseStart_1576305 : Nat := 118140960795 + 1576305 * 2 ^ 59
def prefixEnd_1576305 : Nat := 4983230072969 + 3 ^ 40 * 1576305 * 2
def baseEnd_1576305 : Nat := 809402123085560433138211

theorem tailTrace_1576305 : CollatzResearch.WordTrace tailWord_1576305 prefixEnd_1576305 809402123085560433138211 := by
  unfold tailWord_1576305
  simp only [CollatzResearch.WordTrace]
  refine ⟨57492566554323671306090369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38328377702882447537393579 57492566554323671306090369)
  ·
    refine ⟨43119424915742753479567777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57492566554323671306090369 43119424915742753479567777)
    ·
      refine ⟨32339568686807065109675833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43119424915742753479567777 32339568686807065109675833)
      ·
        refine ⟨24254676515105298832256875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32339568686807065109675833 24254676515105298832256875)
        ·
          refine ⟨36382014772657948248385313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24254676515105298832256875 36382014772657948248385313)
          ·
            refine ⟨27286511079493461186288985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36382014772657948248385313 27286511079493461186288985)
            ·
              refine ⟨20464883309620095889716739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27286511079493461186288985 20464883309620095889716739)
              ·
                refine ⟨30697324964430143834575109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20464883309620095889716739 30697324964430143834575109)
                ·
                  refine ⟨5755748430830651968982833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30697324964430143834575109 5755748430830651968982833)
                  ·
                    refine ⟨4316811323122988976737125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5755748430830651968982833 4316811323122988976737125)
                    ·
                      refine ⟨809402123085560433138211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4316811323122988976737125 809402123085560433138211)
                      ·
                        rfl

theorem cell23_1576305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_1576305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576305 prefixEnd_1576305 := by exact prefixLift 1576305
  have htrace : WordTrace (prefixWord ++ tailWord_1576305) baseStart_1576305 baseEnd_1576305 := by
    simpa [prefixWord, tailWord_1576305, baseEnd_1576305] using wordTrace_append hprefix tailTrace_1576305
  have hstable : (prefixWord ++ tailWord_1576305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576305).length < 2 ^ (prefixWord ++ tailWord_1576305).sum := by decide
  have hdescent : baseEnd_1576305 < baseStart_1576305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576355 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 5]
def baseStart_1576355 : Nat := 118140960795 + 1576355 * 2 ^ 59
def prefixEnd_1576355 : Nat := 4983230072969 + 3 ^ 40 * 1576355 * 2
def baseEnd_1576355 : Nat := 809427797118285237512981

theorem tailTrace_1576355 : CollatzResearch.WordTrace tailWord_1576355 prefixEnd_1576355 809427797118285237512981 := by
  unfold tailWord_1576355
  simp only [CollatzResearch.WordTrace]
  refine ⟨57494390204142529845410519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38329593469428353230273679 57494390204142529845410519)
  ·
    refine ⟨86241585306213794768115779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57494390204142529845410519 86241585306213794768115779)
    ·
      refine ⟨129362377959320692152173669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86241585306213794768115779 129362377959320692152173669)
      ·
        refine ⟨24255445867372629778532563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129362377959320692152173669 24255445867372629778532563)
        ·
          refine ⟨36383168801058944667798845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24255445867372629778532563 36383168801058944667798845)
          ·
            refine ⟨13643688300397104250424567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36383168801058944667798845 13643688300397104250424567)
            ·
              refine ⟨20465532450595656375636851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13643688300397104250424567 20465532450595656375636851)
              ·
                refine ⟨30698298675893484563455277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20465532450595656375636851 30698298675893484563455277)
                ·
                  refine ⟨11511862003460056711295729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30698298675893484563455277 11511862003460056711295729)
                  ·
                    refine ⟨8633896502595042533471797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11511862003460056711295729 8633896502595042533471797)
                    ·
                      refine ⟨809427797118285237512981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8633896502595042533471797 809427797118285237512981)
                      ·
                        rfl

theorem cell23_1576355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_1576355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576355 prefixEnd_1576355 := by exact prefixLift 1576355
  have htrace : WordTrace (prefixWord ++ tailWord_1576355) baseStart_1576355 baseEnd_1576355 := by
    simpa [prefixWord, tailWord_1576355, baseEnd_1576355] using wordTrace_append hprefix tailTrace_1576355
  have hstable : (prefixWord ++ tailWord_1576355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576355).length < 2 ^ (prefixWord ++ tailWord_1576355).sum := by decide
  have hdescent : baseEnd_1576355 < baseStart_1576355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576360 : List Nat := [2, 1, 6, 1, 2, 1, 2, 2, 2, 2, 2]
def baseStart_1576360 : Nat := 118140960795 + 1576360 * 2 ^ 59
def prefixEnd_1576360 : Nat := 4983230072969 + 3 ^ 40 * 1576360 * 2
def baseEnd_1576360 : Nat := 809430364521557717950459

theorem tailTrace_1576360 : CollatzResearch.WordTrace tailWord_1576360 prefixEnd_1576360 809430364521557717950459 := by
  unfold tailWord_1576360
  simp only [CollatzResearch.WordTrace]
  refine ⟨28747286284562207849671267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38329715046082943799561689 28747286284562207849671267)
  ·
    refine ⟨43120929426843311774506901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28747286284562207849671267 43120929426843311774506901)
    ·
      refine ⟨2021293566883280239430011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 43120929426843311774506901 2021293566883280239430011)
      ·
        refine ⟨3031940350324920359145017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2021293566883280239430011 3031940350324920359145017)
        ·
          refine ⟨2273955262743690269358763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3031940350324920359145017 2273955262743690269358763)
          ·
            refine ⟨3410932894115535404038145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2273955262743690269358763 3410932894115535404038145)
            ·
              refine ⟨2558199670586651553028609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3410932894115535404038145 2558199670586651553028609)
              ·
                refine ⟨1918649752939988664771457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2558199670586651553028609 1918649752939988664771457)
                ·
                  refine ⟨1438987314704991498578593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1918649752939988664771457 1438987314704991498578593)
                  ·
                    refine ⟨1079240486028743623933945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1438987314704991498578593 1079240486028743623933945)
                    ·
                      refine ⟨809430364521557717950459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1079240486028743623933945 809430364521557717950459)
                      ·
                        rfl

theorem cell23_1576360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_1576360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576360 prefixEnd_1576360 := by exact prefixLift 1576360
  have htrace : WordTrace (prefixWord ++ tailWord_1576360) baseStart_1576360 baseEnd_1576360 := by
    simpa [prefixWord, tailWord_1576360, baseEnd_1576360] using wordTrace_append hprefix tailTrace_1576360
  have hstable : (prefixWord ++ tailWord_1576360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576360).length < 2 ^ (prefixWord ++ tailWord_1576360).sum := by decide
  have hdescent : baseEnd_1576360 < baseStart_1576360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576382 : List Nat := [4, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4]
def baseStart_1576382 : Nat := 118140960795 + 1576382 * 2 ^ 59
def prefixEnd_1576382 : Nat := 4983230072969 + 3 ^ 40 * 1576382 * 2
def baseEnd_1576382 : Nat := 809441661095956631875357

theorem tailTrace_1576382 : CollatzResearch.WordTrace tailWord_1576382 prefixEnd_1576382 809441661095956631875357 := by
  unfold tailWord_1576382
  simp only [CollatzResearch.WordTrace]
  refine ⟨7186921871880589182080425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38330249983363142304428933 7186921871880589182080425)
  ·
    refine ⟨5390191403910441886560319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7186921871880589182080425 5390191403910441886560319)
    ·
      refine ⟨8085287105865662829840479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5390191403910441886560319 8085287105865662829840479)
      ·
        refine ⟨12127930658798494244760719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8085287105865662829840479 12127930658798494244760719)
        ·
          refine ⟨18191895988197741367141079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12127930658798494244760719 18191895988197741367141079)
          ·
            refine ⟨27287843982296612050711619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18191895988197741367141079 27287843982296612050711619)
            ·
              refine ⟨40931765973444918076067429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27287843982296612050711619 40931765973444918076067429)
              ·
                refine ⟨7674706120020922139262643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40931765973444918076067429 7674706120020922139262643)
                ·
                  refine ⟨11512059180031383208893965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7674706120020922139262643 11512059180031383208893965)
                  ·
                    refine ⟨4317022192511768703335237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11512059180031383208893965 4317022192511768703335237)
                    ·
                      refine ⟨809441661095956631875357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4317022192511768703335237 809441661095956631875357)
                      ·
                        rfl

theorem cell23_1576382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_1576382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576382 prefixEnd_1576382 := by exact prefixLift 1576382
  have htrace : WordTrace (prefixWord ++ tailWord_1576382) baseStart_1576382 baseEnd_1576382 := by
    simpa [prefixWord, tailWord_1576382, baseEnd_1576382] using wordTrace_append hprefix tailTrace_1576382
  have hstable : (prefixWord ++ tailWord_1576382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576382).length < 2 ^ (prefixWord ++ tailWord_1576382).sum := by decide
  have hdescent : baseEnd_1576382 < baseStart_1576382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576426 : List Nat := [3, 1, 3, 1, 4, 1, 2, 1, 3, 4]
def baseStart_1576426 : Nat := 118140960795 + 1576426 * 2 ^ 59
def prefixEnd_1576426 : Nat := 4983230072969 + 3 ^ 40 * 1576426 * 2
def baseEnd_1576426 : Nat := 269821418081584819908385

theorem tailTrace_1576426 : CollatzResearch.WordTrace tailWord_1576426 prefixEnd_1576426 269821418081584819908385 := by
  unfold tailWord_1576426
  simp only [CollatzResearch.WordTrace]
  refine ⟨14374244946721327242811283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38331319857923539314163421 14374244946721327242811283)
  ·
    refine ⟨21561367420081990864216925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14374244946721327242811283 21561367420081990864216925)
    ·
      refine ⟨8085512782530746574081347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21561367420081990864216925 8085512782530746574081347)
      ·
        refine ⟨12128269173796119861122021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8085512782530746574081347 12128269173796119861122021)
        ·
          refine ⟨2274050470086772473960379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12128269173796119861122021 2274050470086772473960379)
          ·
            refine ⟨3411075705130158710940569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2274050470086772473960379 3411075705130158710940569)
            ·
              refine ⟨2558306778847619033205427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3411075705130158710940569 2558306778847619033205427)
              ·
                refine ⟨3837460168271428549808141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2558306778847619033205427 3837460168271428549808141)
                ·
                  refine ⟨1439047563101785706178053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3837460168271428549808141 1439047563101785706178053)
                  ·
                    refine ⟨269821418081584819908385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1439047563101785706178053 269821418081584819908385)
                    ·
                      rfl

theorem cell23_1576426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_1576426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576426 prefixEnd_1576426 := by exact prefixLift 1576426
  have htrace : WordTrace (prefixWord ++ tailWord_1576426) baseStart_1576426 baseEnd_1576426 := by
    simpa [prefixWord, tailWord_1576426, baseEnd_1576426] using wordTrace_append hprefix tailTrace_1576426
  have hstable : (prefixWord ++ tailWord_1576426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576426).length < 2 ^ (prefixWord ++ tailWord_1576426).sum := by decide
  have hdescent : baseEnd_1576426 < baseStart_1576426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576435 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 2, 9]
def baseStart_1576435 : Nat := 118140960795 + 1576435 * 2 ^ 59
def prefixEnd_1576435 : Nat := 4983230072969 + 3 ^ 40 * 1576435 * 2
def baseEnd_1576435 : Nat := 269822958523548308170871

theorem tailTrace_1576435 : CollatzResearch.WordTrace tailWord_1576435 prefixEnd_1576435 269822958523548308170871 := by
  unfold tailWord_1576435
  simp only [CollatzResearch.WordTrace]
  refine ⟨57497308043852703508322759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38331538695901802338881839 57497308043852703508322759)
  ·
    refine ⟨86245962065779055262484139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57497308043852703508322759 86245962065779055262484139)
    ·
      refine ⟨129368943098668582893726209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86245962065779055262484139 129368943098668582893726209)
      ·
        refine ⟨97026707324001437170294657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129368943098668582893726209 97026707324001437170294657)
        ·
          refine ⟨72770030493001077877720993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97026707324001437170294657 72770030493001077877720993)
          ·
            refine ⟨54577522869750808408290745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72770030493001077877720993 54577522869750808408290745)
            ·
              refine ⟨40933142152313106306218059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54577522869750808408290745 40933142152313106306218059)
              ·
                refine ⟨61399713228469659459327089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40933142152313106306218059 61399713228469659459327089)
                ·
                  refine ⟨46049784921352244594495317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61399713228469659459327089 46049784921352244594495317)
                  ·
                    refine ⟨269822958523548308170871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 46049784921352244594495317 269822958523548308170871)
                    ·
                      rfl

theorem cell23_1576435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 9].length) (baseStart_1576435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576435 prefixEnd_1576435 := by exact prefixLift 1576435
  have htrace : WordTrace (prefixWord ++ tailWord_1576435) baseStart_1576435 baseEnd_1576435 := by
    simpa [prefixWord, tailWord_1576435, baseEnd_1576435] using wordTrace_append hprefix tailTrace_1576435
  have hstable : (prefixWord ++ tailWord_1576435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576435).length < 2 ^ (prefixWord ++ tailWord_1576435).sum := by decide
  have hdescent : baseEnd_1576435 < baseStart_1576435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576460 : List Nat := [2, 2, 1, 2, 6, 1, 1, 3, 1, 4]
def baseStart_1576460 : Nat := 118140960795 + 1576460 * 2 ^ 59
def prefixEnd_1576460 : Nat := 4983230072969 + 3 ^ 40 * 1576460 * 2
def baseEnd_1576460 : Nat := 269827237529002442233333

theorem tailTrace_1576460 : CollatzResearch.WordTrace tailWord_1576460 prefixEnd_1576460 269827237529002442233333 := by
  unfold tailWord_1576460
  simp only [CollatzResearch.WordTrace]
  refine ⟨28749109934381066388991417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38332146579174755185321889 28749109934381066388991417)
  ·
    refine ⟨21561832450785799791743563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28749109934381066388991417 21561832450785799791743563)
    ·
      refine ⟨32342748676178699687615345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21561832450785799791743563 32342748676178699687615345)
      ·
        refine ⟨24257061507134024765711509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32342748676178699687615345 24257061507134024765711509)
        ·
          refine ⟨1137049758146907410892727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24257061507134024765711509 1137049758146907410892727)
          ·
            refine ⟨1705574637220361116339091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1137049758146907410892727 1705574637220361116339091)
            ·
              refine ⟨2558361955830541674508637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1705574637220361116339091 2558361955830541674508637)
              ·
                refine ⟨959385733436453127940739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2558361955830541674508637 959385733436453127940739)
                ·
                  refine ⟨1439078600154679691911109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 959385733436453127940739 1439078600154679691911109)
                  ·
                    refine ⟨269827237529002442233333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1439078600154679691911109 269827237529002442233333)
                    ·
                      rfl

theorem cell23_1576460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 3, 1, 4].length) (baseStart_1576460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576460 prefixEnd_1576460 := by exact prefixLift 1576460
  have htrace : WordTrace (prefixWord ++ tailWord_1576460) baseStart_1576460 baseEnd_1576460 := by
    simpa [prefixWord, tailWord_1576460, baseEnd_1576460] using wordTrace_append hprefix tailTrace_1576460
  have hstable : (prefixWord ++ tailWord_1576460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576460).length < 2 ^ (prefixWord ++ tailWord_1576460).sum := by decide
  have hdescent : baseEnd_1576460 < baseStart_1576460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576469 : List Nat := [1, 3, 2, 1, 3, 2, 2, 3, 1, 5]
def baseStart_1576469 : Nat := 118140960795 + 1576469 * 2 ^ 59
def prefixEnd_1576469 : Nat := 4983230072969 + 3 ^ 40 * 1576469 * 2
def baseEnd_1576469 : Nat := 269828777970965930495819

theorem tailTrace_1576469 : CollatzResearch.WordTrace tailWord_1576469 prefixEnd_1576469 269828777970965930495819 := by
  unfold tailWord_1576469
  simp only [CollatzResearch.WordTrace]
  refine ⟨57498548125729527315060461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38332365417153018210040307 57498548125729527315060461)
  ·
    refine ⟨21561955547148572743147673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57498548125729527315060461 21561955547148572743147673)
    ·
      refine ⟨16171466660361429557360755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21561955547148572743147673 16171466660361429557360755)
      ·
        refine ⟨24257199990542144336041133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16171466660361429557360755 24257199990542144336041133)
        ·
          refine ⟨9096449996453304126015425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24257199990542144336041133 9096449996453304126015425)
          ·
            refine ⟨6822337497339978094511569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9096449996453304126015425 6822337497339978094511569)
            ·
              refine ⟨5116753123004983570883677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6822337497339978094511569 5116753123004983570883677)
              ·
                refine ⟨1918782421126868839081379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5116753123004983570883677 1918782421126868839081379)
                ·
                  refine ⟨2878173631690303258622069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1918782421126868839081379 2878173631690303258622069)
                  ·
                    refine ⟨269828777970965930495819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2878173631690303258622069 269828777970965930495819)
                    ·
                      rfl

theorem cell23_1576469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 5].length) (baseStart_1576469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576469 prefixEnd_1576469 := by exact prefixLift 1576469
  have htrace : WordTrace (prefixWord ++ tailWord_1576469) baseStart_1576469 baseEnd_1576469 := by
    simpa [prefixWord, tailWord_1576469, baseEnd_1576469] using wordTrace_append hprefix tailTrace_1576469
  have hstable : (prefixWord ++ tailWord_1576469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576469).length < 2 ^ (prefixWord ++ tailWord_1576469).sum := by decide
  have hdescent : baseEnd_1576469 < baseStart_1576469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576476 : List Nat := [2, 2, 3, 1, 2, 1, 3, 2, 2, 3, 2]
def baseStart_1576476 : Nat := 118140960795 + 1576476 * 2 ^ 59
def prefixEnd_1576476 : Nat := 4983230072969 + 3 ^ 40 * 1576476 * 2
def baseEnd_1576476 : Nat := 809489928277479264099925

theorem tailTrace_1576476 : CollatzResearch.WordTrace tailWord_1576476 prefixEnd_1576476 809489928277479264099925 := by
  unfold tailWord_1576476
  simp only [CollatzResearch.WordTrace]
  refine ⟨28749401718352083755282641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38332535624469445007043521 28749401718352083755282641)
  ·
    refine ⟨21562051288764062816461981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28749401718352083755282641 21562051288764062816461981)
    ·
      refine ⟨8085769233286523556173243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21562051288764062816461981 8085769233286523556173243)
      ·
        refine ⟨12128653849929785334259865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8085769233286523556173243 12128653849929785334259865)
        ·
          refine ⟨9096490387447339000694899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12128653849929785334259865 9096490387447339000694899)
          ·
            refine ⟨13644735581171008501042349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9096490387447339000694899 13644735581171008501042349)
            ·
              refine ⟨5116775842939128187890881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13644735581171008501042349 5116775842939128187890881)
              ·
                refine ⟨3837581882204346140918161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5116775842939128187890881 3837581882204346140918161)
                ·
                  refine ⟨2878186411653259605688621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3837581882204346140918161 2878186411653259605688621)
                  ·
                    refine ⟨1079319904369972352133233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2878186411653259605688621 1079319904369972352133233)
                    ·
                      refine ⟨809489928277479264099925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1079319904369972352133233 809489928277479264099925)
                      ·
                        rfl

theorem cell23_1576476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_1576476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576476 prefixEnd_1576476 := by exact prefixLift 1576476
  have htrace : WordTrace (prefixWord ++ tailWord_1576476) baseStart_1576476 baseEnd_1576476 := by
    simpa [prefixWord, tailWord_1576476, baseEnd_1576476] using wordTrace_append hprefix tailTrace_1576476
  have hstable : (prefixWord ++ tailWord_1576476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576476).length < 2 ^ (prefixWord ++ tailWord_1576476).sum := by decide
  have hdescent : baseEnd_1576476 < baseStart_1576476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576483 : List Nat := [1, 1, 1, 4, 5, 2, 1, 1, 3, 1, 3]
def baseStart_1576483 : Nat := 118140960795 + 1576483 * 2 ^ 59
def prefixEnd_1576483 : Nat := 4983230072969 + 3 ^ 40 * 1576483 * 2
def baseEnd_1576483 : Nat := 809493522642060736712393

theorem tailTrace_1576483 : CollatzResearch.WordTrace tailWord_1576483 prefixEnd_1576483 809493522642060736712393 := by
  unfold tailWord_1576483
  simp only [CollatzResearch.WordTrace]
  refine ⟨57499058747678807706070103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38332705831785871804046735 57499058747678807706070103)
  ·
    refine ⟨86248588121518211559105155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57499058747678807706070103 86248588121518211559105155)
    ·
      refine ⟨129372882182277317338657733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86248588121518211559105155 129372882182277317338657733)
      ·
        refine ⟨24257415409176997000998325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129372882182277317338657733 24257415409176997000998325)
        ·
          refine ⟨2274132694610343468843593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24257415409176997000998325 2274132694610343468843593)
          ·
            refine ⟨1705599520957757601632695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2274132694610343468843593 1705599520957757601632695)
            ·
              refine ⟨2558399281436636402449043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1705599520957757601632695 2558399281436636402449043)
              ·
                refine ⟨3837598922154954603673565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2558399281436636402449043 3837598922154954603673565)
                ·
                  refine ⟨1439099595808107976377587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3837598922154954603673565 1439099595808107976377587)
                  ·
                    refine ⟨2158649393712161964566381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1439099595808107976377587 2158649393712161964566381)
                    ·
                      refine ⟨809493522642060736712393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2158649393712161964566381 809493522642060736712393)
                      ·
                        rfl

theorem cell23_1576483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 3, 1, 3].length) (baseStart_1576483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576483 prefixEnd_1576483 := by exact prefixLift 1576483
  have htrace : WordTrace (prefixWord ++ tailWord_1576483) baseStart_1576483 baseEnd_1576483 := by
    simpa [prefixWord, tailWord_1576483, baseEnd_1576483] using wordTrace_append hprefix tailTrace_1576483
  have hstable : (prefixWord ++ tailWord_1576483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576483).length < 2 ^ (prefixWord ++ tailWord_1576483).sum := by decide
  have hdescent : baseEnd_1576483 < baseStart_1576483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576492 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 3]
def baseStart_1576492 : Nat := 118140960795 + 1576492 * 2 ^ 59
def prefixEnd_1576492 : Nat := 4983230072969 + 3 ^ 40 * 1576492 * 2
def baseEnd_1576492 : Nat := 809498143967951201499851

theorem tailTrace_1576492 : CollatzResearch.WordTrace tailWord_1576492 prefixEnd_1576492 809498143967951201499851 := by
  unfold tailWord_1576492
  simp only [CollatzResearch.WordTrace]
  refine ⟨28749693502323101121573865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38332924669764134828765153 28749693502323101121573865)
  ·
    refine ⟨21562270126742325841180399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28749693502323101121573865 21562270126742325841180399)
    ·
      refine ⟨32343405190113488761770599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21562270126742325841180399 32343405190113488761770599)
      ·
        refine ⟨48515107785170233142655899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32343405190113488761770599 48515107785170233142655899)
        ·
          refine ⟨72772661677755349713983849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48515107785170233142655899 72772661677755349713983849)
          ·
            refine ⟨54579496258316512285487887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72772661677755349713983849 54579496258316512285487887)
            ·
              refine ⟨81869244387474768428231831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54579496258316512285487887 81869244387474768428231831)
              ·
                refine ⟨122803866581212152642347747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81869244387474768428231831 122803866581212152642347747)
                ·
                  refine ⟨184205799871818228963521621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122803866581212152642347747 184205799871818228963521621)
                  ·
                    refine ⟨2158661717247869870666269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 184205799871818228963521621 2158661717247869870666269)
                    ·
                      refine ⟨809498143967951201499851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2158661717247869870666269 809498143967951201499851)
                      ·
                        rfl

theorem cell23_1576492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 3].length) (baseStart_1576492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576492 prefixEnd_1576492 := by exact prefixLift 1576492
  have htrace : WordTrace (prefixWord ++ tailWord_1576492) baseStart_1576492 baseEnd_1576492 := by
    simpa [prefixWord, tailWord_1576492, baseEnd_1576492] using wordTrace_append hprefix tailTrace_1576492
  have hstable : (prefixWord ++ tailWord_1576492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576492).length < 2 ^ (prefixWord ++ tailWord_1576492).sum := by decide
  have hdescent : baseEnd_1576492 < baseStart_1576492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576506 : List Nat := [3, 1, 1, 1, 3, 2, 2, 1, 5, 2, 2]
def baseStart_1576506 : Nat := 118140960795 + 1576506 * 2 ^ 59
def prefixEnd_1576506 : Nat := 4983230072969 + 3 ^ 40 * 1576506 * 2
def baseEnd_1576506 : Nat := 809505332697114146724787

theorem tailTrace_1576506 : CollatzResearch.WordTrace tailWord_1576506 prefixEnd_1576506 809505332697114146724787 := by
  unfold tailWord_1576506
  simp only [CollatzResearch.WordTrace]
  refine ⟨14374974406648870658539343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38333265084396988422771581 14374974406648870658539343)
  ·
    refine ⟨21562461609973305987809015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14374974406648870658539343 21562461609973305987809015)
    ·
      refine ⟨32343692414959958981713523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21562461609973305987809015 32343692414959958981713523)
      ·
        refine ⟨48515538622439938472570285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32343692414959958981713523 48515538622439938472570285)
        ·
          refine ⟨18193326983414976927213857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48515538622439938472570285 18193326983414976927213857)
          ·
            refine ⟨13644995237561232695410393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18193326983414976927213857 13644995237561232695410393)
            ·
              refine ⟨10233746428170924521557795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13644995237561232695410393 10233746428170924521557795)
              ·
                refine ⟨15350619642256386782336693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10233746428170924521557795 15350619642256386782336693)
                ·
                  refine ⟨1439120591461536260844065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15350619642256386782336693 1439120591461536260844065)
                  ·
                    refine ⟨1079340443596152195633049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1439120591461536260844065 1079340443596152195633049)
                    ·
                      refine ⟨809505332697114146724787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1079340443596152195633049 809505332697114146724787)
                      ·
                        rfl

theorem cell23_1576506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 5, 2, 2].length) (baseStart_1576506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576506 prefixEnd_1576506 := by exact prefixLift 1576506
  have htrace : WordTrace (prefixWord ++ tailWord_1576506) baseStart_1576506 baseEnd_1576506 := by
    simpa [prefixWord, tailWord_1576506, baseEnd_1576506] using wordTrace_append hprefix tailTrace_1576506
  have hstable : (prefixWord ++ tailWord_1576506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576506).length < 2 ^ (prefixWord ++ tailWord_1576506).sum := by decide
  have hdescent : baseEnd_1576506 < baseStart_1576506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576523 : List Nat := [1, 1, 1, 1, 3, 1, 3, 7, 1, 2, 2]
def baseStart_1576523 : Nat := 118140960795 + 1576523 * 2 ^ 59
def prefixEnd_1576523 : Nat := 4983230072969 + 3 ^ 40 * 1576523 * 2
def baseEnd_1576523 : Nat := 809514061868240580212209

theorem tailTrace_1576523 : CollatzResearch.WordTrace tailWord_1576523 prefixEnd_1576523 809514061868240580212209 := by
  unfold tailWord_1576523
  simp only [CollatzResearch.WordTrace]
  refine ⟨57500517667533894537526223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38333678445022596358350815 57500517667533894537526223)
  ·
    refine ⟨86250776501300841806289335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57500517667533894537526223 86250776501300841806289335)
    ·
      refine ⟨129376164751951262709434003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86250776501300841806289335 129376164751951262709434003)
      ·
        refine ⟨194064247127926894064151005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129376164751951262709434003 194064247127926894064151005)
        ·
          refine ⟨72774092672972585274056627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194064247127926894064151005 72774092672972585274056627)
          ·
            refine ⟨109161139009458877911084941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72774092672972585274056627 109161139009458877911084941)
            ·
              refine ⟨40935427128547079216656853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109161139009458877911084941 40935427128547079216656853)
              ·
                refine ⟨959424073325322169140395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 40935427128547079216656853 959424073325322169140395)
                ·
                  refine ⟨1439136109987983253710593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 959424073325322169140395 1439136109987983253710593)
                  ·
                    refine ⟨1079352082490987440282945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1439136109987983253710593 1079352082490987440282945)
                    ·
                      refine ⟨809514061868240580212209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1079352082490987440282945 809514061868240580212209)
                      ·
                        rfl

theorem cell23_1576523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 7, 1, 2, 2].length) (baseStart_1576523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576523 prefixEnd_1576523 := by exact prefixLift 1576523
  have htrace : WordTrace (prefixWord ++ tailWord_1576523) baseStart_1576523 baseEnd_1576523 := by
    simpa [prefixWord, tailWord_1576523, baseEnd_1576523] using wordTrace_append hprefix tailTrace_1576523
  have hstable : (prefixWord ++ tailWord_1576523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576523).length < 2 ^ (prefixWord ++ tailWord_1576523).sum := by decide
  have hdescent : baseEnd_1576523 < baseStart_1576523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576534 : List Nat := [5, 2, 2, 2, 1, 1, 1, 4, 1, 1, 3]
def baseStart_1576534 : Nat := 118140960795 + 1576534 * 2 ^ 59
def prefixEnd_1576534 : Nat := 4983230072969 + 3 ^ 40 * 1576534 * 2
def baseEnd_1576534 : Nat := 809519710155440037174659

theorem tailTrace_1576534 : CollatzResearch.WordTrace tailWord_1576534 prefixEnd_1576534 809519710155440037174659 := by
  unfold tailWord_1576534
  simp only [CollatzResearch.WordTrace]
  refine ⟨3593807429405877713511041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38333945913662695610784437 3593807429405877713511041)
  ·
    refine ⟨2695355572054408285133281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3593807429405877713511041 2695355572054408285133281)
    ·
      refine ⟨2021516679040806213849961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2695355572054408285133281 2021516679040806213849961)
      ·
        refine ⟨1516137509280604660387471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2021516679040806213849961 1516137509280604660387471)
        ·
          refine ⟨2274206263920906990581207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1516137509280604660387471 2274206263920906990581207)
          ·
            refine ⟨3411309395881360485871811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2274206263920906990581207 3411309395881360485871811)
            ·
              refine ⟨5116964093822040728807717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3411309395881360485871811 5116964093822040728807717)
              ·
                refine ⟨959430767591632636651447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5116964093822040728807717 959430767591632636651447)
                ·
                  refine ⟨1439146151387448954977171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 959430767591632636651447 1439146151387448954977171)
                  ·
                    refine ⟨2158719227081173432465757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1439146151387448954977171 2158719227081173432465757)
                    ·
                      refine ⟨809519710155440037174659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2158719227081173432465757 809519710155440037174659)
                      ·
                        rfl

theorem cell23_1576534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_1576534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576534 prefixEnd_1576534 := by exact prefixLift 1576534
  have htrace : WordTrace (prefixWord ++ tailWord_1576534) baseStart_1576534 baseEnd_1576534 := by
    simpa [prefixWord, tailWord_1576534, baseEnd_1576534] using wordTrace_append hprefix tailTrace_1576534
  have hstable : (prefixWord ++ tailWord_1576534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576534).length < 2 ^ (prefixWord ++ tailWord_1576534).sum := by decide
  have hdescent : baseEnd_1576534 < baseStart_1576534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576572 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 3, 8]
def baseStart_1576572 : Nat := 118140960795 + 1576572 * 2 ^ 59
def prefixEnd_1576572 : Nat := 4983230072969 + 3 ^ 40 * 1576572 * 2
def baseEnd_1576572 : Nat := 269846407473436962833161

theorem tailTrace_1576572 : CollatzResearch.WordTrace tailWord_1576572 prefixEnd_1576572 269846407473436962833161 := by
  unfold tailWord_1576572
  simp only [CollatzResearch.WordTrace]
  refine ⟨28751152422178187953029985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38334869896237583937373313 28751152422178187953029985)
  ·
    refine ⟨21563364316633640964772489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28751152422178187953029985 21563364316633640964772489)
    ·
      refine ⟨16172523237475230723579367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21563364316633640964772489 16172523237475230723579367)
      ·
        refine ⟨24258784856212846085369051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16172523237475230723579367 24258784856212846085369051)
        ·
          refine ⟨36388177284319269128053577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24258784856212846085369051 36388177284319269128053577)
          ·
            refine ⟨27291132963239451846040183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36388177284319269128053577 27291132963239451846040183)
            ·
              refine ⟨40936699444859177769060275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27291132963239451846040183 40936699444859177769060275)
              ·
                refine ⟨61405049167288766653590413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40936699444859177769060275 61405049167288766653590413)
                ·
                  refine ⟨23026893437733287495096405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61405049167288766653590413 23026893437733287495096405)
                  ·
                    refine ⟨269846407473436962833161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 23026893437733287495096405 269846407473436962833161)
                    ·
                      rfl

theorem cell23_1576572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_1576572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576572 prefixEnd_1576572 := by exact prefixLift 1576572
  have htrace : WordTrace (prefixWord ++ tailWord_1576572) baseStart_1576572 baseEnd_1576572 := by
    simpa [prefixWord, tailWord_1576572, baseEnd_1576572] using wordTrace_append hprefix tailTrace_1576572
  have hstable : (prefixWord ++ tailWord_1576572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576572).length < 2 ^ (prefixWord ++ tailWord_1576572).sum := by decide
  have hdescent : baseEnd_1576572 < baseStart_1576572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576583 : List Nat := [1, 1, 4, 2, 1, 4, 1, 3, 1, 3, 2]
def baseStart_1576583 : Nat := 118140960795 + 1576583 * 2 ^ 59
def prefixEnd_1576583 : Nat := 4983230072969 + 3 ^ 40 * 1576583 * 2
def baseEnd_1576583 : Nat := 809544870707510345461933

theorem tailTrace_1576583 : CollatzResearch.WordTrace tailWord_1576583 prefixEnd_1576583 809544870707510345461933 := by
  unfold tailWord_1576583
  simp only [CollatzResearch.WordTrace]
  refine ⟨57502706047316524784710403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38335137364877683189806935 57502706047316524784710403)
  ·
    refine ⟨86254059070974787177065605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57502706047316524784710403 86254059070974787177065605)
    ·
      refine ⟨16172636075807772595699801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86254059070974787177065605 16172636075807772595699801)
      ·
        refine ⟨12129477056855829446774851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16172636075807772595699801 12129477056855829446774851)
        ·
          refine ⟨18194215585283744170162277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12129477056855829446774851 18194215585283744170162277)
          ·
            refine ⟨3411415422240702031905427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18194215585283744170162277 3411415422240702031905427)
            ·
              refine ⟨5117123133361053047858141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3411415422240702031905427 5117123133361053047858141)
              ·
                refine ⟨1918921175010394892946803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5117123133361053047858141 1918921175010394892946803)
                ·
                  refine ⟨2878381762515592339420205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1918921175010394892946803 2878381762515592339420205)
                  ·
                    refine ⟨1079393160943347127282577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2878381762515592339420205 1079393160943347127282577)
                    ·
                      refine ⟨809544870707510345461933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1079393160943347127282577 809544870707510345461933)
                      ·
                        rfl

theorem cell23_1576583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_1576583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576583 prefixEnd_1576583 := by exact prefixLift 1576583
  have htrace : WordTrace (prefixWord ++ tailWord_1576583) baseStart_1576583 baseEnd_1576583 := by
    simpa [prefixWord, tailWord_1576583, baseEnd_1576583] using wordTrace_append hprefix tailTrace_1576583
  have hstable : (prefixWord ++ tailWord_1576583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576583).length < 2 ^ (prefixWord ++ tailWord_1576583).sum := by decide
  have hdescent : baseEnd_1576583 < baseStart_1576583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576590 : List Nat := [4, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3]
def baseStart_1576590 : Nat := 118140960795 + 1576590 * 2 ^ 59
def prefixEnd_1576590 : Nat := 4983230072969 + 3 ^ 40 * 1576590 * 2
def baseEnd_1576590 : Nat := 809548465072091818074401

theorem tailTrace_1576590 : CollatzResearch.WordTrace tailWord_1576590 prefixEnd_1576590 809548465072091818074401 := by
  unfold tailWord_1576590
  simp only [CollatzResearch.WordTrace]
  refine ⟨7187870169786395622526903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38335307572194109986810149 7187870169786395622526903)
  ·
    refine ⟨10781805254679593433790355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7187870169786395622526903 10781805254679593433790355)
    ·
      refine ⟨16172707882019390150685533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10781805254679593433790355 16172707882019390150685533)
      ·
        refine ⟨6064765455757271306507075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16172707882019390150685533 6064765455757271306507075)
        ·
          refine ⟨9097148183635906959760613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6064765455757271306507075 9097148183635906959760613)
          ·
            refine ⟨1705715284431732554955115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9097148183635906959760613 1705715284431732554955115)
            ·
              refine ⟨2558572926647598832432673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1705715284431732554955115 2558572926647598832432673)
              ·
                refine ⟨1918929694985699124324505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2558572926647598832432673 1918929694985699124324505)
                ·
                  refine ⟨1439197271239274343243379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1918929694985699124324505 1439197271239274343243379)
                  ·
                    refine ⟨2158795906858911514865069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1439197271239274343243379 2158795906858911514865069)
                    ·
                      refine ⟨809548465072091818074401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2158795906858911514865069 809548465072091818074401)
                      ·
                        rfl

theorem cell23_1576590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_1576590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576590 prefixEnd_1576590 := by exact prefixLift 1576590
  have htrace : WordTrace (prefixWord ++ tailWord_1576590) baseStart_1576590 baseEnd_1576590 := by
    simpa [prefixWord, tailWord_1576590, baseEnd_1576590] using wordTrace_append hprefix tailTrace_1576590
  have hstable : (prefixWord ++ tailWord_1576590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576590).length < 2 ^ (prefixWord ++ tailWord_1576590).sum := by decide
  have hdescent : baseEnd_1576590 < baseStart_1576590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576606 : List Nat := [4, 3, 1, 1, 1, 2, 2, 1, 2, 6]
def baseStart_1576606 : Nat := 118140960795 + 1576606 * 2 ^ 59
def prefixEnd_1576606 : Nat := 4983230072969 + 3 ^ 40 * 1576606 * 2
def baseEnd_1576606 : Nat := 269852226920854585158109

theorem tailTrace_1576606 : CollatzResearch.WordTrace tailWord_1576606 prefixEnd_1576606 269852226920854585158109 := by
  unfold tailWord_1576606
  simp only [CollatzResearch.WordTrace]
  refine ⟨7187943115779149964099709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38335696617488799808531781 7187943115779149964099709)
  ·
    refine ⟨2695478668417181236537391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7187943115779149964099709 2695478668417181236537391)
    ·
      refine ⟨4043218002625771854806087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2695478668417181236537391 4043218002625771854806087)
      ·
        refine ⟨6064827003938657782209131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4043218002625771854806087 6064827003938657782209131)
        ·
          refine ⟨9097240505907986673313697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6064827003938657782209131 9097240505907986673313697)
          ·
            refine ⟨6822930379430990004985273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9097240505907986673313697 6822930379430990004985273)
            ·
              refine ⟨5117197784573242503738955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6822930379430990004985273 5117197784573242503738955)
              ·
                refine ⟨7675796676859863755608433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5117197784573242503738955 7675796676859863755608433)
                ·
                  refine ⟨5756847507644897816706325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7675796676859863755608433 5756847507644897816706325)
                  ·
                    refine ⟨269852226920854585158109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5756847507644897816706325 269852226920854585158109)
                    ·
                      rfl

theorem cell23_1576606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_1576606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576606 prefixEnd_1576606 := by exact prefixLift 1576606
  have htrace : WordTrace (prefixWord ++ tailWord_1576606) baseStart_1576606 baseEnd_1576606 := by
    simpa [prefixWord, tailWord_1576606, baseEnd_1576606] using wordTrace_append hprefix tailTrace_1576606
  have hstable : (prefixWord ++ tailWord_1576606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576606).length < 2 ^ (prefixWord ++ tailWord_1576606).sum := by decide
  have hdescent : baseEnd_1576606 < baseStart_1576606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576607 : List Nat := [1, 1, 2, 7, 1, 1, 3, 1, 2, 1, 3]
def baseStart_1576607 : Nat := 118140960795 + 1576607 * 2 ^ 59
def prefixEnd_1576607 : Nat := 4983230072969 + 3 ^ 40 * 1576607 * 2
def baseEnd_1576607 : Nat := 809557194243218251561823

theorem tailTrace_1576607 : CollatzResearch.WordTrace tailWord_1576607 prefixEnd_1576607 809557194243218251561823 := by
  unfold tailWord_1576607
  simp only [CollatzResearch.WordTrace]
  refine ⟨57503581399229576883584075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38335720932819717922389383 57503581399229576883584075)
  ·
    refine ⟨86255372098844365325376113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57503581399229576883584075 86255372098844365325376113)
    ·
      refine ⟨64691529074133273994032085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86255372098844365325376113 64691529074133273994032085)
      ·
        refine ⟨1516207712674998609235127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 64691529074133273994032085 1516207712674998609235127)
        ·
          refine ⟨2274311569012497913852691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1516207712674998609235127 2274311569012497913852691)
          ·
            refine ⟨3411467353518746870779037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2274311569012497913852691 3411467353518746870779037)
            ·
              refine ⟨1279300257569530076542139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3411467353518746870779037 1279300257569530076542139)
              ·
                refine ⟨1918950386354295114813209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1279300257569530076542139 1918950386354295114813209)
                ·
                  refine ⟨1439212789765721336109907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1918950386354295114813209 1439212789765721336109907)
                  ·
                    refine ⟨2158819184648582004164861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1439212789765721336109907 2158819184648582004164861)
                    ·
                      refine ⟨809557194243218251561823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2158819184648582004164861 809557194243218251561823)
                      ·
                        rfl

theorem cell23_1576607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_1576607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576607 prefixEnd_1576607 := by exact prefixLift 1576607
  have htrace : WordTrace (prefixWord ++ tailWord_1576607) baseStart_1576607 baseEnd_1576607 := by
    simpa [prefixWord, tailWord_1576607, baseEnd_1576607] using wordTrace_append hprefix tailTrace_1576607
  have hstable : (prefixWord ++ tailWord_1576607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576607).length < 2 ^ (prefixWord ++ tailWord_1576607).sum := by decide
  have hdescent : baseEnd_1576607 < baseStart_1576607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576613 : List Nat := [1, 3, 1, 2, 1, 2, 2, 5, 2, 2, 2]
def baseStart_1576613 : Nat := 118140960795 + 1576613 * 2 ^ 59
def prefixEnd_1576613 : Nat := 4983230072969 + 3 ^ 40 * 1576613 * 2
def baseEnd_1576613 : Nat := 809560275127145228086795

theorem tailTrace_1576613 : CollatzResearch.WordTrace tailWord_1576613 prefixEnd_1576613 809560275127145228086795 := by
  unfold tailWord_1576613
  simp only [CollatzResearch.WordTrace]
  refine ⟨57503800237207839908302493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38335866824805226605534995 57503800237207839908302493)
  ·
    refine ⟨21563925088952939965613435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57503800237207839908302493 21563925088952939965613435)
    ·
      refine ⟨32345887633429409948420153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21563925088952939965613435 32345887633429409948420153)
      ·
        refine ⟨24259415725072057461315115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32345887633429409948420153 24259415725072057461315115)
        ·
          refine ⟨36389123587608086191972673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24259415725072057461315115 36389123587608086191972673)
          ·
            refine ⟨27291842690706064643979505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36389123587608086191972673 27291842690706064643979505)
            ·
              refine ⟨20468882018029548482984629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27291842690706064643979505 20468882018029548482984629)
              ·
                refine ⟨1918957689190270170279809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20468882018029548482984629 1918957689190270170279809)
                ·
                  refine ⟨1439218266892702627709857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1918957689190270170279809 1439218266892702627709857)
                  ·
                    refine ⟨1079413700169526970782393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1439218266892702627709857 1079413700169526970782393)
                    ·
                      refine ⟨809560275127145228086795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1079413700169526970782393 809560275127145228086795)
                      ·
                        rfl

theorem cell23_1576613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 2, 2, 2].length) (baseStart_1576613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576613 prefixEnd_1576613 := by exact prefixLift 1576613
  have htrace : WordTrace (prefixWord ++ tailWord_1576613) baseStart_1576613 baseEnd_1576613 := by
    simpa [prefixWord, tailWord_1576613, baseEnd_1576613] using wordTrace_append hprefix tailTrace_1576613
  have hstable : (prefixWord ++ tailWord_1576613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576613).length < 2 ^ (prefixWord ++ tailWord_1576613).sum := by decide
  have hdescent : baseEnd_1576613 < baseStart_1576613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576653 : List Nat := [1, 6, 2, 1, 1, 1, 3, 1, 7]
def baseStart_1576653 : Nat := 118140960795 + 1576653 * 2 ^ 59
def prefixEnd_1576653 : Nat := 4983230072969 + 3 ^ 40 * 1576653 * 2
def baseEnd_1576653 : Nat := 89953423817036119065179

theorem tailTrace_1576653 : CollatzResearch.WordTrace tailWord_1576653 prefixEnd_1576653 89953423817036119065179 := by
  unfold tailWord_1576653
  simp only [CollatzResearch.WordTrace]
  refine ⟨57505259157062926739758613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38336839438041951159839075 57505259157062926739758613)
  ·
    refine ⟨2695559022987324690926185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 57505259157062926739758613 2695559022987324690926185)
    ·
      refine ⟨2021669267240493518194639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2695559022987324690926185 2021669267240493518194639)
      ·
        refine ⟨3032503900860740277291959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2021669267240493518194639 3032503900860740277291959)
        ·
          refine ⟨4548755851291110415937939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3032503900860740277291959 4548755851291110415937939)
          ·
            refine ⟨6823133776936665623906909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4548755851291110415937939 6823133776936665623906909)
            ·
              refine ⟨2558675166351249608965091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6823133776936665623906909 2558675166351249608965091)
              ·
                refine ⟨3838012749526874413447637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2558675166351249608965091 3838012749526874413447637)
                ·
                  refine ⟨89953423817036119065179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3838012749526874413447637 89953423817036119065179)
                  ·
                    rfl

theorem cell23_1576653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_1576653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576653 prefixEnd_1576653 := by exact prefixLift 1576653
  have htrace : WordTrace (prefixWord ++ tailWord_1576653) baseStart_1576653 baseEnd_1576653 := by
    simpa [prefixWord, tailWord_1576653, baseEnd_1576653] using wordTrace_append hprefix tailTrace_1576653
  have hstable : (prefixWord ++ tailWord_1576653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576653).length < 2 ^ (prefixWord ++ tailWord_1576653).sum := by decide
  have hdescent : baseEnd_1576653 < baseStart_1576653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576706 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 2, 3, 5]
def baseStart_1576706 : Nat := 118140960795 + 1576706 * 2 ^ 59
def prefixEnd_1576706 : Nat := 4983230072969 + 3 ^ 40 * 1576706 * 2
def baseEnd_1576706 : Nat := 809608028828013364223867

theorem tailTrace_1576706 : CollatzResearch.WordTrace tailWord_1576706 prefixEnd_1576706 809608028828013364223867 := by
  unfold tailWord_1576706
  simp only [CollatzResearch.WordTrace]
  refine ⟨14376798056467729197859493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38338128150580611194291981 14376798056467729197859493)
  ·
    refine ⟨2695649635587699224598655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14376798056467729197859493 2695649635587699224598655)
    ·
      refine ⟨4043474453381548836897983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2695649635587699224598655 4043474453381548836897983)
      ·
        refine ⟨6065211680072323255346975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4043474453381548836897983 6065211680072323255346975)
        ·
          refine ⟨9097817520108484883020463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6065211680072323255346975 9097817520108484883020463)
          ·
            refine ⟨13646726280162727324530695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9097817520108484883020463 13646726280162727324530695)
            ·
              refine ⟨20470089420244090986796043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13646726280162727324530695 20470089420244090986796043)
              ·
                refine ⟨30705134130366136480194065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20470089420244090986796043 30705134130366136480194065)
                ·
                  refine ⟨23028850597774602360145549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30705134130366136480194065 23028850597774602360145549)
                  ·
                    refine ⟨8635818974165475885054581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23028850597774602360145549 8635818974165475885054581)
                    ·
                      refine ⟨809608028828013364223867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8635818974165475885054581 809608028828013364223867)
                      ·
                        rfl

theorem cell23_1576706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_1576706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576706 prefixEnd_1576706 := by exact prefixLift 1576706
  have htrace : WordTrace (prefixWord ++ tailWord_1576706) baseStart_1576706 baseEnd_1576706 := by
    simpa [prefixWord, tailWord_1576706, baseEnd_1576706] using wordTrace_append hprefix tailTrace_1576706
  have hstable : (prefixWord ++ tailWord_1576706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576706).length < 2 ^ (prefixWord ++ tailWord_1576706).sum := by decide
  have hdescent : baseEnd_1576706 < baseStart_1576706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576734 : List Nat := [4, 3, 2, 2, 2, 1, 1, 1, 2, 5]
def baseStart_1576734 : Nat := 118140960795 + 1576734 * 2 ^ 59
def prefixEnd_1576734 : Nat := 4983230072969 + 3 ^ 40 * 1576734 * 2
def baseEnd_1576734 : Nat := 269874135428779751557913

theorem tailTrace_1576734 : CollatzResearch.WordTrace tailWord_1576734 prefixEnd_1576734 269874135428779751557913 := by
  unfold tailWord_1576734
  simp only [CollatzResearch.WordTrace]
  refine ⟨7188526683721184696682157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38338808979846318382304837 7188526683721184696682157)
  ·
    refine ⟨2695697506395444261255809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7188526683721184696682157 2695697506395444261255809)
    ·
      refine ⟨2021773129796583195941857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2695697506395444261255809 2021773129796583195941857)
      ·
        refine ⟨1516329847347437396956393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2021773129796583195941857 1516329847347437396956393)
        ·
          refine ⟨1137247385510578047717295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1516329847347437396956393 1137247385510578047717295)
          ·
            refine ⟨1705871078265867071575943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1137247385510578047717295 1705871078265867071575943)
            ·
              refine ⟨2558806617398800607363915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1705871078265867071575943 2558806617398800607363915)
              ·
                refine ⟨3838209926098200911045873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2558806617398800607363915 3838209926098200911045873)
                ·
                  refine ⟨2878657444573650683284405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3838209926098200911045873 2878657444573650683284405)
                  ·
                    refine ⟨269874135428779751557913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2878657444573650683284405 269874135428779751557913)
                    ·
                      rfl

theorem cell23_1576734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_1576734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576734 prefixEnd_1576734 := by exact prefixLift 1576734
  have htrace : WordTrace (prefixWord ++ tailWord_1576734) baseStart_1576734 baseEnd_1576734 := by
    simpa [prefixWord, tailWord_1576734, baseEnd_1576734] using wordTrace_append hprefix tailTrace_1576734
  have hstable : (prefixWord ++ tailWord_1576734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576734).length < 2 ^ (prefixWord ++ tailWord_1576734).sum := by decide
  have hdescent : baseEnd_1576734 < baseStart_1576734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576740 : List Nat := [2, 3, 1, 3, 2, 3, 1, 1, 2, 2, 3]
def baseStart_1576740 : Nat := 118140960795 + 1576740 * 2 ^ 59
def prefixEnd_1576740 : Nat := 4983230072969 + 3 ^ 40 * 1576740 * 2
def baseEnd_1576740 : Nat := 809625487170266231198711

theorem tailTrace_1576740 : CollatzResearch.WordTrace tailWord_1576740 prefixEnd_1576740 809625487170266231198711 := by
  unfold tailWord_1576740
  simp only [CollatzResearch.WordTrace]
  refine ⟨28754216153873870299087837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38338954871831827065450449 28754216153873870299087837)
  ·
    refine ⟨10782831057702701362157939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28754216153873870299087837 10782831057702701362157939)
    ·
      refine ⟨16174246586554052043236909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10782831057702701362157939 16174246586554052043236909)
      ·
        refine ⟨6065342469957769516213841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16174246586554052043236909 6065342469957769516213841)
        ·
          refine ⟨4549006852468327137160381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6065342469957769516213841 4549006852468327137160381)
          ·
            refine ⟨1705877569675622676435143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4549006852468327137160381 1705877569675622676435143)
            ·
              refine ⟨2558816354513434014652715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1705877569675622676435143 2558816354513434014652715)
              ·
                refine ⟨3838224531770151021979073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2558816354513434014652715 3838224531770151021979073)
                ·
                  refine ⟨2878668398827613266484305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3838224531770151021979073 2878668398827613266484305)
                  ·
                    refine ⟨2159001299120709949863229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2878668398827613266484305 2159001299120709949863229)
                    ·
                      refine ⟨809625487170266231198711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2159001299120709949863229 809625487170266231198711)
                      ·
                        rfl

theorem cell23_1576740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_1576740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576740 prefixEnd_1576740 := by exact prefixLift 1576740
  have htrace : WordTrace (prefixWord ++ tailWord_1576740) baseStart_1576740 baseEnd_1576740 := by
    simpa [prefixWord, tailWord_1576740, baseEnd_1576740] using wordTrace_append hprefix tailTrace_1576740
  have hstable : (prefixWord ++ tailWord_1576740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576740).length < 2 ^ (prefixWord ++ tailWord_1576740).sum := by decide
  have hdescent : baseEnd_1576740 < baseStart_1576740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576793 : List Nat := [1, 2, 1, 2, 2, 3, 4, 2, 1, 1, 4]
def baseStart_1576793 : Nat := 118140960795 + 1576793 * 2 ^ 59
def prefixEnd_1576793 : Nat := 4983230072969 + 3 ^ 40 * 1576793 * 2
def baseEnd_1576793 : Nat := 809652701644954523835967

theorem tailTrace_1576793 : CollatzResearch.WordTrace tailWord_1576793 prefixEnd_1576793 809652701644954523835967 := by
  unfold tailWord_1576793
  simp only [CollatzResearch.WordTrace]
  refine ⟨57510365376555730649855033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38340243584370487099903355 57510365376555730649855033)
  ·
    refine ⟨43132774032416797987391275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57510365376555730649855033 43132774032416797987391275)
    ·
      refine ⟨64699161048625196981086913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43132774032416797987391275 64699161048625196981086913)
      ·
        refine ⟨48524370786468897735815185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64699161048625196981086913 48524370786468897735815185)
        ·
          refine ⟨36393278089851673301861389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48524370786468897735815185 36393278089851673301861389)
          ·
            refine ⟨13647479283694377488198021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36393278089851673301861389 13647479283694377488198021)
            ·
              refine ⟨2558902365692695779037129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13647479283694377488198021 2558902365692695779037129)
              ·
                refine ⟨1919176774269521834277847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2558902365692695779037129 1919176774269521834277847)
                ·
                  refine ⟨2878765161404282751416771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1919176774269521834277847 2878765161404282751416771)
                  ·
                    refine ⟨4318147742106424127125157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2878765161404282751416771 4318147742106424127125157)
                    ·
                      refine ⟨809652701644954523835967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4318147742106424127125157 809652701644954523835967)
                      ·
                        rfl

theorem cell23_1576793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 1, 4].length) (baseStart_1576793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576793 prefixEnd_1576793 := by exact prefixLift 1576793
  have htrace : WordTrace (prefixWord ++ tailWord_1576793) baseStart_1576793 baseEnd_1576793 := by
    simpa [prefixWord, tailWord_1576793, baseEnd_1576793] using wordTrace_append hprefix tailTrace_1576793
  have hstable : (prefixWord ++ tailWord_1576793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576793).length < 2 ^ (prefixWord ++ tailWord_1576793).sum := by decide
  have hdescent : baseEnd_1576793 < baseStart_1576793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576804 : List Nat := [2, 3, 1, 1, 5, 2, 1, 3, 1, 1, 3]
def baseStart_1576804 : Nat := 118140960795 + 1576804 * 2 ^ 59
def prefixEnd_1576804 : Nat := 4983230072969 + 3 ^ 40 * 1576804 * 2
def baseEnd_1576804 : Nat := 809658349932153980798417

theorem tailTrace_1576804 : CollatzResearch.WordTrace tailWord_1576804 prefixEnd_1576804 809658349932153980798417 := by
  unfold tailWord_1576804
  simp only [CollatzResearch.WordTrace]
  refine ⟨28755383289757939764252733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38340511053010586352336977 28755383289757939764252733)
  ·
    refine ⟨10783268733659227411594775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28755383289757939764252733 10783268733659227411594775)
    ·
      refine ⟨16174903100488841117392163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10783268733659227411594775 16174903100488841117392163)
      ·
        refine ⟨24262354650733261676088245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16174903100488841117392163 24262354650733261676088245)
        ·
          refine ⟨2274595748506243282133273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24262354650733261676088245 2274595748506243282133273)
          ·
            refine ⟨1705946811379682461599955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2274595748506243282133273 1705946811379682461599955)
            ·
              refine ⟨2558920217069523692399933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1705946811379682461599955 2558920217069523692399933)
              ·
                refine ⟨959595081401071384649975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2558920217069523692399933 959595081401071384649975)
                ·
                  refine ⟨1439392622101607076974963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 959595081401071384649975 1439392622101607076974963)
                  ·
                    refine ⟨2159088933152410615462445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1439392622101607076974963 2159088933152410615462445)
                    ·
                      refine ⟨809658349932153980798417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2159088933152410615462445 809658349932153980798417)
                      ·
                        rfl

theorem cell23_1576804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 3, 1, 1, 3].length) (baseStart_1576804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576804 prefixEnd_1576804 := by exact prefixLift 1576804
  have htrace : WordTrace (prefixWord ++ tailWord_1576804) baseStart_1576804 baseEnd_1576804 := by
    simpa [prefixWord, tailWord_1576804, baseEnd_1576804] using wordTrace_append hprefix tailTrace_1576804
  have hstable : (prefixWord ++ tailWord_1576804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576804).length < 2 ^ (prefixWord ++ tailWord_1576804).sum := by decide
  have hdescent : baseEnd_1576804 < baseStart_1576804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576830 : List Nat := [4, 2, 3, 1, 1, 1, 2, 2, 1, 1, 5]
def baseStart_1576830 : Nat := 118140960795 + 1576830 * 2 ^ 59
def prefixEnd_1576830 : Nat := 4983230072969 + 3 ^ 40 * 1576830 * 2
def baseEnd_1576830 : Nat := 809671700429170879073297

theorem tailTrace_1576830 : CollatzResearch.WordTrace tailWord_1576830 prefixEnd_1576830 809671700429170879073297 := by
  unfold tailWord_1576830
  simp only [CollatzResearch.WordTrace]
  refine ⟨7188964359677710746118993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38341143251614457312634629 7188964359677710746118993)
  ·
    refine ⟨5391723269758283059589245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7188964359677710746118993 5391723269758283059589245)
    ·
      refine ⟨2021896226159356147345967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5391723269758283059589245 2021896226159356147345967)
      ·
        refine ⟨3032844339239034221018951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2021896226159356147345967 3032844339239034221018951)
        ·
          refine ⟨4549266508858551331528427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3032844339239034221018951 4549266508858551331528427)
          ·
            refine ⟨6823899763287826997292641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4549266508858551331528427 6823899763287826997292641)
            ·
              refine ⟨5117924822465870247969481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6823899763287826997292641 5117924822465870247969481)
              ·
                refine ⟨3838443616849402685977111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5117924822465870247969481 3838443616849402685977111)
                ·
                  refine ⟨5757665425274104028965667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3838443616849402685977111 5757665425274104028965667)
                  ·
                    refine ⟨8636498137911156043448501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5757665425274104028965667 8636498137911156043448501)
                    ·
                      refine ⟨809671700429170879073297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8636498137911156043448501 809671700429170879073297)
                      ·
                        rfl

theorem cell23_1576830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_1576830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576830 prefixEnd_1576830 := by exact prefixLift 1576830
  have htrace : WordTrace (prefixWord ++ tailWord_1576830) baseStart_1576830 baseEnd_1576830 := by
    simpa [prefixWord, tailWord_1576830, baseEnd_1576830] using wordTrace_append hprefix tailTrace_1576830
  have hstable : (prefixWord ++ tailWord_1576830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576830).length < 2 ^ (prefixWord ++ tailWord_1576830).sum := by decide
  have hdescent : baseEnd_1576830 < baseStart_1576830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576860 : List Nat := [2, 2, 3, 3, 1, 2, 1, 2, 1, 3, 3]
def baseStart_1576860 : Nat := 118140960795 + 1576860 * 2 ^ 59
def prefixEnd_1576860 : Nat := 4983230072969 + 3 ^ 40 * 1576860 * 2
def baseEnd_1576860 : Nat := 809687104848805761698159

theorem tailTrace_1576860 : CollatzResearch.WordTrace tailWord_1576860 prefixEnd_1576860 809687104848805761698159 := by
  unfold tailWord_1576860
  simp only [CollatzResearch.WordTrace]
  refine ⟨28756404533656500546272017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38341872711542000728362689 28756404533656500546272017)
  ·
    refine ⟨21567303400242375409704013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28756404533656500546272017 21567303400242375409704013)
    ·
      refine ⟨8087738775090890778639005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21567303400242375409704013 8087738775090890778639005)
      ·
        refine ⟨3032902040659084041989627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8087738775090890778639005 3032902040659084041989627)
        ·
          refine ⟨4549353060988626062984441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3032902040659084041989627 4549353060988626062984441)
          ·
            refine ⟨3412014795741469547238331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4549353060988626062984441 3412014795741469547238331)
            ·
              refine ⟨5118022193612204320857497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3412014795741469547238331 5118022193612204320857497)
              ·
                refine ⟨3838516645209153240643123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5118022193612204320857497 3838516645209153240643123)
                ·
                  refine ⟨5757774967813729860964685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3838516645209153240643123 5757774967813729860964685)
                  ·
                    refine ⟨2159165612930148697861757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5757774967813729860964685 2159165612930148697861757)
                    ·
                      refine ⟨809687104848805761698159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2159165612930148697861757 809687104848805761698159)
                      ·
                        rfl

theorem cell23_1576860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_1576860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576860 prefixEnd_1576860 := by exact prefixLift 1576860
  have htrace : WordTrace (prefixWord ++ tailWord_1576860) baseStart_1576860 baseEnd_1576860 := by
    simpa [prefixWord, tailWord_1576860, baseEnd_1576860] using wordTrace_append hprefix tailTrace_1576860
  have hstable : (prefixWord ++ tailWord_1576860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576860).length < 2 ^ (prefixWord ++ tailWord_1576860).sum := by decide
  have hdescent : baseEnd_1576860 < baseStart_1576860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576883 : List Nat := [1, 1, 1, 2, 3, 1, 3, 2, 3, 4, 2]
def baseStart_1576883 : Nat := 118140960795 + 1576883 * 2 ^ 59
def prefixEnd_1576883 : Nat := 4983230072969 + 3 ^ 40 * 1576883 * 2
def baseEnd_1576883 : Nat := 809698914903859171710553

theorem tailTrace_1576883 : CollatzResearch.WordTrace tailWord_1576883 prefixEnd_1576883 809698914903859171710553 := by
  unfold tailWord_1576883
  simp only [CollatzResearch.WordTrace]
  refine ⟨57513647946229676020631303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38342431964153117347087535 57513647946229676020631303)
  ·
    refine ⟨86270471919344514030946955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57513647946229676020631303 86270471919344514030946955)
    ·
      refine ⟨129405707879016771046420433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86270471919344514030946955 129405707879016771046420433)
      ·
        refine ⟨97054280909262578284815325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129405707879016771046420433 97054280909262578284815325)
        ·
          refine ⟨36395355340973466856805747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97054280909262578284815325 36395355340973466856805747)
          ·
            refine ⟨54593033011460200285208621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36395355340973466856805747 54593033011460200285208621)
            ·
              refine ⟨20472387379297575106953233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54593033011460200285208621 20472387379297575106953233)
              ·
                refine ⟨15354290534473181330214925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20472387379297575106953233 15354290534473181330214925)
                ·
                  refine ⟨5757858950427442998830597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15354290534473181330214925 5757858950427442998830597)
                  ·
                    refine ⟨1079598553205145562280737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5757858950427442998830597 1079598553205145562280737)
                    ·
                      refine ⟨809698914903859171710553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1079598553205145562280737 809698914903859171710553)
                      ·
                        rfl

theorem cell23_1576883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 4, 2].length) (baseStart_1576883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576883 prefixEnd_1576883 := by exact prefixLift 1576883
  have htrace : WordTrace (prefixWord ++ tailWord_1576883) baseStart_1576883 baseEnd_1576883 := by
    simpa [prefixWord, tailWord_1576883, baseEnd_1576883] using wordTrace_append hprefix tailTrace_1576883
  have hstable : (prefixWord ++ tailWord_1576883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576883).length < 2 ^ (prefixWord ++ tailWord_1576883).sum := by decide
  have hdescent : baseEnd_1576883 < baseStart_1576883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576893 : List Nat := [1, 4, 1, 2, 3, 2, 1, 1, 2, 6]
def baseStart_1576893 : Nat := 118140960795 + 1576893 * 2 ^ 59
def prefixEnd_1576893 : Nat := 4983230072969 + 3 ^ 40 * 1576893 * 2
def baseEnd_1576893 : Nat := 269901349903468044195169

theorem tailTrace_1576893 : CollatzResearch.WordTrace tailWord_1576893 prefixEnd_1576893 269901349903468044195169 := by
  unfold tailWord_1576893
  simp only [CollatzResearch.WordTrace]
  refine ⟨57514012676193447728495333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38342675117462298485663555 57514012676193447728495333)
  ·
    refine ⟨10783877376786271449092875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57514012676193447728495333 10783877376786271449092875)
    ·
      refine ⟨16175816065179407173639313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10783877376786271449092875 16175816065179407173639313)
      ·
        refine ⟨12131862048884555380229485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16175816065179407173639313 12131862048884555380229485)
        ·
          refine ⟨4549448268331708267586057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12131862048884555380229485 4549448268331708267586057)
          ·
            refine ⟨3412086201248781200689543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4549448268331708267586057 3412086201248781200689543)
            ·
              refine ⟨5118129301873171801034315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3412086201248781200689543 5118129301873171801034315)
              ·
                refine ⟨7677193952809757701551473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5118129301873171801034315 7677193952809757701551473)
                ·
                  refine ⟨5757895464607318276163605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7677193952809757701551473 5757895464607318276163605)
                  ·
                    refine ⟨269901349903468044195169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5757895464607318276163605 269901349903468044195169)
                    ·
                      rfl

theorem cell23_1576893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_1576893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576893 prefixEnd_1576893 := by exact prefixLift 1576893
  have htrace : WordTrace (prefixWord ++ tailWord_1576893) baseStart_1576893 baseEnd_1576893 := by
    simpa [prefixWord, tailWord_1576893, baseEnd_1576893] using wordTrace_append hprefix tailTrace_1576893
  have hstable : (prefixWord ++ tailWord_1576893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576893).length < 2 ^ (prefixWord ++ tailWord_1576893).sum := by decide
  have hdescent : baseEnd_1576893 < baseStart_1576893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576906 : List Nat := [3, 1, 2, 1, 2, 1, 3, 1, 9]
def baseStart_1576906 : Nat := 118140960795 + 1576906 * 2 ^ 59
def prefixEnd_1576906 : Nat := 4983230072969 + 3 ^ 40 * 1576906 * 2
def baseEnd_1576906 : Nat := 89967858328768064635883

theorem tailTrace_1576906 : CollatzResearch.WordTrace tailWord_1576906 prefixEnd_1576906 89967858328768064635883 := by
  unfold tailWord_1576906
  simp only [CollatzResearch.WordTrace]
  refine ⟨14378621706286587737179643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38342991216764233965812381 14378621706286587737179643)
  ·
    refine ⟨21567932559429881605769465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14378621706286587737179643 21567932559429881605769465)
    ·
      refine ⟨16175949419572411204327099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21567932559429881605769465 16175949419572411204327099)
      ·
        refine ⟨24263924129358616806490649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16175949419572411204327099 24263924129358616806490649)
        ·
          refine ⟨18197943097018962604867987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24263924129358616806490649 18197943097018962604867987)
          ·
            refine ⟨27296914645528443907301981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18197943097018962604867987 27296914645528443907301981)
            ·
              refine ⟨10236342992073166465238243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27296914645528443907301981 10236342992073166465238243)
              ·
                refine ⟨15354514488109749697857365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10236342992073166465238243 15354514488109749697857365)
                ·
                  refine ⟨89967858328768064635883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15354514488109749697857365 89967858328768064635883)
                  ·
                    rfl

theorem cell23_1576906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 9].length) (baseStart_1576906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576906 prefixEnd_1576906 := by exact prefixLift 1576906
  have htrace : WordTrace (prefixWord ++ tailWord_1576906) baseStart_1576906 baseEnd_1576906 := by
    simpa [prefixWord, tailWord_1576906, baseEnd_1576906] using wordTrace_append hprefix tailTrace_1576906
  have hstable : (prefixWord ++ tailWord_1576906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576906).length < 2 ^ (prefixWord ++ tailWord_1576906).sum := by decide
  have hdescent : baseEnd_1576906 < baseStart_1576906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576921 : List Nat := [1, 2, 1, 2, 7, 1, 2, 1, 1, 3, 2]
def baseStart_1576921 : Nat := 118140960795 + 1576921 * 2 ^ 59
def prefixEnd_1576921 : Nat := 4983230072969 + 3 ^ 40 * 1576921 * 2
def baseEnd_1576921 : Nat := 809718427168730023035379

theorem tailTrace_1576921 : CollatzResearch.WordTrace tailWord_1576921 prefixEnd_1576921 809718427168730023035379 := by
  unfold tailWord_1576921
  simp only [CollatzResearch.WordTrace]
  refine ⟨57515033920092008510514617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38343355946728005673676411 57515033920092008510514617)
  ·
    refine ⟨43136275440069006382885963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57515033920092008510514617 43136275440069006382885963)
    ·
      refine ⟨64704413160103509574328945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43136275440069006382885963 64704413160103509574328945)
      ·
        refine ⟨48528309870077632180746709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64704413160103509574328945 48528309870077632180746709)
        ·
          refine ⟨1137382262579944504236251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 48528309870077632180746709 1137382262579944504236251)
          ·
            refine ⟨1706073393869916756354377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1137382262579944504236251 1706073393869916756354377)
            ·
              refine ⟨1279555045402437567265783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1706073393869916756354377 1279555045402437567265783)
              ·
                refine ⟨1919332568103656350898675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1279555045402437567265783 1919332568103656350898675)
                ·
                  refine ⟨2878998852155484526348013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1919332568103656350898675 2878998852155484526348013)
                  ·
                    refine ⟨1079624569558306697380505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2878998852155484526348013 1079624569558306697380505)
                    ·
                      refine ⟨809718427168730023035379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1079624569558306697380505 809718427168730023035379)
                      ·
                        rfl

theorem cell23_1576921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 1, 3, 2].length) (baseStart_1576921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1576921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1576921 prefixEnd_1576921 := by exact prefixLift 1576921
  have htrace : WordTrace (prefixWord ++ tailWord_1576921) baseStart_1576921 baseEnd_1576921 := by
    simpa [prefixWord, tailWord_1576921, baseEnd_1576921] using wordTrace_append hprefix tailTrace_1576921
  have hstable : (prefixWord ++ tailWord_1576921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576921).length < 2 ^ (prefixWord ++ tailWord_1576921).sum := by decide
  have hdescent : baseEnd_1576921 < baseStart_1576921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577023 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 2, 5, 3]
def baseStart_1577023 : Nat := 118140960795 + 1577023 * 2 ^ 59
def prefixEnd_1577023 : Nat := 4983230072969 + 3 ^ 40 * 1577023 * 2
def baseEnd_1577023 : Nat := 809770802195488623959909

theorem tailTrace_1577023 : CollatzResearch.WordTrace tailWord_1577023 prefixEnd_1577023 809770802195488623959909 := by
  unfold tailWord_1577023
  simp only [CollatzResearch.WordTrace]
  refine ⟨57518754165722479930727723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38345836110481653287151815 57518754165722479930727723)
  ·
    refine ⟨86278131248583719896091585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57518754165722479930727723 86278131248583719896091585)
    ·
      refine ⟨64708598436437789922068689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86278131248583719896091585 64708598436437789922068689)
      ·
        refine ⟨48531448827328342441551517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64708598436437789922068689 48531448827328342441551517)
        ·
          refine ⟨18199293310248128415581819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48531448827328342441551517 18199293310248128415581819)
          ·
            refine ⟨27298939965372192623372729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18199293310248128415581819 27298939965372192623372729)
            ·
              refine ⟨20474204974029144467529547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27298939965372192623372729 20474204974029144467529547)
              ·
                refine ⟨30711307461043716701294321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20474204974029144467529547 30711307461043716701294321)
                ·
                  refine ⟨23033480595782787525970741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30711307461043716701294321 23033480595782787525970741)
                  ·
                    refine ⟨2159388805854636330559757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23033480595782787525970741 2159388805854636330559757)
                    ·
                      refine ⟨809770802195488623959909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2159388805854636330559757 809770802195488623959909)
                      ·
                        rfl

theorem cell23_1577023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 5, 3].length) (baseStart_1577023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577023 prefixEnd_1577023 := by exact prefixLift 1577023
  have htrace : WordTrace (prefixWord ++ tailWord_1577023) baseStart_1577023 baseEnd_1577023 := by
    simpa [prefixWord, tailWord_1577023, baseEnd_1577023] using wordTrace_append hprefix tailTrace_1577023
  have hstable : (prefixWord ++ tailWord_1577023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577023).length < 2 ^ (prefixWord ++ tailWord_1577023).sum := by decide
  have hdescent : baseEnd_1577023 < baseStart_1577023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577080 : List Nat := [2, 1, 2, 1, 1, 1, 3, 6, 1, 1, 4]
def baseStart_1577080 : Nat := 118140960795 + 1577080 * 2 ^ 59
def prefixEnd_1577080 : Nat := 4983230072969 + 3 ^ 40 * 1577080 * 2
def baseEnd_1577080 : Nat := 809800070592794900947147

theorem tailTrace_1577080 : CollatzResearch.WordTrace tailWord_1577080 prefixEnd_1577080 809800070592794900947147 := by
  unfold tailWord_1577080
  simp only [CollatzResearch.WordTrace]
  refine ⟨28760416563257989332776347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38347222084343985777035129 28760416563257989332776347)
  ·
    refine ⟨43140624844886983999164521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28760416563257989332776347 43140624844886983999164521)
    ·
      refine ⟨32355468633665237999373391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43140624844886983999164521 32355468633665237999373391)
      ·
        refine ⟨48533202950497856999060087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32355468633665237999373391 48533202950497856999060087)
        ·
          refine ⟨72799804425746785498590131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48533202950497856999060087 72799804425746785498590131)
          ·
            refine ⟨109199706638620178247885197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72799804425746785498590131 109199706638620178247885197)
            ·
              refine ⟨40949889989482566842956949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109199706638620178247885197 40949889989482566842956949)
              ·
                refine ⟨1919526093256995320763607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40949889989482566842956949 1919526093256995320763607)
                ·
                  refine ⟨2879289139885492981145411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1919526093256995320763607 2879289139885492981145411)
                  ·
                    refine ⟨4318933709828239471718117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2879289139885492981145411 4318933709828239471718117)
                    ·
                      refine ⟨809800070592794900947147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4318933709828239471718117 809800070592794900947147)
                      ·
                        rfl

theorem cell23_1577080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 1, 1, 4].length) (baseStart_1577080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577080 prefixEnd_1577080 := by exact prefixLift 1577080
  have htrace : WordTrace (prefixWord ++ tailWord_1577080) baseStart_1577080 baseEnd_1577080 := by
    simpa [prefixWord, tailWord_1577080, baseEnd_1577080] using wordTrace_append hprefix tailTrace_1577080
  have hstable : (prefixWord ++ tailWord_1577080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577080).length < 2 ^ (prefixWord ++ tailWord_1577080).sum := by decide
  have hdescent : baseEnd_1577080 < baseStart_1577080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577084 : List Nat := [2, 2, 2, 1, 1, 6, 1, 1, 2, 3, 2]
def baseStart_1577084 : Nat := 118140960795 + 1577084 * 2 ^ 59
def prefixEnd_1577084 : Nat := 4983230072969 + 3 ^ 40 * 1577084 * 2
def baseEnd_1577084 : Nat := 809802124515412885297129

theorem tailTrace_1577084 : CollatzResearch.WordTrace tailWord_1577084 prefixEnd_1577084 809802124515412885297129 := by
  unfold tailWord_1577084
  simp only [CollatzResearch.WordTrace]
  refine ⟨28760489509250743674349153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38347319345667658232465537 28760489509250743674349153)
  ·
    refine ⟨21570367131938057755761865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28760489509250743674349153 21570367131938057755761865)
    ·
      refine ⟨16177775348953543316821399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21570367131938057755761865 16177775348953543316821399)
      ·
        refine ⟨24266663023430314975232099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16177775348953543316821399 24266663023430314975232099)
        ·
          refine ⟨36399994535145472462848149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24266663023430314975232099 36399994535145472462848149)
          ·
            refine ⟨1706249743834944021696007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 36399994535145472462848149 1706249743834944021696007)
            ·
              refine ⟨2559374615752416032544011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1706249743834944021696007 2559374615752416032544011)
              ·
                refine ⟨3839061923628624048816017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2559374615752416032544011 3839061923628624048816017)
                ·
                  refine ⟨2879296442721468036612013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3839061923628624048816017 2879296442721468036612013)
                  ·
                    refine ⟨1079736166020550513729505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2879296442721468036612013 1079736166020550513729505)
                    ·
                      refine ⟨809802124515412885297129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1079736166020550513729505 809802124515412885297129)
                      ·
                        rfl

theorem cell23_1577084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 2, 3, 2].length) (baseStart_1577084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577084 prefixEnd_1577084 := by exact prefixLift 1577084
  have htrace : WordTrace (prefixWord ++ tailWord_1577084) baseStart_1577084 baseEnd_1577084 := by
    simpa [prefixWord, tailWord_1577084, baseEnd_1577084] using wordTrace_append hprefix tailTrace_1577084
  have hstable : (prefixWord ++ tailWord_1577084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577084).length < 2 ^ (prefixWord ++ tailWord_1577084).sum := by decide
  have hdescent : baseEnd_1577084 < baseStart_1577084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577097 : List Nat := [1, 2, 1, 1, 4, 2, 1, 2, 5, 2, 2]
def baseStart_1577097 : Nat := 118140960795 + 1577097 * 2 ^ 59
def prefixEnd_1577097 : Nat := 4983230072969 + 3 ^ 40 * 1577097 * 2
def baseEnd_1577097 : Nat := 809808799763921334434569

theorem tailTrace_1577097 : CollatzResearch.WordTrace tailWord_1577097 prefixEnd_1577097 809808799763921334434569 := by
  unfold tailWord_1577097
  simp only [CollatzResearch.WordTrace]
  refine ⟨57521453167454390568921545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38347635444969593712614363 57521453167454390568921545)
  ·
    refine ⟨43141089875590792926691159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57521453167454390568921545 43141089875590792926691159)
    ·
      refine ⟨64711634813386189390036739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43141089875590792926691159 64711634813386189390036739)
      ·
        refine ⟨97067452220079284085055109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64711634813386189390036739 97067452220079284085055109)
        ·
          refine ⟨18200147291264865765947833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97067452220079284085055109 18200147291264865765947833)
          ·
            refine ⟨13650110468448649324460875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18200147291264865765947833 13650110468448649324460875)
            ·
              refine ⟨20475165702672973986691313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13650110468448649324460875 20475165702672973986691313)
              ·
                refine ⟨15356374277004730490018485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20475165702672973986691313 15356374277004730490018485)
                ·
                  refine ⟨1439660088469193483439233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15356374277004730490018485 1439660088469193483439233)
                  ·
                    refine ⟨1079745066351895112579425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1439660088469193483439233 1079745066351895112579425)
                    ·
                      refine ⟨809808799763921334434569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1079745066351895112579425 809808799763921334434569)
                      ·
                        rfl

theorem cell23_1577097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 5, 2, 2].length) (baseStart_1577097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577097 prefixEnd_1577097 := by exact prefixLift 1577097
  have htrace : WordTrace (prefixWord ++ tailWord_1577097) baseStart_1577097 baseEnd_1577097 := by
    simpa [prefixWord, tailWord_1577097, baseEnd_1577097] using wordTrace_append hprefix tailTrace_1577097
  have hstable : (prefixWord ++ tailWord_1577097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577097).length < 2 ^ (prefixWord ++ tailWord_1577097).sum := by decide
  have hdescent : baseEnd_1577097 < baseStart_1577097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577124 : List Nat := [2, 3, 1, 2, 5, 1, 1, 1, 1, 6]
def baseStart_1577124 : Nat := 118140960795 + 1577124 * 2 ^ 59
def prefixEnd_1577124 : Nat := 4983230072969 + 3 ^ 40 * 1577124 * 2
def baseEnd_1577124 : Nat := 269940887913864242932315

theorem tailTrace_1577124 : CollatzResearch.WordTrace tailWord_1577124 prefixEnd_1577124 269940887913864242932315 := by
  unfold tailWord_1577124
  simp only [CollatzResearch.WordTrace]
  refine ⟨28761218969178287090077213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38348291958904382786769617 28761218969178287090077213)
  ·
    refine ⟨10785457113441857658778955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28761218969178287090077213 10785457113441857658778955)
    ·
      refine ⟨16178185670162786488168433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10785457113441857658778955 16178185670162786488168433)
      ·
        refine ⟨12133639252622089866126325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16178185670162786488168433 12133639252622089866126325)
        ·
          refine ⟨1137528679933320924949343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12133639252622089866126325 1137528679933320924949343)
          ·
            refine ⟨1706293019899981387424015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1137528679933320924949343 1706293019899981387424015)
            ·
              refine ⟨2559439529849972081136023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1706293019899981387424015 2559439529849972081136023)
              ·
                refine ⟨3839159294774958121704035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2559439529849972081136023 3839159294774958121704035)
                ·
                  refine ⟨5758738942162437182556053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3839159294774958121704035 5758738942162437182556053)
                  ·
                    refine ⟨269940887913864242932315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5758738942162437182556053 269940887913864242932315)
                    ·
                      rfl

theorem cell23_1577124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 1, 6].length) (baseStart_1577124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577124 prefixEnd_1577124 := by exact prefixLift 1577124
  have htrace : WordTrace (prefixWord ++ tailWord_1577124) baseStart_1577124 baseEnd_1577124 := by
    simpa [prefixWord, tailWord_1577124, baseEnd_1577124] using wordTrace_append hprefix tailTrace_1577124
  have hstable : (prefixWord ++ tailWord_1577124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577124).length < 2 ^ (prefixWord ++ tailWord_1577124).sum := by decide
  have hdescent : baseEnd_1577124 < baseStart_1577124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577127 : List Nat := [1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 6]
def baseStart_1577127 : Nat := 118140960795 + 1577127 * 2 ^ 59
def prefixEnd_1577127 : Nat := 4983230072969 + 3 ^ 40 * 1577127 * 2
def baseEnd_1577127 : Nat := 809824204183556217059431

theorem tailTrace_1577127 : CollatzResearch.WordTrace tailWord_1577127 prefixEnd_1577127 809824204183556217059431 := by
  unfold tailWord_1577127
  simp only [CollatzResearch.WordTrace]
  refine ⟨57522547357345705692513635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38348364904897137128342423 57522547357345705692513635)
  ·
    refine ⟨86283821036018558538770453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57522547357345705692513635 86283821036018558538770453)
    ·
      refine ⟨4044554111063369931504865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 86283821036018558538770453 4044554111063369931504865)
      ·
        refine ⟨3033415583297527448628649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4044554111063369931504865 3033415583297527448628649)
        ·
          refine ⟨2275061687473145586471487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3033415583297527448628649 2275061687473145586471487)
          ·
            refine ⟨3412592531209718379707231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2275061687473145586471487 3412592531209718379707231)
            ·
              refine ⟨5118888796814577569560847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3412592531209718379707231 5118888796814577569560847)
              ·
                refine ⟨7678333195221866354341271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5118888796814577569560847 7678333195221866354341271)
                ·
                  refine ⟨11517499792832799531511907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7678333195221866354341271 11517499792832799531511907)
                  ·
                    refine ⟨17276249689249199297267861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11517499792832799531511907 17276249689249199297267861)
                    ·
                      refine ⟨809824204183556217059431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17276249689249199297267861 809824204183556217059431)
                      ·
                        rfl

theorem cell23_1577127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_1577127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577127 prefixEnd_1577127 := by exact prefixLift 1577127
  have htrace : WordTrace (prefixWord ++ tailWord_1577127) baseStart_1577127 baseEnd_1577127 := by
    simpa [prefixWord, tailWord_1577127, baseEnd_1577127] using wordTrace_append hprefix tailTrace_1577127
  have hstable : (prefixWord ++ tailWord_1577127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577127).length < 2 ^ (prefixWord ++ tailWord_1577127).sum := by decide
  have hdescent : baseEnd_1577127 < baseStart_1577127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577154 : List Nat := [3, 5, 1, 1, 1, 3, 9]
def baseStart_1577154 : Nat := 118140960795 + 1577154 * 2 ^ 59
def prefixEnd_1577154 : Nat := 4983230072969 + 3 ^ 40 * 1577154 * 2
def baseEnd_1577154 : Nat := 9998000841496637178047

theorem tailTrace_1577154 : CollatzResearch.WordTrace tailWord_1577154 prefixEnd_1577154 9998000841496637178047 := by
  unfold tailWord_1577154
  simp only [CollatzResearch.WordTrace]
  refine ⟨14380883032061972325936629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38349021418831926202497677 14380883032061972325936629)
  ·
    refine ⟨1348207784255809905556559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14380883032061972325936629 1348207784255809905556559)
    ·
      refine ⟨2022311676383714858334839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1348207784255809905556559 2022311676383714858334839)
      ·
        refine ⟨3033467514575572287502259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2022311676383714858334839 3033467514575572287502259)
        ·
          refine ⟨4550201271863358431253389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3033467514575572287502259 4550201271863358431253389)
          ·
            refine ⟨1706325476948759411720021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4550201271863358431253389 1706325476948759411720021)
            ·
              refine ⟨9998000841496637178047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1706325476948759411720021 9998000841496637178047)
              ·
                rfl

theorem cell23_1577154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 9].length) (baseStart_1577154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577154 prefixEnd_1577154 := by exact prefixLift 1577154
  have htrace : WordTrace (prefixWord ++ tailWord_1577154) baseStart_1577154 baseEnd_1577154 := by
    simpa [prefixWord, tailWord_1577154, baseEnd_1577154] using wordTrace_append hprefix tailTrace_1577154
  have hstable : (prefixWord ++ tailWord_1577154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577154).length < 2 ^ (prefixWord ++ tailWord_1577154).sum := by decide
  have hdescent : baseEnd_1577154 < baseStart_1577154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577181 : List Nat := [1, 4, 3, 2, 1, 2, 1, 3, 2, 1, 3]
def baseStart_1577181 : Nat := 118140960795 + 1577181 * 2 ^ 59
def prefixEnd_1577181 : Nat := 4983230072969 + 3 ^ 40 * 1577181 * 2
def baseEnd_1577181 : Nat := 809851932138899005784183

theorem tailTrace_1577181 : CollatzResearch.WordTrace tailWord_1577181 prefixEnd_1577181 809851932138899005784183 := by
  unfold tailWord_1577181
  simp only [CollatzResearch.WordTrace]
  refine ⟨57524516899150072914979397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38349677932766715276652931 57524516899150072914979397)
  ·
    refine ⟨10785846918590638671558637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57524516899150072914979397 10785846918590638671558637)
    ·
      refine ⟨4044692594471489501834489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10785846918590638671558637 4044692594471489501834489)
      ·
        refine ⟨3033519445853617126375867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4044692594471489501834489 3033519445853617126375867)
        ·
          refine ⟨4550279168780425689563801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3033519445853617126375867 4550279168780425689563801)
          ·
            refine ⟨3412709376585319267172851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4550279168780425689563801 3412709376585319267172851)
            ·
              refine ⟨5119064064877978900759277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3412709376585319267172851 5119064064877978900759277)
              ·
                refine ⟨1919649024329242087784729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5119064064877978900759277 1919649024329242087784729)
                ·
                  refine ⟨1439736768246931565838547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1919649024329242087784729 1439736768246931565838547)
                  ·
                    refine ⟨2159605152370397348757821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1439736768246931565838547 2159605152370397348757821)
                    ·
                      refine ⟨809851932138899005784183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2159605152370397348757821 809851932138899005784183)
                      ·
                        rfl

theorem cell23_1577181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_1577181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577181 prefixEnd_1577181 := by exact prefixLift 1577181
  have htrace : WordTrace (prefixWord ++ tailWord_1577181) baseStart_1577181 baseEnd_1577181 := by
    simpa [prefixWord, tailWord_1577181, baseEnd_1577181] using wordTrace_append hprefix tailTrace_1577181
  have hstable : (prefixWord ++ tailWord_1577181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577181).length < 2 ^ (prefixWord ++ tailWord_1577181).sum := by decide
  have hdescent : baseEnd_1577181 < baseStart_1577181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577191 : List Nat := [1, 1, 5, 3, 1, 1, 3, 2, 1, 3, 2]
def baseStart_1577191 : Nat := 118140960795 + 1577191 * 2 ^ 59
def prefixEnd_1577191 : Nat := 4983230072969 + 3 ^ 40 * 1577191 * 2
def baseEnd_1577191 : Nat := 809857066945443966659137

theorem tailTrace_1577191 : CollatzResearch.WordTrace tailWord_1577191 prefixEnd_1577191 809857066945443966659137 := by
  unfold tailWord_1577191
  simp only [CollatzResearch.WordTrace]
  refine ⟨57524881629113844622843427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38349921086075896415228951 57524881629113844622843427)
  ·
    refine ⟨86287322443670766934265141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57524881629113844622843427 86287322443670766934265141)
    ·
      refine ⟨8089436479094134400087357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86287322443670766934265141 8089436479094134400087357)
      ·
        refine ⟨3033538679660300400032759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8089436479094134400087357 3033538679660300400032759)
        ·
          refine ⟨4550308019490450600049139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3033538679660300400032759 4550308019490450600049139)
          ·
            refine ⟨6825462029235675900073709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4550308019490450600049139 6825462029235675900073709)
            ·
              refine ⟨2559548260963378462527641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6825462029235675900073709 2559548260963378462527641)
              ·
                refine ⟨1919661195722533846895731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2559548260963378462527641 1919661195722533846895731)
                ·
                  refine ⟨2879491793583800770343597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1919661195722533846895731 2879491793583800770343597)
                  ·
                    refine ⟨1079809422593925288878849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2879491793583800770343597 1079809422593925288878849)
                    ·
                      refine ⟨809857066945443966659137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1079809422593925288878849 809857066945443966659137)
                      ·
                        rfl

theorem cell23_1577191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_1577191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577191 prefixEnd_1577191 := by exact prefixLift 1577191
  have htrace : WordTrace (prefixWord ++ tailWord_1577191) baseStart_1577191 baseEnd_1577191 := by
    simpa [prefixWord, tailWord_1577191, baseEnd_1577191] using wordTrace_append hprefix tailTrace_1577191
  have hstable : (prefixWord ++ tailWord_1577191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577191).length < 2 ^ (prefixWord ++ tailWord_1577191).sum := by decide
  have hdescent : baseEnd_1577191 < baseStart_1577191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577227 : List Nat := [1, 1, 1, 1, 5, 2, 3, 4, 5]
def baseStart_1577227 : Nat := 118140960795 + 1577227 * 2 ^ 59
def prefixEnd_1577227 : Nat := 4983230072969 + 3 ^ 40 * 1577227 * 2
def baseEnd_1577227 : Nat := 89986172472111758423219

theorem tailTrace_1577227 : CollatzResearch.WordTrace tailWord_1577227 prefixEnd_1577227 89986172472111758423219 := by
  unfold tailWord_1577227
  simp only [CollatzResearch.WordTrace]
  refine ⟨57526194656983422771153935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38350796437988948514102623 57526194656983422771153935)
  ·
    refine ⟨86289291985475134156730903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57526194656983422771153935 86289291985475134156730903)
    ·
      refine ⟨129433937978212701235096355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86289291985475134156730903 129433937978212701235096355)
      ·
        refine ⟨194150906967319051852644533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129433937978212701235096355 194150906967319051852644533)
        ·
          refine ⟨18201647528186161111185425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 194150906967319051852644533 18201647528186161111185425)
          ·
            refine ⟨13651235646139620833389069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18201647528186161111185425 13651235646139620833389069)
            ·
              refine ⟨5119213367302357812520901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13651235646139620833389069 5119213367302357812520901)
              ·
                refine ⟨959852506369192089847669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5119213367302357812520901 959852506369192089847669)
                ·
                  refine ⟨89986172472111758423219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 959852506369192089847669 89986172472111758423219)
                  ·
                    rfl

theorem cell23_1577227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 4, 5].length) (baseStart_1577227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577227 prefixEnd_1577227 := by exact prefixLift 1577227
  have htrace : WordTrace (prefixWord ++ tailWord_1577227) baseStart_1577227 baseEnd_1577227 := by
    simpa [prefixWord, tailWord_1577227, baseEnd_1577227] using wordTrace_append hprefix tailTrace_1577227
  have hstable : (prefixWord ++ tailWord_1577227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577227).length < 2 ^ (prefixWord ++ tailWord_1577227).sum := by decide
  have hdescent : baseEnd_1577227 < baseStart_1577227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577240 : List Nat := [2, 1, 2, 3, 1, 2, 2, 2, 1, 7]
def baseStart_1577240 : Nat := 118140960795 + 1577240 * 2 ^ 59
def prefixEnd_1577240 : Nat := 4983230072969 + 3 ^ 40 * 1577240 * 2
def baseEnd_1577240 : Nat := 269960742499171424982137

theorem tailTrace_1577240 : CollatzResearch.WordTrace tailWord_1577240 prefixEnd_1577240 269960742499171424982137 := by
  unfold tailWord_1577240
  simp only [CollatzResearch.WordTrace]
  refine ⟨28763334402968162995688587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38351112537290883994251449 28763334402968162995688587)
  ·
    refine ⟨43145001604452244493532881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28763334402968162995688587 43145001604452244493532881)
    ·
      refine ⟨32358751203339183370149661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43145001604452244493532881 32358751203339183370149661)
      ·
        refine ⟨12134531701252193763806123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32358751203339183370149661 12134531701252193763806123)
        ·
          refine ⟨18201797551878290645709185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12134531701252193763806123 18201797551878290645709185)
          ·
            refine ⟨13651348163908717984281889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18201797551878290645709185 13651348163908717984281889)
            ·
              refine ⟨10238511122931538488211417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13651348163908717984281889 10238511122931538488211417)
              ·
                refine ⟨7678883342198653866158563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10238511122931538488211417 7678883342198653866158563)
                ·
                  refine ⟨11518325013297980799237845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7678883342198653866158563 11518325013297980799237845)
                  ·
                    refine ⟨269960742499171424982137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11518325013297980799237845 269960742499171424982137)
                    ·
                      rfl

theorem cell23_1577240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 1, 7].length) (baseStart_1577240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577240 prefixEnd_1577240 := by exact prefixLift 1577240
  have htrace : WordTrace (prefixWord ++ tailWord_1577240) baseStart_1577240 baseEnd_1577240 := by
    simpa [prefixWord, tailWord_1577240, baseEnd_1577240] using wordTrace_append hprefix tailTrace_1577240
  have hstable : (prefixWord ++ tailWord_1577240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577240).length < 2 ^ (prefixWord ++ tailWord_1577240).sum := by decide
  have hdescent : baseEnd_1577240 < baseStart_1577240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577297 : List Nat := [1, 2, 2, 1, 4, 2, 1, 2, 1, 4, 3]
def baseStart_1577297 : Nat := 118140960795 + 1577297 * 2 ^ 59
def prefixEnd_1577297 : Nat := 4983230072969 + 3 ^ 40 * 1577297 * 2
def baseEnd_1577297 : Nat := 809911495894820551933649

theorem tailTrace_1577297 : CollatzResearch.WordTrace tailWord_1577297 prefixEnd_1577297 809911495894820551933649 := by
  unfold tailWord_1577297
  simp only [CollatzResearch.WordTrace]
  refine ⟨57528747766729824726202145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38352498511153216484134763 57528747766729824726202145)
  ·
    refine ⟨43146560825047368544651609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57528747766729824726202145 43146560825047368544651609)
    ·
      refine ⟨32359920618785526408488707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43146560825047368544651609 32359920618785526408488707)
      ·
        refine ⟨48539880928178289612733061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32359920618785526408488707 48539880928178289612733061)
        ·
          refine ⟨9101227674033429302387449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48539880928178289612733061 9101227674033429302387449)
          ·
            refine ⟨6825920755525071976790587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9101227674033429302387449 6825920755525071976790587)
            ·
              refine ⟨10238881133287607965185881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6825920755525071976790587 10238881133287607965185881)
              ·
                refine ⟨7679160849965705973889411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10238881133287607965185881 7679160849965705973889411)
                ·
                  refine ⟨11518741274948558960834117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7679160849965705973889411 11518741274948558960834117)
                  ·
                    refine ⟨2159763989052854805156397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11518741274948558960834117 2159763989052854805156397)
                    ·
                      refine ⟨809911495894820551933649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2159763989052854805156397 809911495894820551933649)
                      ·
                        rfl

theorem cell23_1577297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 4, 3].length) (baseStart_1577297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577297 prefixEnd_1577297 := by exact prefixLift 1577297
  have htrace : WordTrace (prefixWord ++ tailWord_1577297) baseStart_1577297 baseEnd_1577297 := by
    simpa [prefixWord, tailWord_1577297, baseEnd_1577297] using wordTrace_append hprefix tailTrace_1577297
  have hstable : (prefixWord ++ tailWord_1577297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577297).length < 2 ^ (prefixWord ++ tailWord_1577297).sum := by decide
  have hdescent : baseEnd_1577297 < baseStart_1577297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577314 : List Nat := [3, 3, 2, 1, 1, 2, 2, 1, 1, 4, 3]
def baseStart_1577314 : Nat := 118140960795 + 1577314 * 2 ^ 59
def prefixEnd_1577314 : Nat := 4983230072969 + 3 ^ 40 * 1577314 * 2
def baseEnd_1577314 : Nat := 809920225065946985421071

theorem tailTrace_1577314 : CollatzResearch.WordTrace tailWord_1577314 prefixEnd_1577314 809920225065946985421071 := by
  unfold tailWord_1577314
  simp only [CollatzResearch.WordTrace]
  refine ⟨14382341951917059157392749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38352911871778824419713997 14382341951917059157392749)
  ·
    refine ⟨5393378231968897184022281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14382341951917059157392749 5393378231968897184022281)
    ·
      refine ⟨4045033673976672888016711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5393378231968897184022281 4045033673976672888016711)
      ·
        refine ⟨6067550510965009332025067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4045033673976672888016711 6067550510965009332025067)
        ·
          refine ⟨9101325766447513998037601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6067550510965009332025067 9101325766447513998037601)
          ·
            refine ⟨6825994324835635498528201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9101325766447513998037601 6825994324835635498528201)
            ·
              refine ⟨5119495743626726623896151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6825994324835635498528201 5119495743626726623896151)
              ·
                refine ⟨7679243615440089935844227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5119495743626726623896151 7679243615440089935844227)
                ·
                  refine ⟨11518865423160134903766341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7679243615440089935844227 11518865423160134903766341)
                  ·
                    refine ⟨2159787266842525294456189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11518865423160134903766341 2159787266842525294456189)
                    ·
                      refine ⟨809920225065946985421071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2159787266842525294456189 809920225065946985421071)
                      ·
                        rfl

theorem cell23_1577314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_1577314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577314 prefixEnd_1577314 := by exact prefixLift 1577314
  have htrace : WordTrace (prefixWord ++ tailWord_1577314) baseStart_1577314 baseEnd_1577314 := by
    simpa [prefixWord, tailWord_1577314, baseEnd_1577314] using wordTrace_append hprefix tailTrace_1577314
  have hstable : (prefixWord ++ tailWord_1577314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577314).length < 2 ^ (prefixWord ++ tailWord_1577314).sum := by decide
  have hdescent : baseEnd_1577314 < baseStart_1577314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577378 : List Nat := [3, 3, 1, 2, 1, 1, 2, 5, 1, 1, 3]
def baseStart_1577378 : Nat := 118140960795 + 1577378 * 2 ^ 59
def prefixEnd_1577378 : Nat := 4983230072969 + 3 ^ 40 * 1577378 * 2
def baseEnd_1577378 : Nat := 809953087827834735020777

theorem tailTrace_1577378 : CollatzResearch.WordTrace tailWord_1577378 prefixEnd_1577378 809953087827834735020777 := by
  unfold tailWord_1577378
  simp only [CollatzResearch.WordTrace]
  refine ⟨14382925519859093889975197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38354468052957583706600525 14382925519859093889975197)
  ·
    refine ⟨5393597069947160208740699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14382925519859093889975197 5393597069947160208740699)
    ·
      refine ⟨8090395604920740313111049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5393597069947160208740699 8090395604920740313111049)
      ·
        refine ⟨6067796703690555234833287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8090395604920740313111049 6067796703690555234833287)
        ·
          refine ⟨9101695055535832852249931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6067796703690555234833287 9101695055535832852249931)
          ·
            refine ⟨13652542583303749278374897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9101695055535832852249931 13652542583303749278374897)
            ·
              refine ⟨10239406937477811958781173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13652542583303749278374897 10239406937477811958781173)
              ·
                refine ⟨959944400388544871135735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10239406937477811958781173 959944400388544871135735)
                ·
                  refine ⟨1439916600582817306703603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 959944400388544871135735 1439916600582817306703603)
                  ·
                    refine ⟨2159874900874225960055405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1439916600582817306703603 2159874900874225960055405)
                    ·
                      refine ⟨809953087827834735020777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2159874900874225960055405 809953087827834735020777)
                      ·
                        rfl

theorem cell23_1577378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_1577378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577378 prefixEnd_1577378 := by exact prefixLift 1577378
  have htrace : WordTrace (prefixWord ++ tailWord_1577378) baseStart_1577378 baseEnd_1577378 := by
    simpa [prefixWord, tailWord_1577378, baseEnd_1577378] using wordTrace_append hprefix tailTrace_1577378
  have hstable : (prefixWord ++ tailWord_1577378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577378).length < 2 ^ (prefixWord ++ tailWord_1577378).sum := by decide
  have hdescent : baseEnd_1577378 < baseStart_1577378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577434 : List Nat := [3, 1, 1, 2, 3, 1, 1, 4, 1, 3, 3]
def baseStart_1577434 : Nat := 118140960795 + 1577434 * 2 ^ 59
def prefixEnd_1577434 : Nat := 4983230072969 + 3 ^ 40 * 1577434 * 2
def baseEnd_1577434 : Nat := 809981842744486515920519

theorem tailTrace_1577434 : CollatzResearch.WordTrace tailWord_1577434 prefixEnd_1577434 809981842744486515920519 := by
  unfold tailWord_1577434
  simp only [CollatzResearch.WordTrace]
  refine ⟨14383436141808374280984839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38355829711488998082626237 14383436141808374280984839)
  ·
    refine ⟨21575154212712561421477259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14383436141808374280984839 21575154212712561421477259)
    ·
      refine ⟨32362731319068842132215889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21575154212712561421477259 32362731319068842132215889)
      ·
        refine ⟨24272048489301631599161917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32362731319068842132215889 24272048489301631599161917)
        ·
          refine ⟨9102018183488111849685719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24272048489301631599161917 9102018183488111849685719)
          ·
            refine ⟨13653027275232167774528579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9102018183488111849685719 13653027275232167774528579)
            ·
              refine ⟨20479540912848251661792869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13653027275232167774528579 20479540912848251661792869)
              ·
                refine ⟨3839913921159047186586163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20479540912848251661792869 3839913921159047186586163)
                ·
                  refine ⟨5759870881738570779879245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3839913921159047186586163 5759870881738570779879245)
                  ·
                    refine ⟨2159951580651964042454717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5759870881738570779879245 2159951580651964042454717)
                    ·
                      refine ⟨809981842744486515920519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2159951580651964042454717 809981842744486515920519)
                      ·
                        rfl

theorem cell23_1577434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 1, 3, 3].length) (baseStart_1577434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577434 prefixEnd_1577434 := by exact prefixLift 1577434
  have htrace : WordTrace (prefixWord ++ tailWord_1577434) baseStart_1577434 baseEnd_1577434 := by
    simpa [prefixWord, tailWord_1577434, baseEnd_1577434] using wordTrace_append hprefix tailTrace_1577434
  have hstable : (prefixWord ++ tailWord_1577434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577434).length < 2 ^ (prefixWord ++ tailWord_1577434).sum := by decide
  have hdescent : baseEnd_1577434 < baseStart_1577434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577445 : List Nat := [1, 3, 1, 5, 3, 1, 1, 2, 2, 4]
def baseStart_1577445 : Nat := 118140960795 + 1577445 * 2 ^ 59
def prefixEnd_1577445 : Nat := 4983230072969 + 3 ^ 40 * 1577445 * 2
def baseEnd_1577445 : Nat := 269995830343895324294323

theorem tailTrace_1577445 : CollatzResearch.WordTrace tailWord_1577445 prefixEnd_1577445 269995830343895324294323 := by
  unfold tailWord_1577445
  simp only [CollatzResearch.WordTrace]
  refine ⟨57534145770193646002589789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38356097180129097335059859 57534145770193646002589789)
  ·
    refine ⟨21575304663822617250971171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57534145770193646002589789 21575304663822617250971171)
    ·
      refine ⟨32362956995733925876456757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21575304663822617250971171 32362956995733925876456757)
      ·
        refine ⟨3034027218350055550917821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32362956995733925876456757 3034027218350055550917821)
        ·
          refine ⟨1137760206881270831594183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3034027218350055550917821 1137760206881270831594183)
          ·
            refine ⟨1706640310321906247391275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1137760206881270831594183 1706640310321906247391275)
            ·
              refine ⟨2559960465482859371086913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1706640310321906247391275 2559960465482859371086913)
              ·
                refine ⟨1919970349112144528315185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2559960465482859371086913 1919970349112144528315185)
                ·
                  refine ⟨1439977761834108396236389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1919970349112144528315185 1439977761834108396236389)
                  ·
                    refine ⟨269995830343895324294323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1439977761834108396236389 269995830343895324294323)
                    ·
                      rfl

theorem cell23_1577445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 2, 4].length) (baseStart_1577445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577445 prefixEnd_1577445 := by exact prefixLift 1577445
  have htrace : WordTrace (prefixWord ++ tailWord_1577445) baseStart_1577445 baseEnd_1577445 := by
    simpa [prefixWord, tailWord_1577445, baseEnd_1577445] using wordTrace_append hprefix tailTrace_1577445
  have hstable : (prefixWord ++ tailWord_1577445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577445).length < 2 ^ (prefixWord ++ tailWord_1577445).sum := by decide
  have hdescent : baseEnd_1577445 < baseStart_1577445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577485 : List Nat := [1, 7, 1, 1, 1, 1, 1, 2, 4, 1, 3]
def baseStart_1577485 : Nat := 118140960795 + 1577485 * 2 ^ 59
def prefixEnd_1577485 : Nat := 4983230072969 + 3 ^ 40 * 1577485 * 2
def baseEnd_1577485 : Nat := 810008030257865816382785

theorem tailTrace_1577485 : CollatzResearch.WordTrace tailWord_1577485 prefixEnd_1577485 810008030257865816382785 := by
  unfold tailWord_1577485
  simp only [CollatzResearch.WordTrace]
  refine ⟨57535604690048732834045909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38357069793365821889363939 57535604690048732834045909)
  ·
    refine ⟨1348490734923017175797951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 57535604690048732834045909 1348490734923017175797951)
    ·
      refine ⟨2022736102384525763696927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1348490734923017175797951 2022736102384525763696927)
      ·
        refine ⟨3034104153576788645545391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2022736102384525763696927 3034104153576788645545391)
        ·
          refine ⟨4551156230365182968318087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3034104153576788645545391 4551156230365182968318087)
          ·
            refine ⟨6826734345547774452477131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4551156230365182968318087 6826734345547774452477131)
            ·
              refine ⟨10240101518321661678715697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6826734345547774452477131 10240101518321661678715697)
              ·
                refine ⟨7680076138741246259036773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10240101518321661678715697 7680076138741246259036773)
                ·
                  refine ⟨1440014276013983673569395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7680076138741246259036773 1440014276013983673569395)
                  ·
                    refine ⟨2160021414020975510354093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1440014276013983673569395 2160021414020975510354093)
                    ·
                      refine ⟨810008030257865816382785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2160021414020975510354093 810008030257865816382785)
                      ·
                        rfl

theorem cell23_1577485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_1577485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577485 prefixEnd_1577485 := by exact prefixLift 1577485
  have htrace : WordTrace (prefixWord ++ tailWord_1577485) baseStart_1577485 baseEnd_1577485 := by
    simpa [prefixWord, tailWord_1577485, baseEnd_1577485] using wordTrace_append hprefix tailTrace_1577485
  have hstable : (prefixWord ++ tailWord_1577485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577485).length < 2 ^ (prefixWord ++ tailWord_1577485).sum := by decide
  have hdescent : baseEnd_1577485 < baseStart_1577485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577487 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 4]
def baseStart_1577487 : Nat := 118140960795 + 1577487 * 2 ^ 59
def prefixEnd_1577487 : Nat := 4983230072969 + 3 ^ 40 * 1577487 * 2
def baseEnd_1577487 : Nat := 810009057219174808557775

theorem tailTrace_1577487 : CollatzResearch.WordTrace tailWord_1577487 prefixEnd_1577487 810009057219174808557775 := by
  unfold tailWord_1577487
  simp only [CollatzResearch.WordTrace]
  refine ⟨57535677636041487175618715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38357118424027658117079143 57535677636041487175618715)
  ·
    refine ⟨86303516454062230763428073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57535677636041487175618715 86303516454062230763428073)
    ·
      refine ⟨64727637340546673072571055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86303516454062230763428073 64727637340546673072571055)
      ·
        refine ⟨97091456010820009608856583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64727637340546673072571055 97091456010820009608856583)
        ·
          refine ⟨145637184016230014413284875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97091456010820009608856583 145637184016230014413284875)
          ·
            refine ⟨218455776024345021619927313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145637184016230014413284875 218455776024345021619927313)
            ·
              refine ⟨163841832018258766214945485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218455776024345021619927313 163841832018258766214945485)
              ·
                refine ⟨61440687006847037330604557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163841832018258766214945485 61440687006847037330604557)
                ·
                  refine ⟨23040257627567638998976709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61440687006847037330604557 23040257627567638998976709)
                  ·
                    refine ⟨4320048305168932312308133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23040257627567638998976709 4320048305168932312308133)
                    ·
                      refine ⟨810009057219174808557775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4320048305168932312308133 810009057219174808557775)
                      ·
                        rfl

theorem cell23_1577487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 4].length) (baseStart_1577487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577487 prefixEnd_1577487 := by exact prefixLift 1577487
  have htrace : WordTrace (prefixWord ++ tailWord_1577487) baseStart_1577487 baseEnd_1577487 := by
    simpa [prefixWord, tailWord_1577487, baseEnd_1577487] using wordTrace_append hprefix tailTrace_1577487
  have hstable : (prefixWord ++ tailWord_1577487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577487).length < 2 ^ (prefixWord ++ tailWord_1577487).sum := by decide
  have hdescent : baseEnd_1577487 < baseStart_1577487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577491 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 6, 2, 2]
def baseStart_1577491 : Nat := 118140960795 + 1577491 * 2 ^ 59
def prefixEnd_1577491 : Nat := 4983230072969 + 3 ^ 40 * 1577491 * 2
def baseEnd_1577491 : Nat := 810011111141792792907757

theorem tailTrace_1577491 : CollatzResearch.WordTrace tailWord_1577491 prefixEnd_1577491 810011111141792792907757 := by
  unfold tailWord_1577491
  simp only [CollatzResearch.WordTrace]
  refine ⟨57535823528026995858764327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38357215685351330572509551 57535823528026995858764327)
  ·
    refine ⟨86303735292040493788146491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57535823528026995858764327 86303735292040493788146491)
    ·
      refine ⟨129455602938060740682219737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86303735292040493788146491 129455602938060740682219737)
      ·
        refine ⟨97091702203545555511664803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129455602938060740682219737 97091702203545555511664803)
        ·
          refine ⟨145637553305318333267497205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97091702203545555511664803 145637553305318333267497205)
          ·
            refine ⟨13653520622373593743827863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 145637553305318333267497205 13653520622373593743827863)
            ·
              refine ⟨20480280933560390615741795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13653520622373593743827863 20480280933560390615741795)
              ·
                refine ⟨30720421400340585923612693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20480280933560390615741795 30720421400340585923612693)
                ·
                  refine ⟨1440019753140964965169345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 30720421400340585923612693 1440019753140964965169345)
                  ·
                    refine ⟨1080014814855723723877009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1440019753140964965169345 1080014814855723723877009)
                    ·
                      refine ⟨810011111141792792907757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1080014814855723723877009 810011111141792792907757)
                      ·
                        rfl

theorem cell23_1577491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 6, 2, 2].length) (baseStart_1577491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577491 prefixEnd_1577491 := by exact prefixLift 1577491
  have htrace : WordTrace (prefixWord ++ tailWord_1577491) baseStart_1577491 baseEnd_1577491 := by
    simpa [prefixWord, tailWord_1577491, baseEnd_1577491] using wordTrace_append hprefix tailTrace_1577491
  have hstable : (prefixWord ++ tailWord_1577491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577491).length < 2 ^ (prefixWord ++ tailWord_1577491).sum := by decide
  have hdescent : baseEnd_1577491 < baseStart_1577491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577554 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 3, 2, 5]
def baseStart_1577554 : Nat := 118140960795 + 1577554 * 2 ^ 59
def prefixEnd_1577554 : Nat := 4983230072969 + 3 ^ 40 * 1577554 * 2
def baseEnd_1577554 : Nat := 810043460423026046419967

theorem tailTrace_1577554 : CollatzResearch.WordTrace tailWord_1577554 prefixEnd_1577554 810043460423026046419967 := by
  unfold tailWord_1577554
  simp only [CollatzResearch.WordTrace]
  refine ⟨14384530331699689404576929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38358747551199171745538477 14384530331699689404576929)
  ·
    refine ⟨10788397748774767053432697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14384530331699689404576929 10788397748774767053432697)
    ·
      refine ⟨8091298311581075290074523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10788397748774767053432697 8091298311581075290074523)
      ·
        refine ⟨12136947467371612935111785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8091298311581075290074523 12136947467371612935111785)
        ·
          refine ⟨9102710600528709701333839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12136947467371612935111785 9102710600528709701333839)
          ·
            refine ⟨13654065900793064552000759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9102710600528709701333839 13654065900793064552000759)
            ·
              refine ⟨20481098851189596828001139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13654065900793064552000759 20481098851189596828001139)
              ·
                refine ⟨30721648276784395242001709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20481098851189596828001139 30721648276784395242001709)
                ·
                  refine ⟨11520618103794148215750641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30721648276784395242001709 11520618103794148215750641)
                  ·
                    refine ⟨8640463577845611161812981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11520618103794148215750641 8640463577845611161812981)
                    ·
                      refine ⟨810043460423026046419967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8640463577845611161812981 810043460423026046419967)
                      ·
                        rfl

theorem cell23_1577554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_1577554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577554 prefixEnd_1577554 := by exact prefixLift 1577554
  have htrace : WordTrace (prefixWord ++ tailWord_1577554) baseStart_1577554 baseEnd_1577554 := by
    simpa [prefixWord, tailWord_1577554, baseEnd_1577554] using wordTrace_append hprefix tailTrace_1577554
  have hstable : (prefixWord ++ tailWord_1577554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577554).length < 2 ^ (prefixWord ++ tailWord_1577554).sum := by decide
  have hdescent : baseEnd_1577554 < baseStart_1577554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577601 : List Nat := [1, 2, 4, 2, 1, 1, 3, 1, 1, 4, 3]
def baseStart_1577601 : Nat := 118140960795 + 1577601 * 2 ^ 59
def prefixEnd_1577601 : Nat := 4983230072969 + 3 ^ 40 * 1577601 * 2
def baseEnd_1577601 : Nat := 810067594013787362532251

theorem tailTrace_1577601 : CollatzResearch.WordTrace tailWord_1577601 prefixEnd_1577601 810067594013787362532251 := by
  unfold tailWord_1577601
  simp only [CollatzResearch.WordTrace]
  refine ⟨57539835557628484645268657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38359890371752323096845771 57539835557628484645268657)
  ·
    refine ⟨43154876668221363483951493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57539835557628484645268657 43154876668221363483951493)
    ·
      refine ⟨8091539375291505653240905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43154876668221363483951493 8091539375291505653240905)
      ·
        refine ⟨6068654531468629239930679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8091539375291505653240905 6068654531468629239930679)
        ·
          refine ⟨9102981797202943859896019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6068654531468629239930679 9102981797202943859896019)
          ·
            refine ⟨13654472695804415789844029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9102981797202943859896019 13654472695804415789844029)
            ·
              refine ⟨5120427260926655921191511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13654472695804415789844029 5120427260926655921191511)
              ·
                refine ⟨7680640891389983881787267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5120427260926655921191511 7680640891389983881787267)
                ·
                  refine ⟨11520961337084975822680901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7680640891389983881787267 11520961337084975822680901)
                  ·
                    refine ⟨2160180250703432966752669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11520961337084975822680901 2160180250703432966752669)
                    ·
                      refine ⟨810067594013787362532251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2160180250703432966752669 810067594013787362532251)
                      ·
                        rfl

theorem cell23_1577601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_1577601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577601 prefixEnd_1577601 := by exact prefixLift 1577601
  have htrace : WordTrace (prefixWord ++ tailWord_1577601) baseStart_1577601 baseEnd_1577601 := by
    simpa [prefixWord, tailWord_1577601, baseEnd_1577601] using wordTrace_append hprefix tailTrace_1577601
  have hstable : (prefixWord ++ tailWord_1577601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577601).length < 2 ^ (prefixWord ++ tailWord_1577601).sum := by decide
  have hdescent : baseEnd_1577601 < baseStart_1577601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577624 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 1, 1, 8]
def baseStart_1577624 : Nat := 118140960795 + 1577624 * 2 ^ 59
def prefixEnd_1577624 : Nat := 4983230072969 + 3 ^ 40 * 1577624 * 2
def baseEnd_1577624 : Nat := 810079404068840772544645

theorem tailTrace_1577624 : CollatzResearch.WordTrace tailWord_1577624 prefixEnd_1577624 810079404068840772544645 := by
  unfold tailWord_1577624
  simp only [CollatzResearch.WordTrace]
  refine ⟨28770337218272579786677963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38360449624363439715570617 28770337218272579786677963)
  ·
    refine ⟨43155505827408869680016945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28770337218272579786677963 43155505827408869680016945)
    ·
      refine ⟨32366629370556652260012709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43155505827408869680016945 32366629370556652260012709)
      ·
        refine ⟨6068743006979372298752383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32366629370556652260012709 6068743006979372298752383)
        ·
          refine ⟨9103114510469058448128575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6068743006979372298752383 9103114510469058448128575)
          ·
            refine ⟨13654671765703587672192863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9103114510469058448128575 13654671765703587672192863)
            ·
              refine ⟨20482007648555381508289295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13654671765703587672192863 20482007648555381508289295)
              ·
                refine ⟨30723011472833072262433943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20482007648555381508289295 30723011472833072262433943)
                ·
                  refine ⟨46084517209249608393650915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30723011472833072262433943 46084517209249608393650915)
                  ·
                    refine ⟨69126775813874412590476373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46084517209249608393650915 69126775813874412590476373)
                    ·
                      refine ⟨810079404068840772544645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 69126775813874412590476373 810079404068840772544645)
                      ·
                        rfl

theorem cell23_1577624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_1577624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577624 prefixEnd_1577624 := by exact prefixLift 1577624
  have htrace : WordTrace (prefixWord ++ tailWord_1577624) baseStart_1577624 baseEnd_1577624 := by
    simpa [prefixWord, tailWord_1577624, baseEnd_1577624] using wordTrace_append hprefix tailTrace_1577624
  have hstable : (prefixWord ++ tailWord_1577624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577624).length < 2 ^ (prefixWord ++ tailWord_1577624).sum := by decide
  have hdescent : baseEnd_1577624 < baseStart_1577624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577641 : List Nat := [1, 2, 1, 1, 1, 1, 2, 6, 1, 5, 2]
def baseStart_1577641 : Nat := 118140960795 + 1577641 * 2 ^ 59
def prefixEnd_1577641 : Nat := 4983230072969 + 3 ^ 40 * 1577641 * 2
def baseEnd_1577641 : Nat := 810088133239967206032067

theorem tailTrace_1577641 : CollatzResearch.WordTrace tailWord_1577641 prefixEnd_1577641 810088133239967206032067 := by
  unfold tailWord_1577641
  simp only [CollatzResearch.WordTrace]
  refine ⟨57541294477483571476724777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38360862984989047651149851 57541294477483571476724777)
  ·
    refine ⟨43155970858112678607543583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57541294477483571476724777 43155970858112678607543583)
    ·
      refine ⟨64733956287169017911315375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43155970858112678607543583 64733956287169017911315375)
      ·
        refine ⟨97100934430753526866973063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64733956287169017911315375 97100934430753526866973063)
        ·
          refine ⟨145651401646130290300459595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97100934430753526866973063 145651401646130290300459595)
          ·
            refine ⟨218477102469195435450689393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145651401646130290300459595 218477102469195435450689393)
            ·
              refine ⟨163857826851896576588017045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218477102469195435450689393 163857826851896576588017045)
              ·
                refine ⟨7680835633682652027563299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 163857826851896576588017045 7680835633682652027563299)
                ·
                  refine ⟨11521253450523978041344949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7680835633682652027563299 11521253450523978041344949)
                  ·
                    refine ⟨1080117510986622941376089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11521253450523978041344949 1080117510986622941376089)
                    ·
                      refine ⟨810088133239967206032067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1080117510986622941376089 810088133239967206032067)
                      ·
                        rfl

theorem cell23_1577641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 5, 2].length) (baseStart_1577641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577641 prefixEnd_1577641 := by exact prefixLift 1577641
  have htrace : WordTrace (prefixWord ++ tailWord_1577641) baseStart_1577641 baseEnd_1577641 := by
    simpa [prefixWord, tailWord_1577641, baseEnd_1577641] using wordTrace_append hprefix tailTrace_1577641
  have hstable : (prefixWord ++ tailWord_1577641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577641).length < 2 ^ (prefixWord ++ tailWord_1577641).sum := by decide
  have hdescent : baseEnd_1577641 < baseStart_1577641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577651 : List Nat := [1, 1, 1, 2, 3, 4, 1, 4, 1, 5]
def baseStart_1577651 : Nat := 118140960795 + 1577651 * 2 ^ 59
def prefixEnd_1577651 : Nat := 4983230072969 + 3 ^ 40 * 1577651 * 2
def baseEnd_1577651 : Nat := 270031089348837388969007

theorem tailTrace_1577651 : CollatzResearch.WordTrace tailWord_1577651 prefixEnd_1577651 270031089348837388969007 := by
  unfold tailWord_1577651
  simp only [CollatzResearch.WordTrace]
  refine ⟨57541659207447343184588807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38361106138298228789725871 57541659207447343184588807)
  ·
    refine ⟨86312488811171014776883211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57541659207447343184588807 86312488811171014776883211)
    ·
      refine ⟨129468733216756522165324817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86312488811171014776883211 129468733216756522165324817)
      ·
        refine ⟨97101549912567391623993613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129468733216756522165324817 97101549912567391623993613)
        ·
          refine ⟨36413081217212771858997605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97101549912567391623993613 36413081217212771858997605)
          ·
            refine ⟨6827452728227394723562051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36413081217212771858997605 6827452728227394723562051)
            ·
              refine ⟨10241179092341092085343077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6827452728227394723562051 10241179092341092085343077)
              ·
                refine ⟨1920221079813954766001827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10241179092341092085343077 1920221079813954766001827)
                ·
                  refine ⟨2880331619720932149002741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1920221079813954766001827 2880331619720932149002741)
                  ·
                    refine ⟨270031089348837388969007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2880331619720932149002741 270031089348837388969007)
                    ·
                      rfl

theorem cell23_1577651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 5].length) (baseStart_1577651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577651 prefixEnd_1577651 := by exact prefixLift 1577651
  have htrace : WordTrace (prefixWord ++ tailWord_1577651) baseStart_1577651 baseEnd_1577651 := by
    simpa [prefixWord, tailWord_1577651, baseEnd_1577651] using wordTrace_append hprefix tailTrace_1577651
  have hstable : (prefixWord ++ tailWord_1577651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577651).length < 2 ^ (prefixWord ++ tailWord_1577651).sum := by decide
  have hdescent : baseEnd_1577651 < baseStart_1577651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577658 : List Nat := [3, 1, 1, 1, 2, 3, 2, 3, 2, 3, 2]
def baseStart_1577658 : Nat := 118140960795 + 1577658 * 2 ^ 59
def prefixEnd_1577658 : Nat := 4983230072969 + 3 ^ 40 * 1577658 * 2
def baseEnd_1577658 : Nat := 810096862411093639519489

theorem tailTrace_1577658 : CollatzResearch.WordTrace tailWord_1577658 prefixEnd_1577658 810096862411093639519489 := by
  unfold tailWord_1577658
  simp only [CollatzResearch.WordTrace]
  refine ⟨14385478629605495845023407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38361276345614655586729085 14385478629605495845023407)
  ·
    refine ⟨21578217944408243767535111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14385478629605495845023407 21578217944408243767535111)
    ·
      refine ⟨32367326916612365651302667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21578217944408243767535111 32367326916612365651302667)
      ·
        refine ⟨48550990374918548476954001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32367326916612365651302667 48550990374918548476954001)
        ·
          refine ⟨36413242781188911357715501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48550990374918548476954001 36413242781188911357715501)
          ·
            refine ⟨13654966042945841759143313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36413242781188911357715501 13654966042945841759143313)
            ·
              refine ⟨10241224532209381319357485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13654966042945841759143313 10241224532209381319357485)
              ·
                refine ⟨3840459199578517994759057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10241224532209381319357485 3840459199578517994759057)
                ·
                  refine ⟨2880344399683888496069293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3840459199578517994759057 2880344399683888496069293)
                  ·
                    refine ⟨1080129149881458186025985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2880344399683888496069293 1080129149881458186025985)
                    ·
                      refine ⟨810096862411093639519489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1080129149881458186025985 810096862411093639519489)
                      ·
                        rfl

theorem cell23_1577658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 2, 3, 2].length) (baseStart_1577658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577658 prefixEnd_1577658 := by exact prefixLift 1577658
  have htrace : WordTrace (prefixWord ++ tailWord_1577658) baseStart_1577658 baseEnd_1577658 := by
    simpa [prefixWord, tailWord_1577658, baseEnd_1577658] using wordTrace_append hprefix tailTrace_1577658
  have hstable : (prefixWord ++ tailWord_1577658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577658).length < 2 ^ (prefixWord ++ tailWord_1577658).sum := by decide
  have hdescent : baseEnd_1577658 < baseStart_1577658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577668 : List Nat := [2, 3, 3, 1, 1, 2, 2, 3, 1, 5]
def baseStart_1577668 : Nat := 118140960795 + 1577668 * 2 ^ 59
def prefixEnd_1577668 : Nat := 4983230072969 + 3 ^ 40 * 1577668 * 2
def baseEnd_1577668 : Nat := 270033999072546200131481

theorem tailTrace_1577668 : CollatzResearch.WordTrace tailWord_1577668 prefixEnd_1577668 270033999072546200131481 := by
  unfold tailWord_1577668
  simp only [CollatzResearch.WordTrace]
  refine ⟨28771139624192877543978829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38361519498923836725305105 28771139624192877543978829)
  ·
    refine ⟨10789177359072329078992061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28771139624192877543978829 10789177359072329078992061)
    ·
      refine ⟨4045941509652123404622023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10789177359072329078992061 4045941509652123404622023)
      ·
        refine ⟨6068912264478185106933035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4045941509652123404622023 6068912264478185106933035)
        ·
          refine ⟨9103368396717277660399553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6068912264478185106933035 9103368396717277660399553)
          ·
            refine ⟨6827526297537958245299665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9103368396717277660399553 6827526297537958245299665)
            ·
              refine ⟨5120644723153468683974749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6827526297537958245299665 5120644723153468683974749)
              ·
                refine ⟨1920241771182550756490531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5120644723153468683974749 1920241771182550756490531)
                ·
                  refine ⟨2880362656773826134735797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1920241771182550756490531 2880362656773826134735797)
                  ·
                    refine ⟨270033999072546200131481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2880362656773826134735797 270033999072546200131481)
                    ·
                      rfl

theorem cell23_1577668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_1577668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577668 prefixEnd_1577668 := by exact prefixLift 1577668
  have htrace : WordTrace (prefixWord ++ tailWord_1577668) baseStart_1577668 baseEnd_1577668 := by
    simpa [prefixWord, tailWord_1577668, baseEnd_1577668] using wordTrace_append hprefix tailTrace_1577668
  have hstable : (prefixWord ++ tailWord_1577668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577668).length < 2 ^ (prefixWord ++ tailWord_1577668).sum := by decide
  have hdescent : baseEnd_1577668 < baseStart_1577668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577681 : List Nat := [1, 2, 2, 1, 2, 3, 1, 3, 4, 4]
def baseStart_1577681 : Nat := 118140960795 + 1577681 * 2 ^ 59
def prefixEnd_1577681 : Nat := 4983230072969 + 3 ^ 40 * 1577681 * 2
def baseEnd_1577681 : Nat := 270036224155382349843961

theorem tailTrace_1577681 : CollatzResearch.WordTrace tailWord_1577681 prefixEnd_1577681 270036224155382349843961 := by
  unfold tailWord_1577681
  simp only [CollatzResearch.WordTrace]
  refine ⟨57542753397338658308180897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38361835598225772205453931 57542753397338658308180897)
  ·
    refine ⟨43157065048003993731135673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57542753397338658308180897 43157065048003993731135673)
    ·
      refine ⟨32367798786002995298351755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43157065048003993731135673 32367798786002995298351755)
      ·
        refine ⟨48551698179004492947527633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32367798786002995298351755 48551698179004492947527633)
        ·
          refine ⟨36413773634253369710645725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48551698179004492947527633 36413773634253369710645725)
          ·
            refine ⟨13655165112845013641492147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36413773634253369710645725 13655165112845013641492147)
            ·
              refine ⟨20482747669267520462238221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13655165112845013641492147 20482747669267520462238221)
              ·
                refine ⟨7681030375975320173339333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20482747669267520462238221 7681030375975320173339333)
                ·
                  refine ⟨1440193195495372532501125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7681030375975320173339333 1440193195495372532501125)
                  ·
                    refine ⟨270036224155382349843961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1440193195495372532501125 270036224155382349843961)
                    ·
                      rfl

theorem cell23_1577681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 4, 4].length) (baseStart_1577681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577681 prefixEnd_1577681 := by exact prefixLift 1577681
  have htrace : WordTrace (prefixWord ++ tailWord_1577681) baseStart_1577681 baseEnd_1577681 := by
    simpa [prefixWord, tailWord_1577681, baseEnd_1577681] using wordTrace_append hprefix tailTrace_1577681
  have hstable : (prefixWord ++ tailWord_1577681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577681).length < 2 ^ (prefixWord ++ tailWord_1577681).sum := by decide
  have hdescent : baseEnd_1577681 < baseStart_1577681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577682 : List Nat := [3, 2, 2, 2, 3, 2, 1, 1, 3, 1, 3]
def baseStart_1577682 : Nat := 118140960795 + 1577682 * 2 ^ 59
def prefixEnd_1577682 : Nat := 4983230072969 + 3 ^ 40 * 1577682 * 2
def baseEnd_1577682 : Nat := 810109185946801545619379

theorem tailTrace_1577682 : CollatzResearch.WordTrace tailWord_1577682 prefixEnd_1577682 810109185946801545619379 := by
  unfold tailWord_1577682
  simp only [CollatzResearch.WordTrace]
  refine ⟨14385697467583758869741825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38361859913556690319311533 14385697467583758869741825)
  ·
    refine ⟨10789273100687819152306369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14385697467583758869741825 10789273100687819152306369)
    ·
      refine ⟨8091954825515864364229777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10789273100687819152306369 8091954825515864364229777)
      ·
        refine ⟨6068966119136898273172333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8091954825515864364229777 6068966119136898273172333)
        ·
          refine ⟨2275862294676336852439625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6068966119136898273172333 2275862294676336852439625)
          ·
            refine ⟨1706896721007252639329719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2275862294676336852439625 1706896721007252639329719)
            ·
              refine ⟨2560345081510878958994579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1706896721007252639329719 2560345081510878958994579)
              ·
                refine ⟨3840517622266318438491869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2560345081510878958994579 3840517622266318438491869)
                ·
                  refine ⟨1440194108349869414434451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3840517622266318438491869 1440194108349869414434451)
                  ·
                    refine ⟨2160291162524804121651677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1440194108349869414434451 2160291162524804121651677)
                    ·
                      refine ⟨810109185946801545619379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2160291162524804121651677 810109185946801545619379)
                      ·
                        rfl

theorem cell23_1577682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_1577682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577682 prefixEnd_1577682 := by exact prefixLift 1577682
  have htrace : WordTrace (prefixWord ++ tailWord_1577682) baseStart_1577682 baseEnd_1577682 := by
    simpa [prefixWord, tailWord_1577682, baseEnd_1577682] using wordTrace_append hprefix tailTrace_1577682
  have hstable : (prefixWord ++ tailWord_1577682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577682).length < 2 ^ (prefixWord ++ tailWord_1577682).sum := by decide
  have hdescent : baseEnd_1577682 < baseStart_1577682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577701 : List Nat := [1, 3, 1, 4, 1, 2, 2, 1, 1, 1, 6]
def baseStart_1577701 : Nat := 118140960795 + 1577701 * 2 ^ 59
def prefixEnd_1577701 : Nat := 4983230072969 + 3 ^ 40 * 1577701 * 2
def baseEnd_1577701 : Nat := 810118942079236971281791

theorem tailTrace_1577701 : CollatzResearch.WordTrace tailWord_1577701 prefixEnd_1577701 810118942079236971281791 := by
  unfold tailWord_1577701
  simp only [CollatzResearch.WordTrace]
  refine ⟨57543482857266201723908957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38362321904844134482605971 57543482857266201723908957)
  ·
    refine ⟨21578806071474825646465859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57543482857266201723908957 21578806071474825646465859)
    ·
      refine ⟨32368209107212238469698789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21578806071474825646465859 32368209107212238469698789)
      ·
        refine ⟨6069039207602294713068523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32368209107212238469698789 6069039207602294713068523)
        ·
          refine ⟨9103558811403442069602785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6069039207602294713068523 9103558811403442069602785)
          ·
            refine ⟨6827669108552581552202089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9103558811403442069602785 6827669108552581552202089)
            ·
              refine ⟨5120751831414436164151567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6827669108552581552202089 5120751831414436164151567)
              ·
                refine ⟨7681127747121654246227351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5120751831414436164151567 7681127747121654246227351)
                ·
                  refine ⟨11521691620682481369341027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7681127747121654246227351 11521691620682481369341027)
                  ·
                    refine ⟨17282537431023722054011541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11521691620682481369341027 17282537431023722054011541)
                    ·
                      refine ⟨810118942079236971281791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17282537431023722054011541 810118942079236971281791)
                      ·
                        rfl

theorem cell23_1577701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_1577701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577701 prefixEnd_1577701 := by exact prefixLift 1577701
  have htrace : WordTrace (prefixWord ++ tailWord_1577701) baseStart_1577701 baseEnd_1577701 := by
    simpa [prefixWord, tailWord_1577701, baseEnd_1577701] using wordTrace_append hprefix tailTrace_1577701
  have hstable : (prefixWord ++ tailWord_1577701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577701).length < 2 ^ (prefixWord ++ tailWord_1577701).sum := by decide
  have hdescent : baseEnd_1577701 < baseStart_1577701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577718 : List Nat := [5, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4]
def baseStart_1577718 : Nat := 118140960795 + 1577718 * 2 ^ 59
def prefixEnd_1577718 : Nat := 4983230072969 + 3 ^ 40 * 1577718 * 2
def baseEnd_1577718 : Nat := 810127671250363404769213

theorem tailTrace_1577718 : CollatzResearch.WordTrace tailWord_1577718 prefixEnd_1577718 810127671250363404769213 := by
  unfold tailWord_1577718
  simp only [CollatzResearch.WordTrace]
  refine ⟨3596506431137788351704863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38362735265469742418185205 3596506431137788351704863)
  ·
    refine ⟨5394759646706682527557295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3596506431137788351704863 5394759646706682527557295)
    ·
      refine ⟨8092139470060023791335943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5394759646706682527557295 8092139470060023791335943)
      ·
        refine ⟨12138209205090035687003915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8092139470060023791335943 12138209205090035687003915)
        ·
          refine ⟨18207313807635053530505873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12138209205090035687003915 18207313807635053530505873)
          ·
            refine ⟨13655485355726290147879405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18207313807635053530505873 13655485355726290147879405)
            ·
              refine ⟨5120807008397358805454777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13655485355726290147879405 5120807008397358805454777)
              ·
                refine ⟨3840605256298019104091083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5120807008397358805454777 3840605256298019104091083)
                ·
                  refine ⟨5760907884447028656136625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3840605256298019104091083 5760907884447028656136625)
                  ·
                    refine ⟨4320680913335271492102469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5760907884447028656136625 4320680913335271492102469)
                    ·
                      refine ⟨810127671250363404769213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4320680913335271492102469 810127671250363404769213)
                      ·
                        rfl

theorem cell23_1577718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_1577718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577718 prefixEnd_1577718 := by exact prefixLift 1577718
  have htrace : WordTrace (prefixWord ++ tailWord_1577718) baseStart_1577718 baseEnd_1577718 := by
    simpa [prefixWord, tailWord_1577718, baseEnd_1577718] using wordTrace_append hprefix tailTrace_1577718
  have hstable : (prefixWord ++ tailWord_1577718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577718).length < 2 ^ (prefixWord ++ tailWord_1577718).sum := by decide
  have hdescent : baseEnd_1577718 < baseStart_1577718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577725 : List Nat := [1, 4, 1, 1, 1, 1, 7, 1, 1, 2, 3]
def baseStart_1577725 : Nat := 118140960795 + 1577725 * 2 ^ 59
def prefixEnd_1577725 : Nat := 4983230072969 + 3 ^ 40 * 1577725 * 2
def baseEnd_1577725 : Nat := 810131265614944877381681

theorem tailTrace_1577725 : CollatzResearch.WordTrace tailWord_1577725 prefixEnd_1577725 810131265614944877381681 := by
  unfold tailWord_1577725
  simp only [CollatzResearch.WordTrace]
  refine ⟨57544358209179253822782629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38362905472786169215188419 57544358209179253822782629)
  ·
    refine ⟨10789567164221110091771743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57544358209179253822782629 10789567164221110091771743)
    ·
      refine ⟨16184350746331665137657615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10789567164221110091771743 16184350746331665137657615)
      ·
        refine ⟨24276526119497497706486423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16184350746331665137657615 24276526119497497706486423)
        ·
          refine ⟨36414789179246246559729635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24276526119497497706486423 36414789179246246559729635)
          ·
            refine ⟨54622183768869369839594453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36414789179246246559729635 54622183768869369839594453)
            ·
              refine ⟨1280207432082875855615495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 54622183768869369839594453 1280207432082875855615495)
              ·
                refine ⟨1920311148124313783423243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1280207432082875855615495 1920311148124313783423243)
                ·
                  refine ⟨2880466722186470675134865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1920311148124313783423243 2880466722186470675134865)
                  ·
                    refine ⟨2160350041639853006351149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2880466722186470675134865 2160350041639853006351149)
                    ·
                      refine ⟨810131265614944877381681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2160350041639853006351149 810131265614944877381681)
                      ·
                        rfl

theorem cell23_1577725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 1, 2, 3].length) (baseStart_1577725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577725 prefixEnd_1577725 := by exact prefixLift 1577725
  have htrace : WordTrace (prefixWord ++ tailWord_1577725) baseStart_1577725 baseEnd_1577725 := by
    simpa [prefixWord, tailWord_1577725, baseEnd_1577725] using wordTrace_append hprefix tailTrace_1577725
  have hstable : (prefixWord ++ tailWord_1577725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577725).length < 2 ^ (prefixWord ++ tailWord_1577725).sum := by decide
  have hdescent : baseEnd_1577725 < baseStart_1577725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577761 : List Nat := [1, 2, 3, 2, 1, 2, 1, 2, 2, 3, 4]
def baseStart_1577761 : Nat := 118140960795 + 1577761 * 2 ^ 59
def prefixEnd_1577761 : Nat := 4983230072969 + 3 ^ 40 * 1577761 * 2
def baseEnd_1577761 : Nat := 810149750918506736531515

theorem tailTrace_1577761 : CollatzResearch.WordTrace tailWord_1577761 prefixEnd_1577761 810149750918506736531515 := by
  unfold tailWord_1577761
  simp only [CollatzResearch.WordTrace]
  refine ⟨57545671237048831971093137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38363780824699221314062091 57545671237048831971093137)
  ·
    refine ⟨43159253427786623978319853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57545671237048831971093137 43159253427786623978319853)
    ·
      refine ⟨16184720035419983991869945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43159253427786623978319853 16184720035419983991869945)
      ·
        refine ⟨12138540026564987993902459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16184720035419983991869945 12138540026564987993902459)
        ·
          refine ⟨18207810039847481990853689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12138540026564987993902459 18207810039847481990853689)
          ·
            refine ⟨13655857529885611493140267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18207810039847481990853689 13655857529885611493140267)
            ·
              refine ⟨20483786294828417239710401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13655857529885611493140267 20483786294828417239710401)
              ·
                refine ⟨15362839721121312929782801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20483786294828417239710401 15362839721121312929782801)
                ·
                  refine ⟨11522129790840984697337101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15362839721121312929782801 11522129790840984697337101)
                  ·
                    refine ⟨4320798671565369261501413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11522129790840984697337101 4320798671565369261501413)
                    ·
                      refine ⟨810149750918506736531515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4320798671565369261501413 810149750918506736531515)
                      ·
                        rfl

theorem cell23_1577761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_1577761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577761 prefixEnd_1577761 := by exact prefixLift 1577761
  have htrace : WordTrace (prefixWord ++ tailWord_1577761) baseStart_1577761 baseEnd_1577761 := by
    simpa [prefixWord, tailWord_1577761, baseEnd_1577761] using wordTrace_append hprefix tailTrace_1577761
  have hstable : (prefixWord ++ tailWord_1577761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577761).length < 2 ^ (prefixWord ++ tailWord_1577761).sum := by decide
  have hdescent : baseEnd_1577761 < baseStart_1577761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577765 : List Nat := [1, 3, 1, 2, 3, 1, 2, 4, 1, 3, 2]
def baseStart_1577765 : Nat := 118140960795 + 1577765 * 2 ^ 59
def prefixEnd_1577765 : Nat := 4983230072969 + 3 ^ 40 * 1577765 * 2
def baseEnd_1577765 : Nat := 810151804841124720881497

theorem tailTrace_1577765 : CollatzResearch.WordTrace tailWord_1577765 prefixEnd_1577765 810151804841124720881497 := by
  unfold tailWord_1577765
  simp only [CollatzResearch.WordTrace]
  refine ⟨57545817129034340654238749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38363878086022893769492499 57545817129034340654238749)
  ·
    refine ⟨21579681423387877745339531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57545817129034340654238749 21579681423387877745339531)
    ·
      refine ⟨32369522135081816618009297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21579681423387877745339531 32369522135081816618009297)
      ·
        refine ⟨24277141601311362463506973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32369522135081816618009297 24277141601311362463506973)
        ·
          refine ⟨9103928100491760923815115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24277141601311362463506973 9103928100491760923815115)
          ·
            refine ⟨13655892150737641385722673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9103928100491760923815115 13655892150737641385722673)
            ·
              refine ⟨10241919113053231039292005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13655892150737641385722673 10241919113053231039292005)
              ·
                refine ⟨1920359833697480819867251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10241919113053231039292005 1920359833697480819867251)
                ·
                  refine ⟨2880539750546221229800877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1920359833697480819867251 2880539750546221229800877)
                  ·
                    refine ⟨1080202406454832961175329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2880539750546221229800877 1080202406454832961175329)
                    ·
                      refine ⟨810151804841124720881497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1080202406454832961175329 810151804841124720881497)
                      ·
                        rfl

theorem cell23_1577765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 3, 2].length) (baseStart_1577765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577765 prefixEnd_1577765 := by exact prefixLift 1577765
  have htrace : WordTrace (prefixWord ++ tailWord_1577765) baseStart_1577765 baseEnd_1577765 := by
    simpa [prefixWord, tailWord_1577765, baseEnd_1577765] using wordTrace_append hprefix tailTrace_1577765
  have hstable : (prefixWord ++ tailWord_1577765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577765).length < 2 ^ (prefixWord ++ tailWord_1577765).sum := by decide
  have hdescent : baseEnd_1577765 < baseStart_1577765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577773 : List Nat := [1, 5, 3, 2, 1, 1, 2, 3, 1, 2, 2]
def baseStart_1577773 : Nat := 118140960795 + 1577773 * 2 ^ 59
def prefixEnd_1577773 : Nat := 4983230072969 + 3 ^ 40 * 1577773 * 2
def baseEnd_1577773 : Nat := 810155912686360689581461

theorem tailTrace_1577773 : CollatzResearch.WordTrace tailWord_1577773 prefixEnd_1577773 810155912686360689581461 := by
  unfold tailWord_1577773
  simp only [CollatzResearch.WordTrace]
  refine ⟨57546108913005358020529973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38364072608670238680353315 57546108913005358020529973)
  ·
    refine ⟨5394947710594252314424685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57546108913005358020529973 5394947710594252314424685)
    ·
      refine ⟨2023105391472844617909257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5394947710594252314424685 2023105391472844617909257)
      ·
        refine ⟨1517329043604633463431943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2023105391472844617909257 1517329043604633463431943)
        ·
          refine ⟨2275993565406950195147915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1517329043604633463431943 2275993565406950195147915)
          ·
            refine ⟨3413990348110425292721873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2275993565406950195147915 3413990348110425292721873)
            ·
              refine ⟨2560492761082818969541405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3413990348110425292721873 2560492761082818969541405)
              ·
                refine ⟨960184785406057113578027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2560492761082818969541405 960184785406057113578027)
                ·
                  refine ⟨1440277178109085670367041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 960184785406057113578027 1440277178109085670367041)
                  ·
                    refine ⟨1080207883581814252775281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1440277178109085670367041 1080207883581814252775281)
                    ·
                      refine ⟨810155912686360689581461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1080207883581814252775281 810155912686360689581461)
                      ·
                        rfl

theorem cell23_1577773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_1577773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577773 prefixEnd_1577773 := by exact prefixLift 1577773
  have htrace : WordTrace (prefixWord ++ tailWord_1577773) baseStart_1577773 baseEnd_1577773 := by
    simpa [prefixWord, tailWord_1577773, baseEnd_1577773] using wordTrace_append hprefix tailTrace_1577773
  have hstable : (prefixWord ++ tailWord_1577773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577773).length < 2 ^ (prefixWord ++ tailWord_1577773).sum := by decide
  have hdescent : baseEnd_1577773 < baseStart_1577773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577789 : List Nat := [1, 4, 1, 4, 2, 2, 1, 2, 2, 1, 3]
def baseStart_1577789 : Nat := 118140960795 + 1577789 * 2 ^ 59
def prefixEnd_1577789 : Nat := 4983230072969 + 3 ^ 40 * 1577789 * 2
def baseEnd_1577789 : Nat := 810164128376832626981387

theorem tailTrace_1577789 : CollatzResearch.WordTrace tailWord_1577789 prefixEnd_1577789 810164128376832626981387 := by
  unfold tailWord_1577789
  simp only [CollatzResearch.WordTrace]
  refine ⟨57546692480947392753112421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38364461653964928502074947 57546692480947392753112421)
  ·
    refine ⟨10790004840177636141208579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57546692480947392753112421 10790004840177636141208579)
    ·
      refine ⟨16185007260266454211812869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10790004840177636141208579 16185007260266454211812869)
      ·
        refine ⟨3034688861299960164714913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16185007260266454211812869 3034688861299960164714913)
        ·
          refine ⟨2276016645974970123536185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3034688861299960164714913 2276016645974970123536185)
          ·
            refine ⟨1707012484481227592652139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2276016645974970123536185 1707012484481227592652139)
            ·
              refine ⟨2560518726721841388978209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1707012484481227592652139 2560518726721841388978209)
              ·
                refine ⟨1920389045041381041733657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2560518726721841388978209 1920389045041381041733657)
                ·
                  refine ⟨1440291783781035781300243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1920389045041381041733657 1440291783781035781300243)
                  ·
                    refine ⟨2160437675671553671950365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1440291783781035781300243 2160437675671553671950365)
                    ·
                      refine ⟨810164128376832626981387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2160437675671553671950365 810164128376832626981387)
                      ·
                        rfl

theorem cell23_1577789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_1577789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577789 prefixEnd_1577789 := by exact prefixLift 1577789
  have htrace : WordTrace (prefixWord ++ tailWord_1577789) baseStart_1577789 baseEnd_1577789 := by
    simpa [prefixWord, tailWord_1577789, baseEnd_1577789] using wordTrace_append hprefix tailTrace_1577789
  have hstable : (prefixWord ++ tailWord_1577789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577789).length < 2 ^ (prefixWord ++ tailWord_1577789).sum := by decide
  have hdescent : baseEnd_1577789 < baseStart_1577789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577795 : List Nat := [1, 1, 1, 3, 1, 4, 3, 1, 4, 2, 2]
def baseStart_1577795 : Nat := 118140960795 + 1577795 * 2 ^ 59
def prefixEnd_1577795 : Nat := 4983230072969 + 3 ^ 40 * 1577795 * 2
def baseEnd_1577795 : Nat := 810167209260759603506359

theorem tailTrace_1577795 : CollatzResearch.WordTrace tailWord_1577795 prefixEnd_1577795 810167209260759603506359 := by
  unfold tailWord_1577795
  simp only [CollatzResearch.WordTrace]
  refine ⟨57546911318925655777830839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38364607545950437185220559 57546911318925655777830839)
  ·
    refine ⟨86320366978388483666746259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57546911318925655777830839 86320366978388483666746259)
    ·
      refine ⟨129480550467582725500119389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86320366978388483666746259 129480550467582725500119389)
      ·
        refine ⟨48555206425343522062544771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129480550467582725500119389 48555206425343522062544771)
        ·
          refine ⟨72832809638015283093817157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48555206425343522062544771 72832809638015283093817157)
          ·
            refine ⟨13656151807127865580090717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72832809638015283093817157 13656151807127865580090717)
            ·
              refine ⟨5121056927672949592534019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13656151807127865580090717 5121056927672949592534019)
              ·
                refine ⟨7681585391509424388801029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5121056927672949592534019 7681585391509424388801029)
                ·
                  refine ⟨1440297260908017072900193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7681585391509424388801029 1440297260908017072900193)
                  ·
                    refine ⟨1080222945681012804675145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1440297260908017072900193 1080222945681012804675145)
                    ·
                      refine ⟨810167209260759603506359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1080222945681012804675145 810167209260759603506359)
                      ·
                        rfl

theorem cell23_1577795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 4, 2, 2].length) (baseStart_1577795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577795 prefixEnd_1577795 := by exact prefixLift 1577795
  have htrace : WordTrace (prefixWord ++ tailWord_1577795) baseStart_1577795 baseEnd_1577795 := by
    simpa [prefixWord, tailWord_1577795, baseEnd_1577795] using wordTrace_append hprefix tailTrace_1577795
  have hstable : (prefixWord ++ tailWord_1577795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577795).length < 2 ^ (prefixWord ++ tailWord_1577795).sum := by decide
  have hdescent : baseEnd_1577795 < baseStart_1577795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577801 : List Nat := [1, 2, 1, 1, 2, 5, 1, 3, 7]
def baseStart_1577801 : Nat := 118140960795 + 1577801 * 2 ^ 59
def prefixEnd_1577801 : Nat := 4983230072969 + 3 ^ 40 * 1577801 * 2
def baseEnd_1577801 : Nat := 90018921127187397781259

theorem tailTrace_1577801 : CollatzResearch.WordTrace tailWord_1577801 prefixEnd_1577801 90018921127187397781259 := by
  unfold tailWord_1577801
  simp only [CollatzResearch.WordTrace]
  refine ⟨57547130156903918802549257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38364753437935945868366171 57547130156903918802549257)
  ·
    refine ⟨43160347617677939101911943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57547130156903918802549257 43160347617677939101911943)
    ·
      refine ⟨64740521426516908652867915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43160347617677939101911943 64740521426516908652867915)
      ·
        refine ⟨97110782139775362979301873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64740521426516908652867915 97110782139775362979301873)
        ·
          refine ⟨72833086604831522234476405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97110782139775362979301873 72833086604831522234476405)
          ·
            refine ⟨6828101869202955209482163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72833086604831522234476405 6828101869202955209482163)
            ·
              refine ⟨10242152803804432814223245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6828101869202955209482163 10242152803804432814223245)
              ·
                refine ⟨3840807301426662305333717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10242152803804432814223245 3840807301426662305333717)
                ·
                  refine ⟨90018921127187397781259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3840807301426662305333717 90018921127187397781259)
                  ·
                    rfl

theorem cell23_1577801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 7].length) (baseStart_1577801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577801 prefixEnd_1577801 := by exact prefixLift 1577801
  have htrace : WordTrace (prefixWord ++ tailWord_1577801) baseStart_1577801 baseEnd_1577801 := by
    simpa [prefixWord, tailWord_1577801, baseEnd_1577801] using wordTrace_append hprefix tailTrace_1577801
  have hstable : (prefixWord ++ tailWord_1577801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577801).length < 2 ^ (prefixWord ++ tailWord_1577801).sum := by decide
  have hdescent : baseEnd_1577801 < baseStart_1577801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577881 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 1, 3, 6]
def baseStart_1577881 : Nat := 118140960795 + 1577881 * 2 ^ 59
def prefixEnd_1577881 : Nat := 4983230072969 + 3 ^ 40 * 1577881 * 2
def baseEnd_1577881 : Nat := 810211368597046267030963

theorem tailTrace_1577881 : CollatzResearch.WordTrace tailWord_1577881 prefixEnd_1577881 810211368597046267030963 := by
  unfold tailWord_1577881
  simp only [CollatzResearch.WordTrace]
  refine ⟨57550047996614092465461497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38366698664409394976974331 57550047996614092465461497)
  ·
    refine ⟨43162535997460569349096123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57550047996614092465461497 43162535997460569349096123)
    ·
      refine ⟨64743803996190854023644185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43162535997460569349096123 64743803996190854023644185)
      ·
        refine ⟨48557852997143140517733139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64743803996190854023644185 48557852997143140517733139)
        ·
          refine ⟨72836779495714710776599709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48557852997143140517733139 72836779495714710776599709)
          ·
            refine ⟨27313792310893016541224891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72836779495714710776599709 27313792310893016541224891)
            ·
              refine ⟨40970688466339524811837337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27313792310893016541224891 40970688466339524811837337)
              ·
                refine ⟨30728016349754643608878003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40970688466339524811837337 30728016349754643608878003)
                ·
                  refine ⟨46092024524631965413317005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30728016349754643608878003 46092024524631965413317005)
                  ·
                    refine ⟨17284509196736987029993877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46092024524631965413317005 17284509196736987029993877)
                    ·
                      refine ⟨810211368597046267030963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17284509196736987029993877 810211368597046267030963)
                      ·
                        rfl

theorem cell23_1577881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_1577881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577881 prefixEnd_1577881 := by exact prefixLift 1577881
  have htrace : WordTrace (prefixWord ++ tailWord_1577881) baseStart_1577881 baseEnd_1577881 := by
    simpa [prefixWord, tailWord_1577881, baseEnd_1577881] using wordTrace_append hprefix tailTrace_1577881
  have hstable : (prefixWord ++ tailWord_1577881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577881).length < 2 ^ (prefixWord ++ tailWord_1577881).sum := by decide
  have hdescent : baseEnd_1577881 < baseStart_1577881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577885 : List Nat := [1, 4, 2, 1, 2, 1, 4, 1, 2, 1, 4]
def baseStart_1577885 : Nat := 118140960795 + 1577885 * 2 ^ 59
def prefixEnd_1577885 : Nat := 4983230072969 + 3 ^ 40 * 1577885 * 2
def baseEnd_1577885 : Nat := 810213422519664251380945

theorem tailTrace_1577885 : CollatzResearch.WordTrace tailWord_1577885 prefixEnd_1577885 810213422519664251380945 := by
  unfold tailWord_1577885
  simp only [CollatzResearch.WordTrace]
  refine ⟨57550193888599601148607109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38366795925733067432404739 57550193888599601148607109)
  ·
    refine ⟨10790661354112425215363833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57550193888599601148607109 10790661354112425215363833)
    ·
      refine ⟨8092996015584318911522875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10790661354112425215363833 8092996015584318911522875)
      ·
        refine ⟨12139494023376478367284313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8092996015584318911522875 12139494023376478367284313)
        ·
          refine ⟨9104620517532358775463235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12139494023376478367284313 9104620517532358775463235)
          ·
            refine ⟨13656930776298538163194853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9104620517532358775463235 13656930776298538163194853)
            ·
              refine ⟨2560674520555975905599035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13656930776298538163194853 2560674520555975905599035)
              ·
                refine ⟨3841011780833963858398553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2560674520555975905599035 3841011780833963858398553)
                ·
                  refine ⟨2880758835625472893798915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3841011780833963858398553 2880758835625472893798915)
                  ·
                    refine ⟨4321138253438209340698373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2880758835625472893798915 4321138253438209340698373)
                    ·
                      refine ⟨810213422519664251380945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4321138253438209340698373 810213422519664251380945)
                      ·
                        rfl

theorem cell23_1577885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_1577885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577885 prefixEnd_1577885 := by exact prefixLift 1577885
  have htrace : WordTrace (prefixWord ++ tailWord_1577885) baseStart_1577885 baseEnd_1577885 := by
    simpa [prefixWord, tailWord_1577885, baseEnd_1577885] using wordTrace_append hprefix tailTrace_1577885
  have hstable : (prefixWord ++ tailWord_1577885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577885).length < 2 ^ (prefixWord ++ tailWord_1577885).sum := by decide
  have hdescent : baseEnd_1577885 < baseStart_1577885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577888 : List Nat := [2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 3]
def baseStart_1577888 : Nat := 118140960795 + 1577888 * 2 ^ 59
def prefixEnd_1577888 : Nat := 4983230072969 + 3 ^ 40 * 1577888 * 2
def baseEnd_1577888 : Nat := 810214962961627739643431

theorem tailTrace_1577888 : CollatzResearch.WordTrace tailWord_1577888 prefixEnd_1577888 810214962961627739643431 := by
  unfold tailWord_1577888
  simp only [CollatzResearch.WordTrace]
  refine ⟨28775151653794366330483159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38366868871725821773977545 28775151653794366330483159)
  ·
    refine ⟨43162727480691549495724739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28775151653794366330483159 43162727480691549495724739)
    ·
      refine ⟨64744091221037324243587109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43162727480691549495724739 64744091221037324243587109)
      ·
        refine ⟨12139517103944498295672583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64744091221037324243587109 12139517103944498295672583)
        ·
          refine ⟨18209275655916747443508875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12139517103944498295672583 18209275655916747443508875)
          ·
            refine ⟨27313913483875121165263313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18209275655916747443508875 27313913483875121165263313)
            ·
              refine ⟨20485435112906340873947485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27313913483875121165263313 20485435112906340873947485)
              ·
                refine ⟨7682038167339877827730307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20485435112906340873947485 7682038167339877827730307)
                ·
                  refine ⟨11523057251009816741595461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7682038167339877827730307 11523057251009816741595461)
                  ·
                    refine ⟨2160573234564340639049149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11523057251009816741595461 2160573234564340639049149)
                    ·
                      refine ⟨810214962961627739643431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2160573234564340639049149 810214962961627739643431)
                      ·
                        rfl

theorem cell23_1577888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_1577888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577888 prefixEnd_1577888 := by exact prefixLift 1577888
  have htrace : WordTrace (prefixWord ++ tailWord_1577888) baseStart_1577888 baseEnd_1577888 := by
    simpa [prefixWord, tailWord_1577888, baseEnd_1577888] using wordTrace_append hprefix tailTrace_1577888
  have hstable : (prefixWord ++ tailWord_1577888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577888).length < 2 ^ (prefixWord ++ tailWord_1577888).sum := by decide
  have hdescent : baseEnd_1577888 < baseStart_1577888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577891 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 10]
def baseStart_1577891 : Nat := 118140960795 + 1577891 * 2 ^ 59
def prefixEnd_1577891 : Nat := 4983230072969 + 3 ^ 40 * 1577891 * 2
def baseEnd_1577891 : Nat := 90024055933732358656213

theorem tailTrace_1577891 : CollatzResearch.WordTrace tailWord_1577891 prefixEnd_1577891 90024055933732358656213 := by
  unfold tailWord_1577891
  simp only [CollatzResearch.WordTrace]
  refine ⟨57550412726577864173325527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38366941817718576115550351 57550412726577864173325527)
  ·
    refine ⟨86325619089866796259988291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57550412726577864173325527 86325619089866796259988291)
    ·
      refine ⟨129488428634800194389982437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86325619089866796259988291 129488428634800194389982437)
      ·
        refine ⟨24279080369025036448121707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129488428634800194389982437 24279080369025036448121707)
        ·
          refine ⟨36418620553537554672182561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24279080369025036448121707 36418620553537554672182561)
          ·
            refine ⟨27313965415153166004136921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36418620553537554672182561 27313965415153166004136921)
            ·
              refine ⟨20485474061364874503102691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27313965415153166004136921 20485474061364874503102691)
              ·
                refine ⟨30728211092047311754654037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20485474061364874503102691 30728211092047311754654037)
                ·
                  refine ⟨90024055933732358656213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 30728211092047311754654037 90024055933732358656213)
                  ·
                    rfl

theorem cell23_1577891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 10].length) (baseStart_1577891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577891 prefixEnd_1577891 := by exact prefixLift 1577891
  have htrace : WordTrace (prefixWord ++ tailWord_1577891) baseStart_1577891 baseEnd_1577891 := by
    simpa [prefixWord, tailWord_1577891, baseEnd_1577891] using wordTrace_append hprefix tailTrace_1577891
  have hstable : (prefixWord ++ tailWord_1577891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577891).length < 2 ^ (prefixWord ++ tailWord_1577891).sum := by decide
  have hdescent : baseEnd_1577891 < baseStart_1577891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577912 : List Nat := [2, 1, 2, 1, 2, 5, 1, 4, 1, 4]
def baseStart_1577912 : Nat := 118140960795 + 1577912 * 2 ^ 59
def prefixEnd_1577912 : Nat := 4983230072969 + 3 ^ 40 * 1577912 * 2
def baseEnd_1577912 : Nat := 270075762165778548581107

theorem tailTrace_1577912 : CollatzResearch.WordTrace tailWord_1577912 prefixEnd_1577912 270075762165778548581107 := by
  unfold tailWord_1577912
  simp only [CollatzResearch.WordTrace]
  refine ⟨28775589329750892379919995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38367452439667856506559993 28775589329750892379919995)
  ·
    refine ⟨43163383994626338569879993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28775589329750892379919995 43163383994626338569879993)
    ·
      refine ⟨32372537995969753927409995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43163383994626338569879993 32372537995969753927409995)
      ·
        refine ⟨48558806993954630891114993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32372537995969753927409995 48558806993954630891114993)
        ·
          refine ⟨36419105245465973168336245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48558806993954630891114993 36419105245465973168336245)
          ·
            refine ⟨3414291116762434984531523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36419105245465973168336245 3414291116762434984531523)
            ·
              refine ⟨5121436675143652476797285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3414291116762434984531523 5121436675143652476797285)
              ·
                refine ⟨960269376589434839399491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5121436675143652476797285 960269376589434839399491)
                ·
                  refine ⟨1440404064884152259099237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 960269376589434839399491 1440404064884152259099237)
                  ·
                    refine ⟨270075762165778548581107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1440404064884152259099237 270075762165778548581107)
                    ·
                      rfl

theorem cell23_1577912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 4, 1, 4].length) (baseStart_1577912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577912 prefixEnd_1577912 := by exact prefixLift 1577912
  have htrace : WordTrace (prefixWord ++ tailWord_1577912) baseStart_1577912 baseEnd_1577912 := by
    simpa [prefixWord, tailWord_1577912, baseEnd_1577912] using wordTrace_append hprefix tailTrace_1577912
  have hstable : (prefixWord ++ tailWord_1577912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577912).length < 2 ^ (prefixWord ++ tailWord_1577912).sum := by decide
  have hdescent : baseEnd_1577912 < baseStart_1577912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577933 : List Nat := [1, 6, 3, 1, 2, 1, 1, 1, 2, 5]
def baseStart_1577933 : Nat := 118140960795 + 1577933 * 2 ^ 59
def prefixEnd_1577933 : Nat := 4983230072969 + 3 ^ 40 * 1577933 * 2
def baseEnd_1577933 : Nat := 270079356530360021193575

theorem tailTrace_1577933 : CollatzResearch.WordTrace tailWord_1577933 prefixEnd_1577933 270079356530360021193575 := by
  unfold tailWord_1577933
  simp only [CollatzResearch.WordTrace]
  refine ⟨57551944592425705346354453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38367963061617136897569635 57551944592425705346354453)
  ·
    refine ⟨2697747402769954938110365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 57551944592425705346354453 2697747402769954938110365)
    ·
      refine ⟨1011655276038733101791387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2697747402769954938110365 1011655276038733101791387)
      ·
        refine ⟨1517482914058099652687081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1011655276038733101791387 1517482914058099652687081)
        ·
          refine ⟨1138112185543574739515311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1517482914058099652687081 1138112185543574739515311)
          ·
            refine ⟨1707168278315362109272967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1138112185543574739515311 1707168278315362109272967)
            ·
              refine ⟨2560752417473043163909451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1707168278315362109272967 2560752417473043163909451)
              ·
                refine ⟨3841128626209564745864177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2560752417473043163909451 3841128626209564745864177)
                ·
                  refine ⟨2880846469657173559398133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3841128626209564745864177 2880846469657173559398133)
                  ·
                    refine ⟨270079356530360021193575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2880846469657173559398133 270079356530360021193575)
                    ·
                      rfl

theorem cell23_1577933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_1577933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577933 prefixEnd_1577933 := by exact prefixLift 1577933
  have htrace : WordTrace (prefixWord ++ tailWord_1577933) baseStart_1577933 baseEnd_1577933 := by
    simpa [prefixWord, tailWord_1577933, baseEnd_1577933] using wordTrace_append hprefix tailTrace_1577933
  have hstable : (prefixWord ++ tailWord_1577933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577933).length < 2 ^ (prefixWord ++ tailWord_1577933).sum := by decide
  have hdescent : baseEnd_1577933 < baseStart_1577933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577935 : List Nat := [1, 1, 2, 1, 1, 6, 1, 1, 5, 1, 3]
def baseStart_1577935 : Nat := 118140960795 + 1577935 * 2 ^ 59
def prefixEnd_1577935 : Nat := 4983230072969 + 3 ^ 40 * 1577935 * 2
def baseEnd_1577935 : Nat := 810239096552389055755715

theorem tailTrace_1577935 : CollatzResearch.WordTrace tailWord_1577935 prefixEnd_1577935 810239096552389055755715 := by
  unfold tailWord_1577935
  simp only [CollatzResearch.WordTrace]
  refine ⟨57552017538418459687927259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38368011692278973125284839 57552017538418459687927259)
  ·
    refine ⟨86328026307627689531890889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57552017538418459687927259 86328026307627689531890889)
    ·
      refine ⟨64746019730720767148918167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86328026307627689531890889 64746019730720767148918167)
      ·
        refine ⟨97119029596081150723377251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64746019730720767148918167 97119029596081150723377251)
        ·
          refine ⟨145678544394121726085065877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97119029596081150723377251 145678544394121726085065877)
          ·
            refine ⟨6828681768474455910237463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 145678544394121726085065877 6828681768474455910237463)
            ·
              refine ⟨10243022652711683865356195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6828681768474455910237463 10243022652711683865356195)
              ·
                refine ⟨15364533979067525798034293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10243022652711683865356195 15364533979067525798034293)
                ·
                  refine ⟨1440425060537580543565715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15364533979067525798034293 1440425060537580543565715)
                  ·
                    refine ⟨2160637590806370815348573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1440425060537580543565715 2160637590806370815348573)
                    ·
                      refine ⟨810239096552389055755715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2160637590806370815348573 810239096552389055755715)
                      ·
                        rfl

theorem cell23_1577935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 5, 1, 3].length) (baseStart_1577935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577935 prefixEnd_1577935 := by exact prefixLift 1577935
  have htrace : WordTrace (prefixWord ++ tailWord_1577935) baseStart_1577935 baseEnd_1577935 := by
    simpa [prefixWord, tailWord_1577935, baseEnd_1577935] using wordTrace_append hprefix tailTrace_1577935
  have hstable : (prefixWord ++ tailWord_1577935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577935).length < 2 ^ (prefixWord ++ tailWord_1577935).sum := by decide
  have hdescent : baseEnd_1577935 < baseStart_1577935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577955 : List Nat := [1, 1, 1, 6, 1, 1, 3, 3, 1, 5]
def baseStart_1577955 : Nat := 118140960795 + 1577955 * 2 ^ 59
def prefixEnd_1577955 : Nat := 4983230072969 + 3 ^ 40 * 1577955 * 2
def baseEnd_1577955 : Nat := 270083122055159659168541

theorem tailTrace_1577955 : CollatzResearch.WordTrace tailWord_1577955 prefixEnd_1577955 270083122055159659168541 := by
  unfold tailWord_1577955
  simp only [CollatzResearch.WordTrace]
  refine ⟨57552746998346003103655319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38368497998897335402436879 57552746998346003103655319)
  ·
    refine ⟨86329120497519004655482979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57552746998346003103655319 86329120497519004655482979)
    ·
      refine ⟨129493680746278506983224469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86329120497519004655482979 129493680746278506983224469)
      ·
        refine ⟨6070016284981805014838647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 129493680746278506983224469 6070016284981805014838647)
        ·
          refine ⟨9105024427472707522257971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6070016284981805014838647 9105024427472707522257971)
          ·
            refine ⟨13657536641209061283386957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9105024427472707522257971 13657536641209061283386957)
            ·
              refine ⟨5121576240453397981270109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13657536641209061283386957 5121576240453397981270109)
              ·
                refine ⟨1920591090170024242976291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5121576240453397981270109 1920591090170024242976291)
                ·
                  refine ⟨2880886635255036364464437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1920591090170024242976291 2880886635255036364464437)
                  ·
                    refine ⟨270083122055159659168541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2880886635255036364464437 270083122055159659168541)
                    ·
                      rfl

theorem cell23_1577955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 5].length) (baseStart_1577955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577955 prefixEnd_1577955 := by exact prefixLift 1577955
  have htrace : WordTrace (prefixWord ++ tailWord_1577955) baseStart_1577955 baseEnd_1577955 := by
    simpa [prefixWord, tailWord_1577955, baseEnd_1577955] using wordTrace_append hprefix tailTrace_1577955
  have hstable : (prefixWord ++ tailWord_1577955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577955).length < 2 ^ (prefixWord ++ tailWord_1577955).sum := by decide
  have hdescent : baseEnd_1577955 < baseStart_1577955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577969 : List Nat := [1, 2, 2, 2, 4, 1, 2, 4, 1, 1, 3]
def baseStart_1577969 : Nat := 118140960795 + 1577969 * 2 ^ 59
def prefixEnd_1577969 : Nat := 4983230072969 + 3 ^ 40 * 1577969 * 2
def baseEnd_1577969 : Nat := 810256554894641922730559

theorem tailTrace_1577969 : CollatzResearch.WordTrace tailWord_1577969 prefixEnd_1577969 810256554894641922730559 := by
  unfold tailWord_1577969
  simp only [CollatzResearch.WordTrace]
  refine ⟨57553257620295283494664961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38368838413530188996443307 57553257620295283494664961)
  ·
    refine ⟨43164943215221462620998721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57553257620295283494664961 43164943215221462620998721)
    ·
      refine ⟨32373707411416096965749041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43164943215221462620998721 32373707411416096965749041)
      ·
        refine ⟨24280280558562072724311781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32373707411416096965749041 24280280558562072724311781)
        ·
          refine ⟨4552552604730388635808459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24280280558562072724311781 4552552604730388635808459)
          ·
            refine ⟨6828828907095582953712689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4552552604730388635808459 6828828907095582953712689)
            ·
              refine ⟨5121621680321687215284517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6828828907095582953712689 5121621680321687215284517)
              ·
                refine ⟨960304065060316352865847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5121621680321687215284517 960304065060316352865847)
                ·
                  refine ⟨1440456097590474529298771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 960304065060316352865847 1440456097590474529298771)
                  ·
                    refine ⟨2160684146385711793948157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1440456097590474529298771 2160684146385711793948157)
                    ·
                      refine ⟨810256554894641922730559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2160684146385711793948157 810256554894641922730559)
                      ·
                        rfl

theorem cell23_1577969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 4, 1, 1, 3].length) (baseStart_1577969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577969 prefixEnd_1577969 := by exact prefixLift 1577969
  have htrace : WordTrace (prefixWord ++ tailWord_1577969) baseStart_1577969 baseEnd_1577969 := by
    simpa [prefixWord, tailWord_1577969, baseEnd_1577969] using wordTrace_append hprefix tailTrace_1577969
  have hstable : (prefixWord ++ tailWord_1577969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577969).length < 2 ^ (prefixWord ++ tailWord_1577969).sum := by decide
  have hdescent : baseEnd_1577969 < baseStart_1577969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577985 : List Nat := [1, 2, 4, 1, 2, 2, 3, 1, 1, 6]
def baseStart_1577985 : Nat := 118140960795 + 1577985 * 2 ^ 59
def prefixEnd_1577985 : Nat := 4983230072969 + 3 ^ 40 * 1577985 * 2
def baseEnd_1577985 : Nat := 270088256861704620043495

theorem tailTrace_1577985 : CollatzResearch.WordTrace tailWord_1577985 prefixEnd_1577985 270088256861704620043495 := by
  unfold tailWord_1577985
  simp only [CollatzResearch.WordTrace]
  refine ⟨57553841188237318227247409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38369227458824878818164939 57553841188237318227247409)
  ·
    refine ⟨43165380891177988670435557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57553841188237318227247409 43165380891177988670435557)
    ·
      refine ⟨8093508917095872875706667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43165380891177988670435557 8093508917095872875706667)
      ·
        refine ⟨12140263375643809313560001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8093508917095872875706667 12140263375643809313560001)
        ·
          refine ⟨9105197531732856985170001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12140263375643809313560001 9105197531732856985170001)
          ·
            refine ⟨6828898148799642738877501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9105197531732856985170001 6828898148799642738877501)
            ·
              refine ⟨2560836805799866027079063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6828898148799642738877501 2560836805799866027079063)
              ·
                refine ⟨3841255208699799040618595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2560836805799866027079063 3841255208699799040618595)
                ·
                  refine ⟨5761882813049698560927893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3841255208699799040618595 5761882813049698560927893)
                  ·
                    refine ⟨270088256861704620043495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5761882813049698560927893 270088256861704620043495)
                    ·
                      rfl

theorem cell23_1577985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_1577985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577985 prefixEnd_1577985 := by exact prefixLift 1577985
  have htrace : WordTrace (prefixWord ++ tailWord_1577985) baseStart_1577985 baseEnd_1577985 := by
    simpa [prefixWord, tailWord_1577985, baseEnd_1577985] using wordTrace_append hprefix tailTrace_1577985
  have hstable : (prefixWord ++ tailWord_1577985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577985).length < 2 ^ (prefixWord ++ tailWord_1577985).sum := by decide
  have hdescent : baseEnd_1577985 < baseStart_1577985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577992 : List Nat := [2, 1, 3, 2, 1, 4, 2, 2, 1, 1, 4]
def baseStart_1577992 : Nat := 118140960795 + 1577992 * 2 ^ 59
def prefixEnd_1577992 : Nat := 4983230072969 + 3 ^ 40 * 1577992 * 2
def baseEnd_1577992 : Nat := 810268364949695332742953

theorem tailTrace_1577992 : CollatzResearch.WordTrace tailWord_1577992 prefixEnd_1577992 810268364949695332742953 := by
  unfold tailWord_1577992
  simp only [CollatzResearch.WordTrace]
  refine ⟨28777048249605979211376115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38369397666141305615168153 28777048249605979211376115)
  ·
    refine ⟨43165572374408968817064173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28777048249605979211376115 43165572374408968817064173)
    ·
      refine ⟨16187089640403363306399065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43165572374408968817064173 16187089640403363306399065)
      ·
        refine ⟨12140317230302522479799299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16187089640403363306399065 12140317230302522479799299)
        ·
          refine ⟨18210475845453783719698949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12140317230302522479799299 18210475845453783719698949)
          ·
            refine ⟨3414464221022584447443553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18210475845453783719698949 3414464221022584447443553)
            ·
              refine ⟨2560848165766938335582665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3414464221022584447443553 2560848165766938335582665)
              ·
                refine ⟨1920636124325203751686999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2560848165766938335582665 1920636124325203751686999)
                ·
                  refine ⟨2880954186487805627530499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1920636124325203751686999 2880954186487805627530499)
                  ·
                    refine ⟨4321431279731708441295749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2880954186487805627530499 4321431279731708441295749)
                    ·
                      refine ⟨810268364949695332742953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4321431279731708441295749 810268364949695332742953)
                      ·
                        rfl

theorem cell23_1577992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_1577992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1577992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1577992 prefixEnd_1577992 := by exact prefixLift 1577992
  have htrace : WordTrace (prefixWord ++ tailWord_1577992) baseStart_1577992 baseEnd_1577992 := by
    simpa [prefixWord, tailWord_1577992, baseEnd_1577992] using wordTrace_append hprefix tailTrace_1577992
  have hstable : (prefixWord ++ tailWord_1577992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577992).length < 2 ^ (prefixWord ++ tailWord_1577992).sum := by decide
  have hdescent : baseEnd_1577992 < baseStart_1577992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578012 : List Nat := [2, 2, 3, 1, 4, 1, 2, 1, 1, 1, 5]
def baseStart_1578012 : Nat := 118140960795 + 1578012 * 2 ^ 59
def prefixEnd_1578012 : Nat := 4983230072969 + 3 ^ 40 * 1578012 * 2
def baseEnd_1578012 : Nat := 810278634562785254492861

theorem tailTrace_1578012 : CollatzResearch.WordTrace tailWord_1578012 prefixEnd_1578012 810278634562785254492861 := by
  unfold tailWord_1578012
  simp only [CollatzResearch.WordTrace]
  refine ⟨28777412979569750919240145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38369883972759667892320193 28777412979569750919240145)
  ·
    refine ⟨21583059734677313189430109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28777412979569750919240145 21583059734677313189430109)
    ·
      refine ⟨8093647400503992446036291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21583059734677313189430109 8093647400503992446036291)
      ·
        refine ⟨12140471100755988669054437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8093647400503992446036291 12140471100755988669054437)
        ·
          refine ⟨2276338331391747875447707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12140471100755988669054437 2276338331391747875447707)
          ·
            refine ⟨3414507497087621813171561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2276338331391747875447707 3414507497087621813171561)
            ·
              refine ⟨2560880622815716359878671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3414507497087621813171561 2560880622815716359878671)
              ·
                refine ⟨3841320934223574539818007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2560880622815716359878671 3841320934223574539818007)
                ·
                  refine ⟨5761981401335361809727011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3841320934223574539818007 5761981401335361809727011)
                  ·
                    refine ⟨8642972102003042714590517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5761981401335361809727011 8642972102003042714590517)
                    ·
                      refine ⟨810278634562785254492861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8642972102003042714590517 810278634562785254492861)
                      ·
                        rfl

theorem cell23_1578012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_1578012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578012 prefixEnd_1578012 := by exact prefixLift 1578012
  have htrace : WordTrace (prefixWord ++ tailWord_1578012) baseStart_1578012 baseEnd_1578012 := by
    simpa [prefixWord, tailWord_1578012, baseEnd_1578012] using wordTrace_append hprefix tailTrace_1578012
  have hstable : (prefixWord ++ tailWord_1578012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578012).length < 2 ^ (prefixWord ++ tailWord_1578012).sum := by decide
  have hdescent : baseEnd_1578012 < baseStart_1578012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578028 : List Nat := [2, 2, 1, 1, 1, 2, 4, 1, 2, 7]
def baseStart_1578028 : Nat := 118140960795 + 1578028 * 2 ^ 59
def prefixEnd_1578028 : Nat := 4983230072969 + 3 ^ 40 * 1578028 * 2
def baseEnd_1578028 : Nat := 270095616751085730630929

theorem tailTrace_1578028 : CollatzResearch.WordTrace tailWord_1578028 prefixEnd_1578028 270095616751085730630929 := by
  unfold tailWord_1578028
  simp only [CollatzResearch.WordTrace]
  refine ⟨28777704763540768285531369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38370273018054357714041825 28777704763540768285531369)
  ·
    refine ⟨21583278572655576214148527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28777704763540768285531369 21583278572655576214148527)
    ·
      refine ⟨32374917858983364321222791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21583278572655576214148527 32374917858983364321222791)
      ·
        refine ⟨48562376788475046481834187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32374917858983364321222791 48562376788475046481834187)
        ·
          refine ⟨72843565182712569722751281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48562376788475046481834187 72843565182712569722751281)
          ·
            refine ⟨54632673887034427292063461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72843565182712569722751281 54632673887034427292063461)
            ·
              refine ⟨10243626353818955117261899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54632673887034427292063461 10243626353818955117261899)
              ·
                refine ⟨15365439530728432675892849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10243626353818955117261899 15365439530728432675892849)
                ·
                  refine ⟨11524079648046324506919637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15365439530728432675892849 11524079648046324506919637)
                  ·
                    refine ⟨270095616751085730630929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11524079648046324506919637 270095616751085730630929)
                    ·
                      rfl

theorem cell23_1578028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 7].length) (baseStart_1578028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578028 prefixEnd_1578028 := by exact prefixLift 1578028
  have htrace : WordTrace (prefixWord ++ tailWord_1578028) baseStart_1578028 baseEnd_1578028 := by
    simpa [prefixWord, tailWord_1578028, baseEnd_1578028] using wordTrace_append hprefix tailTrace_1578028
  have hstable : (prefixWord ++ tailWord_1578028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578028).length < 2 ^ (prefixWord ++ tailWord_1578028).sum := by decide
  have hdescent : baseEnd_1578028 < baseStart_1578028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578035 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 2, 7, 2]
def baseStart_1578035 : Nat := 118140960795 + 1578035 * 2 ^ 59
def prefixEnd_1578035 : Nat := 4983230072969 + 3 ^ 40 * 1578035 * 2
def baseEnd_1578035 : Nat := 810290444617838664505255

theorem tailTrace_1578035 : CollatzResearch.WordTrace tailWord_1578035 prefixEnd_1578035 810290444617838664505255 := by
  unfold tailWord_1578035
  simp only [CollatzResearch.WordTrace]
  refine ⟨57555664838056176766567559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38370443225370784511045039 57555664838056176766567559)
  ·
    refine ⟨86333497257084265149851339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57555664838056176766567559 86333497257084265149851339)
    ·
      refine ⟨129500245885626397724777009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86333497257084265149851339 129500245885626397724777009)
      ·
        refine ⟨97125184414219798293582757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129500245885626397724777009 97125184414219798293582757)
        ·
          refine ⟨18210972077666212180046767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97125184414219798293582757 18210972077666212180046767)
          ·
            refine ⟨27316458116499318270070151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18210972077666212180046767 27316458116499318270070151)
            ·
              refine ⟨40974687174748977405105227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27316458116499318270070151 40974687174748977405105227)
              ·
                refine ⟨61462030762123466107657841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40974687174748977405105227 61462030762123466107657841)
                ·
                  refine ⟨46096523071592599580743381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61462030762123466107657841 46096523071592599580743381)
                  ·
                    refine ⟨1080387259490451552673673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46096523071592599580743381 1080387259490451552673673)
                    ·
                      refine ⟨810290444617838664505255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1080387259490451552673673 810290444617838664505255)
                      ·
                        rfl

theorem cell23_1578035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 7, 2].length) (baseStart_1578035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578035 prefixEnd_1578035 := by exact prefixLift 1578035
  have htrace : WordTrace (prefixWord ++ tailWord_1578035) baseStart_1578035 baseEnd_1578035 := by
    simpa [prefixWord, tailWord_1578035, baseEnd_1578035] using wordTrace_append hprefix tailTrace_1578035
  have hstable : (prefixWord ++ tailWord_1578035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578035).length < 2 ^ (prefixWord ++ tailWord_1578035).sum := by decide
  have hdescent : baseEnd_1578035 < baseStart_1578035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578036 : List Nat := [2, 5, 1, 2, 1, 1, 4, 1, 2, 4]
def baseStart_1578036 : Nat := 118140960795 + 1578036 * 2 ^ 59
def prefixEnd_1578036 : Nat := 4983230072969 + 3 ^ 40 * 1578036 * 2
def baseEnd_1578036 : Nat := 270096986032831053530917

theorem tailTrace_1578036 : CollatzResearch.WordTrace tailWord_1578036 prefixEnd_1578036 270096986032831053530917 := by
  unfold tailWord_1578036
  simp only [CollatzResearch.WordTrace]
  refine ⟨28777850655526276968676981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38370467540701702624902641 28777850655526276968676981)
  ·
    refine ⟨2697923498955588465813467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28777850655526276968676981 2697923498955588465813467)
    ·
      refine ⟨4046885248433382698720201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2697923498955588465813467 4046885248433382698720201)
      ·
        refine ⟨3035163936325037024040151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4046885248433382698720201 3035163936325037024040151)
        ·
          refine ⟨4552745904487555536060227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3035163936325037024040151 4552745904487555536060227)
          ·
            refine ⟨6829118856731333304090341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4552745904487555536060227 6829118856731333304090341)
            ·
              refine ⟨1280459785637124994516939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6829118856731333304090341 1280459785637124994516939)
              ·
                refine ⟨1920689678455687491775409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1280459785637124994516939 1920689678455687491775409)
                ·
                  refine ⟨1440517258841765618831557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1920689678455687491775409 1440517258841765618831557)
                  ·
                    refine ⟨270096986032831053530917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1440517258841765618831557 270096986032831053530917)
                    ·
                      rfl

theorem cell23_1578036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_1578036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578036 prefixEnd_1578036 := by exact prefixLift 1578036
  have htrace : WordTrace (prefixWord ++ tailWord_1578036) baseStart_1578036 baseEnd_1578036 := by
    simpa [prefixWord, tailWord_1578036, baseEnd_1578036] using wordTrace_append hprefix tailTrace_1578036
  have hstable : (prefixWord ++ tailWord_1578036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578036).length < 2 ^ (prefixWord ++ tailWord_1578036).sum := by decide
  have hdescent : baseEnd_1578036 < baseStart_1578036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578046 : List Nat := [4, 2, 1, 3, 1, 3, 1, 2, 1, 2, 3]
def baseStart_1578046 : Nat := 118140960795 + 1578046 * 2 ^ 59
def prefixEnd_1578046 : Nat := 4983230072969 + 3 ^ 40 * 1578046 * 2
def baseEnd_1578046 : Nat := 810296092905038121467705

theorem tailTrace_1578046 : CollatzResearch.WordTrace tailWord_1578046 prefixEnd_1578046 810296092905038121467705 := by
  unfold tailWord_1578046
  simp only [CollatzResearch.WordTrace]
  refine ⟨7194508255127040705652249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38370710694010883763478661 7194508255127040705652249)
  ·
    refine ⟨5395881191345280529239187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7194508255127040705652249 5395881191345280529239187)
    ·
      refine ⟨8093821787017920793858781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5395881191345280529239187 8093821787017920793858781)
      ·
        refine ⟨3035183170131720297697043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8093821787017920793858781 3035183170131720297697043)
        ·
          refine ⟨4552774755197580446545565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3035183170131720297697043 4552774755197580446545565)
          ·
            refine ⟨1707290533199092667454587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4552774755197580446545565 1707290533199092667454587)
            ·
              refine ⟨2560935799798639001181881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1707290533199092667454587 2560935799798639001181881)
              ·
                refine ⟨1920701849848979250886411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2560935799798639001181881 1920701849848979250886411)
                ·
                  refine ⟨2881052774773468876329617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1920701849848979250886411 2881052774773468876329617)
                  ·
                    refine ⟨2160789581080101657247213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2881052774773468876329617 2160789581080101657247213)
                    ·
                      refine ⟨810296092905038121467705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2160789581080101657247213 810296092905038121467705)
                      ·
                        rfl

theorem cell23_1578046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_1578046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578046 prefixEnd_1578046 := by exact prefixLift 1578046
  have htrace : WordTrace (prefixWord ++ tailWord_1578046) baseStart_1578046 baseEnd_1578046 := by
    simpa [prefixWord, tailWord_1578046, baseEnd_1578046] using wordTrace_append hprefix tailTrace_1578046
  have hstable : (prefixWord ++ tailWord_1578046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578046).length < 2 ^ (prefixWord ++ tailWord_1578046).sum := by decide
  have hdescent : baseEnd_1578046 < baseStart_1578046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578077 : List Nat := [1, 4, 4, 1, 2, 2, 2, 2, 1, 2, 2]
def baseStart_1578077 : Nat := 118140960795 + 1578077 * 2 ^ 59
def prefixEnd_1578077 : Nat := 4983230072969 + 3 ^ 40 * 1578077 * 2
def baseEnd_1578077 : Nat := 810312010805327500180063

theorem tailTrace_1578077 : CollatzResearch.WordTrace tailWord_1578077 prefixEnd_1578077 810312010805327500180063 := by
  unfold tailWord_1578077
  simp only [CollatzResearch.WordTrace]
  refine ⟨57557196703904017939596485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38371464469269345293064323 57557196703904017939596485)
  ·
    refine ⟨10791974381982003363674341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57557196703904017939596485 10791974381982003363674341)
    ·
      refine ⟨2023495196621625630688939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10791974381982003363674341 2023495196621625630688939)
      ·
        refine ⟨3035242794932438446033409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2023495196621625630688939 3035242794932438446033409)
        ·
          refine ⟨2276432096199328834525057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3035242794932438446033409 2276432096199328834525057)
          ·
            refine ⟨1707324072149496625893793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2276432096199328834525057 1707324072149496625893793)
            ·
              refine ⟨1280493054112122469420345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1707324072149496625893793 1280493054112122469420345)
              ·
                refine ⟨960369790584091852065259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1280493054112122469420345 960369790584091852065259)
                ·
                  refine ⟨1440554685876137778097889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 960369790584091852065259 1440554685876137778097889)
                  ·
                    refine ⟨1080416014407103333573417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1440554685876137778097889 1080416014407103333573417)
                    ·
                      refine ⟨810312010805327500180063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1080416014407103333573417 810312010805327500180063)
                      ·
                        rfl

theorem cell23_1578077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_1578077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578077 prefixEnd_1578077 := by exact prefixLift 1578077
  have htrace : WordTrace (prefixWord ++ tailWord_1578077) baseStart_1578077 baseEnd_1578077 := by
    simpa [prefixWord, tailWord_1578077, baseEnd_1578077] using wordTrace_append hprefix tailTrace_1578077
  have hstable : (prefixWord ++ tailWord_1578077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578077).length < 2 ^ (prefixWord ++ tailWord_1578077).sum := by decide
  have hdescent : baseEnd_1578077 < baseStart_1578077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578082 : List Nat := [3, 3, 2, 2, 1, 1, 1, 1, 2, 3, 4]
def baseStart_1578082 : Nat := 118140960795 + 1578082 * 2 ^ 59
def prefixEnd_1578082 : Nat := 4983230072969 + 3 ^ 40 * 1578082 * 2
def baseEnd_1578082 : Nat := 810314578208599980617539

theorem tailTrace_1578082 : CollatzResearch.WordTrace tailWord_1578082 prefixEnd_1578082 810314578208599980617539 := by
  unfold tailWord_1578082
  simp only [CollatzResearch.WordTrace]
  refine ⟨14389344767221475948382125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38371586045923935862352333 14389344767221475948382125)
  ·
    refine ⟨5396004287708053480643297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14389344767221475948382125 5396004287708053480643297)
    ·
      refine ⟨4047003215781040110482473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5396004287708053480643297 4047003215781040110482473)
      ·
        refine ⟨3035252411835780082861855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4047003215781040110482473 3035252411835780082861855)
        ·
          refine ⟨4552878617753670124292783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3035252411835780082861855 4552878617753670124292783)
          ·
            refine ⟨6829317926630505186439175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4552878617753670124292783 6829317926630505186439175)
            ·
              refine ⟨10243976889945757779658763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6829317926630505186439175 10243976889945757779658763)
              ·
                refine ⟨15365965334918636669488145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10243976889945757779658763 15365965334918636669488145)
                ·
                  refine ⟨11524474001188977502116109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15365965334918636669488145 11524474001188977502116109)
                  ·
                    refine ⟨4321677750445866563293541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11524474001188977502116109 4321677750445866563293541)
                    ·
                      refine ⟨810314578208599980617539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4321677750445866563293541 810314578208599980617539)
                      ·
                        rfl

theorem cell23_1578082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_1578082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578082 prefixEnd_1578082 := by exact prefixLift 1578082
  have htrace : WordTrace (prefixWord ++ tailWord_1578082) baseStart_1578082 baseEnd_1578082 := by
    simpa [prefixWord, tailWord_1578082, baseEnd_1578082] using wordTrace_append hprefix tailTrace_1578082
  have hstable : (prefixWord ++ tailWord_1578082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578082).length < 2 ^ (prefixWord ++ tailWord_1578082).sum := by decide
  have hdescent : baseEnd_1578082 < baseStart_1578082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578085 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 1, 6, 3]
def baseStart_1578085 : Nat := 118140960795 + 1578085 * 2 ^ 59
def prefixEnd_1578085 : Nat := 4983230072969 + 3 ^ 40 * 1578085 * 2
def baseEnd_1578085 : Nat := 810316118650563468880025

theorem tailTrace_1578085 : CollatzResearch.WordTrace tailWord_1578085 prefixEnd_1578085 810316118650563468880025 := by
  unfold tailWord_1578085
  simp only [CollatzResearch.WordTrace]
  refine ⟨57557488487875035305887709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38371658991916690203925139 57557488487875035305887709)
  ·
    refine ⟨21584058182953138239707891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57557488487875035305887709 21584058182953138239707891)
    ·
      refine ⟨32376087274429707359561837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21584058182953138239707891 32376087274429707359561837)
      ·
        refine ⟨12141032727911140259835689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32376087274429707359561837 12141032727911140259835689)
        ·
          refine ⟨9105774545933355194876767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12141032727911140259835689 9105774545933355194876767)
          ·
            refine ⟨13658661818900032792315151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9105774545933355194876767 13658661818900032792315151)
            ·
              refine ⟨20487992728350049188472727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13658661818900032792315151 20487992728350049188472727)
              ·
                refine ⟨30731989092525073782709091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20487992728350049188472727 30731989092525073782709091)
                ·
                  refine ⟨46097983638787610674063637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30731989092525073782709091 46097983638787610674063637)
                  ·
                    refine ⟨2160842983068169250346733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 46097983638787610674063637 2160842983068169250346733)
                    ·
                      refine ⟨810316118650563468880025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2160842983068169250346733 810316118650563468880025)
                      ·
                        rfl

theorem cell23_1578085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_1578085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578085 prefixEnd_1578085 := by exact prefixLift 1578085
  have htrace : WordTrace (prefixWord ++ tailWord_1578085) baseStart_1578085 baseEnd_1578085 := by
    simpa [prefixWord, tailWord_1578085, baseEnd_1578085] using wordTrace_append hprefix tailTrace_1578085
  have hstable : (prefixWord ++ tailWord_1578085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578085).length < 2 ^ (prefixWord ++ tailWord_1578085).sum := by decide
  have hdescent : baseEnd_1578085 < baseStart_1578085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578095 : List Nat := [1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 4]
def baseStart_1578095 : Nat := 118140960795 + 1578095 * 2 ^ 59
def prefixEnd_1578095 : Nat := 4983230072969 + 3 ^ 40 * 1578095 * 2
def baseEnd_1578095 : Nat := 810321253457108429754979

theorem tailTrace_1578095 : CollatzResearch.WordTrace tailWord_1578095 prefixEnd_1578095 810321253457108429754979 := by
  unfold tailWord_1578095
  simp only [CollatzResearch.WordTrace]
  refine ⟨57557853217838807013751739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38371902145225871342501159 57557853217838807013751739)
  ·
    refine ⟨86336779826758210520627609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57557853217838807013751739 86336779826758210520627609)
    ·
      refine ⟨64752584870068657890470707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86336779826758210520627609 64752584870068657890470707)
      ·
        refine ⟨97128877305102986835706061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64752584870068657890470707 97128877305102986835706061)
        ·
          refine ⟨36423328989413620063389773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97128877305102986835706061 36423328989413620063389773)
          ·
            refine ⟨13658748371030107523771165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36423328989413620063389773 13658748371030107523771165)
            ·
              refine ⟨5122030639136290321414187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13658748371030107523771165 5122030639136290321414187)
              ·
                refine ⟨7683045958704435482121281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5122030639136290321414187 7683045958704435482121281)
                ·
                  refine ⟨5762284469028326611590961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7683045958704435482121281 5762284469028326611590961)
                  ·
                    refine ⟨4321713351771244958693221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5762284469028326611590961 4321713351771244958693221)
                    ·
                      refine ⟨810321253457108429754979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4321713351771244958693221 810321253457108429754979)
                      ·
                        rfl

theorem cell23_1578095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 4].length) (baseStart_1578095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578095 prefixEnd_1578095 := by exact prefixLift 1578095
  have htrace : WordTrace (prefixWord ++ tailWord_1578095) baseStart_1578095 baseEnd_1578095 := by
    simpa [prefixWord, tailWord_1578095, baseEnd_1578095] using wordTrace_append hprefix tailTrace_1578095
  have hstable : (prefixWord ++ tailWord_1578095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578095).length < 2 ^ (prefixWord ++ tailWord_1578095).sum := by decide
  have hdescent : baseEnd_1578095 < baseStart_1578095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578102 : List Nat := [5, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3]
def baseStart_1578102 : Nat := 118140960795 + 1578102 * 2 ^ 59
def prefixEnd_1578102 : Nat := 4983230072969 + 3 ^ 40 * 1578102 * 2
def baseEnd_1578102 : Nat := 810324847821689902367447

theorem tailTrace_1578102 : CollatzResearch.WordTrace tailWord_1578102 prefixEnd_1578102 810324847821689902367447 := by
  unfold tailWord_1578102
  simp only [CollatzResearch.WordTrace]
  refine ⟨3597381783050840450578535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38372072352542298139504373 3597381783050840450578535)
  ·
    refine ⟨5396072674576260675867803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3597381783050840450578535 5396072674576260675867803)
    ·
      refine ⟨8094109011864391013801705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5396072674576260675867803 8094109011864391013801705)
      ·
        refine ⟨6070581758898293260351279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8094109011864391013801705 6070581758898293260351279)
        ·
          refine ⟨9105872638347439890526919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6070581758898293260351279 9105872638347439890526919)
          ·
            refine ⟨13658808957521159835790379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9105872638347439890526919 13658808957521159835790379)
            ·
              refine ⟨20488213436281739753685569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13658808957521159835790379 20488213436281739753685569)
              ·
                refine ⟨15366160077211304815264177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20488213436281739753685569 15366160077211304815264177)
                ·
                  refine ⟨11524620057908478611448133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15366160077211304815264177 11524620057908478611448133)
                  ·
                    refine ⟨2160866260857839739646525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11524620057908478611448133 2160866260857839739646525)
                    ·
                      refine ⟨810324847821689902367447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2160866260857839739646525 810324847821689902367447)
                      ·
                        rfl

theorem cell23_1578102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_1578102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578102 prefixEnd_1578102 := by exact prefixLift 1578102
  have htrace : WordTrace (prefixWord ++ tailWord_1578102) baseStart_1578102 baseEnd_1578102 := by
    simpa [prefixWord, tailWord_1578102, baseEnd_1578102] using wordTrace_append hprefix tailTrace_1578102
  have hstable : (prefixWord ++ tailWord_1578102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578102).length < 2 ^ (prefixWord ++ tailWord_1578102).sum := by decide
  have hdescent : baseEnd_1578102 < baseStart_1578102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578115 : List Nat := [1, 1, 1, 3, 3, 2, 1, 2, 1, 5, 3]
def baseStart_1578115 : Nat := 118140960795 + 1578115 * 2 ^ 59
def prefixEnd_1578115 : Nat := 4983230072969 + 3 ^ 40 * 1578115 * 2
def baseEnd_1578115 : Nat := 810331523070198351504887

theorem tailTrace_1578115 : CollatzResearch.WordTrace tailWord_1578115 prefixEnd_1578115 810331523070198351504887 := by
  unfold tailWord_1578115
  simp only [CollatzResearch.WordTrace]
  refine ⟨57558582677766350429479799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38372388451844233619653199 57558582677766350429479799)
  ·
    refine ⟨86337874016649525644219699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57558582677766350429479799 86337874016649525644219699)
    ·
      refine ⟨129506811024974288466329549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86337874016649525644219699 129506811024974288466329549)
      ·
        refine ⟨48565054134365358174873581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129506811024974288466329549 48565054134365358174873581)
        ·
          refine ⟨18211895300387009315577593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48565054134365358174873581 18211895300387009315577593)
          ·
            refine ⟨13658921475290256986683195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18211895300387009315577593 13658921475290256986683195)
            ·
              refine ⟨20488382212935385480024793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13658921475290256986683195 20488382212935385480024793)
              ·
                refine ⟨15366286659701539110018595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20488382212935385480024793 15366286659701539110018595)
                ·
                  refine ⟨23049429989552308665027893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15366286659701539110018595 23049429989552308665027893)
                  ·
                    refine ⟨2160884061520528937346365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23049429989552308665027893 2160884061520528937346365)
                    ·
                      refine ⟨810331523070198351504887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2160884061520528937346365 810331523070198351504887)
                      ·
                        rfl

theorem cell23_1578115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 5, 3].length) (baseStart_1578115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578115 prefixEnd_1578115 := by exact prefixLift 1578115
  have htrace : WordTrace (prefixWord ++ tailWord_1578115) baseStart_1578115 baseEnd_1578115 := by
    simpa [prefixWord, tailWord_1578115, baseEnd_1578115] using wordTrace_append hprefix tailTrace_1578115
  have hstable : (prefixWord ++ tailWord_1578115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578115).length < 2 ^ (prefixWord ++ tailWord_1578115).sum := by decide
  have hdescent : baseEnd_1578115 < baseStart_1578115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578120 : List Nat := [2, 1, 3, 4, 3, 1, 2, 1, 1, 3, 2]
def baseStart_1578120 : Nat := 118140960795 + 1578120 * 2 ^ 59
def prefixEnd_1578120 : Nat := 4983230072969 + 3 ^ 40 * 1578120 * 2
def baseEnd_1578120 : Nat := 810334090473470831942365

theorem tailTrace_1578120 : CollatzResearch.WordTrace tailWord_1578120 prefixEnd_1578120 810334090473470831942365 := by
  unfold tailWord_1578120
  simp only [CollatzResearch.WordTrace]
  refine ⟨28779382521374118141705907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38372510028498824188941209 28779382521374118141705907)
  ·
    refine ⟨43169073782061177212558861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28779382521374118141705907 43169073782061177212558861)
    ·
      refine ⟨16188402668272941454709573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43169073782061177212558861 16188402668272941454709573)
      ·
        refine ⟨3035325500301176522758045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16188402668272941454709573 3035325500301176522758045)
        ·
          refine ⟨1138247062612941196034267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3035325500301176522758045 1138247062612941196034267)
          ·
            refine ⟨1707370593919411794051401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1138247062612941196034267 1707370593919411794051401)
            ·
              refine ⟨1280527945439558845538551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1707370593919411794051401 1280527945439558845538551)
              ·
                refine ⟨1920791918159338268307827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1280527945439558845538551 1920791918159338268307827)
                ·
                  refine ⟨2881187877239007402461741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1920791918159338268307827 2881187877239007402461741)
                  ·
                    refine ⟨1080445453964627775923153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2881187877239007402461741 1080445453964627775923153)
                    ·
                      refine ⟨810334090473470831942365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1080445453964627775923153 810334090473470831942365)
                      ·
                        rfl

theorem cell23_1578120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_1578120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578120 prefixEnd_1578120 := by exact prefixLift 1578120
  have htrace : WordTrace (prefixWord ++ tailWord_1578120) baseStart_1578120 baseEnd_1578120 := by
    simpa [prefixWord, tailWord_1578120, baseEnd_1578120] using wordTrace_append hprefix tailTrace_1578120
  have hstable : (prefixWord ++ tailWord_1578120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578120).length < 2 ^ (prefixWord ++ tailWord_1578120).sum := by decide
  have hdescent : baseEnd_1578120 < baseStart_1578120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578145 : List Nat := [1, 2, 3, 3, 1, 1, 2, 1, 1, 1, 7]
def baseStart_1578145 : Nat := 118140960795 + 1578145 * 2 ^ 59
def prefixEnd_1578145 : Nat := 4983230072969 + 3 ^ 40 * 1578145 * 2
def baseEnd_1578145 : Nat := 810346927489833234129749

theorem tailTrace_1578145 : CollatzResearch.WordTrace tailWord_1578145 prefixEnd_1578145 810346927489833234129749 := by
  unfold tailWord_1578145
  simp only [CollatzResearch.WordTrace]
  refine ⟨57559676867657665553071889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38373117911771777035381259 57559676867657665553071889)
  ·
    refine ⟨43169757650743249164803917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57559676867657665553071889 43169757650743249164803917)
    ·
      refine ⟨16188659119028718436801469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43169757650743249164803917 16188659119028718436801469)
      ·
        refine ⟨6070747169635769413800551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16188659119028718436801469 6070747169635769413800551)
        ·
          refine ⟨9106120754453654120700827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6070747169635769413800551 9106120754453654120700827)
          ·
            refine ⟨13659181131680481181051241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9106120754453654120700827 13659181131680481181051241)
            ·
              refine ⟨10244385848760360885788431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13659181131680481181051241 10244385848760360885788431)
              ·
                refine ⟨15366578773140541328682647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10244385848760360885788431 15366578773140541328682647)
                ·
                  refine ⟨23049868159710811993023971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15366578773140541328682647 23049868159710811993023971)
                  ·
                    refine ⟨34574802239566217989535957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23049868159710811993023971 34574802239566217989535957)
                    ·
                      refine ⟨810346927489833234129749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 34574802239566217989535957 810346927489833234129749)
                      ·
                        rfl

theorem cell23_1578145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_1578145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578145 prefixEnd_1578145 := by exact prefixLift 1578145
  have htrace : WordTrace (prefixWord ++ tailWord_1578145) baseStart_1578145 baseEnd_1578145 := by
    simpa [prefixWord, tailWord_1578145, baseEnd_1578145] using wordTrace_append hprefix tailTrace_1578145
  have hstable : (prefixWord ++ tailWord_1578145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578145).length < 2 ^ (prefixWord ++ tailWord_1578145).sum := by decide
  have hdescent : baseEnd_1578145 < baseStart_1578145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578172 : List Nat := [2, 2, 2, 3, 2, 1, 2, 1, 1, 3, 4]
def baseStart_1578172 : Nat := 118140960795 + 1578172 * 2 ^ 59
def prefixEnd_1578172 : Nat := 4983230072969 + 3 ^ 40 * 1578172 * 2
def baseEnd_1578172 : Nat := 810360791467504628492125

theorem tailTrace_1578172 : CollatzResearch.WordTrace tailWord_1578172 prefixEnd_1578172 810360791467504628492125 := by
  unfold tailWord_1578172
  simp only [CollatzResearch.WordTrace]
  refine ⟨28780330819279924582152385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38373774425706566109536513 28780330819279924582152385)
  ·
    refine ⟨21585248114459943436614289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28780330819279924582152385 21585248114459943436614289)
    ·
      refine ⟨16188936085844957577460717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21585248114459943436614289 16188936085844957577460717)
      ·
        refine ⟨6070851032191859091547769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16188936085844957577460717 6070851032191859091547769)
        ·
          refine ⟨4553138274143894318660827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6070851032191859091547769 4553138274143894318660827)
          ·
            refine ⟨6829707411215841477991241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4553138274143894318660827 6829707411215841477991241)
            ·
              refine ⟨5122280558411881108493431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6829707411215841477991241 5122280558411881108493431)
              ·
                refine ⟨7683420837617821662740147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5122280558411881108493431 7683420837617821662740147)
                ·
                  refine ⟨11525131256426732494110221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7683420837617821662740147 11525131256426732494110221)
                  ·
                    refine ⟨4321924221160024685291333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11525131256426732494110221 4321924221160024685291333)
                    ·
                      refine ⟨810360791467504628492125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4321924221160024685291333 810360791467504628492125)
                      ·
                        rfl

theorem cell23_1578172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_1578172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578172 prefixEnd_1578172 := by exact prefixLift 1578172
  have htrace : WordTrace (prefixWord ++ tailWord_1578172) baseStart_1578172 baseEnd_1578172 := by
    simpa [prefixWord, tailWord_1578172, baseEnd_1578172] using wordTrace_append hprefix tailTrace_1578172
  have hstable : (prefixWord ++ tailWord_1578172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578172).length < 2 ^ (prefixWord ++ tailWord_1578172).sum := by decide
  have hdescent : baseEnd_1578172 < baseStart_1578172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578199 : List Nat := [1, 1, 3, 2, 1, 2, 2, 6, 1, 4]
def baseStart_1578199 : Nat := 118140960795 + 1578199 * 2 ^ 59
def prefixEnd_1578199 : Nat := 4983230072969 + 3 ^ 40 * 1578199 * 2
def baseEnd_1578199 : Nat := 270124885148392007618167

theorem tailTrace_1578199 : CollatzResearch.WordTrace tailWord_1578199 prefixEnd_1578199 270124885148392007618167 := by
  unfold tailWord_1578199
  simp only [CollatzResearch.WordTrace]
  refine ⟨57561646409462032775537651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38374430939641355183691767 57561646409462032775537651)
  ·
    refine ⟨86342469614193049163306477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57561646409462032775537651 86342469614193049163306477)
    ·
      refine ⟨32378426105322393436239929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86342469614193049163306477 32378426105322393436239929)
      ·
        refine ⟨24283819578991795077179947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32378426105322393436239929 24283819578991795077179947)
        ·
          refine ⟨36425729368487692615769921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24283819578991795077179947 36425729368487692615769921)
          ·
            refine ⟨27319297026365769461827441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36425729368487692615769921 27319297026365769461827441)
            ·
              refine ⟨20489472769774327096370581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27319297026365769461827441 20489472769774327096370581)
              ·
                refine ⟨960444036083171582642371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20489472769774327096370581 960444036083171582642371)
                ·
                  refine ⟨1440666054124757373963557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 960444036083171582642371 1440666054124757373963557)
                  ·
                    refine ⟨270124885148392007618167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1440666054124757373963557 270124885148392007618167)
                    ·
                      rfl

theorem cell23_1578199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 6, 1, 4].length) (baseStart_1578199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578199 prefixEnd_1578199 := by exact prefixLift 1578199
  have htrace : WordTrace (prefixWord ++ tailWord_1578199) baseStart_1578199 baseEnd_1578199 := by
    simpa [prefixWord, tailWord_1578199, baseEnd_1578199] using wordTrace_append hprefix tailTrace_1578199
  have hstable : (prefixWord ++ tailWord_1578199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578199).length < 2 ^ (prefixWord ++ tailWord_1578199).sum := by decide
  have hdescent : baseEnd_1578199 < baseStart_1578199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578222 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 2, 5, 3]
def baseStart_1578222 : Nat := 118140960795 + 1578222 * 2 ^ 59
def prefixEnd_1578222 : Nat := 4983230072969 + 3 ^ 40 * 1578222 * 2
def baseEnd_1578222 : Nat := 810386465500229432866895

theorem tailTrace_1578222 : CollatzResearch.WordTrace tailWord_1578222 prefixEnd_1578222 810386465500229432866895 := by
  unfold tailWord_1578222
  simp only [CollatzResearch.WordTrace]
  refine ⟨7195310661047338462953115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38374990192252471802416613 7195310661047338462953115)
  ·
    refine ⟨10792965991571007694429673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7195310661047338462953115 10792965991571007694429673)
    ·
      refine ⟨8094724493678255770822255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10792965991571007694429673 8094724493678255770822255)
      ·
        refine ⟨12142086740517383656233383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8094724493678255770822255 12142086740517383656233383)
        ·
          refine ⟨18213130110776075484350075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12142086740517383656233383 18213130110776075484350075)
          ·
            refine ⟨27319695166164113226525113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18213130110776075484350075 27319695166164113226525113)
            ·
              refine ⟨20489771374623084919893835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27319695166164113226525113 20489771374623084919893835)
              ·
                refine ⟨30734657061934627379840753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20489771374623084919893835 30734657061934627379840753)
                ·
                  refine ⟨23050992796450970534880565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30734657061934627379840753 23050992796450970534880565)
                  ·
                    refine ⟨2161030574667278487645053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23050992796450970534880565 2161030574667278487645053)
                    ·
                      refine ⟨810386465500229432866895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2161030574667278487645053 810386465500229432866895)
                      ·
                        rfl

theorem cell23_1578222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_1578222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578222 prefixEnd_1578222 := by exact prefixLift 1578222
  have htrace : WordTrace (prefixWord ++ tailWord_1578222) baseStart_1578222 baseEnd_1578222 := by
    simpa [prefixWord, tailWord_1578222, baseEnd_1578222] using wordTrace_append hprefix tailTrace_1578222
  have hstable : (prefixWord ++ tailWord_1578222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578222).length < 2 ^ (prefixWord ++ tailWord_1578222).sum := by decide
  have hdescent : baseEnd_1578222 < baseStart_1578222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578226 : List Nat := [3, 2, 1, 3, 3, 1, 2, 1, 2, 2, 3]
def baseStart_1578226 : Nat := 118140960795 + 1578226 * 2 ^ 59
def prefixEnd_1578226 : Nat := 4983230072969 + 3 ^ 40 * 1578226 * 2
def baseEnd_1578226 : Nat := 810388519422847417216877

theorem tailTrace_1578226 : CollatzResearch.WordTrace tailWord_1578226 prefixEnd_1578226 810388519422847417216877 := by
  unfold tailWord_1578226
  simp only [CollatzResearch.WordTrace]
  refine ⟨14390657795091054096692633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38375087453576144257847021 14390657795091054096692633)
  ·
    refine ⟨10792993346318290572519475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14390657795091054096692633 10792993346318290572519475)
    ·
      refine ⟨16189490019477435858779213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10792993346318290572519475 16189490019477435858779213)
      ·
        refine ⟨6071058757304038447042205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16189490019477435858779213 6071058757304038447042205)
        ·
          refine ⟨2276647033989014417640827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6071058757304038447042205 2276647033989014417640827)
          ·
            refine ⟨3414970550983521626461241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2276647033989014417640827 3414970550983521626461241)
            ·
              refine ⟨2561227913237641219845931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3414970550983521626461241 2561227913237641219845931)
              ·
                refine ⟨3841841869856461829768897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2561227913237641219845931 3841841869856461829768897)
                ·
                  refine ⟨2881381402392346372326673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3841841869856461829768897 2881381402392346372326673)
                  ·
                    refine ⟨2161036051794259779245005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2881381402392346372326673 2161036051794259779245005)
                    ·
                      refine ⟨810388519422847417216877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2161036051794259779245005 810388519422847417216877)
                      ·
                        rfl

theorem cell23_1578226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_1578226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578226 prefixEnd_1578226 := by exact prefixLift 1578226
  have htrace : WordTrace (prefixWord ++ tailWord_1578226) baseStart_1578226 baseEnd_1578226 := by
    simpa [prefixWord, tailWord_1578226, baseEnd_1578226] using wordTrace_append hprefix tailTrace_1578226
  have hstable : (prefixWord ++ tailWord_1578226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578226).length < 2 ^ (prefixWord ++ tailWord_1578226).sum := by decide
  have hdescent : baseEnd_1578226 < baseStart_1578226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578249 : List Nat := [1, 2, 1, 1, 3, 3, 1, 4, 2, 3, 2]
def baseStart_1578249 : Nat := 118140960795 + 1578249 * 2 ^ 59
def prefixEnd_1578249 : Nat := 4983230072969 + 3 ^ 40 * 1578249 * 2
def baseEnd_1578249 : Nat := 810400329477900827229271

theorem tailTrace_1578249 : CollatzResearch.WordTrace tailWord_1578249 prefixEnd_1578249 810400329477900827229271 := by
  unfold tailWord_1578249
  simp only [CollatzResearch.WordTrace]
  refine ⟨57563470059280891314857801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38375646706187260876571867 57563470059280891314857801)
  ·
    refine ⟨43172602544460668486143351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57563470059280891314857801 43172602544460668486143351)
    ·
      refine ⟨64758903816691002729215027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43172602544460668486143351 64758903816691002729215027)
      ·
        refine ⟨97138355725036504093822541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64758903816691002729215027 97138355725036504093822541)
        ·
          refine ⟨36426883396888689035183453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97138355725036504093822541 36426883396888689035183453)
          ·
            refine ⟨13660081273833258388193795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36426883396888689035183453 13660081273833258388193795)
            ·
              refine ⟨20490121910749887582290693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13660081273833258388193795 20490121910749887582290693)
              ·
                refine ⟨3841897858265603921679505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20490121910749887582290693 3841897858265603921679505)
                ·
                  refine ⟨2881423393699202941259629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3841897858265603921679505 2881423393699202941259629)
                  ·
                    refine ⟨1080533772637201102972361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2881423393699202941259629 1080533772637201102972361)
                    ·
                      refine ⟨810400329477900827229271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1080533772637201102972361 810400329477900827229271)
                      ·
                        rfl

theorem cell23_1578249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 3, 2].length) (baseStart_1578249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578249 prefixEnd_1578249 := by exact prefixLift 1578249
  have htrace : WordTrace (prefixWord ++ tailWord_1578249) baseStart_1578249 baseEnd_1578249 := by
    simpa [prefixWord, tailWord_1578249, baseEnd_1578249] using wordTrace_append hprefix tailTrace_1578249
  have hstable : (prefixWord ++ tailWord_1578249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578249).length < 2 ^ (prefixWord ++ tailWord_1578249).sum := by decide
  have hdescent : baseEnd_1578249 < baseStart_1578249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578302 : List Nat := [4, 2, 1, 2, 1, 1, 12]
def baseStart_1578302 : Nat := 118140960795 + 1578302 * 2 ^ 59
def prefixEnd_1578302 : Nat := 4983230072969 + 3 ^ 40 * 1578302 * 2
def baseEnd_1578302 : Nat := 10005278320402334813167

theorem tailTrace_1578302 : CollatzResearch.WordTrace tailWord_1578302 prefixEnd_1578302 10005278320402334813167 := by
  unfold tailWord_1578302
  simp only [CollatzResearch.WordTrace]
  refine ⟨7195675391011110170817145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38376935418725920911024773 7195675391011110170817145)
  ·
    refine ⟨5396756543258332628112859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7195675391011110170817145 5396756543258332628112859)
    ·
      refine ⟨8095134814887498942169289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5396756543258332628112859 8095134814887498942169289)
      ·
        refine ⟨6071351111165624206626967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8095134814887498942169289 6071351111165624206626967)
        ·
          refine ⟨9107026666748436309940451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6071351111165624206626967 9107026666748436309940451)
          ·
            refine ⟨13660540000122654464910677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9107026666748436309940451 13660540000122654464910677)
            ·
              refine ⟨10005278320402334813167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 13660540000122654464910677 10005278320402334813167)
              ·
                rfl

theorem cell23_1578302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 12].length) (baseStart_1578302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578302 prefixEnd_1578302 := by exact prefixLift 1578302
  have htrace : WordTrace (prefixWord ++ tailWord_1578302) baseStart_1578302 baseEnd_1578302 := by
    simpa [prefixWord, tailWord_1578302, baseEnd_1578302] using wordTrace_append hprefix tailTrace_1578302
  have hstable : (prefixWord ++ tailWord_1578302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578302).length < 2 ^ (prefixWord ++ tailWord_1578302).sum := by decide
  have hdescent : baseEnd_1578302 < baseStart_1578302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578313 : List Nat := [1, 2, 1, 1, 2, 3, 4, 4, 1, 2, 2]
def baseStart_1578313 : Nat := 118140960795 + 1578313 * 2 ^ 59
def prefixEnd_1578313 : Nat := 4983230072969 + 3 ^ 40 * 1578313 * 2
def baseEnd_1578313 : Nat := 810433192239788576828977

theorem tailTrace_1578313 : CollatzResearch.WordTrace tailWord_1578313 prefixEnd_1578313 810433192239788576828977 := by
  unfold tailWord_1578313
  simp only [CollatzResearch.WordTrace]
  refine ⟨57565804331049030245187593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38377202887366020163458395 57565804331049030245187593)
  ·
    refine ⟨43174353248286772683890695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57565804331049030245187593 43174353248286772683890695)
    ·
      refine ⟨64761529872430159025836043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43174353248286772683890695 64761529872430159025836043)
      ·
        refine ⟨97142294808645238538754065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64761529872430159025836043 97142294808645238538754065)
        ·
          refine ⟨72856721106483928904065549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97142294808645238538754065 72856721106483928904065549)
          ·
            refine ⟨27321270414931473339024581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72856721106483928904065549 27321270414931473339024581)
            ·
              refine ⟨5122738202799651251067109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27321270414931473339024581 5122738202799651251067109)
              ·
                refine ⟨960513413024934609575083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5122738202799651251067109 960513413024934609575083)
                ·
                  refine ⟨1440770119537401914362625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 960513413024934609575083 1440770119537401914362625)
                  ·
                    refine ⟨1080577589653051435771969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1440770119537401914362625 1080577589653051435771969)
                    ·
                      refine ⟨810433192239788576828977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1080577589653051435771969 810433192239788576828977)
                      ·
                        rfl

theorem cell23_1578313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 4, 1, 2, 2].length) (baseStart_1578313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578313 prefixEnd_1578313 := by exact prefixLift 1578313
  have htrace : WordTrace (prefixWord ++ tailWord_1578313) baseStart_1578313 baseEnd_1578313 := by
    simpa [prefixWord, tailWord_1578313, baseEnd_1578313] using wordTrace_append hprefix tailTrace_1578313
  have hstable : (prefixWord ++ tailWord_1578313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578313).length < 2 ^ (prefixWord ++ tailWord_1578313).sum := by decide
  have hdescent : baseEnd_1578313 < baseStart_1578313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578329 : List Nat := [1, 2, 1, 2, 2, 2, 5, 1, 1, 3, 3]
def baseStart_1578329 : Nat := 118140960795 + 1578329 * 2 ^ 59
def prefixEnd_1578329 : Nat := 4983230072969 + 3 ^ 40 * 1578329 * 2
def baseEnd_1578329 : Nat := 810441407930260514228903

theorem tailTrace_1578329 : CollatzResearch.WordTrace tailWord_1578329 prefixEnd_1578329 810441407930260514228903 := by
  unfold tailWord_1578329
  simp only [CollatzResearch.WordTrace]
  refine ⟨57566387898991064977770041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38377591932660709985180027 57566387898991064977770041)
  ·
    refine ⟨43174790924243298733327531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57566387898991064977770041 43174790924243298733327531)
    ·
      refine ⟨64762186386364948099991297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43174790924243298733327531 64762186386364948099991297)
      ·
        refine ⟨48571639789773711074993473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64762186386364948099991297 48571639789773711074993473)
        ·
          refine ⟨36428729842330283306245105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48571639789773711074993473 36428729842330283306245105)
          ·
            refine ⟨27321547381747712479683829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36428729842330283306245105 27321547381747712479683829)
            ·
              refine ⟨2561395067038848044970359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27321547381747712479683829 2561395067038848044970359)
              ·
                refine ⟨3842092600558272067455539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2561395067038848044970359 3842092600558272067455539)
                ·
                  refine ⟨5763138900837408101183309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3842092600558272067455539 5763138900837408101183309)
                  ·
                    refine ⟨2161177087814028037943741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5763138900837408101183309 2161177087814028037943741)
                    ·
                      refine ⟨810441407930260514228903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2161177087814028037943741 810441407930260514228903)
                      ·
                        rfl

theorem cell23_1578329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 3, 3].length) (baseStart_1578329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578329 prefixEnd_1578329 := by exact prefixLift 1578329
  have htrace : WordTrace (prefixWord ++ tailWord_1578329) baseStart_1578329 baseEnd_1578329 := by
    simpa [prefixWord, tailWord_1578329, baseEnd_1578329] using wordTrace_append hprefix tailTrace_1578329
  have hstable : (prefixWord ++ tailWord_1578329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578329).length < 2 ^ (prefixWord ++ tailWord_1578329).sum := by decide
  have hdescent : baseEnd_1578329 < baseStart_1578329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578436 : List Nat := [2, 3, 3, 2, 1, 1, 1, 1, 1, 5, 3]
def baseStart_1578436 : Nat := 118140960795 + 1578436 * 2 ^ 59
def prefixEnd_1578436 : Nat := 4983230072969 + 3 ^ 40 * 1578436 * 2
def baseEnd_1578436 : Nat := 810496350360291595590911

theorem tailTrace_1578436 : CollatzResearch.WordTrace tailWord_1578436 prefixEnd_1578436 810496350360291595590911 := by
  unfold tailWord_1578436
  simp only [CollatzResearch.WordTrace]
  refine ⟨28785145254801711125957581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38380193673068948167943441 28785145254801711125957581)
  ·
    refine ⟨10794429470550641672234093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28785145254801711125957581 10794429470550641672234093)
    ·
      refine ⟨4047911051456490627087785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10794429470550641672234093 4047911051456490627087785)
      ·
        refine ⟨3035933288592367970315839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4047911051456490627087785 3035933288592367970315839)
        ·
          refine ⟨4553899932888551955473759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3035933288592367970315839 4553899932888551955473759)
          ·
            refine ⟨6830849899332827933210639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4553899932888551955473759 6830849899332827933210639)
            ·
              refine ⟨10246274848999241899815959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6830849899332827933210639 10246274848999241899815959)
              ·
                refine ⟨15369412273498862849723939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10246274848999241899815959 15369412273498862849723939)
                ·
                  refine ⟨23054118410248294274585909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15369412273498862849723939 23054118410248294274585909)
                  ·
                    refine ⟨2161323600960777588242429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23054118410248294274585909 2161323600960777588242429)
                    ·
                      refine ⟨810496350360291595590911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2161323600960777588242429 810496350360291595590911)
                      ·
                        rfl

theorem cell23_1578436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_1578436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578436 prefixEnd_1578436 := by exact prefixLift 1578436
  have htrace : WordTrace (prefixWord ++ tailWord_1578436) baseStart_1578436 baseEnd_1578436 := by
    simpa [prefixWord, tailWord_1578436, baseEnd_1578436] using wordTrace_append hprefix tailTrace_1578436
  have hstable : (prefixWord ++ tailWord_1578436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578436).length < 2 ^ (prefixWord ++ tailWord_1578436).sum := by decide
  have hdescent : baseEnd_1578436 < baseStart_1578436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578569 : List Nat := [1, 2, 1, 1, 2, 2, 1, 4, 3, 1, 5]
def baseStart_1578569 : Nat := 118140960795 + 1578569 * 2 ^ 59
def prefixEnd_1578569 : Nat := 4983230072969 + 3 ^ 40 * 1578569 * 2
def baseEnd_1578569 : Nat := 810564643287339575227799

theorem tailTrace_1578569 : CollatzResearch.WordTrace tailWord_1578569 prefixEnd_1578569 810564643287339575227799 := by
  unfold tailWord_1578569
  simp only [CollatzResearch.WordTrace]
  refine ⟨57575141418121585966506761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38383427612081057311004507 57575141418121585966506761)
  ·
    refine ⟨43181356063591189474880071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57575141418121585966506761 43181356063591189474880071)
    ·
      refine ⟨64772034095386784212320107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43181356063591189474880071 64772034095386784212320107)
      ·
        refine ⟨97158051143080176318480161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64772034095386784212320107 97158051143080176318480161)
        ·
          refine ⟨72868538357310132238860121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97158051143080176318480161 72868538357310132238860121)
          ·
            refine ⟨54651403767982599179145091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72868538357310132238860121 54651403767982599179145091)
            ·
              refine ⟨81977105651973898768717637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54651403767982599179145091 81977105651973898768717637)
              ·
                refine ⟨15370707309745106019134557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81977105651973898768717637 15370707309745106019134557)
                ·
                  refine ⟨5764015241154414757175459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15370707309745106019134557 5764015241154414757175459)
                  ·
                    refine ⟨8646022861731622135763189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5764015241154414757175459 8646022861731622135763189)
                    ·
                      refine ⟨810564643287339575227799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8646022861731622135763189 810564643287339575227799)
                      ·
                        rfl

theorem cell23_1578569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 1, 5].length) (baseStart_1578569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578569 prefixEnd_1578569 := by exact prefixLift 1578569
  have htrace : WordTrace (prefixWord ++ tailWord_1578569) baseStart_1578569 baseEnd_1578569 := by
    simpa [prefixWord, tailWord_1578569, baseEnd_1578569] using wordTrace_append hprefix tailTrace_1578569
  have hstable : (prefixWord ++ tailWord_1578569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578569).length < 2 ^ (prefixWord ++ tailWord_1578569).sum := by decide
  have hdescent : baseEnd_1578569 < baseStart_1578569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578593 : List Nat := [1, 2, 3, 1, 1, 3, 4, 2, 2, 4]
def baseStart_1578593 : Nat := 118140960795 + 1578593 * 2 ^ 59
def prefixEnd_1578593 : Nat := 4983230072969 + 3 ^ 40 * 1578593 * 2
def baseEnd_1578593 : Nat := 270192322274349160442563

theorem tailTrace_1578593 : CollatzResearch.WordTrace tailWord_1578593 prefixEnd_1578593 270192322274349160442563 := by
  unfold tailWord_1578593
  simp only [CollatzResearch.WordTrace]
  refine ⟨57576016770034638065380433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38384011180023092043586955 57576016770034638065380433)
  ·
    refine ⟨43182012577525978549035325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57576016770034638065380433 43182012577525978549035325)
    ·
      refine ⟨16193254716572241955888247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43182012577525978549035325 16193254716572241955888247)
      ·
        refine ⟨24289882074858362933832371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16193254716572241955888247 24289882074858362933832371)
        ·
          refine ⟨36434823112287544400748557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24289882074858362933832371 36434823112287544400748557)
          ·
            refine ⟨13663058667107829150280709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36434823112287544400748557 13663058667107829150280709)
            ·
              refine ⟨2561823500082717965677633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13663058667107829150280709 2561823500082717965677633)
              ·
                refine ⟨1921367625062038474258225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2561823500082717965677633 1921367625062038474258225)
                ·
                  refine ⟨1441025718796528855693669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1921367625062038474258225 1441025718796528855693669)
                  ·
                    refine ⟨270192322274349160442563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1441025718796528855693669 270192322274349160442563)
                    ·
                      rfl

theorem cell23_1578593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 2, 4].length) (baseStart_1578593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578593 prefixEnd_1578593 := by exact prefixLift 1578593
  have htrace : WordTrace (prefixWord ++ tailWord_1578593) baseStart_1578593 baseEnd_1578593 := by
    simpa [prefixWord, tailWord_1578593, baseEnd_1578593] using wordTrace_append hprefix tailTrace_1578593
  have hstable : (prefixWord ++ tailWord_1578593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578593).length < 2 ^ (prefixWord ++ tailWord_1578593).sum := by decide
  have hdescent : baseEnd_1578593 < baseStart_1578593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578609 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 2, 2, 6]
def baseStart_1578609 : Nat := 118140960795 + 1578609 * 2 ^ 59
def prefixEnd_1578609 : Nat := 4983230072969 + 3 ^ 40 * 1578609 * 2
def baseEnd_1578609 : Nat := 810585182513519418727615

theorem tailTrace_1578609 : CollatzResearch.WordTrace tailWord_1578609 prefixEnd_1578609 810585182513519418727615 := by
  unfold tailWord_1578609
  simp only [CollatzResearch.WordTrace]
  refine ⟨57576600337976672797962881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38384400225317781865308587 57576600337976672797962881)
  ·
    refine ⟨43182450253482504598472161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57576600337976672797962881 43182450253482504598472161)
    ·
      refine ⟨32386837690111878448854121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43182450253482504598472161 32386837690111878448854121)
      ·
        refine ⟨24290128267583908836640591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32386837690111878448854121 24290128267583908836640591)
        ·
          refine ⟨36435192401375863254960887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24290128267583908836640591 36435192401375863254960887)
          ·
            refine ⟨54652788602063794882441331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36435192401375863254960887 54652788602063794882441331)
            ·
              refine ⟨81979182903095692323661997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54652788602063794882441331 81979182903095692323661997)
              ·
                refine ⟨30742193588660884621373249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81979182903095692323661997 30742193588660884621373249)
                ·
                  refine ⟨23056645191495663466029937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30742193588660884621373249 23056645191495663466029937)
                  ·
                    refine ⟨17292483893621747599522453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23056645191495663466029937 17292483893621747599522453)
                    ·
                      refine ⟨810585182513519418727615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17292483893621747599522453 810585182513519418727615)
                      ·
                        rfl

theorem cell23_1578609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_1578609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578609 prefixEnd_1578609 := by exact prefixLift 1578609
  have htrace : WordTrace (prefixWord ++ tailWord_1578609) baseStart_1578609 baseEnd_1578609 := by
    simpa [prefixWord, tailWord_1578609, baseEnd_1578609] using wordTrace_append hprefix tailTrace_1578609
  have hstable : (prefixWord ++ tailWord_1578609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578609).length < 2 ^ (prefixWord ++ tailWord_1578609).sum := by decide
  have hdescent : baseEnd_1578609 < baseStart_1578609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578613 : List Nat := [1, 3, 4, 2, 1, 1, 1, 3, 1, 2, 4]
def baseStart_1578613 : Nat := 118140960795 + 1578613 * 2 ^ 59
def prefixEnd_1578613 : Nat := 4983230072969 + 3 ^ 40 * 1578613 * 2
def baseEnd_1578613 : Nat := 810587236436137403077597

theorem tailTrace_1578613 : CollatzResearch.WordTrace tailWord_1578613 prefixEnd_1578613 810587236436137403077597 := by
  unfold tailWord_1578613
  simp only [CollatzResearch.WordTrace]
  refine ⟨57576746229962181481108493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38384497486641454320738995 57576746229962181481108493)
  ·
    refine ⟨21591279836235818055415685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57576746229962181481108493 21591279836235818055415685)
    ·
      refine ⟨4048364969294215885390441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21591279836235818055415685 4048364969294215885390441)
      ·
        refine ⟨3036273726970661914042831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4048364969294215885390441 3036273726970661914042831)
        ·
          refine ⟨4554410590455992871064247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3036273726970661914042831 4554410590455992871064247)
          ·
            refine ⟨6831615885683989306596371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4554410590455992871064247 6831615885683989306596371)
            ·
              refine ⟨10247423828525983959894557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6831615885683989306596371 10247423828525983959894557)
              ·
                refine ⟨3842783935697243984960459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10247423828525983959894557 3842783935697243984960459)
                ·
                  refine ⟨5764175903545865977440689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3842783935697243984960459 5764175903545865977440689)
                  ·
                    refine ⟨4323131927659399483080517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5764175903545865977440689 4323131927659399483080517)
                    ·
                      refine ⟨810587236436137403077597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4323131927659399483080517 810587236436137403077597)
                      ·
                        rfl

theorem cell23_1578613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_1578613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578613 prefixEnd_1578613 := by exact prefixLift 1578613
  have htrace : WordTrace (prefixWord ++ tailWord_1578613) baseStart_1578613 baseEnd_1578613 := by
    simpa [prefixWord, tailWord_1578613, baseEnd_1578613] using wordTrace_append hprefix tailTrace_1578613
  have hstable : (prefixWord ++ tailWord_1578613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578613).length < 2 ^ (prefixWord ++ tailWord_1578613).sum := by decide
  have hdescent : baseEnd_1578613 < baseStart_1578613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578619 : List Nat := [1, 1, 1, 1, 1, 4, 3, 2, 2, 7]
def baseStart_1578619 : Nat := 118140960795 + 1578619 * 2 ^ 59
def prefixEnd_1578619 : Nat := 4983230072969 + 3 ^ 40 * 1578619 * 2
def baseEnd_1578619 : Nat := 270196772440021459867523

theorem tailTrace_1578619 : CollatzResearch.WordTrace tailWord_1578619 prefixEnd_1578619 270196772440021459867523 := by
  unfold tailWord_1578619
  simp only [CollatzResearch.WordTrace]
  refine ⟨57576965067940444505826911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38384643378626963003884607 57576965067940444505826911)
  ·
    refine ⟨86365447601910666758740367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57576965067940444505826911 86365447601910666758740367)
    ·
      refine ⟨129548171402866000138110551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86365447601910666758740367 129548171402866000138110551)
      ·
        refine ⟨194322257104299000207165827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129548171402866000138110551 194322257104299000207165827)
        ·
          refine ⟨291483385656448500310748741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194322257104299000207165827 291483385656448500310748741)
          ·
            refine ⟨54653134810584093808265389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 291483385656448500310748741 54653134810584093808265389)
            ·
              refine ⟨20494925553969035178099521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54653134810584093808265389 20494925553969035178099521)
              ·
                refine ⟨15371194165476776383574641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20494925553969035178099521 15371194165476776383574641)
                ·
                  refine ⟨11528395624107582287680981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15371194165476776383574641 11528395624107582287680981)
                  ·
                    refine ⟨270196772440021459867523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11528395624107582287680981 270196772440021459867523)
                    ·
                      rfl

theorem cell23_1578619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 7].length) (baseStart_1578619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578619 prefixEnd_1578619 := by exact prefixLift 1578619
  have htrace : WordTrace (prefixWord ++ tailWord_1578619) baseStart_1578619 baseEnd_1578619 := by
    simpa [prefixWord, tailWord_1578619, baseEnd_1578619] using wordTrace_append hprefix tailTrace_1578619
  have hstable : (prefixWord ++ tailWord_1578619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578619).length < 2 ^ (prefixWord ++ tailWord_1578619).sum := by decide
  have hdescent : baseEnd_1578619 < baseStart_1578619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578634 : List Nat := [3, 1, 2, 3, 2, 2, 2, 3, 1, 2, 2]
def baseStart_1578634 : Nat := 118140960795 + 1578634 * 2 ^ 59
def prefixEnd_1578634 : Nat := 4983230072969 + 3 ^ 40 * 1578634 * 2
def baseEnd_1578634 : Nat := 810598019529881820915001

theorem tailTrace_1578634 : CollatzResearch.WordTrace tailWord_1578634 prefixEnd_1578634 810598019529881820915001 := by
  unfold tailWord_1578634
  simp only [CollatzResearch.WordTrace]
  refine ⟨14394378040721525516905739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38385008108590734711748637 14394378040721525516905739)
  ·
    refine ⟨21591567061082288275358609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14394378040721525516905739 21591567061082288275358609)
    ·
      refine ⟨16193675295811716206518957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21591567061082288275358609 16193675295811716206518957)
      ·
        refine ⟨6072628235929393577444609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16193675295811716206518957 6072628235929393577444609)
        ·
          refine ⟨4554471176947045183083457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6072628235929393577444609 4554471176947045183083457)
          ·
            refine ⟨3415853382710283887312593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4554471176947045183083457 3415853382710283887312593)
            ·
              refine ⟨2561890037032712915484445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3415853382710283887312593 2561890037032712915484445)
              ·
                refine ⟨960708763887267343306667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2561890037032712915484445 960708763887267343306667)
                ·
                  refine ⟨1441063145830901014960001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 960708763887267343306667 1441063145830901014960001)
                  ·
                    refine ⟨1080797359373175761220001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1441063145830901014960001 1080797359373175761220001)
                    ·
                      refine ⟨810598019529881820915001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1080797359373175761220001 810598019529881820915001)
                      ·
                        rfl

theorem cell23_1578634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_1578634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578634 prefixEnd_1578634 := by exact prefixLift 1578634
  have htrace : WordTrace (prefixWord ++ tailWord_1578634) baseStart_1578634 baseEnd_1578634 := by
    simpa [prefixWord, tailWord_1578634, baseEnd_1578634] using wordTrace_append hprefix tailTrace_1578634
  have hstable : (prefixWord ++ tailWord_1578634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578634).length < 2 ^ (prefixWord ++ tailWord_1578634).sum := by decide
  have hdescent : baseEnd_1578634 < baseStart_1578634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578644 : List Nat := [2, 4, 2, 2, 3, 1, 1, 2, 2, 4]
def baseStart_1578644 : Nat := 118140960795 + 1578644 * 2 ^ 59
def prefixEnd_1578644 : Nat := 4983230072969 + 3 ^ 40 * 1578644 * 2
def baseEnd_1578644 : Nat := 270201051445475593929985

theorem tailTrace_1578644 : CollatzResearch.WordTrace tailWord_1578644 prefixEnd_1578644 270201051445475593929985 := by
  unfold tailWord_1578644
  simp only [CollatzResearch.WordTrace]
  refine ⟨28788938446424936887743493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38385251261899915850324657 28788938446424936887743493)
  ·
    refine ⟨5397925958704675666451905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28788938446424936887743493 5397925958704675666451905)
    ·
      refine ⟨4048444469028506749838929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5397925958704675666451905 4048444469028506749838929)
      ·
        refine ⟨3036333351771380062379197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4048444469028506749838929 3036333351771380062379197)
        ·
          refine ⟨1138625006914267523392199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3036333351771380062379197 1138625006914267523392199)
          ·
            refine ⟨1707937510371401285088299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1138625006914267523392199 1707937510371401285088299)
            ·
              refine ⟨2561906265557101927632449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1707937510371401285088299 2561906265557101927632449)
              ·
                refine ⟨1921429699167826445724337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2561906265557101927632449 1921429699167826445724337)
                ·
                  refine ⟨1441072274375869834293253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1921429699167826445724337 1441072274375869834293253)
                  ·
                    refine ⟨270201051445475593929985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1441072274375869834293253 270201051445475593929985)
                    ·
                      rfl

theorem cell23_1578644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_1578644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578644 prefixEnd_1578644 := by exact prefixLift 1578644
  have htrace : WordTrace (prefixWord ++ tailWord_1578644) baseStart_1578644 baseEnd_1578644 := by
    simpa [prefixWord, tailWord_1578644, baseEnd_1578644] using wordTrace_append hprefix tailTrace_1578644
  have hstable : (prefixWord ++ tailWord_1578644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578644).length < 2 ^ (prefixWord ++ tailWord_1578644).sum := by decide
  have hdescent : baseEnd_1578644 < baseStart_1578644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578664 : List Nat := [2, 1, 7, 1, 1, 2, 1, 1, 1, 2, 4]
def baseStart_1578664 : Nat := 118140960795 + 1578664 * 2 ^ 59
def prefixEnd_1578664 : Nat := 4983230072969 + 3 ^ 40 * 1578664 * 2
def baseEnd_1578664 : Nat := 810613423949516703539863

theorem tailTrace_1578664 : CollatzResearch.WordTrace tailWord_1578664 prefixEnd_1578664 810613423949516703539863 := by
  unfold tailWord_1578664
  simp only [CollatzResearch.WordTrace]
  refine ⟨28789303176388708595607523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38385737568518278127476697 28789303176388708595607523)
  ·
    refine ⟨43183954764583062893411285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28789303176388708595607523 43183954764583062893411285)
    ·
      refine ⟨1012123939794915536564327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 43183954764583062893411285 1012123939794915536564327)
      ·
        refine ⟨1518185909692373304846491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1012123939794915536564327 1518185909692373304846491)
        ·
          refine ⟨2277278864538559957269737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1518185909692373304846491 2277278864538559957269737)
          ·
            refine ⟨1707959148403919967952303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2277278864538559957269737 1707959148403919967952303)
            ·
              refine ⟨2561938722605879951928455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1707959148403919967952303 2561938722605879951928455)
              ·
                refine ⟨3842908083908819927892683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2561938722605879951928455 3842908083908819927892683)
                ·
                  refine ⟨5764362125863229891839025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3842908083908819927892683 5764362125863229891839025)
                  ·
                    refine ⟨4323271594397422418879269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5764362125863229891839025 4323271594397422418879269)
                    ·
                      refine ⟨810613423949516703539863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4323271594397422418879269 810613423949516703539863)
                      ·
                        rfl

theorem cell23_1578664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_1578664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578664 prefixEnd_1578664 := by exact prefixLift 1578664
  have htrace : WordTrace (prefixWord ++ tailWord_1578664) baseStart_1578664 baseEnd_1578664 := by
    simpa [prefixWord, tailWord_1578664, baseEnd_1578664] using wordTrace_append hprefix tailTrace_1578664
  have hstable : (prefixWord ++ tailWord_1578664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578664).length < 2 ^ (prefixWord ++ tailWord_1578664).sum := by decide
  have hdescent : baseEnd_1578664 < baseStart_1578664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578713 : List Nat := [1, 2, 1, 2, 3, 5, 1, 1, 7]
def baseStart_1578713 : Nat := 118140960795 + 1578713 * 2 ^ 59
def prefixEnd_1578713 : Nat := 4983230072969 + 3 ^ 40 * 1578713 * 2
def baseEnd_1578713 : Nat := 90070953833509667980793

theorem tailTrace_1578713 : CollatzResearch.WordTrace tailWord_1578713 prefixEnd_1578713 90070953833509667980793 := by
  unfold tailWord_1578713
  simp only [CollatzResearch.WordTrace]
  refine ⟨57580393529599898559748793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38386929019733265706499195 57580393529599898559748793)
  ·
    refine ⟨43185295147199923919811595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57580393529599898559748793 43185295147199923919811595)
    ·
      refine ⟨64777942720799885879717393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43185295147199923919811595 64777942720799885879717393)
      ·
        refine ⟨48583457040599914409788045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64777942720799885879717393 48583457040599914409788045)
        ·
          refine ⟨18218796390224967903670517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48583457040599914409788045 18218796390224967903670517)
          ·
            refine ⟨1708012161583590740969111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18218796390224967903670517 1708012161583590740969111)
            ·
              refine ⟨2562018242375386111453667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1708012161583590740969111 2562018242375386111453667)
              ·
                refine ⟨3843027363563079167180501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2562018242375386111453667 3843027363563079167180501)
                ·
                  refine ⟨90070953833509667980793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3843027363563079167180501 90070953833509667980793)
                  ·
                    rfl

theorem cell23_1578713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 7].length) (baseStart_1578713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578713 prefixEnd_1578713 := by exact prefixLift 1578713
  have htrace : WordTrace (prefixWord ++ tailWord_1578713) baseStart_1578713 baseEnd_1578713 := by
    simpa [prefixWord, tailWord_1578713, baseEnd_1578713] using wordTrace_append hprefix tailTrace_1578713
  have hstable : (prefixWord ++ tailWord_1578713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578713).length < 2 ^ (prefixWord ++ tailWord_1578713).sum := by decide
  have hdescent : baseEnd_1578713 < baseStart_1578713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578763 : List Nat := [1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 4]
def baseStart_1578763 : Nat := 118140960795 + 1578763 * 2 ^ 59
def prefixEnd_1578763 : Nat := 4983230072969 + 3 ^ 40 * 1578763 * 2
def baseEnd_1578763 : Nat := 810664258534311816201907

theorem tailTrace_1578763 : CollatzResearch.WordTrace tailWord_1578763 prefixEnd_1578763 810664258534311816201907 := by
  unfold tailWord_1578763
  simp only [CollatzResearch.WordTrace]
  refine ⟨57582217179418757099068943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38388144786279171399379295 57582217179418757099068943)
  ·
    refine ⟨86373325769128135648603415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57582217179418757099068943 86373325769128135648603415)
    ·
      refine ⟨129559988653692203472905123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86373325769128135648603415 129559988653692203472905123)
      ·
        refine ⟨194339982980538305209357685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129559988653692203472905123 194339982980538305209357685)
        ·
          refine ⟨18219373404425466113377283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 194339982980538305209357685 18219373404425466113377283)
          ·
            refine ⟨27329060106638199170065925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18219373404425466113377283 27329060106638199170065925)
            ·
              refine ⟨5124198769994662344387361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27329060106638199170065925 5124198769994662344387361)
              ·
                refine ⟨3843149077495996758290521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5124198769994662344387361 3843149077495996758290521)
                ·
                  refine ⟨2882361808121997568717891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3843149077495996758290521 2882361808121997568717891)
                  ·
                    refine ⟨4323542712182996353076837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2882361808121997568717891 4323542712182996353076837)
                    ·
                      refine ⟨810664258534311816201907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4323542712182996353076837 810664258534311816201907)
                      ·
                        rfl

theorem cell23_1578763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 4].length) (baseStart_1578763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578763 prefixEnd_1578763 := by exact prefixLift 1578763
  have htrace : WordTrace (prefixWord ++ tailWord_1578763) baseStart_1578763 baseEnd_1578763 := by
    simpa [prefixWord, tailWord_1578763, baseEnd_1578763] using wordTrace_append hprefix tailTrace_1578763
  have hstable : (prefixWord ++ tailWord_1578763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578763).length < 2 ^ (prefixWord ++ tailWord_1578763).sum := by decide
  have hdescent : baseEnd_1578763 < baseStart_1578763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578770 : List Nat := [3, 2, 4, 1, 1, 1, 2, 1, 1, 2, 5]
def baseStart_1578770 : Nat := 118140960795 + 1578770 * 2 ^ 59
def prefixEnd_1578770 : Nat := 4983230072969 + 3 ^ 40 * 1578770 * 2
def baseEnd_1578770 : Nat := 810667852898893288814375

theorem tailTrace_1578770 : CollatzResearch.WordTrace tailWord_1578770 prefixEnd_1578770 810667852898893288814375 := by
  unfold tailWord_1578770
  simp only [CollatzResearch.WordTrace]
  refine ⟨14395618122598349323643441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38388314993595598196382509 14395618122598349323643441)
  ·
    refine ⟨10796713591948761992732581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14395618122598349323643441 10796713591948761992732581)
    ·
      refine ⟨2024383798490392873637359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10796713591948761992732581 2024383798490392873637359)
      ·
        refine ⟨3036575697735589310456039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2024383798490392873637359 3036575697735589310456039)
        ·
          refine ⟨4554863546603383965684059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3036575697735589310456039 4554863546603383965684059)
          ·
            refine ⟨6832295319905075948526089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4554863546603383965684059 6832295319905075948526089)
            ·
              refine ⟨5124221489928806961394567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6832295319905075948526089 5124221489928806961394567)
              ·
                refine ⟨7686332234893210442091851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5124221489928806961394567 7686332234893210442091851)
                ·
                  refine ⟨11529498352339815663137777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7686332234893210442091851 11529498352339815663137777)
                  ·
                    refine ⟨8647123764254861747353333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11529498352339815663137777 8647123764254861747353333)
                    ·
                      refine ⟨810667852898893288814375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8647123764254861747353333 810667852898893288814375)
                      ·
                        rfl

theorem cell23_1578770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_1578770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578770 prefixEnd_1578770 := by exact prefixLift 1578770
  have htrace : WordTrace (prefixWord ++ tailWord_1578770) baseStart_1578770 baseEnd_1578770 := by
    simpa [prefixWord, tailWord_1578770, baseEnd_1578770] using wordTrace_append hprefix tailTrace_1578770
  have hstable : (prefixWord ++ tailWord_1578770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578770).length < 2 ^ (prefixWord ++ tailWord_1578770).sum := by decide
  have hdescent : baseEnd_1578770 < baseStart_1578770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578780 : List Nat := [2, 2, 3, 1, 1, 2, 3, 1, 2, 4, 2]
def baseStart_1578780 : Nat := 118140960795 + 1578780 * 2 ^ 59
def prefixEnd_1578780 : Nat := 4983230072969 + 3 ^ 40 * 1578780 * 2
def baseEnd_1578780 : Nat := 810672987705438249689329

theorem tailTrace_1578780 : CollatzResearch.WordTrace tailWord_1578780 prefixEnd_1578780 810672987705438249689329 := by
  unfold tailWord_1578780
  simp only [CollatzResearch.WordTrace]
  refine ⟨28791418610178584501218897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38388558146904779334958529 28791418610178584501218897)
  ·
    refine ⟨21593563957633938375914173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28791418610178584501218897 21593563957633938375914173)
    ·
      refine ⟨8097586484112726890967815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21593563957633938375914173 8097586484112726890967815)
      ·
        refine ⟨12146379726169090336451723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8097586484112726890967815 12146379726169090336451723)
        ·
          refine ⟨18219569589253635504677585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12146379726169090336451723 18219569589253635504677585)
          ·
            refine ⟨13664677191940226628508189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18219569589253635504677585 13664677191940226628508189)
            ·
              refine ⟨5124253946977584985690571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13664677191940226628508189 5124253946977584985690571)
              ·
                refine ⟨7686380920466377478535857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5124253946977584985690571 7686380920466377478535857)
                ·
                  refine ⟨5764785690349783108901893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7686380920466377478535857 5764785690349783108901893)
                  ·
                    refine ⟨1080897316940584332919105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5764785690349783108901893 1080897316940584332919105)
                    ·
                      refine ⟨810672987705438249689329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1080897316940584332919105 810672987705438249689329)
                      ·
                        rfl

theorem cell23_1578780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_1578780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578780 prefixEnd_1578780 := by exact prefixLift 1578780
  have htrace : WordTrace (prefixWord ++ tailWord_1578780) baseStart_1578780 baseEnd_1578780 := by
    simpa [prefixWord, tailWord_1578780, baseEnd_1578780] using wordTrace_append hprefix tailTrace_1578780
  have hstable : (prefixWord ++ tailWord_1578780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578780).length < 2 ^ (prefixWord ++ tailWord_1578780).sum := by decide
  have hdescent : baseEnd_1578780 < baseStart_1578780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578783 : List Nat := [1, 1, 2, 4, 2, 1, 2, 2, 1, 4, 3]
def baseStart_1578783 : Nat := 118140960795 + 1578783 * 2 ^ 59
def prefixEnd_1578783 : Nat := 4983230072969 + 3 ^ 40 * 1578783 * 2
def baseEnd_1578783 : Nat := 810674528147401737951815

theorem tailTrace_1578783 : CollatzResearch.WordTrace tailWord_1578783 prefixEnd_1578783 810674528147401737951815 := by
  unfold tailWord_1578783
  simp only [CollatzResearch.WordTrace]
  refine ⟨57582946639346300514797003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38388631092897533676531335 57582946639346300514797003)
  ·
    refine ⟨86374419959019450772195505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57582946639346300514797003 86374419959019450772195505)
    ·
      refine ⟨64780814969264588079146629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86374419959019450772195505 64780814969264588079146629)
      ·
        refine ⟨12146402806737110264839993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64780814969264588079146629 12146402806737110264839993)
        ·
          refine ⟨9109802105052832698629995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12146402806737110264839993 9109802105052832698629995)
          ·
            refine ⟨13664703157579249047944993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9109802105052832698629995 13664703157579249047944993)
            ·
              refine ⟨10248527368184436785958745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13664703157579249047944993 10248527368184436785958745)
              ·
                refine ⟨7686395526138327589469059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10248527368184436785958745 7686395526138327589469059)
                ·
                  refine ⟨11529593289207491384203589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7686395526138327589469059 11529593289207491384203589)
                  ·
                    refine ⟨2161798741726404634538173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11529593289207491384203589 2161798741726404634538173)
                    ·
                      refine ⟨810674528147401737951815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2161798741726404634538173 810674528147401737951815)
                      ·
                        rfl

theorem cell23_1578783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_1578783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578783 prefixEnd_1578783 := by exact prefixLift 1578783
  have htrace : WordTrace (prefixWord ++ tailWord_1578783) baseStart_1578783 baseEnd_1578783 := by
    simpa [prefixWord, tailWord_1578783, baseEnd_1578783] using wordTrace_append hprefix tailTrace_1578783
  have hstable : (prefixWord ++ tailWord_1578783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578783).length < 2 ^ (prefixWord ++ tailWord_1578783).sum := by decide
  have hdescent : baseEnd_1578783 < baseStart_1578783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578858 : List Nat := [3, 1, 3, 4, 2, 1, 1, 3, 1, 4]
def baseStart_1578858 : Nat := 118140960795 + 1578858 * 2 ^ 59
def prefixEnd_1578858 : Nat := 4983230072969 + 3 ^ 40 * 1578858 * 2
def baseEnd_1578858 : Nat := 270237679732162981504657

theorem tailTrace_1578858 : CollatzResearch.WordTrace tailWord_1578858 prefixEnd_1578858 270237679732162981504657 := by
  unfold tailWord_1578858
  simp only [CollatzResearch.WordTrace]
  refine ⟨14396420528518647080944307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38390454742716392215851485 14396420528518647080944307)
  ·
    refine ⟨21594630792777970621416461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14396420528518647080944307 21594630792777970621416461)
    ·
      refine ⟨8097986547291738983031173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21594630792777970621416461 8097986547291738983031173)
      ·
        refine ⟨1518372477617201059318345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8097986547291738983031173 1518372477617201059318345)
        ·
          refine ⟨1138779358212900794488759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1518372477617201059318345 1138779358212900794488759)
          ·
            refine ⟨1708169037319351191733139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1138779358212900794488759 1708169037319351191733139)
            ·
              refine ⟨2562253555979026787599709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1708169037319351191733139 2562253555979026787599709)
              ·
                refine ⟨960845083492135045349891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2562253555979026787599709 960845083492135045349891)
                ·
                  refine ⟨1441267625238202568024837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 960845083492135045349891 1441267625238202568024837)
                  ·
                    refine ⟨270237679732162981504657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1441267625238202568024837 270237679732162981504657)
                    ·
                      rfl

theorem cell23_1578858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_1578858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578858 prefixEnd_1578858 := by exact prefixLift 1578858
  have htrace : WordTrace (prefixWord ++ tailWord_1578858) baseStart_1578858 baseEnd_1578858 := by
    simpa [prefixWord, tailWord_1578858, baseEnd_1578858] using wordTrace_append hprefix tailTrace_1578858
  have hstable : (prefixWord ++ tailWord_1578858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578858).length < 2 ^ (prefixWord ++ tailWord_1578858).sum := by decide
  have hdescent : baseEnd_1578858 < baseStart_1578858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578880 : List Nat := [2, 1, 1, 2, 1, 2, 4, 4, 2, 4]
def baseStart_1578880 : Nat := 118140960795 + 1578880 * 2 ^ 59
def prefixEnd_1578880 : Nat := 4983230072969 + 3 ^ 40 * 1578880 * 2
def baseEnd_1578880 : Nat := 270241445256962619479623

theorem tailTrace_1578880 : CollatzResearch.WordTrace tailWord_1578880 prefixEnd_1578880 270241445256962619479623 := by
  unfold tailWord_1578880
  simp only [CollatzResearch.WordTrace]
  refine ⟨28793242259997443040539047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38390989679996590720718729 28793242259997443040539047)
  ·
    refine ⟨43189863389996164560808571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28793242259997443040539047 43189863389996164560808571)
    ·
      refine ⟨64784795084994246841212857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43189863389996164560808571 64784795084994246841212857)
      ·
        refine ⟨48588596313745685130909643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64784795084994246841212857 48588596313745685130909643)
        ·
          refine ⟨72882894470618527696364465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48588596313745685130909643 72882894470618527696364465)
          ·
            refine ⟨54662170852963895772273349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72882894470618527696364465 54662170852963895772273349)
            ·
              refine ⟨10249157034930730457301253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54662170852963895772273349 10249157034930730457301253)
              ·
                refine ⟨1921716944049511960743985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10249157034930730457301253 1921716944049511960743985)
                ·
                  refine ⟨1441287708037133970557989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1921716944049511960743985 1441287708037133970557989)
                  ·
                    refine ⟨270241445256962619479623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1441287708037133970557989 270241445256962619479623)
                    ·
                      rfl

theorem cell23_1578880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 2, 4].length) (baseStart_1578880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578880 prefixEnd_1578880 := by exact prefixLift 1578880
  have htrace : WordTrace (prefixWord ++ tailWord_1578880) baseStart_1578880 baseEnd_1578880 := by
    simpa [prefixWord, tailWord_1578880, baseEnd_1578880] using wordTrace_append hprefix tailTrace_1578880
  have hstable : (prefixWord ++ tailWord_1578880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578880).length < 2 ^ (prefixWord ++ tailWord_1578880).sum := by decide
  have hdescent : baseEnd_1578880 < baseStart_1578880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578881 : List Nat := [1, 2, 4, 4, 1, 2, 1, 1, 3, 1, 3]
def baseStart_1578881 : Nat := 118140960795 + 1578881 * 2 ^ 59
def prefixEnd_1578881 : Nat := 4983230072969 + 3 ^ 40 * 1578881 * 2
def baseEnd_1578881 : Nat := 810724849251542354526365

theorem tailTrace_1578881 : CollatzResearch.WordTrace tailWord_1578881 prefixEnd_1578881 810724849251542354526365 := by
  unfold tailWord_1578881
  simp only [CollatzResearch.WordTrace]
  refine ⟨57586520992991263251864497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38391013995327508834576331 57586520992991263251864497)
  ·
    refine ⟨43189890744743447438898373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57586520992991263251864497 43189890744743447438898373)
    ·
      refine ⟨8098104514639396394793445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43189890744743447438898373 8098104514639396394793445)
      ·
        refine ⟨1518394596494886824023771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8098104514639396394793445 1518394596494886824023771)
        ·
          refine ⟨2277591894742330236035657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1518394596494886824023771 2277591894742330236035657)
          ·
            refine ⟨1708193921056747677026743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2277591894742330236035657 1708193921056747677026743)
            ·
              refine ⟨2562290881585121515540115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1708193921056747677026743 2562290881585121515540115)
              ·
                refine ⟨3843436322377682273310173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2562290881585121515540115 3843436322377682273310173)
                ·
                  refine ⟨1441288620891630852491315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3843436322377682273310173 1441288620891630852491315)
                  ·
                    refine ⟨2161932931337446278736973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1441288620891630852491315 2161932931337446278736973)
                    ·
                      refine ⟨810724849251542354526365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2161932931337446278736973 810724849251542354526365)
                      ·
                        rfl

theorem cell23_1578881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_1578881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578881 prefixEnd_1578881 := by exact prefixLift 1578881
  have htrace : WordTrace (prefixWord ++ tailWord_1578881) baseStart_1578881 baseEnd_1578881 := by
    simpa [prefixWord, tailWord_1578881, baseEnd_1578881] using wordTrace_append hprefix tailTrace_1578881
  have hstable : (prefixWord ++ tailWord_1578881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578881).length < 2 ^ (prefixWord ++ tailWord_1578881).sum := by decide
  have hdescent : baseEnd_1578881 < baseStart_1578881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578883 : List Nat := [1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 6]
def baseStart_1578883 : Nat := 118140960795 + 1578883 * 2 ^ 59
def prefixEnd_1578883 : Nat := 4983230072969 + 3 ^ 40 * 1578883 * 2
def baseEnd_1578883 : Nat := 810725876212851346701355

theorem tailTrace_1578883 : CollatzResearch.WordTrace tailWord_1578883 prefixEnd_1578883 810725876212851346701355 := by
  unfold tailWord_1578883
  simp only [CollatzResearch.WordTrace]
  refine ⟨57586593938984017593437303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38391062625989345062291535 57586593938984017593437303)
  ·
    refine ⟨86379890908476026390155955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57586593938984017593437303 86379890908476026390155955)
    ·
      refine ⟨129569836362714039585233933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86379890908476026390155955 129569836362714039585233933)
      ·
        refine ⟨48588688636017764844462725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129569836362714039585233933 48588688636017764844462725)
        ·
          refine ⟨9110379119253330908336761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48588688636017764844462725 9110379119253330908336761)
          ·
            refine ⟨6832784339439998181252571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9110379119253330908336761 6832784339439998181252571)
            ·
              refine ⟨10249176509159997271878857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6832784339439998181252571 10249176509159997271878857)
              ·
                refine ⟨7686882381869997953909143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10249176509159997271878857 7686882381869997953909143)
                ·
                  refine ⟨11530323572804996930863715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7686882381869997953909143 11530323572804996930863715)
                  ·
                    refine ⟨17295485359207495396295573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11530323572804996930863715 17295485359207495396295573)
                    ·
                      refine ⟨810725876212851346701355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17295485359207495396295573 810725876212851346701355)
                      ·
                        rfl

theorem cell23_1578883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 6].length) (baseStart_1578883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578883 prefixEnd_1578883 := by exact prefixLift 1578883
  have htrace : WordTrace (prefixWord ++ tailWord_1578883) baseStart_1578883 baseEnd_1578883 := by
    simpa [prefixWord, tailWord_1578883, baseEnd_1578883] using wordTrace_append hprefix tailTrace_1578883
  have hstable : (prefixWord ++ tailWord_1578883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578883).length < 2 ^ (prefixWord ++ tailWord_1578883).sum := by decide
  have hdescent : baseEnd_1578883 < baseStart_1578883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578897 : List Nat := [1, 2, 2, 1, 1, 1, 8, 1, 2, 4]
def baseStart_1578897 : Nat := 118140960795 + 1578897 * 2 ^ 59
def prefixEnd_1578897 : Nat := 4983230072969 + 3 ^ 40 * 1578897 * 2
def baseEnd_1578897 : Nat := 270244354980671430642097

theorem tailTrace_1578897 : CollatzResearch.WordTrace tailWord_1578897 prefixEnd_1578897 270244354980671430642097 := by
  unfold tailWord_1578897
  simp only [CollatzResearch.WordTrace]
  refine ⟨57587104560933297984446945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38391403040622198656297963 57587104560933297984446945)
  ·
    refine ⟨43190328420699973488335209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57587104560933297984446945 43190328420699973488335209)
    ·
      refine ⟨32392746315524980116251407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43190328420699973488335209 32392746315524980116251407)
      ·
        refine ⟨48589119473287470174377111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32392746315524980116251407 48589119473287470174377111)
        ·
          refine ⟨72883679209931205261565667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48589119473287470174377111 72883679209931205261565667)
          ·
            refine ⟨109325518814896807892348501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72883679209931205261565667 109325518814896807892348501)
            ·
              refine ⟨1281158423612071967488459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 109325518814896807892348501 1281158423612071967488459)
              ·
                refine ⟨1921737635418107951232689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1281158423612071967488459 1921737635418107951232689)
                ·
                  refine ⟨1441303226563580963424517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1921737635418107951232689 1441303226563580963424517)
                  ·
                    refine ⟨270244354980671430642097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1441303226563580963424517 270244354980671430642097)
                    ·
                      rfl

theorem cell23_1578897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 2, 4].length) (baseStart_1578897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578897 prefixEnd_1578897 := by exact prefixLift 1578897
  have htrace : WordTrace (prefixWord ++ tailWord_1578897) baseStart_1578897 baseEnd_1578897 := by
    simpa [prefixWord, tailWord_1578897, baseEnd_1578897] using wordTrace_append hprefix tailTrace_1578897
  have hstable : (prefixWord ++ tailWord_1578897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578897).length < 2 ^ (prefixWord ++ tailWord_1578897).sum := by decide
  have hdescent : baseEnd_1578897 < baseStart_1578897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578900 : List Nat := [2, 4, 2, 1, 1, 2, 2, 1, 1, 1, 6]
def baseStart_1578900 : Nat := 118140960795 + 1578900 * 2 ^ 59
def prefixEnd_1578900 : Nat := 4983230072969 + 3 ^ 40 * 1578900 * 2
def baseEnd_1578900 : Nat := 810734605383977780188777

theorem tailTrace_1578900 : CollatzResearch.WordTrace tailWord_1578900 prefixEnd_1578900 810734605383977780188777 := by
  unfold tailWord_1578900
  simp only [CollatzResearch.WordTrace]
  refine ⟨28793606989961214748403077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38391475986614952997870769 28793606989961214748403077)
  ·
    refine ⟨5398801310617727765325577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28793606989961214748403077 5398801310617727765325577)
    ·
      refine ⟨4049100982963295823994183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5398801310617727765325577 4049100982963295823994183)
      ·
        refine ⟨6073651474444943735991275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4049100982963295823994183 6073651474444943735991275)
        ·
          refine ⟨9110477211667415603986913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6073651474444943735991275 9110477211667415603986913)
          ·
            refine ⟨6832857908750561702990185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9110477211667415603986913 6832857908750561702990185)
            ·
              refine ⟨5124643431562921277242639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6832857908750561702990185 5124643431562921277242639)
              ·
                refine ⟨7686965147344381915863959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5124643431562921277242639 7686965147344381915863959)
                ·
                  refine ⟨11530447721016572873795939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7686965147344381915863959 11530447721016572873795939)
                  ·
                    refine ⟨17295671581524859310693909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11530447721016572873795939 17295671581524859310693909)
                    ·
                      refine ⟨810734605383977780188777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17295671581524859310693909 810734605383977780188777)
                      ·
                        rfl

theorem cell23_1578900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_1578900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578900 prefixEnd_1578900 := by exact prefixLift 1578900
  have htrace : WordTrace (prefixWord ++ tailWord_1578900) baseStart_1578900 baseEnd_1578900 := by
    simpa [prefixWord, tailWord_1578900, baseEnd_1578900] using wordTrace_append hprefix tailTrace_1578900
  have hstable : (prefixWord ++ tailWord_1578900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578900).length < 2 ^ (prefixWord ++ tailWord_1578900).sum := by decide
  have hdescent : baseEnd_1578900 < baseStart_1578900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578932 : List Nat := [2, 5, 2, 1, 3, 1, 2, 2, 1, 1, 3]
def baseStart_1578932 : Nat := 118140960795 + 1578932 * 2 ^ 59
def prefixEnd_1578932 : Nat := 4983230072969 + 3 ^ 40 * 1578932 * 2
def baseEnd_1578932 : Nat := 810751036764921654988631

theorem tailTrace_1578932 : CollatzResearch.WordTrace tailWord_1578932 prefixEnd_1578932 810751036764921654988631 := by
  unfold tailWord_1578932
  simp only [CollatzResearch.WordTrace]
  refine ⟨28794190557903249480985525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38392254077204332641314033 28794190557903249480985525)
  ·
    refine ⟨2699455364803429638842393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28794190557903249480985525 2699455364803429638842393)
    ·
      refine ⟨2024591523602572229131795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2699455364803429638842393 2024591523602572229131795)
      ·
        refine ⟨3036887285403858343697693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2024591523602572229131795 3036887285403858343697693)
        ·
          refine ⟨1138832732026446878886635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3036887285403858343697693 1138832732026446878886635)
          ·
            refine ⟨1708249098039670318329953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1138832732026446878886635 1708249098039670318329953)
            ·
              refine ⟨1281186823529752738747465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1708249098039670318329953 1281186823529752738747465)
              ·
                refine ⟨960890117647314554060599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1281186823529752738747465 960890117647314554060599)
                ·
                  refine ⟨1441335176470971831090899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 960890117647314554060599 1441335176470971831090899)
                  ·
                    refine ⟨2162002764706457746636349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1441335176470971831090899 2162002764706457746636349)
                    ·
                      refine ⟨810751036764921654988631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2162002764706457746636349 810751036764921654988631)
                      ·
                        rfl

theorem cell23_1578932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_1578932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578932 prefixEnd_1578932 := by exact prefixLift 1578932
  have htrace : WordTrace (prefixWord ++ tailWord_1578932) baseStart_1578932 baseEnd_1578932 := by
    simpa [prefixWord, tailWord_1578932, baseEnd_1578932] using wordTrace_append hprefix tailTrace_1578932
  have hstable : (prefixWord ++ tailWord_1578932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578932).length < 2 ^ (prefixWord ++ tailWord_1578932).sum := by decide
  have hdescent : baseEnd_1578932 < baseStart_1578932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578943 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 4]
def baseStart_1578943 : Nat := 118140960795 + 1578943 * 2 ^ 59
def prefixEnd_1578943 : Nat := 4983230072969 + 3 ^ 40 * 1578943 * 2
def baseEnd_1578943 : Nat := 810756685052121111951079

theorem tailTrace_1578943 : CollatzResearch.WordTrace tailWord_1578943 prefixEnd_1578943 810756685052121111951079 := by
  unfold tailWord_1578943
  simp only [CollatzResearch.WordTrace]
  refine ⟨57588782318766647840621483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38392521545844431893747655 57588782318766647840621483)
  ·
    refine ⟨86383173478149971760932225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57588782318766647840621483 86383173478149971760932225)
    ·
      refine ⟨64787380108612478820699169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86383173478149971760932225 64787380108612478820699169)
      ·
        refine ⟨48590535081459359115524377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64787380108612478820699169 48590535081459359115524377)
        ·
          refine ⟨36442901311094519336643283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48590535081459359115524377 36442901311094519336643283)
          ·
            refine ⟨54664351966641779004964925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36442901311094519336643283 54664351966641779004964925)
            ·
              refine ⟨20499131987490667126861847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54664351966641779004964925 20499131987490667126861847)
              ·
                refine ⟨30748697981236000690292771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20499131987490667126861847 30748697981236000690292771)
                ·
                  refine ⟨46123046971854001035439157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30748697981236000690292771 46123046971854001035439157)
                  ·
                    refine ⟨4324035653611312597072421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46123046971854001035439157 4324035653611312597072421)
                    ·
                      refine ⟨810756685052121111951079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4324035653611312597072421 810756685052121111951079)
                      ·
                        rfl

theorem cell23_1578943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 4].length) (baseStart_1578943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578943 prefixEnd_1578943 := by exact prefixLift 1578943
  have htrace : WordTrace (prefixWord ++ tailWord_1578943) baseStart_1578943 baseEnd_1578943 := by
    simpa [prefixWord, tailWord_1578943, baseEnd_1578943] using wordTrace_append hprefix tailTrace_1578943
  have hstable : (prefixWord ++ tailWord_1578943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578943).length < 2 ^ (prefixWord ++ tailWord_1578943).sum := by decide
  have hdescent : baseEnd_1578943 < baseStart_1578943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578953 : List Nat := [1, 2, 1, 1, 2, 1, 2, 5, 2, 6]
def baseStart_1578953 : Nat := 118140960795 + 1578953 * 2 ^ 59
def prefixEnd_1578953 : Nat := 4983230072969 + 3 ^ 40 * 1578953 * 2
def baseEnd_1578953 : Nat := 270253939952888690942011

theorem tailTrace_1578953 : CollatzResearch.WordTrace tailWord_1578953 prefixEnd_1578953 270253939952888690942011 := by
  unfold tailWord_1578953
  simp only [CollatzResearch.WordTrace]
  refine ⟨57589147048730419548485513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38392764699153613032323675 57589147048730419548485513)
  ·
    refine ⟨43191860286547814661364135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57589147048730419548485513 43191860286547814661364135)
    ·
      refine ⟨64787790429821721992046203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43191860286547814661364135 64787790429821721992046203)
      ·
        refine ⟨97181685644732582988069305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64787790429821721992046203 97181685644732582988069305)
        ·
          refine ⟨72886264233549437241051979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97181685644732582988069305 72886264233549437241051979)
          ·
            refine ⟨109329396350324155861577969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72886264233549437241051979 109329396350324155861577969)
            ·
              refine ⟨81997047262743116896183477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109329396350324155861577969 81997047262743116896183477)
              ·
                refine ⟨7687223180882167209017201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81997047262743116896183477 7687223180882167209017201)
                ·
                  refine ⟨5765417385661625406762901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7687223180882167209017201 5765417385661625406762901)
                  ·
                    refine ⟨270253939952888690942011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5765417385661625406762901 270253939952888690942011)
                    ·
                      rfl

theorem cell23_1578953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 6].length) (baseStart_1578953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578953 prefixEnd_1578953 := by exact prefixLift 1578953
  have htrace : WordTrace (prefixWord ++ tailWord_1578953) baseStart_1578953 baseEnd_1578953 := by
    simpa [prefixWord, tailWord_1578953, baseEnd_1578953] using wordTrace_append hprefix tailTrace_1578953
  have hstable : (prefixWord ++ tailWord_1578953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578953).length < 2 ^ (prefixWord ++ tailWord_1578953).sum := by decide
  have hdescent : baseEnd_1578953 < baseStart_1578953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578964 : List Nat := [2, 4, 1, 2, 1, 1, 2, 4, 1, 3, 2]
def baseStart_1578964 : Nat := 118140960795 + 1578964 * 2 ^ 59
def prefixEnd_1578964 : Nat := 4983230072969 + 3 ^ 40 * 1578964 * 2
def baseEnd_1578964 : Nat := 810767468145865529788483

theorem tailTrace_1578964 : CollatzResearch.WordTrace tailWord_1578964 prefixEnd_1578964 810767468145865529788483 := by
  unfold tailWord_1578964
  simp only [CollatzResearch.WordTrace]
  refine ⟨28794774125845284213567973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38393032167793712284757297 28794774125845284213567973)
  ·
    refine ⟨5399020148595990790043995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28794774125845284213567973 5399020148595990790043995)
    ·
      refine ⟨8098530222893986185065993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5399020148595990790043995 8098530222893986185065993)
      ·
        refine ⟨6073897667170489638799495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8098530222893986185065993 6073897667170489638799495)
        ·
          refine ⟨9110846500755734458199243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6073897667170489638799495 9110846500755734458199243)
          ·
            refine ⟨13666269751133601687298865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9110846500755734458199243 13666269751133601687298865)
            ·
              refine ⟨10249702313350201265474149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13666269751133601687298865 10249702313350201265474149)
              ·
                refine ⟨1921819183753162737276403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10249702313350201265474149 1921819183753162737276403)
                ·
                  refine ⟨2882728775629744105914605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1921819183753162737276403 2882728775629744105914605)
                  ·
                    refine ⟨1081023290861154039717977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2882728775629744105914605 1081023290861154039717977)
                    ·
                      refine ⟨810767468145865529788483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1081023290861154039717977 810767468145865529788483)
                      ·
                        rfl

theorem cell23_1578964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_1578964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578964 prefixEnd_1578964 := by exact prefixLift 1578964
  have htrace : WordTrace (prefixWord ++ tailWord_1578964) baseStart_1578964 baseEnd_1578964 := by
    simpa [prefixWord, tailWord_1578964, baseEnd_1578964] using wordTrace_append hprefix tailTrace_1578964
  have hstable : (prefixWord ++ tailWord_1578964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578964).length < 2 ^ (prefixWord ++ tailWord_1578964).sum := by decide
  have hdescent : baseEnd_1578964 < baseStart_1578964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578972 : List Nat := [2, 2, 6, 1, 1, 1, 2, 3, 1, 2, 2]
def baseStart_1578972 : Nat := 118140960795 + 1578972 * 2 ^ 59
def prefixEnd_1578972 : Nat := 4983230072969 + 3 ^ 40 * 1578972 * 2
def baseEnd_1578972 : Nat := 810771575991101498488447

theorem tailTrace_1578972 : CollatzResearch.WordTrace tailWord_1578972 prefixEnd_1578972 810771575991101498488447 := by
  unfold tailWord_1578972
  simp only [CollatzResearch.WordTrace]
  refine ⟨28794920017830792896713585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38393226690441057195618113 28794920017830792896713585)
  ·
    refine ⟨21596190013373094672535189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28794920017830792896713585 21596190013373094672535189)
    ·
      refine ⟨1012321406876863812775087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21596190013373094672535189 1012321406876863812775087)
      ·
        refine ⟨1518482110315295719162631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1012321406876863812775087 1518482110315295719162631)
        ·
          refine ⟨2277723165472943578743947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1518482110315295719162631 2277723165472943578743947)
          ·
            refine ⟨3416584748209415368115921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2277723165472943578743947 3416584748209415368115921)
            ·
              refine ⟨2562438561157061526086941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3416584748209415368115921 2562438561157061526086941)
              ·
                refine ⟨960914460433898072282603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2562438561157061526086941 960914460433898072282603)
                ·
                  refine ⟨1441371690650847108423905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 960914460433898072282603 1441371690650847108423905)
                  ·
                    refine ⟨1081028767988135331317929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1441371690650847108423905 1081028767988135331317929)
                    ·
                      refine ⟨810771575991101498488447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1081028767988135331317929 810771575991101498488447)
                      ·
                        rfl

theorem cell23_1578972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_1578972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578972 prefixEnd_1578972 := by exact prefixLift 1578972
  have htrace : WordTrace (prefixWord ++ tailWord_1578972) baseStart_1578972 baseEnd_1578972 := by
    simpa [prefixWord, tailWord_1578972, baseEnd_1578972] using wordTrace_append hprefix tailTrace_1578972
  have hstable : (prefixWord ++ tailWord_1578972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578972).length < 2 ^ (prefixWord ++ tailWord_1578972).sum := by decide
  have hdescent : baseEnd_1578972 < baseStart_1578972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578977 : List Nat := [1, 2, 3, 1, 2, 1, 4, 2, 1, 4, 2]
def baseStart_1578977 : Nat := 118140960795 + 1578977 * 2 ^ 59
def prefixEnd_1578977 : Nat := 4983230072969 + 3 ^ 40 * 1578977 * 2
def baseEnd_1578977 : Nat := 810774143394373978925923

theorem tailTrace_1578977 : CollatzResearch.WordTrace tailWord_1578977 prefixEnd_1578977 810774143394373978925923 := by
  unfold tailWord_1578977
  simp only [CollatzResearch.WordTrace]
  refine ⟨57590022400643471647359185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38393348267095647764906123 57590022400643471647359185)
  ·
    refine ⟨43192516800482603735519389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57590022400643471647359185 43192516800482603735519389)
    ·
      refine ⟨16197193800180976400819771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43192516800482603735519389 16197193800180976400819771)
      ·
        refine ⟨24295790700271464601229657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16197193800180976400819771 24295790700271464601229657)
        ·
          refine ⟨18221843025203598450922243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24295790700271464601229657 18221843025203598450922243)
          ·
            refine ⟨27332764537805397676383365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18221843025203598450922243 27332764537805397676383365)
            ·
              refine ⟨5124893350838512064321881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27332764537805397676383365 5124893350838512064321881)
              ·
                refine ⟨3843670013128884048241411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5124893350838512064321881 3843670013128884048241411)
                ·
                  refine ⟨5765505019693326072362117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3843670013128884048241411 5765505019693326072362117)
                  ·
                    refine ⟨1081032191192498638567897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5765505019693326072362117 1081032191192498638567897)
                    ·
                      refine ⟨810774143394373978925923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1081032191192498638567897 810774143394373978925923)
                      ·
                        rfl

theorem cell23_1578977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 4, 2].length) (baseStart_1578977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1578977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1578977 prefixEnd_1578977 := by exact prefixLift 1578977
  have htrace : WordTrace (prefixWord ++ tailWord_1578977) baseStart_1578977 baseEnd_1578977 := by
    simpa [prefixWord, tailWord_1578977, baseEnd_1578977] using wordTrace_append hprefix tailTrace_1578977
  have hstable : (prefixWord ++ tailWord_1578977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578977).length < 2 ^ (prefixWord ++ tailWord_1578977).sum := by decide
  have hdescent : baseEnd_1578977 < baseStart_1578977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579034 : List Nat := [3, 1, 1, 3, 1, 5, 1, 3, 5]
def baseStart_1579034 : Nat := 118140960795 + 1579034 * 2 ^ 59
def prefixEnd_1579034 : Nat := 4983230072969 + 3 ^ 40 * 1579034 * 2
def baseEnd_1579034 : Nat := 90089267976853361768129

theorem tailTrace_1579034 : CollatzResearch.WordTrace tailWord_1579034 prefixEnd_1579034 90089267976853361768129 := by
  unfold tailWord_1579034
  simp only [CollatzResearch.WordTrace]
  refine ⟨14398025340359242595546039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38394734240957980254789437 14398025340359242595546039)
  ·
    refine ⟨21597038010538863893319059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14398025340359242595546039 21597038010538863893319059)
    ·
      refine ⟨32395557015808295839978589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21597038010538863893319059 32395557015808295839978589)
      ·
        refine ⟨12148333880928110939991971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32395557015808295839978589 12148333880928110939991971)
        ·
          refine ⟨18222500821392166409987957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12148333880928110939991971 18222500821392166409987957)
          ·
            refine ⟨1708359452005515600936371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18222500821392166409987957 1708359452005515600936371)
            ·
              refine ⟨2562539178008273401404557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1708359452005515600936371 2562539178008273401404557)
              ·
                refine ⟨960952191753102525526709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2562539178008273401404557 960952191753102525526709)
                ·
                  refine ⟨90089267976853361768129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 960952191753102525526709 90089267976853361768129)
                  ·
                    rfl

theorem cell23_1579034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 3, 5].length) (baseStart_1579034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1579034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1579034 prefixEnd_1579034 := by exact prefixLift 1579034
  have htrace : WordTrace (prefixWord ++ tailWord_1579034) baseStart_1579034 baseEnd_1579034 := by
    simpa [prefixWord, tailWord_1579034, baseEnd_1579034] using wordTrace_append hprefix tailTrace_1579034
  have hstable : (prefixWord ++ tailWord_1579034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579034).length < 2 ^ (prefixWord ++ tailWord_1579034).sum := by decide
  have hdescent : baseEnd_1579034 < baseStart_1579034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579102 : List Nat := [4, 4, 1, 1, 3, 1, 2, 2, 5]
def baseStart_1579102 : Nat := 118140960795 + 1579102 * 2 ^ 59
def prefixEnd_1579102 : Nat := 4983230072969 + 3 ^ 40 * 1579102 * 2
def baseEnd_1579102 : Nat := 90093147608465109984761

theorem tailTrace_1579102 : CollatzResearch.WordTrace tailWord_1579102 prefixEnd_1579102 90093147608465109984761 := by
  unfold tailWord_1579102
  simp only [CollatzResearch.WordTrace]
  refine ⟨7199322690648827249457445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38396387683460411997106373 7199322690648827249457445)
  ·
    refine ⟨1349873004496655109273271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7199322690648827249457445 1349873004496655109273271)
    ·
      refine ⟨2024809506744982663909907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1349873004496655109273271 2024809506744982663909907)
      ·
        refine ⟨3037214260117473995864861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2024809506744982663909907 3037214260117473995864861)
        ·
          refine ⟨1138955347544052748449323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3037214260117473995864861 1138955347544052748449323)
          ·
            refine ⟨1708433021316079122673985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1138955347544052748449323 1708433021316079122673985)
            ·
              refine ⟨1281324765987059342005489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1708433021316079122673985 1281324765987059342005489)
              ·
                refine ⟨960993574490294506504117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1281324765987059342005489 960993574490294506504117)
                ·
                  refine ⟨90093147608465109984761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 960993574490294506504117 90093147608465109984761)
                  ·
                    rfl

theorem cell23_1579102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_1579102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1579102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1579102 prefixEnd_1579102 := by exact prefixLift 1579102
  have htrace : WordTrace (prefixWord ++ tailWord_1579102) baseStart_1579102 baseEnd_1579102 := by
    simpa [prefixWord, tailWord_1579102, baseEnd_1579102] using wordTrace_append hprefix tailTrace_1579102
  have hstable : (prefixWord ++ tailWord_1579102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579102).length < 2 ^ (prefixWord ++ tailWord_1579102).sum := by decide
  have hdescent : baseEnd_1579102 < baseStart_1579102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579154 : List Nat := [3, 2, 3, 1, 1, 1, 3, 3, 1, 5]
def baseStart_1579154 : Nat := 118140960795 + 1579154 * 2 ^ 59
def prefixEnd_1579154 : Nat := 4983230072969 + 3 ^ 40 * 1579154 * 2
def baseEnd_1579154 : Nat := 270288343156739928804203

theorem tailTrace_1579154 : CollatzResearch.WordTrace tailWord_1579154 prefixEnd_1579154 270288343156739928804203 := by
  unfold tailWord_1579154
  simp only [CollatzResearch.WordTrace]
  refine ⟨14399119530250557719138129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38397652080668153917701677 14399119530250557719138129)
  ·
    refine ⟨10799339647687918289353597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14399119530250557719138129 10799339647687918289353597)
    ·
      refine ⟨4049752367882969358507599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10799339647687918289353597 4049752367882969358507599)
      ·
        refine ⟨6074628551824454037761399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4049752367882969358507599 6074628551824454037761399)
        ·
          refine ⟨9111942827736681056642099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6074628551824454037761399 9111942827736681056642099)
          ·
            refine ⟨13667914241605021584963149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9111942827736681056642099 13667914241605021584963149)
            ·
              refine ⟨5125467840601883094361181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13667914241605021584963149 5125467840601883094361181)
              ·
                refine ⟨1922050440225706160385443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5125467840601883094361181 1922050440225706160385443)
                ·
                  refine ⟨2883075660338559240578165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1922050440225706160385443 2883075660338559240578165)
                  ·
                    refine ⟨270288343156739928804203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2883075660338559240578165 270288343156739928804203)
                    ·
                      rfl

theorem cell23_1579154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_1579154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1579154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1579154 prefixEnd_1579154 := by exact prefixLift 1579154
  have htrace : WordTrace (prefixWord ++ tailWord_1579154) baseStart_1579154 baseEnd_1579154 := by
    simpa [prefixWord, tailWord_1579154, baseEnd_1579154] using wordTrace_append hprefix tailTrace_1579154
  have hstable : (prefixWord ++ tailWord_1579154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579154).length < 2 ^ (prefixWord ++ tailWord_1579154).sum := by decide
  have hdescent : baseEnd_1579154 < baseStart_1579154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579191 : List Nat := [1, 1, 3, 1, 4, 2, 2, 2, 3, 2, 2]
def baseStart_1579191 : Nat := 118140960795 + 1579191 * 2 ^ 59
def prefixEnd_1579191 : Nat := 4983230072969 + 3 ^ 40 * 1579191 * 2
def baseEnd_1579191 : Nat := 810884028254436141649939

theorem tailTrace_1579191 : CollatzResearch.WordTrace tailWord_1579191 prefixEnd_1579191 810884028254436141649939 := by
  unfold tailWord_1579191
  simp only [CollatzResearch.WordTrace]
  refine ⟨57597827621868186195649427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38398551747912124130432951 57597827621868186195649427)
  ·
    refine ⟨86396741432802279293474141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57597827621868186195649427 86396741432802279293474141)
    ·
      refine ⟨32398778037300854735052803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86396741432802279293474141 32398778037300854735052803)
      ·
        refine ⟨48598167055951282102579205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32398778037300854735052803 48598167055951282102579205)
        ·
          refine ⟨9112156322990865394233601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48598167055951282102579205 9112156322990865394233601)
          ·
            refine ⟨6834117242243149045675201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9112156322990865394233601 6834117242243149045675201)
            ·
              refine ⟨5125587931682361784256401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6834117242243149045675201 5125587931682361784256401)
              ·
                refine ⟨3844190948761771338192301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5125587931682361784256401 3844190948761771338192301)
                ·
                  refine ⟨1441571605785664251822113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3844190948761771338192301 1441571605785664251822113)
                  ·
                    refine ⟨1081178704339248188866585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1441571605785664251822113 1081178704339248188866585)
                    ·
                      refine ⟨810884028254436141649939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1081178704339248188866585 810884028254436141649939)
                      ·
                        rfl

theorem cell23_1579191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 3, 2, 2].length) (baseStart_1579191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1579191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1579191 prefixEnd_1579191 := by exact prefixLift 1579191
  have htrace : WordTrace (prefixWord ++ tailWord_1579191) baseStart_1579191 baseEnd_1579191 := by
    simpa [prefixWord, tailWord_1579191, baseEnd_1579191] using wordTrace_append hprefix tailTrace_1579191
  have hstable : (prefixWord ++ tailWord_1579191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579191).length < 2 ^ (prefixWord ++ tailWord_1579191).sum := by decide
  have hdescent : baseEnd_1579191 < baseStart_1579191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579194 : List Nat := [3, 1, 1, 1, 2, 2, 3, 4, 1, 2, 3]
def baseStart_1579194 : Nat := 118140960795 + 1579194 * 2 ^ 59
def prefixEnd_1579194 : Nat := 4983230072969 + 3 ^ 40 * 1579194 * 2
def baseEnd_1579194 : Nat := 810885568696399629912425

theorem tailTrace_1579194 : CollatzResearch.WordTrace tailWord_1579194 prefixEnd_1579194 810885568696399629912425 := by
  unfold tailWord_1579194
  simp only [CollatzResearch.WordTrace]
  refine ⟨14399484260214329427002159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38398624693904878472005757 14399484260214329427002159)
  ·
    refine ⟨21599226390321494140503239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14399484260214329427002159 21599226390321494140503239)
    ·
      refine ⟨32398839585482241210754859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21599226390321494140503239 32398839585482241210754859)
      ·
        refine ⟨48598259378223361816132289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32398839585482241210754859 48598259378223361816132289)
        ·
          refine ⟨36448694533667521362099217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48598259378223361816132289 36448694533667521362099217)
          ·
            refine ⟨27336520900250641021574413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36448694533667521362099217 27336520900250641021574413)
            ·
              refine ⟨10251195337593990383090405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27336520900250641021574413 10251195337593990383090405)
              ·
                refine ⟨1922099125798873196829451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10251195337593990383090405 1922099125798873196829451)
                ·
                  refine ⟨2883148688698309795244177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1922099125798873196829451 2883148688698309795244177)
                  ·
                    refine ⟨2162361516523732346433133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2883148688698309795244177 2162361516523732346433133)
                    ·
                      refine ⟨810885568696399629912425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2162361516523732346433133 810885568696399629912425)
                      ·
                        rfl

theorem cell23_1579194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 1, 2, 3].length) (baseStart_1579194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1579194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1579194 prefixEnd_1579194 := by exact prefixLift 1579194
  have htrace : WordTrace (prefixWord ++ tailWord_1579194) baseStart_1579194 baseEnd_1579194 := by
    simpa [prefixWord, tailWord_1579194, baseEnd_1579194] using wordTrace_append hprefix tailTrace_1579194
  have hstable : (prefixWord ++ tailWord_1579194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579194).length < 2 ^ (prefixWord ++ tailWord_1579194).sum := by decide
  have hdescent : baseEnd_1579194 < baseStart_1579194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579202 : List Nat := [3, 5, 1, 1, 1, 1, 3, 3, 1, 1, 3]
def baseStart_1579202 : Nat := 118140960795 + 1579202 * 2 ^ 59
def prefixEnd_1579202 : Nat := 4983230072969 + 3 ^ 40 * 1579202 * 2
def baseEnd_1579202 : Nat := 810889676541635598612389

theorem tailTrace_1579202 : CollatzResearch.WordTrace tailWord_1579202 prefixEnd_1579202 810889676541635598612389 := by
  unfold tailWord_1579202
  simp only [CollatzResearch.WordTrace]
  refine ⟨14399557206207083768574965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38398819216552223382866573 14399557206207083768574965)
  ·
    refine ⟨1349958488081914103303903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14399557206207083768574965 1349958488081914103303903)
    ·
      refine ⟨2024937732122871154955855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1349958488081914103303903 2024937732122871154955855)
      ·
        refine ⟨3037406598184306732433783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2024937732122871154955855 3037406598184306732433783)
        ·
          refine ⟨4556109897276460098650675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3037406598184306732433783 4556109897276460098650675)
          ·
            refine ⟨6834164845914690147976013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4556109897276460098650675 6834164845914690147976013)
            ·
              refine ⟨2562811817218008805491005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6834164845914690147976013 2562811817218008805491005)
              ·
                refine ⟨961054431456753302059127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2562811817218008805491005 961054431456753302059127)
                ·
                  refine ⟨1441581647185129953088691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 961054431456753302059127 1441581647185129953088691)
                  ·
                    refine ⟨2162372470777694929633037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1441581647185129953088691 2162372470777694929633037)
                    ·
                      refine ⟨810889676541635598612389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2162372470777694929633037 810889676541635598612389)
                      ·
                        rfl

theorem cell23_1579202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_1579202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1579202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1579202 prefixEnd_1579202 := by exact prefixLift 1579202
  have htrace : WordTrace (prefixWord ++ tailWord_1579202) baseStart_1579202 baseEnd_1579202 := by
    simpa [prefixWord, tailWord_1579202, baseEnd_1579202] using wordTrace_append hprefix tailTrace_1579202
  have hstable : (prefixWord ++ tailWord_1579202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579202).length < 2 ^ (prefixWord ++ tailWord_1579202).sum := by decide
  have hdescent : baseEnd_1579202 < baseStart_1579202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579235 : List Nat := [1, 1, 1, 8, 1, 2, 2, 1, 2, 4]
def baseStart_1579235 : Nat := 118140960795 + 1579235 * 2 ^ 59
def prefixEnd_1579235 : Nat := 4983230072969 + 3 ^ 40 * 1579235 * 2
def baseEnd_1579235 : Nat := 270302207134411323166579

theorem tailTrace_1579235 : CollatzResearch.WordTrace tailWord_1579235 prefixEnd_1579235 270302207134411323166579 := by
  unfold tailWord_1579235
  simp only [CollatzResearch.WordTrace]
  refine ⟨57599432433708781710251159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38399621622472521140167439 57599432433708781710251159)
  ·
    refine ⟨86399148650563172565376739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57599432433708781710251159 86399148650563172565376739)
    ·
      refine ⟨129598722975844758848065109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86399148650563172565376739 129598722975844758848065109)
      ·
        refine ⟨1518735034873180767750763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 129598722975844758848065109 1518735034873180767750763)
        ·
          refine ⟨2278102552309771151626145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1518735034873180767750763 2278102552309771151626145)
          ·
            refine ⟨1708576914232328363719609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2278102552309771151626145 1708576914232328363719609)
            ·
              refine ⟨1281432685674246272789707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1708576914232328363719609 1281432685674246272789707)
              ·
                refine ⟨1922149028511369409184561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1281432685674246272789707 1922149028511369409184561)
                ·
                  refine ⟨1441611771383527056888421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1922149028511369409184561 1441611771383527056888421)
                  ·
                    refine ⟨270302207134411323166579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1441611771383527056888421 270302207134411323166579)
                    ·
                      rfl

theorem cell23_1579235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 2, 4].length) (baseStart_1579235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1579235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1579235 prefixEnd_1579235 := by exact prefixLift 1579235
  have htrace : WordTrace (prefixWord ++ tailWord_1579235) baseStart_1579235 baseEnd_1579235 := by
    simpa [prefixWord, tailWord_1579235, baseEnd_1579235] using wordTrace_append hprefix tailTrace_1579235
  have hstable : (prefixWord ++ tailWord_1579235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579235).length < 2 ^ (prefixWord ++ tailWord_1579235).sum := by decide
  have hdescent : baseEnd_1579235 < baseStart_1579235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579245 : List Nat := [1, 5, 1, 2, 4, 1, 1, 2, 1, 2, 3]
def baseStart_1579245 : Nat := 118140960795 + 1579245 * 2 ^ 59
def prefixEnd_1579245 : Nat := 4983230072969 + 3 ^ 40 * 1579245 * 2
def baseEnd_1579245 : Nat := 810911756209778930374691

theorem tailTrace_1579245 : CollatzResearch.WordTrace tailWord_1579245 prefixEnd_1579245 810911756209778930374691 := by
  unfold tailWord_1579245
  simp only [CollatzResearch.WordTrace]
  refine ⟨57599797163672553418115189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38399864775781702278743459 57599797163672553418115189)
  ·
    refine ⟨5399980984094301882948299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57599797163672553418115189 5399980984094301882948299)
    ·
      refine ⟨8099971476141452824422449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5399980984094301882948299 8099971476141452824422449)
      ·
        refine ⟨6074978607106089618316837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8099971476141452824422449 6074978607106089618316837)
        ·
          refine ⟨1139058488832391803434407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6074978607106089618316837 1139058488832391803434407)
          ·
            refine ⟨1708587733248587705151611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1139058488832391803434407 1708587733248587705151611)
            ·
              refine ⟨2562881599872881557727417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1708587733248587705151611 2562881599872881557727417)
              ·
                refine ⟨1922161199904661168295563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2562881599872881557727417 1922161199904661168295563)
                ·
                  refine ⟨2883241799856991752443345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1922161199904661168295563 2883241799856991752443345)
                  ·
                    refine ⟨2162431349892743814332509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2883241799856991752443345 2162431349892743814332509)
                    ·
                      refine ⟨810911756209778930374691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2162431349892743814332509 810911756209778930374691)
                      ·
                        rfl

theorem cell23_1579245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_1579245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1579245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1579245 prefixEnd_1579245 := by exact prefixLift 1579245
  have htrace : WordTrace (prefixWord ++ tailWord_1579245) baseStart_1579245 baseEnd_1579245 := by
    simpa [prefixWord, tailWord_1579245, baseEnd_1579245] using wordTrace_append hprefix tailTrace_1579245
  have hstable : (prefixWord ++ tailWord_1579245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579245).length < 2 ^ (prefixWord ++ tailWord_1579245).sum := by decide
  have hdescent : baseEnd_1579245 < baseStart_1579245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579264 : List Nat := [2, 1, 1, 2, 1, 1, 5, 1, 3, 4, 2]
def baseStart_1579264 : Nat := 118140960795 + 1579264 * 2 ^ 59
def prefixEnd_1579264 : Nat := 4983230072969 + 3 ^ 40 * 1579264 * 2
def baseEnd_1579264 : Nat := 810921512342214356037103

theorem tailTrace_1579264 : CollatzResearch.WordTrace tailWord_1579264 prefixEnd_1579264 810921512342214356037103 := by
  unfold tailWord_1579264
  simp only [CollatzResearch.WordTrace]
  refine ⟨28800245075301859831528423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38400326767069146442037897 28800245075301859831528423)
  ·
    refine ⟨43200367612952789747292635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28800245075301859831528423 43200367612952789747292635)
    ·
      refine ⟨64800551419429184620938953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43200367612952789747292635 64800551419429184620938953)
      ·
        refine ⟨48600413564571888465704215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64800551419429184620938953 48600413564571888465704215)
        ·
          refine ⟨72900620346857832698556323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48600413564571888465704215 72900620346857832698556323)
          ·
            refine ⟨109350930520286749047834485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72900620346857832698556323 109350930520286749047834485)
            ·
              refine ⟨10251649736276882723234483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109350930520286749047834485 10251649736276882723234483)
              ·
                refine ⟨15377474604415324084851725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10251649736276882723234483 15377474604415324084851725)
                ·
                  refine ⟨5766552976655746531819397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15377474604415324084851725 5766552976655746531819397)
                  ·
                    refine ⟨1081228683122952474716137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5766552976655746531819397 1081228683122952474716137)
                    ·
                      refine ⟨810921512342214356037103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1081228683122952474716137 810921512342214356037103)
                      ·
                        rfl

theorem cell23_1579264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 3, 4, 2].length) (baseStart_1579264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1579264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1579264 prefixEnd_1579264 := by exact prefixLift 1579264
  have htrace : WordTrace (prefixWord ++ tailWord_1579264) baseStart_1579264 baseEnd_1579264 := by
    simpa [prefixWord, tailWord_1579264, baseEnd_1579264] using wordTrace_append hprefix tailTrace_1579264
  have hstable : (prefixWord ++ tailWord_1579264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579264).length < 2 ^ (prefixWord ++ tailWord_1579264).sum := by decide
  have hdescent : baseEnd_1579264 < baseStart_1579264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579267 : List Nat := [1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 5]
def baseStart_1579267 : Nat := 118140960795 + 1579267 * 2 ^ 59
def prefixEnd_1579267 : Nat := 4983230072969 + 3 ^ 40 * 1579267 * 2
def baseEnd_1579267 : Nat := 810923052784177844299589

theorem tailTrace_1579267 : CollatzResearch.WordTrace tailWord_1579267 prefixEnd_1579267 810923052784177844299589 := by
  unfold tailWord_1579267
  simp only [CollatzResearch.WordTrace]
  refine ⟨57600599569592851175416055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38400399713061900783610703 57600599569592851175416055)
  ·
    refine ⟨86400899354389276763124083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57600599569592851175416055 86400899354389276763124083)
    ·
      refine ⟨129601349031583915144686125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86400899354389276763124083 129601349031583915144686125)
      ·
        refine ⟨48600505886843968179257297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129601349031583915144686125 48600505886843968179257297)
        ·
          refine ⟨36450379415132976134442973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48600505886843968179257297 36450379415132976134442973)
          ·
            refine ⟨13668892280674866050416115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36450379415132976134442973 13668892280674866050416115)
            ·
              refine ⟨20503338421012299075624173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13668892280674866050416115 20503338421012299075624173)
              ·
                refine ⟨7688751907879612153359065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20503338421012299075624173 7688751907879612153359065)
                ·
                  refine ⟨5766563930909709115019299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7688751907879612153359065 5766563930909709115019299)
                  ·
                    refine ⟨8649845896364563672528949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5766563930909709115019299 8649845896364563672528949)
                    ·
                      refine ⟨810923052784177844299589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8649845896364563672528949 810923052784177844299589)
                      ·
                        rfl

theorem cell23_1579267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 5].length) (baseStart_1579267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1579267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1579267 prefixEnd_1579267 := by exact prefixLift 1579267
  have htrace : WordTrace (prefixWord ++ tailWord_1579267) baseStart_1579267 baseEnd_1579267 := by
    simpa [prefixWord, tailWord_1579267, baseEnd_1579267] using wordTrace_append hprefix tailTrace_1579267
  have hstable : (prefixWord ++ tailWord_1579267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579267).length < 2 ^ (prefixWord ++ tailWord_1579267).sum := by decide
  have hdescent : baseEnd_1579267 < baseStart_1579267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579298 : List Nat := [3, 3, 1, 1, 3, 2, 2, 1, 1, 4, 2]
def baseStart_1579298 : Nat := 118140960795 + 1579298 * 2 ^ 59
def prefixEnd_1579298 : Nat := 4983230072969 + 3 ^ 40 * 1579298 * 2
def baseEnd_1579298 : Nat := 810938970684467223011947

theorem tailTrace_1579298 : CollatzResearch.WordTrace tailWord_1579298 prefixEnd_1579298 810938970684467223011947 := by
  unfold tailWord_1579298
  simp only [CollatzResearch.WordTrace]
  refine ⟨14400432558120135867448637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38401153488320362313196365 14400432558120135867448637)
  ·
    refine ⟨5400162209295050950293239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14400432558120135867448637 5400162209295050950293239)
    ·
      refine ⟨8100243313942576425439859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5400162209295050950293239 8100243313942576425439859)
      ·
        refine ⟨12150364970913864638159789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8100243313942576425439859 12150364970913864638159789)
        ·
          refine ⟨4556386864092699239309921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12150364970913864638159789 4556386864092699239309921)
          ·
            refine ⟨3417290148069524429482441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4556386864092699239309921 3417290148069524429482441)
            ·
              refine ⟨2562967611052143322111831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3417290148069524429482441 2562967611052143322111831)
              ·
                refine ⟨3844451416578214983167747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2562967611052143322111831 3844451416578214983167747)
                ·
                  refine ⟨5766677124867322474751621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3844451416578214983167747 5766677124867322474751621)
                  ·
                    refine ⟨1081251960912622964015929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5766677124867322474751621 1081251960912622964015929)
                    ·
                      refine ⟨810938970684467223011947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1081251960912622964015929 810938970684467223011947)
                      ·
                        rfl

theorem cell23_1579298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_1579298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1579298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1579298 prefixEnd_1579298 := by exact prefixLift 1579298
  have htrace : WordTrace (prefixWord ++ tailWord_1579298) baseStart_1579298 baseEnd_1579298 := by
    simpa [prefixWord, tailWord_1579298, baseEnd_1579298] using wordTrace_append hprefix tailTrace_1579298
  have hstable : (prefixWord ++ tailWord_1579298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579298).length < 2 ^ (prefixWord ++ tailWord_1579298).sum := by decide
  have hdescent : baseEnd_1579298 < baseStart_1579298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579321 : List Nat := [1, 2, 1, 6, 1, 1, 1, 5, 5]
def baseStart_1579321 : Nat := 118140960795 + 1579321 * 2 ^ 59
def prefixEnd_1579321 : Nat := 4983230072969 + 3 ^ 40 * 1579321 * 2
def baseEnd_1579321 : Nat := 90105642304391181447149

theorem tailTrace_1579321 : CollatzResearch.WordTrace tailWord_1579321 prefixEnd_1579321 90105642304391181447149 := by
  unfold tailWord_1579321
  simp only [CollatzResearch.WordTrace]
  refine ⟨57602569111397218397881817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38401712740931478931921211 57602569111397218397881817)
  ·
    refine ⟨43201926833547913798411363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57602569111397218397881817 43201926833547913798411363)
    ·
      refine ⟨64802890250321870697617045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43201926833547913798411363 64802890250321870697617045)
      ·
        refine ⟨3037635480483837688950799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 64802890250321870697617045 3037635480483837688950799)
        ·
          refine ⟨4556453220725756533426199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3037635480483837688950799 4556453220725756533426199)
          ·
            refine ⟨6834679831088634800139299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4556453220725756533426199 6834679831088634800139299)
            ·
              refine ⟨10252019746632952200208949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6834679831088634800139299 10252019746632952200208949)
              ·
                refine ⟨961126851246839268769589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10252019746632952200208949 961126851246839268769589)
                ·
                  refine ⟨90105642304391181447149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 961126851246839268769589 90105642304391181447149)
                  ·
                    rfl

theorem cell23_1579321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 5, 5].length) (baseStart_1579321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1579321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1579321 prefixEnd_1579321 := by exact prefixLift 1579321
  have htrace : WordTrace (prefixWord ++ tailWord_1579321) baseStart_1579321 baseEnd_1579321 := by
    simpa [prefixWord, tailWord_1579321, baseEnd_1579321] using wordTrace_append hprefix tailTrace_1579321
  have hstable : (prefixWord ++ tailWord_1579321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579321).length < 2 ^ (prefixWord ++ tailWord_1579321).sum := by decide
  have hdescent : baseEnd_1579321 < baseStart_1579321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579425 : List Nat := [1, 2, 3, 5, 1, 1, 2, 1, 2, 2, 3]
def baseStart_1579425 : Nat := 118140960795 + 1579425 * 2 ^ 59
def prefixEnd_1579425 : Nat := 4983230072969 + 3 ^ 40 * 1579425 * 2
def baseEnd_1579425 : Nat := 811004182727588226123863

theorem tailTrace_1579425 : CollatzResearch.WordTrace tailWord_1579425 prefixEnd_1579425 811004182727588226123863 := by
  unfold tailWord_1579425
  simp only [CollatzResearch.WordTrace]
  refine ⟨57606362303020444159667729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38404241535346962773111819 57606362303020444159667729)
  ·
    refine ⟨43204771727265333119750797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57606362303020444159667729 43204771727265333119750797)
    ·
      refine ⟨16201789397724499919906549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43204771727265333119750797 16201789397724499919906549)
      ·
        refine ⟨1518917756036671867491239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16201789397724499919906549 1518917756036671867491239)
        ·
          refine ⟨2278376634055007801236859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1518917756036671867491239 2278376634055007801236859)
          ·
            refine ⟨3417564951082511701855289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2278376634055007801236859 3417564951082511701855289)
            ·
              refine ⟨2563173713311883776391467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3417564951082511701855289 2563173713311883776391467)
              ·
                refine ⟨3844760569967825664587201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2563173713311883776391467 3844760569967825664587201)
                ·
                  refine ⟨2883570427475869248440401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3844760569967825664587201 2883570427475869248440401)
                  ·
                    refine ⟨2162677820606901936330301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2883570427475869248440401 2162677820606901936330301)
                    ·
                      refine ⟨811004182727588226123863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2162677820606901936330301 811004182727588226123863)
                      ·
                        rfl

theorem cell23_1579425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_1579425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1579425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1579425 prefixEnd_1579425 := by exact prefixLift 1579425
  have htrace : WordTrace (prefixWord ++ tailWord_1579425) baseStart_1579425 baseEnd_1579425 := by
    simpa [prefixWord, tailWord_1579425, baseEnd_1579425] using wordTrace_append hprefix tailTrace_1579425
  have hstable : (prefixWord ++ tailWord_1579425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579425).length < 2 ^ (prefixWord ++ tailWord_1579425).sum := by decide
  have hdescent : baseEnd_1579425 < baseStart_1579425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579478 : List Nat := [5, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4]
def baseStart_1579478 : Nat := 118140960795 + 1579478 * 2 ^ 59
def prefixEnd_1579478 : Nat := 4983230072969 + 3 ^ 40 * 1579478 * 2
def baseEnd_1579478 : Nat := 811031397202276518761119

theorem tailTrace_1579478 : CollatzResearch.WordTrace tailWord_1579478 prefixEnd_1579478 811031397202276518761119 := by
  unfold tailWord_1579478
  simp only [CollatzResearch.WordTrace]
  refine ⟨3600518460739277138209193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38405530247885622807564725 3600518460739277138209193)
  ·
    refine ⟨2700388845554457853656895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3600518460739277138209193 2700388845554457853656895)
    ·
      refine ⟨4050583268331686780485343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2700388845554457853656895 4050583268331686780485343)
      ·
        refine ⟨6075874902497530170728015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4050583268331686780485343 6075874902497530170728015)
        ·
          refine ⟨9113812353746295256092023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6075874902497530170728015 9113812353746295256092023)
          ·
            refine ⟨13670718530619442884138035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9113812353746295256092023 13670718530619442884138035)
            ·
              refine ⟨20506077795929164326207053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13670718530619442884138035 20506077795929164326207053)
              ·
                refine ⟨7689779173473436622327645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20506077795929164326207053 7689779173473436622327645)
                ·
                  refine ⟨2883667190052538733372867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7689779173473436622327645 2883667190052538733372867)
                  ·
                    refine ⟨4325500785078808100059301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2883667190052538733372867 4325500785078808100059301)
                    ·
                      refine ⟨811031397202276518761119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4325500785078808100059301 811031397202276518761119)
                      ·
                        rfl

theorem cell23_1579478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_1579478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1579478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1579478 prefixEnd_1579478 := by exact prefixLift 1579478
  have htrace : WordTrace (prefixWord ++ tailWord_1579478) baseStart_1579478 baseEnd_1579478 := by
    simpa [prefixWord, tailWord_1579478, baseEnd_1579478] using wordTrace_append hprefix tailTrace_1579478
  have hstable : (prefixWord ++ tailWord_1579478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579478).length < 2 ^ (prefixWord ++ tailWord_1579478).sum := by decide
  have hdescent : baseEnd_1579478 < baseStart_1579478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579481 : List Nat := [1, 2, 1, 2, 4, 1, 1, 3, 3, 2, 3]
def baseStart_1579481 : Nat := 118140960795 + 1579481 * 2 ^ 59
def prefixEnd_1579481 : Nat := 4983230072969 + 3 ^ 40 * 1579481 * 2
def baseEnd_1579481 : Nat := 811032937644240007023605

theorem tailTrace_1579481 : CollatzResearch.WordTrace tailWord_1579481 prefixEnd_1579481 811032937644240007023605 := by
  unfold tailWord_1579481
  simp only [CollatzResearch.WordTrace]
  refine ⟨57608404790817565723706297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38405603193878377149137531 57608404790817565723706297)
  ·
    refine ⟨43206303593113174292779723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57608404790817565723706297 43206303593113174292779723)
    ·
      refine ⟨64809455389669761439169585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43206303593113174292779723 64809455389669761439169585)
      ·
        refine ⟨48607091542252321079377189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64809455389669761439169585 48607091542252321079377189)
        ·
          refine ⟨9113829664172310202383223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48607091542252321079377189 9113829664172310202383223)
          ·
            refine ⟨13670744496258465303574835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9113829664172310202383223 13670744496258465303574835)
            ·
              refine ⟨20506116744387697955362253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13670744496258465303574835 20506116744387697955362253)
              ·
                refine ⟨7689793779145386733260845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20506116744387697955362253 7689793779145386733260845)
                ·
                  refine ⟨2883672667179520024972817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7689793779145386733260845 2883672667179520024972817)
                  ·
                    refine ⟨2162754500384640018729613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2883672667179520024972817 2162754500384640018729613)
                    ·
                      refine ⟨811032937644240007023605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2162754500384640018729613 811032937644240007023605)
                      ·
                        rfl

theorem cell23_1579481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 2, 3].length) (baseStart_1579481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1579481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1579481 prefixEnd_1579481 := by exact prefixLift 1579481
  have htrace : WordTrace (prefixWord ++ tailWord_1579481) baseStart_1579481 baseEnd_1579481 := by
    simpa [prefixWord, tailWord_1579481, baseEnd_1579481] using wordTrace_append hprefix tailTrace_1579481
  have hstable : (prefixWord ++ tailWord_1579481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579481).length < 2 ^ (prefixWord ++ tailWord_1579481).sum := by decide
  have hdescent : baseEnd_1579481 < baseStart_1579481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579501 : List Nat := [1, 5, 1, 3, 1, 2, 10]
def baseStart_1579501 : Nat := 118140960795 + 1579501 * 2 ^ 59
def prefixEnd_1579501 : Nat := 4983230072969 + 3 ^ 40 * 1579501 * 2
def baseEnd_1579501 : Nat := 10012879101942344799673

theorem tailTrace_1579501 : CollatzResearch.WordTrace tailWord_1579501 prefixEnd_1579501 10012879101942344799673 := by
  unfold tailWord_1579501
  simp only [CollatzResearch.WordTrace]
  refine ⟨57609134250745109139434357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38406089500496739426289571 57609134250745109139434357)
  ·
    refine ⟨5400856336007353981821971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57609134250745109139434357 5400856336007353981821971)
    ·
      refine ⟨8101284504011030972732957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5400856336007353981821971 8101284504011030972732957)
      ·
        refine ⟨3037981689004136614774859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8101284504011030972732957 3037981689004136614774859)
        ·
          refine ⟨4556972533506204922162289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3037981689004136614774859 4556972533506204922162289)
          ·
            refine ⟨3417729400129653691621717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4556972533506204922162289 3417729400129653691621717)
            ·
              refine ⟨10012879101942344799673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3417729400129653691621717 10012879101942344799673)
              ·
                rfl

theorem cell23_1579501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 10].length) (baseStart_1579501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1579501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1579501 prefixEnd_1579501 := by exact prefixLift 1579501
  have htrace : WordTrace (prefixWord ++ tailWord_1579501) baseStart_1579501 baseEnd_1579501 := by
    simpa [prefixWord, tailWord_1579501, baseEnd_1579501] using wordTrace_append hprefix tailTrace_1579501
  have hstable : (prefixWord ++ tailWord_1579501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579501).length < 2 ^ (prefixWord ++ tailWord_1579501).sum := by decide
  have hdescent : baseEnd_1579501 < baseStart_1579501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579514 : List Nat := [3, 1, 1, 1, 1, 2, 2, 3, 2, 7]
def baseStart_1579514 : Nat := 118140960795 + 1579514 * 2 ^ 59
def prefixEnd_1579514 : Nat := 4983230072969 + 3 ^ 40 * 1579514 * 2
def baseEnd_1579514 : Nat := 270349960835279459303651

theorem tailTrace_1579514 : CollatzResearch.WordTrace tailWord_1579514 prefixEnd_1579514 270349960835279459303651 := by
  unfold tailWord_1579514
  simp only [CollatzResearch.WordTrace]
  refine ⟨14402402099924503089914399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38406405599798674906438397 14402402099924503089914399)
  ·
    refine ⟨21603603149886754634871599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14402402099924503089914399 21603603149886754634871599)
    ·
      refine ⟨32405404724830131952307399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21603603149886754634871599 32405404724830131952307399)
      ·
        refine ⟨48608107087245197928461099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32405404724830131952307399 48608107087245197928461099)
        ·
          refine ⟨72912160630867796892691649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48608107087245197928461099 72912160630867796892691649)
          ·
            refine ⟨54684120473150847669518737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72912160630867796892691649 54684120473150847669518737)
            ·
              refine ⟨41013090354863135752139053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54684120473150847669518737 41013090354863135752139053)
              ·
                refine ⟨15379908883073675907052145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41013090354863135752139053 15379908883073675907052145)
                ·
                  refine ⟨11534931662305256930289109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15379908883073675907052145 11534931662305256930289109)
                  ·
                    refine ⟨270349960835279459303651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11534931662305256930289109 270349960835279459303651)
                    ·
                      rfl

theorem cell23_1579514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 2, 7].length) (baseStart_1579514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1579514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1579514 prefixEnd_1579514 := by exact prefixLift 1579514
  have htrace : WordTrace (prefixWord ++ tailWord_1579514) baseStart_1579514 baseEnd_1579514 := by
    simpa [prefixWord, tailWord_1579514, baseEnd_1579514] using wordTrace_append hprefix tailTrace_1579514
  have hstable : (prefixWord ++ tailWord_1579514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579514).length < 2 ^ (prefixWord ++ tailWord_1579514).sum := by decide
  have hdescent : baseEnd_1579514 < baseStart_1579514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579522 : List Nat := [3, 4, 1, 2, 3, 1, 1, 1, 1, 6]
def baseStart_1579522 : Nat := 118140960795 + 1579522 * 2 ^ 59
def prefixEnd_1579522 : Nat := 4983230072969 + 3 ^ 40 * 1579522 * 2
def baseEnd_1579522 : Nat := 270351330117024782203639

theorem tailTrace_1579522 : CollatzResearch.WordTrace tailWord_1579522 prefixEnd_1579522 270351330117024782203639 := by
  unfold tailWord_1579522
  simp only [CollatzResearch.WordTrace]
  refine ⟨14402475045917257431487205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38406600122446019817299213 14402475045917257431487205)
  ·
    refine ⟨2700464071109485768403851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14402475045917257431487205 2700464071109485768403851)
    ·
      refine ⟨4050696106664228652605777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2700464071109485768403851 4050696106664228652605777)
      ·
        refine ⟨3038022079998171489454333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4050696106664228652605777 3038022079998171489454333)
        ·
          refine ⟨1139258279999314308545375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3038022079998171489454333 1139258279999314308545375)
          ·
            refine ⟨1708887419998971462818063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1139258279999314308545375 1708887419998971462818063)
            ·
              refine ⟨2563331129998457194227095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1708887419998971462818063 2563331129998457194227095)
              ·
                refine ⟨3844996694997685791340643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2563331129998457194227095 3844996694997685791340643)
                ·
                  refine ⟨5767495042496528687010965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3844996694997685791340643 5767495042496528687010965)
                  ·
                    refine ⟨270351330117024782203639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5767495042496528687010965 270351330117024782203639)
                    ·
                      rfl

theorem cell23_1579522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_1579522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1579522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1579522 prefixEnd_1579522 := by exact prefixLift 1579522
  have htrace : WordTrace (prefixWord ++ tailWord_1579522) baseStart_1579522 baseEnd_1579522 := by
    simpa [prefixWord, tailWord_1579522, baseEnd_1579522] using wordTrace_append hprefix tailTrace_1579522
  have hstable : (prefixWord ++ tailWord_1579522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579522).length < 2 ^ (prefixWord ++ tailWord_1579522).sum := by decide
  have hdescent : baseEnd_1579522 < baseStart_1579522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579555 : List Nat := [1, 1, 1, 4, 4, 1, 2, 3, 1, 3, 2]
def baseStart_1579555 : Nat := 118140960795 + 1579555 * 2 ^ 59
def prefixEnd_1579555 : Nat := 4983230072969 + 3 ^ 40 * 1579555 * 2
def baseEnd_1579555 : Nat := 811070935212672717498265

theorem tailTrace_1579555 : CollatzResearch.WordTrace tailWord_1579555 prefixEnd_1579555 811070935212672717498265 := by
  unfold tailWord_1579555
  simp only [CollatzResearch.WordTrace]
  refine ⟨57611103792549476361900119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38407402528366317574600079 57611103792549476361900119)
  ·
    refine ⟨86416655688824214542850179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57611103792549476361900119 86416655688824214542850179)
    ·
      refine ⟨129624983533236321814275269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86416655688824214542850179 129624983533236321814275269)
      ·
        refine ⟨24304684412481810340176613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129624983533236321814275269 24304684412481810340176613)
        ·
          refine ⟨4557128327340339438783115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24304684412481810340176613 4557128327340339438783115)
          ·
            refine ⟨6835692491010509158174673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4557128327340339438783115 6835692491010509158174673)
            ·
              refine ⟨5126769368257881868631005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6835692491010509158174673 5126769368257881868631005)
              ·
                refine ⟨1922538513096705700736627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5126769368257881868631005 1922538513096705700736627)
                ·
                  refine ⟨2883807769645058551104941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1922538513096705700736627 2883807769645058551104941)
                  ·
                    refine ⟨1081427913616896956664353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2883807769645058551104941 1081427913616896956664353)
                    ·
                      refine ⟨811070935212672717498265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1081427913616896956664353 811070935212672717498265)
                      ·
                        rfl

theorem cell23_1579555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 3, 2].length) (baseStart_1579555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1579555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1579555 prefixEnd_1579555 := by exact prefixLift 1579555
  have htrace : WordTrace (prefixWord ++ tailWord_1579555) baseStart_1579555 baseEnd_1579555 := by
    simpa [prefixWord, tailWord_1579555, baseEnd_1579555] using wordTrace_append hprefix tailTrace_1579555
  have hstable : (prefixWord ++ tailWord_1579555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579555).length < 2 ^ (prefixWord ++ tailWord_1579555).sum := by decide
  have hdescent : baseEnd_1579555 < baseStart_1579555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579571 : List Nat := [1, 1, 1, 2, 4, 2, 2, 1, 2, 4, 3]
def baseStart_1579571 : Nat := 118140960795 + 1579571 * 2 ^ 59
def prefixEnd_1579571 : Nat := 4983230072969 + 3 ^ 40 * 1579571 * 2
def baseEnd_1579571 : Nat := 811079150903144654898191

theorem tailTrace_1579571 : CollatzResearch.WordTrace tailWord_1579571 prefixEnd_1579571 811079150903144654898191 := by
  unfold tailWord_1579571
  simp only [CollatzResearch.WordTrace]
  refine ⟨57611687360491511094482567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38407791573661007396321711 57611687360491511094482567)
  ·
    refine ⟨86417531040737266641723851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57611687360491511094482567 86417531040737266641723851)
    ·
      refine ⟨129626296561105899962585777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86417531040737266641723851 129626296561105899962585777)
      ·
        refine ⟨97219722420829424971939333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129626296561105899962585777 97219722420829424971939333)
        ·
          refine ⟨18228697953905517182238625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97219722420829424971939333 18228697953905517182238625)
          ·
            refine ⟨13671523465429137886678969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18228697953905517182238625 13671523465429137886678969)
            ·
              refine ⟨10253642599071853415009227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13671523465429137886678969 10253642599071853415009227)
              ·
                refine ⟨15380463898607780122513841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10253642599071853415009227 15380463898607780122513841)
                ·
                  refine ⟨11535347923955835091885381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15380463898607780122513841 11535347923955835091885381)
                  ·
                    refine ⟨2162877735741719079728509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11535347923955835091885381 2162877735741719079728509)
                    ·
                      refine ⟨811079150903144654898191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2162877735741719079728509 811079150903144654898191)
                      ·
                        rfl

theorem cell23_1579571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 4, 3].length) (baseStart_1579571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1579571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1579571 prefixEnd_1579571 := by exact prefixLift 1579571
  have htrace : WordTrace (prefixWord ++ tailWord_1579571) baseStart_1579571 baseEnd_1579571 := by
    simpa [prefixWord, tailWord_1579571, baseEnd_1579571] using wordTrace_append hprefix tailTrace_1579571
  have hstable : (prefixWord ++ tailWord_1579571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579571).length < 2 ^ (prefixWord ++ tailWord_1579571).sum := by decide
  have hdescent : baseEnd_1579571 < baseStart_1579571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
