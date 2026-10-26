import V185TrunkScan23Chunk0432

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2560760 : List Nat := [2, 1, 2, 1, 1, 2, 5, 2, 2, 1, 4]
def baseStart_2560760 : Nat := 118140960795 + 2560760 * 2 ^ 59
def prefixEnd_2560760 : Nat := 4983230072969 + 3 ^ 40 * 2560760 * 2
def baseEnd_2560760 : Nat := 1314900720807506248423285

theorem tailTrace_2560760 : CollatzResearch.WordTrace tailWord_2560760 prefixEnd_2560760 1314900720807506248423285 := by
  unfold tailWord_2560760
  simp only [CollatzResearch.WordTrace]
  refine ⟨46699295101405668917227867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62265726801874225222970489 46699295101405668917227867)
  ·
    refine ⟨70048942652108503375841801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46699295101405668917227867 70048942652108503375841801)
    ·
      refine ⟨52536706989081377531881351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70048942652108503375841801 52536706989081377531881351)
      ·
        refine ⟨78805060483622066297822027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52536706989081377531881351 78805060483622066297822027)
        ·
          refine ⟨118207590725433099446733041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78805060483622066297822027 118207590725433099446733041)
          ·
            refine ⟨88655693044074824585049781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118207590725433099446733041 88655693044074824585049781)
            ·
              refine ⟨8311471222882014804848417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 88655693044074824585049781 8311471222882014804848417)
              ·
                refine ⟨6233603417161511103636313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8311471222882014804848417 6233603417161511103636313)
                ·
                  refine ⟨4675202562871133327727235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6233603417161511103636313 4675202562871133327727235)
                  ·
                    refine ⟨7012803844306699991590853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4675202562871133327727235 7012803844306699991590853)
                    ·
                      refine ⟨1314900720807506248423285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7012803844306699991590853 1314900720807506248423285)
                      ·
                        rfl

theorem cell23_2560760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 2, 1, 4].length) (baseStart_2560760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560760 prefixEnd_2560760 := by exact prefixLift 2560760
  have htrace : WordTrace (prefixWord ++ tailWord_2560760) baseStart_2560760 baseEnd_2560760 := by
    simpa [prefixWord, tailWord_2560760, baseEnd_2560760] using wordTrace_append hprefix tailTrace_2560760
  have hstable : (prefixWord ++ tailWord_2560760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560760).length < 2 ^ (prefixWord ++ tailWord_2560760).sum := by decide
  have hdescent : baseEnd_2560760 < baseStart_2560760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560773 : List Nat := [1, 3, 1, 1, 2, 1, 1, 4, 2, 1, 6]
def baseStart_2560773 : Nat := 118140960795 + 2560773 * 2 ^ 59
def prefixEnd_2560773 : Nat := 4983230072969 + 3 ^ 40 * 2560773 * 2
def baseEnd_2560773 : Nat := 1314907396056014697560725

theorem tailTrace_2560773 : CollatzResearch.WordTrace tailWord_2560773 prefixEnd_2560773 1314907396056014697560725 := by
  unfold tailWord_2560773
  simp only [CollatzResearch.WordTrace]
  refine ⟨93399064351764241054678973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62266042901176160703119315 93399064351764241054678973)
  ·
    refine ⟨35024649131911590395504615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93399064351764241054678973 35024649131911590395504615)
    ·
      refine ⟨52536973697867385593256923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35024649131911590395504615 52536973697867385593256923)
      ·
        refine ⟨78805460546801078389885385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52536973697867385593256923 78805460546801078389885385)
        ·
          refine ⟨59104095410100808792414039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78805460546801078389885385 59104095410100808792414039)
          ·
            refine ⟨88656143115151213188621059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59104095410100808792414039 88656143115151213188621059)
            ·
              refine ⟨132984214672726819782931589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88656143115151213188621059 132984214672726819782931589)
              ·
                refine ⟨24934540251136278709299673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 132984214672726819782931589 24934540251136278709299673)
                ·
                  refine ⟨18700905188352209031974755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24934540251136278709299673 18700905188352209031974755)
                  ·
                    refine ⟨28051357782528313547962133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18700905188352209031974755 28051357782528313547962133)
                    ·
                      refine ⟨1314907396056014697560725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28051357782528313547962133 1314907396056014697560725)
                      ·
                        rfl

theorem cell23_2560773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_2560773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560773 prefixEnd_2560773 := by exact prefixLift 2560773
  have htrace : WordTrace (prefixWord ++ tailWord_2560773) baseStart_2560773 baseEnd_2560773 := by
    simpa [prefixWord, tailWord_2560773, baseEnd_2560773] using wordTrace_append hprefix tailTrace_2560773
  have hstable : (prefixWord ++ tailWord_2560773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560773).length < 2 ^ (prefixWord ++ tailWord_2560773).sum := by decide
  have hdescent : baseEnd_2560773 < baseStart_2560773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560780 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 6, 2, 3]
def baseStart_2560780 : Nat := 118140960795 + 2560780 * 2 ^ 59
def prefixEnd_2560780 : Nat := 4983230072969 + 3 ^ 40 * 2560780 * 2
def baseEnd_2560780 : Nat := 1314910990420596170173193

theorem tailTrace_2560780 : CollatzResearch.WordTrace tailWord_2560780 prefixEnd_2560780 1314910990420596170173193 := by
  unfold tailWord_2560780
  simp only [CollatzResearch.WordTrace]
  refine ⟨46699659831369440625091897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62266213108492587500122529 46699659831369440625091897)
  ·
    refine ⟨35024744873527080468818923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46699659831369440625091897 35024744873527080468818923)
    ·
      refine ⟨52537117310290620703228385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35024744873527080468818923 52537117310290620703228385)
      ·
        refine ⟨39402837982717965527421289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52537117310290620703228385 39402837982717965527421289)
        ·
          refine ⟨29552128487038474145565967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39402837982717965527421289 29552128487038474145565967)
          ·
            refine ⟨44328192730557711218348951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29552128487038474145565967 44328192730557711218348951)
            ·
              refine ⟨66492289095836566827523427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44328192730557711218348951 66492289095836566827523427)
              ·
                refine ⟨99738433643754850241285141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66492289095836566827523427 99738433643754850241285141)
                ·
                  refine ⟨4675239077051008605060241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 99738433643754850241285141 4675239077051008605060241)
                  ·
                    refine ⟨3506429307788256453795181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4675239077051008605060241 3506429307788256453795181)
                    ·
                      refine ⟨1314910990420596170173193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3506429307788256453795181 1314910990420596170173193)
                      ·
                        rfl

theorem cell23_2560780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_2560780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560780 prefixEnd_2560780 := by exact prefixLift 2560780
  have htrace : WordTrace (prefixWord ++ tailWord_2560780) baseStart_2560780 baseEnd_2560780 := by
    simpa [prefixWord, tailWord_2560780, baseEnd_2560780] using wordTrace_append hprefix tailTrace_2560780
  have hstable : (prefixWord ++ tailWord_2560780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560780).length < 2 ^ (prefixWord ++ tailWord_2560780).sum := by decide
  have hdescent : baseEnd_2560780 < baseStart_2560780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560803 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 8]
def baseStart_2560803 : Nat := 118140960795 + 2560803 * 2 ^ 59
def prefixEnd_2560803 : Nat := 4983230072969 + 3 ^ 40 * 2560803 * 2
def baseEnd_2560803 : Nat := 1314922800475649580185587

theorem tailTrace_2560803 : CollatzResearch.WordTrace tailWord_2560803 prefixEnd_2560803 1314922800475649580185587 := by
  unfold tailWord_2560803
  simp only [CollatzResearch.WordTrace]
  refine ⟨93400158541655556178271063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62266772361103704118847375 93400158541655556178271063)
  ·
    refine ⟨140100237812483334267406595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93400158541655556178271063 140100237812483334267406595)
    ·
      refine ⟨210150356718725001401109893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140100237812483334267406595 210150356718725001401109893)
      ·
        refine ⟨39403191884760937762708105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 210150356718725001401109893 39403191884760937762708105)
        ·
          refine ⟨29552393913570703322031079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39403191884760937762708105 29552393913570703322031079)
          ·
            refine ⟨44328590870356054983046619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29552393913570703322031079 44328590870356054983046619)
            ·
              refine ⟨66492886305534082474569929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44328590870356054983046619 66492886305534082474569929)
              ·
                refine ⟨49869664729150561855927447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66492886305534082474569929 49869664729150561855927447)
                ·
                  refine ⟨74804497093725842783891171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49869664729150561855927447 74804497093725842783891171)
                  ·
                    refine ⟨112206745640588764175836757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 74804497093725842783891171 112206745640588764175836757)
                    ·
                      refine ⟨1314922800475649580185587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 112206745640588764175836757 1314922800475649580185587)
                      ·
                        rfl

theorem cell23_2560803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_2560803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560803 prefixEnd_2560803 := by exact prefixLift 2560803
  have htrace : WordTrace (prefixWord ++ tailWord_2560803) baseStart_2560803 baseEnd_2560803 := by
    simpa [prefixWord, tailWord_2560803, baseEnd_2560803] using wordTrace_append hprefix tailTrace_2560803
  have hstable : (prefixWord ++ tailWord_2560803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560803).length < 2 ^ (prefixWord ++ tailWord_2560803).sum := by decide
  have hdescent : baseEnd_2560803 < baseStart_2560803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560814 : List Nat := [4, 1, 3, 2, 1, 1, 2, 2, 2, 2, 3]
def baseStart_2560814 : Nat := 118140960795 + 2560814 * 2 ^ 59
def prefixEnd_2560814 : Nat := 4983230072969 + 3 ^ 40 * 2560814 * 2
def baseEnd_2560814 : Nat := 1314928448762849037148037

theorem tailTrace_2560814 : CollatzResearch.WordTrace tailWord_2560814 prefixEnd_2560814 1314928448762849037148037 := by
  unfold tailWord_2560814
  simp only [CollatzResearch.WordTrace]
  refine ⟨11675069968076963132115187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62267039829743803371280997 11675069968076963132115187)
  ·
    refine ⟨17512604952115444698172781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11675069968076963132115187 17512604952115444698172781)
    ·
      refine ⟨6567226857043291761814793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17512604952115444698172781 6567226857043291761814793)
      ·
        refine ⟨4925420142782468821361095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6567226857043291761814793 4925420142782468821361095)
        ·
          refine ⟨7388130214173703232041643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4925420142782468821361095 7388130214173703232041643)
          ·
            refine ⟨11082195321260554848062465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7388130214173703232041643 11082195321260554848062465)
            ·
              refine ⟨8311646490945416136046849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11082195321260554848062465 8311646490945416136046849)
              ·
                refine ⟨6233734868209062102035137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8311646490945416136046849 6233734868209062102035137)
                ·
                  refine ⟨4675301151156796576526353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6233734868209062102035137 4675301151156796576526353)
                  ·
                    refine ⟨3506475863367597432394765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4675301151156796576526353 3506475863367597432394765)
                    ·
                      refine ⟨1314928448762849037148037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3506475863367597432394765 1314928448762849037148037)
                      ·
                        rfl

theorem cell23_2560814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_2560814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560814 prefixEnd_2560814 := by exact prefixLift 2560814
  have htrace : WordTrace (prefixWord ++ tailWord_2560814) baseStart_2560814 baseEnd_2560814 := by
    simpa [prefixWord, tailWord_2560814, baseEnd_2560814] using wordTrace_append hprefix tailTrace_2560814
  have hstable : (prefixWord ++ tailWord_2560814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560814).length < 2 ^ (prefixWord ++ tailWord_2560814).sum := by decide
  have hdescent : baseEnd_2560814 < baseStart_2560814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560821 : List Nat := [1, 3, 3, 1, 3, 1, 4, 2, 1, 4]
def baseStart_2560821 : Nat := 118140960795 + 2560821 * 2 ^ 59
def prefixEnd_2560821 : Nat := 4983230072969 + 3 ^ 40 * 2560821 * 2
def baseEnd_2560821 : Nat := 438310681042476836586835

theorem tailTrace_2560821 : CollatzResearch.WordTrace tailWord_2560821 prefixEnd_2560821 438310681042476836586835 := by
  unfold tailWord_2560821
  simp only [CollatzResearch.WordTrace]
  refine ⟨93400815055590345252426317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62267210037060230168284211 93400815055590345252426317)
  ·
    refine ⟨35025305645846379469659869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93400815055590345252426317 35025305645846379469659869)
    ·
      refine ⟨13134489617192392301122451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35025305645846379469659869 13134489617192392301122451)
      ·
        refine ⟨19701734425788588451683677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13134489617192392301122451 19701734425788588451683677)
        ·
          refine ⟨7388150409670720669381379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19701734425788588451683677 7388150409670720669381379)
          ·
            refine ⟨11082225614506081004072069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7388150409670720669381379 11082225614506081004072069)
            ·
              refine ⟨2077917302719890188263513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11082225614506081004072069 2077917302719890188263513)
              ·
                refine ⟨1558437977039917641197635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2077917302719890188263513 1558437977039917641197635)
                ·
                  refine ⟨2337656965559876461796453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1558437977039917641197635 2337656965559876461796453)
                  ·
                    refine ⟨438310681042476836586835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2337656965559876461796453 438310681042476836586835)
                    ·
                      rfl

theorem cell23_2560821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_2560821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560821 prefixEnd_2560821 := by exact prefixLift 2560821
  have htrace : WordTrace (prefixWord ++ tailWord_2560821) baseStart_2560821 baseEnd_2560821 := by
    simpa [prefixWord, tailWord_2560821, baseEnd_2560821] using wordTrace_append hprefix tailTrace_2560821
  have hstable : (prefixWord ++ tailWord_2560821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560821).length < 2 ^ (prefixWord ++ tailWord_2560821).sum := by decide
  have hdescent : baseEnd_2560821 < baseStart_2560821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560844 : List Nat := [2, 2, 1, 3, 3, 2, 1, 2, 3, 1, 3]
def baseStart_2560844 : Nat := 118140960795 + 2560844 * 2 ^ 59
def prefixEnd_2560844 : Nat := 4983230072969 + 3 ^ 40 * 2560844 * 2
def baseEnd_2560844 : Nat := 1314943853182483919772899

theorem tailTrace_2560844 : CollatzResearch.WordTrace tailWord_2560844 prefixEnd_2560844 1314943853182483919772899 := by
  unfold tailWord_2560844
  simp only [CollatzResearch.WordTrace]
  refine ⟨46700826967253510090256793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62267769289671346787009057 46700826967253510090256793)
  ·
    refine ⟨35025620225440132567692595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46700826967253510090256793 35025620225440132567692595)
    ·
      refine ⟨52538430338160198851538893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35025620225440132567692595 52538430338160198851538893)
      ·
        refine ⟨19701911376810074569327085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52538430338160198851538893 19701911376810074569327085)
        ·
          refine ⟨7388216766303777963497657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19701911376810074569327085 7388216766303777963497657)
          ·
            refine ⟨5541162574727833472623243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7388216766303777963497657 5541162574727833472623243)
            ·
              refine ⟨8311743862091750208934865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5541162574727833472623243 8311743862091750208934865)
              ·
                refine ⟨6233807896568812656701149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8311743862091750208934865 6233807896568812656701149)
                ·
                  refine ⟨2337677961213304746262931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6233807896568812656701149 2337677961213304746262931)
                  ·
                    refine ⟨3506516941819957119394397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2337677961213304746262931 3506516941819957119394397)
                    ·
                      refine ⟨1314943853182483919772899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3506516941819957119394397 1314943853182483919772899)
                      ·
                        rfl

theorem cell23_2560844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_2560844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560844 prefixEnd_2560844 := by exact prefixLift 2560844
  have htrace : WordTrace (prefixWord ++ tailWord_2560844) baseStart_2560844 baseEnd_2560844 := by
    simpa [prefixWord, tailWord_2560844, baseEnd_2560844] using wordTrace_append hprefix tailTrace_2560844
  have hstable : (prefixWord ++ tailWord_2560844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560844).length < 2 ^ (prefixWord ++ tailWord_2560844).sum := by decide
  have hdescent : baseEnd_2560844 < baseStart_2560844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560880 : List Nat := [2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 4]
def baseStart_2560880 : Nat := 118140960795 + 2560880 * 2 ^ 59
def prefixEnd_2560880 : Nat := 4983230072969 + 3 ^ 40 * 2560880 * 2
def baseEnd_2560880 : Nat := 1314962338486045778922733

theorem tailTrace_2560880 : CollatzResearch.WordTrace tailWord_2560880 prefixEnd_2560880 1314962338486045778922733 := by
  unfold tailWord_2560880
  simp only [CollatzResearch.WordTrace]
  refine ⟨46701483481188299164412047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62268644641584398885882729 46701483481188299164412047)
  ·
    refine ⟨70052225221782448746618071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46701483481188299164412047 70052225221782448746618071)
    ·
      refine ⟨105078337832673673119927107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70052225221782448746618071 105078337832673673119927107)
      ·
        refine ⟨157617506749010509679890661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105078337832673673119927107 157617506749010509679890661)
        ·
          refine ⟨29553282515439470564979499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 157617506749010509679890661 29553282515439470564979499)
          ·
            refine ⟨44329923773159205847469249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29553282515439470564979499 44329923773159205847469249)
            ·
              refine ⟨33247442829869404385601937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44329923773159205847469249 33247442829869404385601937)
              ·
                refine ⟨24935582122402053289201453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33247442829869404385601937 24935582122402053289201453)
                ·
                  refine ⟨9350843295900769983450545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24935582122402053289201453 9350843295900769983450545)
                  ·
                    refine ⟨7013132471925577487587909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9350843295900769983450545 7013132471925577487587909)
                    ·
                      refine ⟨1314962338486045778922733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7013132471925577487587909 1314962338486045778922733)
                      ·
                        rfl

theorem cell23_2560880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 4].length) (baseStart_2560880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560880 prefixEnd_2560880 := by exact prefixLift 2560880
  have htrace : WordTrace (prefixWord ++ tailWord_2560880) baseStart_2560880 baseEnd_2560880 := by
    simpa [prefixWord, tailWord_2560880, baseEnd_2560880] using wordTrace_append hprefix tailTrace_2560880
  have hstable : (prefixWord ++ tailWord_2560880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560880).length < 2 ^ (prefixWord ++ tailWord_2560880).sum := by decide
  have hdescent : baseEnd_2560880 < baseStart_2560880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560898 : List Nat := [3, 4, 2, 2, 1, 1, 2, 2, 1, 5]
def baseStart_2560898 : Nat := 118140960795 + 2560898 * 2 ^ 59
def prefixEnd_2560898 : Nat := 4983230072969 + 3 ^ 40 * 2560898 * 2
def baseEnd_2560898 : Nat := 438323860379275569499217

theorem tailTrace_2560898 : CollatzResearch.WordTrace tailWord_2560898 prefixEnd_2560898 438323860379275569499217 := by
  unfold tailWord_2560898
  simp only [CollatzResearch.WordTrace]
  refine ⟨23350905869077846850744837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62269082317540924935319565 23350905869077846850744837)
  ·
    refine ⟨4378294850452096284514657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23350905869077846850744837 4378294850452096284514657)
    ·
      refine ⟨3283721137839072213385993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4378294850452096284514657 3283721137839072213385993)
      ·
        refine ⟨2462790853379304160039495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3283721137839072213385993 2462790853379304160039495)
        ·
          refine ⟨3694186280068956240059243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2462790853379304160039495 3694186280068956240059243)
          ·
            refine ⟨5541279420103434360088865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3694186280068956240059243 5541279420103434360088865)
            ·
              refine ⟨4155959565077575770066649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5541279420103434360088865 4155959565077575770066649)
              ·
                refine ⟨3116969673808181827549987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4155959565077575770066649 3116969673808181827549987)
                ·
                  refine ⟨4675454510712272741324981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3116969673808181827549987 4675454510712272741324981)
                  ·
                    refine ⟨438323860379275569499217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4675454510712272741324981 438323860379275569499217)
                    ·
                      rfl

theorem cell23_2560898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_2560898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560898 prefixEnd_2560898 := by exact prefixLift 2560898
  have htrace : WordTrace (prefixWord ++ tailWord_2560898) baseStart_2560898 baseEnd_2560898 := by
    simpa [prefixWord, tailWord_2560898, baseEnd_2560898] using wordTrace_append hprefix tailTrace_2560898
  have hstable : (prefixWord ++ tailWord_2560898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560898).length < 2 ^ (prefixWord ++ tailWord_2560898).sum := by decide
  have hdescent : baseEnd_2560898 < baseStart_2560898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560904 : List Nat := [2, 1, 3, 3, 2, 1, 1, 4, 1, 2, 3]
def baseStart_2560904 : Nat := 118140960795 + 2560904 * 2 ^ 59
def prefixEnd_2560904 : Nat := 4983230072969 + 3 ^ 40 * 2560904 * 2
def baseEnd_2560904 : Nat := 1314974662021753685022623

theorem tailTrace_2560904 : CollatzResearch.WordTrace tailWord_2560904 prefixEnd_2560904 1314974662021753685022623 := by
  unfold tailWord_2560904
  simp only [CollatzResearch.WordTrace]
  refine ⟨46701921157144825213848883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62269228209526433618465177 46701921157144825213848883)
  ·
    refine ⟨70052881735717237820773325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46701921157144825213848883 70052881735717237820773325)
    ·
      refine ⟨26269830650893964182789997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70052881735717237820773325 26269830650893964182789997)
      ·
        refine ⟨9851186494085236568546249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26269830650893964182789997 9851186494085236568546249)
        ·
          refine ⟨7388389870563927426409687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9851186494085236568546249 7388389870563927426409687)
          ·
            refine ⟨11082584805845891139614531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7388389870563927426409687 11082584805845891139614531)
            ·
              refine ⟨16623877208768836709421797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11082584805845891139614531 16623877208768836709421797)
              ·
                refine ⟨3116976976644156883016587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16623877208768836709421797 3116976976644156883016587)
                ·
                  refine ⟨4675465464966235324524881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3116976976644156883016587 4675465464966235324524881)
                  ·
                    refine ⟨3506599098724676493393661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4675465464966235324524881 3506599098724676493393661)
                    ·
                      refine ⟨1314974662021753685022623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3506599098724676493393661 1314974662021753685022623)
                      ·
                        rfl

theorem cell23_2560904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_2560904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560904 prefixEnd_2560904 := by exact prefixLift 2560904
  have htrace : WordTrace (prefixWord ++ tailWord_2560904) baseStart_2560904 baseEnd_2560904 := by
    simpa [prefixWord, tailWord_2560904, baseEnd_2560904] using wordTrace_append hprefix tailTrace_2560904
  have hstable : (prefixWord ++ tailWord_2560904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560904).length < 2 ^ (prefixWord ++ tailWord_2560904).sum := by decide
  have hdescent : baseEnd_2560904 < baseStart_2560904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560918 : List Nat := [5, 3, 1, 1, 1, 1, 2, 3, 1, 1, 4]
def baseStart_2560918 : Nat := 118140960795 + 2560918 * 2 ^ 59
def prefixEnd_2560918 : Nat := 4983230072969 + 3 ^ 40 * 2560918 * 2
def baseEnd_2560918 : Nat := 1314981850750916630247559

theorem tailTrace_2560918 : CollatzResearch.WordTrace tailWord_2560918 prefixEnd_2560918 1314981850750916630247559 := by
  unfold tailWord_2560918
  simp only [CollatzResearch.WordTrace]
  refine ⟨5837772058514933176169213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62269568624159287212471605 5837772058514933176169213)
  ·
    refine ⟨2189164521943099941063455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5837772058514933176169213 2189164521943099941063455)
    ·
      refine ⟨3283746782914649911595183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2189164521943099941063455 3283746782914649911595183)
      ·
        refine ⟨4925620174371974867392775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3283746782914649911595183 4925620174371974867392775)
        ·
          refine ⟨7388430261557962301089163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4925620174371974867392775 7388430261557962301089163)
          ·
            refine ⟨11082645392336943451633745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7388430261557962301089163 11082645392336943451633745)
            ·
              refine ⟨8311984044252707588725309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11082645392336943451633745 8311984044252707588725309)
              ·
                refine ⟨3116994016594765345771991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8311984044252707588725309 3116994016594765345771991)
                ·
                  refine ⟨4675491024892148018657987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3116994016594765345771991 4675491024892148018657987)
                  ·
                    refine ⟨7013236537338222027986981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4675491024892148018657987 7013236537338222027986981)
                    ·
                      refine ⟨1314981850750916630247559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7013236537338222027986981 1314981850750916630247559)
                      ·
                        rfl

theorem cell23_2560918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_2560918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560918 prefixEnd_2560918 := by exact prefixLift 2560918
  have htrace : WordTrace (prefixWord ++ tailWord_2560918) baseStart_2560918 baseEnd_2560918 := by
    simpa [prefixWord, tailWord_2560918, baseEnd_2560918] using wordTrace_append hprefix tailTrace_2560918
  have hstable : (prefixWord ++ tailWord_2560918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560918).length < 2 ^ (prefixWord ++ tailWord_2560918).sum := by decide
  have hdescent : baseEnd_2560918 < baseStart_2560918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560924 : List Nat := [2, 2, 3, 3, 3, 1, 9]
def baseStart_2560924 : Nat := 118140960795 + 2560924 * 2 ^ 59
def prefixEnd_2560924 : Nat := 4983230072969 + 3 ^ 40 * 2560924 * 2
def baseEnd_2560924 : Nat := 16234381872035106256451

theorem tailTrace_2560924 : CollatzResearch.WordTrace tailWord_2560924 prefixEnd_2560924 16234381872035106256451 := by
  unfold tailWord_2560924
  simp only [CollatzResearch.WordTrace]
  refine ⟨46702285887108596921712913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62269714516144795895617217 46702285887108596921712913)
  ·
    refine ⟨35026714415331447691284685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46702285887108596921712913 35026714415331447691284685)
    ·
      refine ⟨13135017905749292884231757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35026714415331447691284685 13135017905749292884231757)
      ·
        refine ⟨4925631714655984831586909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13135017905749292884231757 4925631714655984831586909)
        ·
          refine ⟨1847111892995994311845091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4925631714655984831586909 1847111892995994311845091)
          ·
            refine ⟨2770667839493991467767637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1847111892995994311845091 2770667839493991467767637)
            ·
              refine ⟨16234381872035106256451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2770667839493991467767637 16234381872035106256451)
              ·
                rfl

theorem cell23_2560924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 9].length) (baseStart_2560924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560924 prefixEnd_2560924 := by exact prefixLift 2560924
  have htrace : WordTrace (prefixWord ++ tailWord_2560924) baseStart_2560924 baseEnd_2560924 := by
    simpa [prefixWord, tailWord_2560924, baseEnd_2560924] using wordTrace_append hprefix tailTrace_2560924
  have hstable : (prefixWord ++ tailWord_2560924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560924).length < 2 ^ (prefixWord ++ tailWord_2560924).sum := by decide
  have hdescent : baseEnd_2560924 < baseStart_2560924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560935 : List Nat := [1, 1, 6, 1, 4, 1, 1, 1, 3, 2, 2]
def baseStart_2560935 : Nat := 118140960795 + 2560935 * 2 ^ 59
def prefixEnd_2560935 : Nat := 4983230072969 + 3 ^ 40 * 2560935 * 2
def baseEnd_2560935 : Nat := 1314990579922043063734981

theorem tailTrace_2560935 : CollatzResearch.WordTrace tailWord_2560935 prefixEnd_2560935 1314990579922043063734981 := by
  unfold tailWord_2560935
  simp only [CollatzResearch.WordTrace]
  refine ⟨93404972977177342722076259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62269981984784895148050839 93404972977177342722076259)
  ·
    refine ⟨140107459465766014083114389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93404972977177342722076259 140107459465766014083114389)
    ·
      refine ⟨6567537162457781910145987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 140107459465766014083114389 6567537162457781910145987)
      ·
        refine ⟨9851305743686672865218981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6567537162457781910145987 9851305743686672865218981)
        ·
          refine ⟨1847119826941251162228559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9851305743686672865218981 1847119826941251162228559)
          ·
            refine ⟨2770679740411876743342839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1847119826941251162228559 2770679740411876743342839)
            ·
              refine ⟨4156019610617815115014259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2770679740411876743342839 4156019610617815115014259)
              ·
                refine ⟨6234029415926722672521389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4156019610617815115014259 6234029415926722672521389)
                ·
                  refine ⟨2337761030972521002195521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6234029415926722672521389 2337761030972521002195521)
                  ·
                    refine ⟨1753320773229390751646641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2337761030972521002195521 1753320773229390751646641)
                    ·
                      refine ⟨1314990579922043063734981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1753320773229390751646641 1314990579922043063734981)
                      ·
                        rfl

theorem cell23_2560935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_2560935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560935 prefixEnd_2560935 := by exact prefixLift 2560935
  have htrace : WordTrace (prefixWord ++ tailWord_2560935) baseStart_2560935 baseEnd_2560935 := by
    simpa [prefixWord, tailWord_2560935, baseEnd_2560935] using wordTrace_append hprefix tailTrace_2560935
  have hstable : (prefixWord ++ tailWord_2560935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560935).length < 2 ^ (prefixWord ++ tailWord_2560935).sum := by decide
  have hdescent : baseEnd_2560935 < baseStart_2560935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560940 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 4]
def baseStart_2560940 : Nat := 118140960795 + 2560940 * 2 ^ 59
def prefixEnd_2560940 : Nat := 4983230072969 + 3 ^ 40 * 2560940 * 2
def baseEnd_2560940 : Nat := 1314993147325315544172457

theorem tailTrace_2560940 : CollatzResearch.WordTrace tailWord_2560940 prefixEnd_2560940 1314993147325315544172457 := by
  unfold tailWord_2560940
  simp only [CollatzResearch.WordTrace]
  refine ⟨46702577671079614288004137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62270103561439485717338849 46702577671079614288004137)
  ·
    refine ⟨35026933253309710716003103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46702577671079614288004137 35026933253309710716003103)
    ·
      refine ⟨52540399879964566074004655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35026933253309710716003103 52540399879964566074004655)
      ·
        refine ⟨78810599819946849111006983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52540399879964566074004655 78810599819946849111006983)
        ·
          refine ⟨118215899729920273666510475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78810599819946849111006983 118215899729920273666510475)
          ·
            refine ⟨177323849594880410499765713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118215899729920273666510475 177323849594880410499765713)
            ·
              refine ⟨132992887196160307874824285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177323849594880410499765713 132992887196160307874824285)
              ·
                refine ⟨49872332698560115453059107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132992887196160307874824285 49872332698560115453059107)
                ·
                  refine ⟨74808499047840173179588661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49872332698560115453059107 74808499047840173179588661)
                  ·
                    refine ⟨7013296785735016235586437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 74808499047840173179588661 7013296785735016235586437)
                    ·
                      refine ⟨1314993147325315544172457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7013296785735016235586437 1314993147325315544172457)
                      ·
                        rfl

theorem cell23_2560940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 4].length) (baseStart_2560940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560940 prefixEnd_2560940 := by exact prefixLift 2560940
  have htrace : WordTrace (prefixWord ++ tailWord_2560940) baseStart_2560940 baseEnd_2560940 := by
    simpa [prefixWord, tailWord_2560940, baseEnd_2560940] using wordTrace_append hprefix tailTrace_2560940
  have hstable : (prefixWord ++ tailWord_2560940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560940).length < 2 ^ (prefixWord ++ tailWord_2560940).sum := by decide
  have hdescent : baseEnd_2560940 < baseStart_2560940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560951 : List Nat := [1, 1, 3, 1, 3, 1, 6, 1, 2, 1, 3]
def baseStart_2560951 : Nat := 118140960795 + 2560951 * 2 ^ 59
def prefixEnd_2560951 : Nat := 4983230072969 + 3 ^ 40 * 2560951 * 2
def baseEnd_2560951 : Nat := 1314998795612515001134907

theorem tailTrace_2560951 : CollatzResearch.WordTrace tailWord_2560951 prefixEnd_2560951 1314998795612515001134907 := by
  unfold tailWord_2560951
  simp only [CollatzResearch.WordTrace]
  refine ⟨93405556545119377454658707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62270371030079584969772471 93405556545119377454658707)
  ·
    refine ⟨140108334817679066181988061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93405556545119377454658707 140108334817679066181988061)
    ·
      refine ⟨52540625556629649818245523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140108334817679066181988061 52540625556629649818245523)
      ·
        refine ⟨78810938334944474727368285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52540625556629649818245523 78810938334944474727368285)
        ·
          refine ⟨29554101875604178022763107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78810938334944474727368285 29554101875604178022763107)
          ·
            refine ⟨44331152813406267034144661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29554101875604178022763107 44331152813406267034144661)
            ·
              refine ⟨2078022788128418767225531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 44331152813406267034144661 2078022788128418767225531)
              ·
                refine ⟨3117034182192628150838297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2078022788128418767225531 3117034182192628150838297)
                ·
                  refine ⟨2337775636644471113128723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3117034182192628150838297 2337775636644471113128723)
                  ·
                    refine ⟨3506663454966706669693085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2337775636644471113128723 3506663454966706669693085)
                    ·
                      refine ⟨1314998795612515001134907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3506663454966706669693085 1314998795612515001134907)
                      ·
                        rfl

theorem cell23_2560951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 2, 1, 3].length) (baseStart_2560951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560951 prefixEnd_2560951 := by exact prefixLift 2560951
  have htrace : WordTrace (prefixWord ++ tailWord_2560951) baseStart_2560951 baseEnd_2560951 := by
    simpa [prefixWord, tailWord_2560951, baseEnd_2560951] using wordTrace_append hprefix tailTrace_2560951
  have hstable : (prefixWord ++ tailWord_2560951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560951).length < 2 ^ (prefixWord ++ tailWord_2560951).sum := by decide
  have hdescent : baseEnd_2560951 < baseStart_2560951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560974 : List Nat := [4, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2]
def baseStart_2560974 : Nat := 118140960795 + 2560974 * 2 ^ 59
def prefixEnd_2560974 : Nat := 4983230072969 + 3 ^ 40 * 2560974 * 2
def baseEnd_2560974 : Nat := 1315010605667568411147301

theorem tailTrace_2560974 : CollatzResearch.WordTrace tailWord_2560974 prefixEnd_2560974 1315010605667568411147301 := by
  unfold tailWord_2560974
  simp only [CollatzResearch.WordTrace]
  refine ⟨11675799428004506547843247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62270930282690701588497317 11675799428004506547843247)
  ·
    refine ⟨17513699142006759821764871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11675799428004506547843247 17513699142006759821764871)
    ·
      refine ⟨26270548713010139732647307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17513699142006759821764871 26270548713010139732647307)
      ·
        refine ⟨39405823069515209598970961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26270548713010139732647307 39405823069515209598970961)
        ·
          refine ⟨29554367302136407199228221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39405823069515209598970961 29554367302136407199228221)
          ·
            refine ⟨11082887738301152699710583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29554367302136407199228221 11082887738301152699710583)
            ·
              refine ⟨16624331607451729049565875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11082887738301152699710583 16624331607451729049565875)
              ·
                refine ⟨24936497411177593574348813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16624331607451729049565875 24936497411177593574348813)
                ·
                  refine ⟨9351186529191597590380805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24936497411177593574348813 9351186529191597590380805)
                  ·
                    refine ⟨1753347474223424548196401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9351186529191597590380805 1753347474223424548196401)
                    ·
                      refine ⟨1315010605667568411147301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1753347474223424548196401 1315010605667568411147301)
                      ·
                        rfl

theorem cell23_2560974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2].length) (baseStart_2560974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560974 prefixEnd_2560974 := by exact prefixLift 2560974
  have htrace : WordTrace (prefixWord ++ tailWord_2560974) baseStart_2560974 baseEnd_2560974 := by
    simpa [prefixWord, tailWord_2560974, baseEnd_2560974] using wordTrace_append hprefix tailTrace_2560974
  have hstable : (prefixWord ++ tailWord_2560974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560974).length < 2 ^ (prefixWord ++ tailWord_2560974).sum := by decide
  have hdescent : baseEnd_2560974 < baseStart_2560974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561007 : List Nat := [1, 1, 2, 1, 4, 3, 1, 1, 1, 5, 3]
def baseStart_2561007 : Nat := 118140960795 + 2561007 * 2 ^ 59
def prefixEnd_2561007 : Nat := 4983230072969 + 3 ^ 40 * 2561007 * 2
def baseEnd_2561007 : Nat := 1315027550529166782034649

theorem tailTrace_2561007 : CollatzResearch.WordTrace tailWord_2561007 prefixEnd_2561007 1315027550529166782034649 := by
  unfold tailWord_2561007
  simp only [CollatzResearch.WordTrace]
  refine ⟨93407599032916499018697275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62271732688610999345798183 93407599032916499018697275)
  ·
    refine ⟨140111398549374748528045913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93407599032916499018697275 140111398549374748528045913)
    ·
      refine ⟨105083548912031061396034435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140111398549374748528045913 105083548912031061396034435)
      ·
        refine ⟨157625323368046592094051653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105083548912031061396034435 157625323368046592094051653)
        ·
          refine ⟨29554748131508736017634685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 157625323368046592094051653 29554748131508736017634685)
          ·
            refine ⟨11083030549315776006613007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29554748131508736017634685 11083030549315776006613007)
            ·
              refine ⟨16624545823973664009919511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11083030549315776006613007 16624545823973664009919511)
              ·
                refine ⟨24936818735960496014879267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16624545823973664009919511 24936818735960496014879267)
                ·
                  refine ⟨37405228103940744022318901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24936818735960496014879267 37405228103940744022318901)
                  ·
                    refine ⟨3506740134744444752092397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37405228103940744022318901 3506740134744444752092397)
                    ·
                      refine ⟨1315027550529166782034649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3506740134744444752092397 1315027550529166782034649)
                      ·
                        rfl

theorem cell23_2561007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 5, 3].length) (baseStart_2561007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561007 prefixEnd_2561007 := by exact prefixLift 2561007
  have htrace : WordTrace (prefixWord ++ tailWord_2561007) baseStart_2561007 baseEnd_2561007 := by
    simpa [prefixWord, tailWord_2561007, baseEnd_2561007] using wordTrace_append hprefix tailTrace_2561007
  have hstable : (prefixWord ++ tailWord_2561007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561007).length < 2 ^ (prefixWord ++ tailWord_2561007).sum := by decide
  have hdescent : baseEnd_2561007 < baseStart_2561007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561014 : List Nat := [5, 1, 1, 1, 3, 2, 1, 2, 7]
def baseStart_2561014 : Nat := 118140960795 + 2561014 * 2 ^ 59
def prefixEnd_2561014 : Nat := 4983230072969 + 3 ^ 40 * 2561014 * 2
def baseEnd_2561014 : Nat := 146114571654860917183013

theorem tailTrace_2561014 : CollatzResearch.WordTrace tailWord_2561014 prefixEnd_2561014 146114571654860917183013 := by
  unfold tailWord_2561014
  simp only [CollatzResearch.WordTrace]
  refine ⟨5837990896493196200887631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62271902895927426142801397 5837990896493196200887631)
  ·
    refine ⟨8756986344739794301331447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5837990896493196200887631 8756986344739794301331447)
    ·
      refine ⟨13135479517109691451997171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8756986344739794301331447 13135479517109691451997171)
      ·
        refine ⟨19703219275664537177995757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13135479517109691451997171 19703219275664537177995757)
        ·
          refine ⟨7388707228374201441748409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19703219275664537177995757 7388707228374201441748409)
          ·
            refine ⟨5541530421280651081311307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7388707228374201441748409 5541530421280651081311307)
            ·
              refine ⟨8312295631920976621966961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5541530421280651081311307 8312295631920976621966961)
              ·
                refine ⟨6234221723940732466475221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8312295631920976621966961 6234221723940732466475221)
                ·
                  refine ⟨146114571654860917183013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6234221723940732466475221 146114571654860917183013)
                  ·
                    rfl

theorem cell23_2561014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_2561014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561014 prefixEnd_2561014 := by exact prefixLift 2561014
  have htrace : WordTrace (prefixWord ++ tailWord_2561014) baseStart_2561014 baseEnd_2561014 := by
    simpa [prefixWord, tailWord_2561014, baseEnd_2561014] using wordTrace_append hprefix tailTrace_2561014
  have hstable : (prefixWord ++ tailWord_2561014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561014).length < 2 ^ (prefixWord ++ tailWord_2561014).sum := by decide
  have hdescent : baseEnd_2561014 < baseStart_2561014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561042 : List Nat := [3, 2, 5, 1, 1, 1, 1, 1, 4, 2, 2]
def baseStart_2561042 : Nat := 118140960795 + 2561042 * 2 ^ 59
def prefixEnd_2561042 : Nat := 4983230072969 + 3 ^ 40 * 2561042 * 2
def baseEnd_2561042 : Nat := 1315045522352074145096989

theorem tailTrace_2561042 : CollatzResearch.WordTrace tailWord_2561042 prefixEnd_2561042 1315045522352074145096989 := by
  unfold tailWord_2561042
  simp only [CollatzResearch.WordTrace]
  refine ⟨23352218896947424999055345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62272583725193133330814253 23352218896947424999055345)
  ·
    refine ⟨17514164172710568749291509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23352218896947424999055345 17514164172710568749291509)
    ·
      refine ⟨1641952891191615820246079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17514164172710568749291509 1641952891191615820246079)
      ·
        refine ⟨2462929336787423730369119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1641952891191615820246079 2462929336787423730369119)
        ·
          refine ⟨3694394005181135595553679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2462929336787423730369119 3694394005181135595553679)
          ·
            refine ⟨5541591007771703393330519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3694394005181135595553679 5541591007771703393330519)
            ·
              refine ⟨8312386511657555089995779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5541591007771703393330519 8312386511657555089995779)
              ·
                refine ⟨12468579767486332634993669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8312386511657555089995779 12468579767486332634993669)
                ·
                  refine ⟨2337858706403687369061313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12468579767486332634993669 2337858706403687369061313)
                  ·
                    refine ⟨1753394029802765526795985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2337858706403687369061313 1753394029802765526795985)
                    ·
                      refine ⟨1315045522352074145096989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1753394029802765526795985 1315045522352074145096989)
                      ·
                        rfl

theorem cell23_2561042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_2561042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561042 prefixEnd_2561042 := by exact prefixLift 2561042
  have htrace : WordTrace (prefixWord ++ tailWord_2561042) baseStart_2561042 baseEnd_2561042 := by
    simpa [prefixWord, tailWord_2561042, baseEnd_2561042] using wordTrace_append hprefix tailTrace_2561042
  have hstable : (prefixWord ++ tailWord_2561042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561042).length < 2 ^ (prefixWord ++ tailWord_2561042).sum := by decide
  have hdescent : baseEnd_2561042 < baseStart_2561042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561067 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 3, 4, 3]
def baseStart_2561067 : Nat := 118140960795 + 2561067 * 2 ^ 59
def prefixEnd_2561067 : Nat := 4983230072969 + 3 ^ 40 * 2561067 * 2
def baseEnd_2561067 : Nat := 1315058359368436547284373

theorem tailTrace_2561067 : CollatzResearch.WordTrace tailWord_2561067 prefixEnd_2561067 1315058359368436547284373 := by
  unfold tailWord_2561067
  simp only [CollatzResearch.WordTrace]
  refine ⟨93409787412699129265881455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62273191608466086177254303 93409787412699129265881455)
  ·
    refine ⟨140114681119048693898822183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93409787412699129265881455 140114681119048693898822183)
    ·
      refine ⟨210172021678573040848233275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140114681119048693898822183 210172021678573040848233275)
      ·
        refine ⟨315258032517859561272349913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210172021678573040848233275 315258032517859561272349913)
        ·
          refine ⟨236443524388394670954262435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315258032517859561272349913 236443524388394670954262435)
          ·
            refine ⟨354665286582592006431393653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236443524388394670954262435 354665286582592006431393653)
            ·
              refine ⟨33249870617118000602943155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 354665286582592006431393653 33249870617118000602943155)
              ·
                refine ⟨49874805925677000904414733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33249870617118000602943155 49874805925677000904414733)
                ·
                  refine ⟨18703052222128875339155525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49874805925677000904414733 18703052222128875339155525)
                  ·
                    refine ⟨3506822291649164126091661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18703052222128875339155525 3506822291649164126091661)
                    ·
                      refine ⟨1315058359368436547284373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3506822291649164126091661 1315058359368436547284373)
                      ·
                        rfl

theorem cell23_2561067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 4, 3].length) (baseStart_2561067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561067 prefixEnd_2561067 := by exact prefixLift 2561067
  have htrace : WordTrace (prefixWord ++ tailWord_2561067) baseStart_2561067 baseEnd_2561067 := by
    simpa [prefixWord, tailWord_2561067, baseEnd_2561067] using wordTrace_append hprefix tailTrace_2561067
  have hstable : (prefixWord ++ tailWord_2561067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561067).length < 2 ^ (prefixWord ++ tailWord_2561067).sum := by decide
  have hdescent : baseEnd_2561067 < baseStart_2561067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561074 : List Nat := [3, 2, 1, 1, 2, 2, 1, 4, 3, 4]
def baseStart_2561074 : Nat := 118140960795 + 2561074 * 2 ^ 59
def prefixEnd_2561074 : Nat := 4983230072969 + 3 ^ 40 * 2561074 * 2
def baseEnd_2561074 : Nat := 438353984577672673298947

theorem tailTrace_2561074 : CollatzResearch.WordTrace tailWord_2561074 prefixEnd_2561074 438353984577672673298947 := by
  unfold tailWord_2561074
  simp only [CollatzResearch.WordTrace]
  refine ⟨23352510680918442365346569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62273361815782512974257517 23352510680918442365346569)
  ·
    refine ⟨17514383010688831774009927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23352510680918442365346569 17514383010688831774009927)
    ·
      refine ⟨26271574516033247661014891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17514383010688831774009927 26271574516033247661014891)
      ·
        refine ⟨39407361774049871491522337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26271574516033247661014891 39407361774049871491522337)
        ·
          refine ⟨29555521330537403618641753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39407361774049871491522337 29555521330537403618641753)
          ·
            refine ⟨22166640997903052713981315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29555521330537403618641753 22166640997903052713981315)
            ·
              refine ⟨33249961496854579070971973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22166640997903052713981315 33249961496854579070971973)
              ·
                refine ⟨6234367780660233575807245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33249961496854579070971973 6234367780660233575807245)
                ·
                  refine ⟨2337887917747587590927717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6234367780660233575807245 2337887917747587590927717)
                  ·
                    refine ⟨438353984577672673298947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2337887917747587590927717 438353984577672673298947)
                    ·
                      rfl

theorem cell23_2561074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 3, 4].length) (baseStart_2561074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561074 prefixEnd_2561074 := by exact prefixLift 2561074
  have htrace : WordTrace (prefixWord ++ tailWord_2561074) baseStart_2561074 baseEnd_2561074 := by
    simpa [prefixWord, tailWord_2561074, baseEnd_2561074] using wordTrace_append hprefix tailTrace_2561074
  have hstable : (prefixWord ++ tailWord_2561074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561074).length < 2 ^ (prefixWord ++ tailWord_2561074).sum := by decide
  have hdescent : baseEnd_2561074 < baseStart_2561074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561077 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 1, 6, 4]
def baseStart_2561077 : Nat := 118140960795 + 2561077 * 2 ^ 59
def prefixEnd_2561077 : Nat := 4983230072969 + 3 ^ 40 * 2561077 * 2
def baseEnd_2561077 : Nat := 1315063494174981508159327

theorem tailTrace_2561077 : CollatzResearch.WordTrace tailWord_2561077 prefixEnd_2561077 1315063494174981508159327 := by
  unfold tailWord_2561077
  simp only [CollatzResearch.WordTrace]
  refine ⟨93410152142662900973745485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62273434761775267315830323 93410152142662900973745485)
  ·
    refine ⟨35028807053498587865154557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93410152142662900973745485 35028807053498587865154557)
    ·
      refine ⟨13135802645061970449432959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35028807053498587865154557 13135802645061970449432959)
      ·
        refine ⟨19703703967592955674149439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13135802645061970449432959 19703703967592955674149439)
        ·
          refine ⟨29555555951389433511224159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19703703967592955674149439 29555555951389433511224159)
          ·
            refine ⟨44333333927084150266836239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29555555951389433511224159 44333333927084150266836239)
            ·
              refine ⟨66500000890626225400254359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44333333927084150266836239 66500000890626225400254359)
              ·
                refine ⟨99750001335939338100381539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66500000890626225400254359 99750001335939338100381539)
                ·
                  refine ⟨149625002003909007150572309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99750001335939338100381539 149625002003909007150572309)
                  ·
                    refine ⟨7013671968933234710183077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 149625002003909007150572309 7013671968933234710183077)
                    ·
                      refine ⟨1315063494174981508159327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7013671968933234710183077 1315063494174981508159327)
                      ·
                        rfl

theorem cell23_2561077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_2561077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561077 prefixEnd_2561077 := by exact prefixLift 2561077
  have htrace : WordTrace (prefixWord ++ tailWord_2561077) baseStart_2561077 baseEnd_2561077 := by
    simpa [prefixWord, tailWord_2561077, baseEnd_2561077] using wordTrace_append hprefix tailTrace_2561077
  have hstable : (prefixWord ++ tailWord_2561077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561077).length < 2 ^ (prefixWord ++ tailWord_2561077).sum := by decide
  have hdescent : baseEnd_2561077 < baseStart_2561077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561084 : List Nat := [2, 2, 2, 2, 2, 2, 2, 1, 1, 4, 3]
def baseStart_2561084 : Nat := 118140960795 + 2561084 * 2 ^ 59
def prefixEnd_2561084 : Nat := 4983230072969 + 3 ^ 40 * 2561084 * 2
def baseEnd_2561084 : Nat := 1315067088539562980771795

theorem tailTrace_2561084 : CollatzResearch.WordTrace tailWord_2561084 prefixEnd_2561084 1315067088539562980771795 := by
  unfold tailWord_2561084
  simp only [CollatzResearch.WordTrace]
  refine ⟨46705203726818770584625153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62273604969091694112833537 46705203726818770584625153)
  ·
    refine ⟨35028902795114077938468865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46705203726818770584625153 35028902795114077938468865)
    ·
      refine ⟨26271677096335558453851649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35028902795114077938468865 26271677096335558453851649)
      ·
        refine ⟨19703757822251668840388737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26271677096335558453851649 19703757822251668840388737)
        ·
          refine ⟨14777818366688751630291553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19703757822251668840388737 14777818366688751630291553)
          ·
            refine ⟨11083363775016563722718665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14777818366688751630291553 11083363775016563722718665)
            ·
              refine ⟨8312522831262422792038999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11083363775016563722718665 8312522831262422792038999)
              ·
                refine ⟨12468784246893634188058499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8312522831262422792038999 12468784246893634188058499)
                ·
                  refine ⟨18703176370340451282087749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12468784246893634188058499 18703176370340451282087749)
                  ·
                    refine ⟨3506845569438834615391453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18703176370340451282087749 3506845569438834615391453)
                    ·
                      refine ⟨1315067088539562980771795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3506845569438834615391453 1315067088539562980771795)
                      ·
                        rfl

theorem cell23_2561084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_2561084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561084 prefixEnd_2561084 := by exact prefixLift 2561084
  have htrace : WordTrace (prefixWord ++ tailWord_2561084) baseStart_2561084 baseEnd_2561084 := by
    simpa [prefixWord, tailWord_2561084, baseEnd_2561084] using wordTrace_append hprefix tailTrace_2561084
  have hstable : (prefixWord ++ tailWord_2561084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561084).length < 2 ^ (prefixWord ++ tailWord_2561084).sum := by decide
  have hdescent : baseEnd_2561084 < baseStart_2561084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561101 : List Nat := [1, 6, 1, 1, 1, 2, 1, 1, 4, 2, 3]
def baseStart_2561101 : Nat := 118140960795 + 2561101 * 2 ^ 59
def prefixEnd_2561101 : Nat := 4983230072969 + 3 ^ 40 * 2561101 * 2
def baseEnd_2561101 : Nat := 1315075817710689414259217

theorem tailTrace_2561101 : CollatzResearch.WordTrace tailWord_2561101 prefixEnd_2561101 1315075817710689414259217 := by
  unfold tailWord_2561101
  simp only [CollatzResearch.WordTrace]
  refine ⟨93411027494575953072619157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62274018329717302048412771 93411027494575953072619157)
  ·
    refine ⟨4378641913808247800279023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 93411027494575953072619157 4378641913808247800279023)
    ·
      refine ⟨6567962870712371700418535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4378641913808247800279023 6567962870712371700418535)
      ·
        refine ⟨9851944306068557550627803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6567962870712371700418535 9851944306068557550627803)
        ·
          refine ⟨14777916459102836325941705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9851944306068557550627803 14777916459102836325941705)
          ·
            refine ⟨11083437344327127244456279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14777916459102836325941705 11083437344327127244456279)
            ·
              refine ⟨16625156016490690866684419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11083437344327127244456279 16625156016490690866684419)
              ·
                refine ⟨24937734024736036300026629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16625156016490690866684419 24937734024736036300026629)
                ·
                  refine ⟨4675825129638006806254993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24937734024736036300026629 4675825129638006806254993)
                  ·
                    refine ⟨3506868847228505104691245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4675825129638006806254993 3506868847228505104691245)
                    ·
                      refine ⟨1315075817710689414259217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3506868847228505104691245 1315075817710689414259217)
                      ·
                        rfl

theorem cell23_2561101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_2561101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561101 prefixEnd_2561101 := by exact prefixLift 2561101
  have htrace : WordTrace (prefixWord ++ tailWord_2561101) baseStart_2561101 baseEnd_2561101 := by
    simpa [prefixWord, tailWord_2561101, baseEnd_2561101] using wordTrace_append hprefix tailTrace_2561101
  have hstable : (prefixWord ++ tailWord_2561101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561101).length < 2 ^ (prefixWord ++ tailWord_2561101).sum := by decide
  have hdescent : baseEnd_2561101 < baseStart_2561101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561148 : List Nat := [2, 2, 2, 1, 1, 3, 2, 5, 1, 1, 3]
def baseStart_2561148 : Nat := 118140960795 + 2561148 * 2 ^ 59
def prefixEnd_2561148 : Nat := 4983230072969 + 3 ^ 40 * 2561148 * 2
def baseEnd_2561148 : Nat := 1315099951301450730371501

theorem tailTrace_2561148 : CollatzResearch.WordTrace tailWord_2561148 prefixEnd_2561148 1315099951301450730371501 := by
  unfold tailWord_2561148
  simp only [CollatzResearch.WordTrace]
  refine ⟨46706370862702840049790049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62275161150270453399720065 46706370862702840049790049)
  ·
    refine ⟨35029778147027130037342537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46706370862702840049790049 35029778147027130037342537)
    ·
      refine ⟨26272333610270347528006903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35029778147027130037342537 26272333610270347528006903)
      ·
        refine ⟨39408500415405521292010355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26272333610270347528006903 39408500415405521292010355)
        ·
          refine ⟨59112750623108281938015533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39408500415405521292010355 59112750623108281938015533)
          ·
            refine ⟨22167281483665605726755825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59112750623108281938015533 22167281483665605726755825)
            ·
              refine ⟨16625461112749204295066869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22167281483665605726755825 16625461112749204295066869)
              ·
                refine ⟨1558636979320237902662519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16625461112749204295066869 1558636979320237902662519)
                ·
                  refine ⟨2337955468980356853993779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1558636979320237902662519 2337955468980356853993779)
                  ·
                    refine ⟨3506933203470535280990669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2337955468980356853993779 3506933203470535280990669)
                    ·
                      refine ⟨1315099951301450730371501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3506933203470535280990669 1315099951301450730371501)
                      ·
                        rfl

theorem cell23_2561148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 5, 1, 1, 3].length) (baseStart_2561148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561148 prefixEnd_2561148 := by exact prefixLift 2561148
  have htrace : WordTrace (prefixWord ++ tailWord_2561148) baseStart_2561148 baseEnd_2561148 := by
    simpa [prefixWord, tailWord_2561148, baseEnd_2561148] using wordTrace_append hprefix tailTrace_2561148
  have hstable : (prefixWord ++ tailWord_2561148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561148).length < 2 ^ (prefixWord ++ tailWord_2561148).sum := by decide
  have hdescent : baseEnd_2561148 < baseStart_2561148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561164 : List Nat := [2, 2, 1, 2, 1, 1, 1, 5, 4, 4]
def baseStart_2561164 : Nat := 118140960795 + 2561164 * 2 ^ 59
def prefixEnd_2561164 : Nat := 4983230072969 + 3 ^ 40 * 2561164 * 2
def baseEnd_2561164 : Nat := 438369388997307555923809

theorem tailTrace_2561164 : CollatzResearch.WordTrace tailWord_2561164 prefixEnd_2561164 438369388997307555923809 := by
  unfold tailWord_2561164
  simp only [CollatzResearch.WordTrace]
  refine ⟨46706662646673857416081273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62275550195565143221441697 46706662646673857416081273)
  ·
    refine ⟨35029996985005393062060955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46706662646673857416081273 35029996985005393062060955)
    ·
      refine ⟨52544995477508089593091433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35029996985005393062060955 52544995477508089593091433)
      ·
        refine ⟨39408746608131067194818575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52544995477508089593091433 39408746608131067194818575)
        ·
          refine ⟨59113119912196600792227863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39408746608131067194818575 59113119912196600792227863)
          ·
            refine ⟨88669679868294901188341795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59113119912196600792227863 88669679868294901188341795)
            ·
              refine ⟨133004519802442351782512693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88669679868294901188341795 133004519802442351782512693)
              ·
                refine ⟨12469173731478970479610565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 133004519802442351782512693 12469173731478970479610565)
                ·
                  refine ⟨2337970074652306964926981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12469173731478970479610565 2337970074652306964926981)
                  ·
                    refine ⟨438369388997307555923809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2337970074652306964926981 438369388997307555923809)
                    ·
                      rfl

theorem cell23_2561164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 4, 4].length) (baseStart_2561164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561164 prefixEnd_2561164 := by exact prefixLift 2561164
  have htrace : WordTrace (prefixWord ++ tailWord_2561164) baseStart_2561164 baseEnd_2561164 := by
    simpa [prefixWord, tailWord_2561164, baseEnd_2561164] using wordTrace_append hprefix tailTrace_2561164
  have hstable : (prefixWord ++ tailWord_2561164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561164).length < 2 ^ (prefixWord ++ tailWord_2561164).sum := by decide
  have hdescent : baseEnd_2561164 < baseStart_2561164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561181 : List Nat := [1, 4, 2, 1, 1, 2, 1, 5, 2, 4]
def baseStart_2561181 : Nat := 118140960795 + 2561181 * 2 ^ 59
def prefixEnd_2561181 : Nat := 4983230072969 + 3 ^ 40 * 2561181 * 2
def baseEnd_2561181 : Nat := 438372298721016367086283

theorem tailTrace_2561181 : CollatzResearch.WordTrace tailWord_2561181 prefixEnd_2561181 438372298721016367086283 := by
  unfold tailWord_2561181
  simp only [CollatzResearch.WordTrace]
  refine ⟨93413945334286126735531397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62275963556190751157020931 93413945334286126735531397)
  ·
    refine ⟨17515114750178648762912137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93413945334286126735531397 17515114750178648762912137)
    ·
      refine ⟨13136336062633986572184103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17515114750178648762912137 13136336062633986572184103)
      ·
        refine ⟨19704504093950979858276155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13136336062633986572184103 19704504093950979858276155)
        ·
          refine ⟨29556756140926469787414233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19704504093950979858276155 29556756140926469787414233)
          ·
            refine ⟨22167567105694852340560675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29556756140926469787414233 22167567105694852340560675)
            ·
              refine ⟨33251350658542278510841013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22167567105694852340560675 33251350658542278510841013)
              ·
                refine ⟨3117314124238338610391345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33251350658542278510841013 3117314124238338610391345)
                ·
                  refine ⟨2337985593178753957793509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3117314124238338610391345 2337985593178753957793509)
                  ·
                    refine ⟨438372298721016367086283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2337985593178753957793509 438372298721016367086283)
                    ·
                      rfl

theorem cell23_2561181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_2561181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561181 prefixEnd_2561181 := by exact prefixLift 2561181
  have htrace : WordTrace (prefixWord ++ tailWord_2561181) baseStart_2561181 baseEnd_2561181 := by
    simpa [prefixWord, tailWord_2561181, baseEnd_2561181] using wordTrace_append hprefix tailTrace_2561181
  have hstable : (prefixWord ++ tailWord_2561181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561181).length < 2 ^ (prefixWord ++ tailWord_2561181).sum := by decide
  have hdescent : baseEnd_2561181 < baseStart_2561181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561187 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 7]
def baseStart_2561187 : Nat := 118140960795 + 2561187 * 2 ^ 59
def prefixEnd_2561187 : Nat := 4983230072969 + 3 ^ 40 * 2561187 * 2
def baseEnd_2561187 : Nat := 1315119977046976077783821

theorem tailTrace_2561187 : CollatzResearch.WordTrace tailWord_2561187 prefixEnd_2561187 1315119977046976077783821 := by
  unfold tailWord_2561187
  simp only [CollatzResearch.WordTrace]
  refine ⟨93414164172264389760249815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62276109448176259840166543 93414164172264389760249815)
  ·
    refine ⟨140121246258396584640374723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93414164172264389760249815 140121246258396584640374723)
    ·
      refine ⟨210181869387594876960562085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140121246258396584640374723 210181869387594876960562085)
      ·
        refine ⟨39409100510174039430105391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 210181869387594876960562085 39409100510174039430105391)
        ·
          refine ⟨59113650765261059145158087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39409100510174039430105391 59113650765261059145158087)
          ·
            refine ⟨88670476147891588717737131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59113650765261059145158087 88670476147891588717737131)
            ·
              refine ⟨133005714221837383076605697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88670476147891588717737131 133005714221837383076605697)
              ·
                refine ⟨99754285666378037307454273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133005714221837383076605697 99754285666378037307454273)
                ·
                  refine ⟨74815714249783527980590705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99754285666378037307454273 74815714249783527980590705)
                  ·
                    refine ⟨56111785687337645985443029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74815714249783527980590705 56111785687337645985443029)
                    ·
                      refine ⟨1315119977046976077783821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 56111785687337645985443029 1315119977046976077783821)
                      ·
                        rfl

theorem cell23_2561187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_2561187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561187 prefixEnd_2561187 := by exact prefixLift 2561187
  have htrace : WordTrace (prefixWord ++ tailWord_2561187) baseStart_2561187 baseEnd_2561187 := by
    simpa [prefixWord, tailWord_2561187, baseEnd_2561187] using wordTrace_append hprefix tailTrace_2561187
  have hstable : (prefixWord ++ tailWord_2561187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561187).length < 2 ^ (prefixWord ++ tailWord_2561187).sum := by decide
  have hdescent : baseEnd_2561187 < baseStart_2561187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561188 : List Nat := [2, 3, 1, 2, 3, 1, 1, 1, 5, 2, 2]
def baseStart_2561188 : Nat := 118140960795 + 2561188 * 2 ^ 59
def prefixEnd_2561188 : Nat := 4983230072969 + 3 ^ 40 * 2561188 * 2
def baseEnd_2561188 : Nat := 1315120490527630573871317

theorem tailTrace_2561188 : CollatzResearch.WordTrace tailWord_2561188 prefixEnd_2561188 1315120490527630573871317 := by
  unfold tailWord_2561188
  simp only [CollatzResearch.WordTrace]
  refine ⟨46707100322630383465518109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62276133763507177954024145 46707100322630383465518109)
  ·
    refine ⟨17515162620986393799569291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46707100322630383465518109 17515162620986393799569291)
    ·
      refine ⟨26272743931479590699353937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17515162620986393799569291 26272743931479590699353937)
      ·
        refine ⟨19704557948609693024515453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26272743931479590699353937 19704557948609693024515453)
        ·
          refine ⟨7389209230728634884193295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19704557948609693024515453 7389209230728634884193295)
          ·
            refine ⟨11083813846092952326289943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7389209230728634884193295 11083813846092952326289943)
            ·
              refine ⟨16625720769139428489434915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11083813846092952326289943 16625720769139428489434915)
              ·
                refine ⟨24938581153709142734152373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16625720769139428489434915 24938581153709142734152373)
                ·
                  refine ⟨2337991983160232131326785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24938581153709142734152373 2337991983160232131326785)
                  ·
                    refine ⟨1753493987370174098495089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2337991983160232131326785 1753493987370174098495089)
                    ·
                      refine ⟨1315120490527630573871317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1753493987370174098495089 1315120490527630573871317)
                      ·
                        rfl

theorem cell23_2561188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_2561188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561188 prefixEnd_2561188 := by exact prefixLift 2561188
  have htrace : WordTrace (prefixWord ++ tailWord_2561188) baseStart_2561188 baseEnd_2561188 := by
    simpa [prefixWord, tailWord_2561188, baseEnd_2561188] using wordTrace_append hprefix tailTrace_2561188
  have hstable : (prefixWord ++ tailWord_2561188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561188).length < 2 ^ (prefixWord ++ tailWord_2561188).sum := by decide
  have hdescent : baseEnd_2561188 < baseStart_2561188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561201 : List Nat := [1, 2, 2, 5, 1, 1, 2, 2, 1, 2, 4]
def baseStart_2561201 : Nat := 118140960795 + 2561201 * 2 ^ 59
def prefixEnd_2561201 : Nat := 4983230072969 + 3 ^ 40 * 2561201 * 2
def baseEnd_2561201 : Nat := 1315127165776139023008757

theorem tailTrace_2561201 : CollatzResearch.WordTrace tailWord_2561201 prefixEnd_2561201 1315127165776139023008757 := by
  unfold tailWord_2561201
  simp only [CollatzResearch.WordTrace]
  refine ⟨93414674794213670151259457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62276449862809113434172971 93414674794213670151259457)
  ·
    refine ⟨70061006095660252613444593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93414674794213670151259457 70061006095660252613444593)
    ·
      refine ⟨52545754571745189460083445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70061006095660252613444593 52545754571745189460083445)
      ·
        refine ⟨4926164491101111511882823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52545754571745189460083445 4926164491101111511882823)
        ·
          refine ⟨7389246736651667267824235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4926164491101111511882823 7389246736651667267824235)
          ·
            refine ⟨11083870104977500901736353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7389246736651667267824235 11083870104977500901736353)
            ·
              refine ⟨8312902578733125676302265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11083870104977500901736353 8312902578733125676302265)
              ·
                refine ⟨6234676934049844257226699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8312902578733125676302265 6234676934049844257226699)
                ·
                  refine ⟨9352015401074766385840049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6234676934049844257226699 9352015401074766385840049)
                  ·
                    refine ⟨7014011550806074789380037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9352015401074766385840049 7014011550806074789380037)
                    ·
                      refine ⟨1315127165776139023008757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7014011550806074789380037 1315127165776139023008757)
                      ·
                        rfl

theorem cell23_2561201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_2561201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561201 prefixEnd_2561201 := by exact prefixLift 2561201
  have htrace : WordTrace (prefixWord ++ tailWord_2561201) baseStart_2561201 baseEnd_2561201 := by
    simpa [prefixWord, tailWord_2561201, baseEnd_2561201] using wordTrace_append hprefix tailTrace_2561201
  have hstable : (prefixWord ++ tailWord_2561201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561201).length < 2 ^ (prefixWord ++ tailWord_2561201).sum := by decide
  have hdescent : baseEnd_2561201 < baseStart_2561201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561231 : List Nat := [1, 1, 2, 1, 1, 3, 2, 4, 3, 3, 2]
def baseStart_2561231 : Nat := 118140960795 + 2561231 * 2 ^ 59
def prefixEnd_2561231 : Nat := 4983230072969 + 3 ^ 40 * 2561231 * 2
def baseEnd_2561231 : Nat := 1315142570195773905633619

theorem tailTrace_2561231 : CollatzResearch.WordTrace tailWord_2561231 prefixEnd_2561231 1315142570195773905633619 := by
  unfold tailWord_2561231
  simp only [CollatzResearch.WordTrace]
  refine ⟨93415768984104985274851547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62277179322736656849901031 93415768984104985274851547)
  ·
    refine ⟨140123653476157477912277321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93415768984104985274851547 140123653476157477912277321)
    ·
      refine ⟨105092740107118108434207991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140123653476157477912277321 105092740107118108434207991)
      ·
        refine ⟨157639110160677162651311987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105092740107118108434207991 157639110160677162651311987)
        ·
          refine ⟨236458665241015743976967981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157639110160677162651311987 236458665241015743976967981)
          ·
            refine ⟨88671999465380903991362993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 236458665241015743976967981 88671999465380903991362993)
            ·
              refine ⟨66503999599035677993522245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88671999465380903991362993 66503999599035677993522245)
              ·
                refine ⟨12469499924819189623785421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66503999599035677993522245 12469499924819189623785421)
                ·
                  refine ⟨4676062471807196108919533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12469499924819189623785421 4676062471807196108919533)
                  ·
                    refine ⟨1753523426927698540844825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4676062471807196108919533 1753523426927698540844825)
                    ·
                      refine ⟨1315142570195773905633619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1753523426927698540844825 1315142570195773905633619)
                      ·
                        rfl

theorem cell23_2561231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 3, 2].length) (baseStart_2561231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561231 prefixEnd_2561231 := by exact prefixLift 2561231
  have htrace : WordTrace (prefixWord ++ tailWord_2561231) baseStart_2561231 baseEnd_2561231 := by
    simpa [prefixWord, tailWord_2561231, baseEnd_2561231] using wordTrace_append hprefix tailTrace_2561231
  have hstable : (prefixWord ++ tailWord_2561231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561231).length < 2 ^ (prefixWord ++ tailWord_2561231).sum := by decide
  have hdescent : baseEnd_2561231 < baseStart_2561231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561245 : List Nat := [1, 4, 3, 2, 3, 1, 2, 7]
def baseStart_2561245 : Nat := 118140960795 + 2561245 * 2 ^ 59
def prefixEnd_2561245 : Nat := 4983230072969 + 3 ^ 40 * 2561245 * 2
def baseEnd_2561245 : Nat := 48709250330553216698465

theorem tailTrace_2561245 : CollatzResearch.WordTrace tailWord_2561245 prefixEnd_2561245 48709250330553216698465 := by
  unfold tailWord_2561245
  simp only [CollatzResearch.WordTrace]
  refine ⟨93416279606054265665861189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62277519737369510443907459 93416279606054265665861189)
  ·
    refine ⟨17515552426135174812348973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93416279606054265665861189 17515552426135174812348973)
    ·
      refine ⟨6568332159800690554630865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17515552426135174812348973 6568332159800690554630865)
      ·
        refine ⟨4926249119850517915973149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6568332159800690554630865 4926249119850517915973149)
        ·
          refine ⟨1847343419943944218489931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4926249119850517915973149 1847343419943944218489931)
          ·
            refine ⟨2771015129915916327734897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1847343419943944218489931 2771015129915916327734897)
            ·
              refine ⟨2078261347436937245801173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2771015129915916327734897 2078261347436937245801173)
              ·
                refine ⟨48709250330553216698465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2078261347436937245801173 48709250330553216698465)
                ·
                  rfl

theorem cell23_2561245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 7].length) (baseStart_2561245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561245 prefixEnd_2561245 := by exact prefixLift 2561245
  have htrace : WordTrace (prefixWord ++ tailWord_2561245) baseStart_2561245 baseEnd_2561245 := by
    simpa [prefixWord, tailWord_2561245, baseEnd_2561245] using wordTrace_append hprefix tailTrace_2561245
  have hstable : (prefixWord ++ tailWord_2561245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561245).length < 2 ^ (prefixWord ++ tailWord_2561245).sum := by decide
  have hdescent : baseEnd_2561245 < baseStart_2561245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561248 : List Nat := [2, 1, 1, 3, 1, 4, 1, 4, 1, 3, 2]
def baseStart_2561248 : Nat := 118140960795 + 2561248 * 2 ^ 59
def prefixEnd_2561248 : Nat := 4983230072969 + 3 ^ 40 * 2561248 * 2
def baseEnd_2561248 : Nat := 1315151299366900339121041

theorem tailTrace_2561248 : CollatzResearch.WordTrace tailWord_2561248 prefixEnd_2561248 1315151299366900339121041 := by
  unfold tailWord_2561248
  simp only [CollatzResearch.WordTrace]
  refine ⟨46708194512521698589110199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62277592683362264785480265 46708194512521698589110199)
  ·
    refine ⟨70062291768782547883665299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46708194512521698589110199 70062291768782547883665299)
    ·
      refine ⟨105093437653173821825497949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70062291768782547883665299 105093437653173821825497949)
      ·
        refine ⟨39410039119940183184561731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105093437653173821825497949 39410039119940183184561731)
        ·
          refine ⟨59115058679910274776842597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39410039119940183184561731 59115058679910274776842597)
          ·
            refine ⟨11084073502483176520657987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59115058679910274776842597 11084073502483176520657987)
            ·
              refine ⟨16626110253724764780986981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11084073502483176520657987 16626110253724764780986981)
              ·
                refine ⟨3117395672573393396435059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16626110253724764780986981 3117395672573393396435059)
                ·
                  refine ⟨4676093508860090094652589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3117395672573393396435059 4676093508860090094652589)
                  ·
                    refine ⟨1753535065822533785494721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4676093508860090094652589 1753535065822533785494721)
                    ·
                      refine ⟨1315151299366900339121041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1753535065822533785494721 1315151299366900339121041)
                      ·
                        rfl

theorem cell23_2561248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 1, 3, 2].length) (baseStart_2561248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561248 prefixEnd_2561248 := by exact prefixLift 2561248
  have htrace : WordTrace (prefixWord ++ tailWord_2561248) baseStart_2561248 baseEnd_2561248 := by
    simpa [prefixWord, tailWord_2561248, baseEnd_2561248] using wordTrace_append hprefix tailTrace_2561248
  have hstable : (prefixWord ++ tailWord_2561248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561248).length < 2 ^ (prefixWord ++ tailWord_2561248).sum := by decide
  have hdescent : baseEnd_2561248 < baseStart_2561248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561264 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 3]
def baseStart_2561264 : Nat := 118140960795 + 2561264 * 2 ^ 59
def prefixEnd_2561264 : Nat := 4983230072969 + 3 ^ 40 * 2561264 * 2
def baseEnd_2561264 : Nat := 1315159515057372276520967

theorem tailTrace_2561264 : CollatzResearch.WordTrace tailWord_2561264 prefixEnd_2561264 1315159515057372276520967 := by
  unfold tailWord_2561264
  simp only [CollatzResearch.WordTrace]
  refine ⟨46708486296492715955401423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62277981728656954607201897 46708486296492715955401423)
  ·
    refine ⟨70062729444739073933102135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46708486296492715955401423 70062729444739073933102135)
    ·
      refine ⟨105094094167108610899653203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70062729444739073933102135 105094094167108610899653203)
      ·
        refine ⟨157641141250662916349479805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105094094167108610899653203 157641141250662916349479805)
        ·
          refine ⟨59115427968998593631054927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157641141250662916349479805 59115427968998593631054927)
          ·
            refine ⟨88673141953497890446582391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59115427968998593631054927 88673141953497890446582391)
            ·
              refine ⟨133009712930246835669873587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88673141953497890446582391 133009712930246835669873587)
              ·
                refine ⟨199514569395370253504810381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133009712930246835669873587 199514569395370253504810381)
                ·
                  refine ⟨74817963523263845064303893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 199514569395370253504810381 74817963523263845064303893)
                  ·
                    refine ⟨3507092040152992737389245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 74817963523263845064303893 3507092040152992737389245)
                    ·
                      refine ⟨1315159515057372276520967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3507092040152992737389245 1315159515057372276520967)
                      ·
                        rfl

theorem cell23_2561264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 3].length) (baseStart_2561264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561264 prefixEnd_2561264 := by exact prefixLift 2561264
  have htrace : WordTrace (prefixWord ++ tailWord_2561264) baseStart_2561264 baseEnd_2561264 := by
    simpa [prefixWord, tailWord_2561264, baseEnd_2561264] using wordTrace_append hprefix tailTrace_2561264
  have hstable : (prefixWord ++ tailWord_2561264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561264).length < 2 ^ (prefixWord ++ tailWord_2561264).sum := by decide
  have hdescent : baseEnd_2561264 < baseStart_2561264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561331 : List Nat := [1, 1, 1, 2, 5, 2, 2, 2, 2, 5]
def baseStart_2561331 : Nat := 118140960795 + 2561331 * 2 ^ 59
def prefixEnd_2561331 : Nat := 4983230072969 + 3 ^ 40 * 2561331 * 2
def baseEnd_2561331 : Nat := 438397972753741171461053

theorem tailTrace_2561331 : CollatzResearch.WordTrace tailWord_2561331 prefixEnd_2561331 438397972753741171461053 := by
  unfold tailWord_2561331
  simp only [CollatzResearch.WordTrace]
  refine ⟨93419416283742702353491847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62279610855828468235661231 93419416283742702353491847)
  ·
    refine ⟨140129124425614053530237771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93419416283742702353491847 140129124425614053530237771)
    ·
      refine ⟨210193686638421080295356657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140129124425614053530237771 210193686638421080295356657)
      ·
        refine ⟨157645264978815810221517493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210193686638421080295356657 157645264978815810221517493)
        ·
          refine ⟨14779243591763982208267265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 157645264978815810221517493 14779243591763982208267265)
          ·
            refine ⟨11084432693822986656200449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14779243591763982208267265 11084432693822986656200449)
            ·
              refine ⟨8313324520367239992150337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11084432693822986656200449 8313324520367239992150337)
              ·
                refine ⟨6234993390275429994112753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8313324520367239992150337 6234993390275429994112753)
                ·
                  refine ⟨4676245042706572495584565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6234993390275429994112753 4676245042706572495584565)
                  ·
                    refine ⟨438397972753741171461053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4676245042706572495584565 438397972753741171461053)
                    ·
                      rfl

theorem cell23_2561331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 5].length) (baseStart_2561331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561331 prefixEnd_2561331 := by exact prefixLift 2561331
  have htrace : WordTrace (prefixWord ++ tailWord_2561331) baseStart_2561331 baseEnd_2561331 := by
    simpa [prefixWord, tailWord_2561331, baseEnd_2561331] using wordTrace_append hprefix tailTrace_2561331
  have hstable : (prefixWord ++ tailWord_2561331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561331).length < 2 ^ (prefixWord ++ tailWord_2561331).sum := by decide
  have hdescent : baseEnd_2561331 < baseStart_2561331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561378 : List Nat := [3, 3, 2, 1, 1, 1, 1, 2, 5, 4]
def baseStart_2561378 : Nat := 118140960795 + 2561378 * 2 ^ 59
def prefixEnd_2561378 : Nat := 4983230072969 + 3 ^ 40 * 2561378 * 2
def baseEnd_2561378 : Nat := 438406017283994943498481

theorem tailTrace_2561378 : CollatzResearch.WordTrace tailWord_2561378 prefixEnd_2561378 438406017283994943498481 := by
  unfold tailWord_2561378
  simp only [CollatzResearch.WordTrace]
  refine ⟨23355282628643107345113197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62280753676381619586968525 23355282628643107345113197)
  ·
    refine ⟨8758230985741165254417449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23355282628643107345113197 8758230985741165254417449)
    ·
      refine ⟨6568673239305873940813087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8758230985741165254417449 6568673239305873940813087)
      ·
        refine ⟨9853009858958810911219631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6568673239305873940813087 9853009858958810911219631)
        ·
          refine ⟨14779514788438216366829447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9853009858958810911219631 14779514788438216366829447)
          ·
            refine ⟨22169272182657324550244171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14779514788438216366829447 22169272182657324550244171)
            ·
              refine ⟨33253908273985986825366257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22169272182657324550244171 33253908273985986825366257)
              ·
                refine ⟨24940431205489490119024693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33253908273985986825366257 24940431205489490119024693)
                ·
                  refine ⟨2338165425514639698658565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24940431205489490119024693 2338165425514639698658565)
                  ·
                    refine ⟨438406017283994943498481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2338165425514639698658565 438406017283994943498481)
                    ·
                      rfl

theorem cell23_2561378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_2561378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561378 prefixEnd_2561378 := by exact prefixLift 2561378
  have htrace : WordTrace (prefixWord ++ tailWord_2561378) baseStart_2561378 baseEnd_2561378 := by
    simpa [prefixWord, tailWord_2561378, baseEnd_2561378] using wordTrace_append hprefix tailTrace_2561378
  have hstable : (prefixWord ++ tailWord_2561378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561378).length < 2 ^ (prefixWord ++ tailWord_2561378).sum := by decide
  have hdescent : baseEnd_2561378 < baseStart_2561378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561458 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2]
def baseStart_2561458 : Nat := 118140960795 + 2561458 * 2 ^ 59
def prefixEnd_2561458 : Nat := 4983230072969 + 3 ^ 40 * 2561458 * 2
def baseEnd_2561458 : Nat := 1315259130304344517495075

theorem tailTrace_2561458 : CollatzResearch.WordTrace tailWord_2561458 prefixEnd_2561458 1315259130304344517495075 := by
  unfold tailWord_2561458
  simp only [CollatzResearch.WordTrace]
  refine ⟨23356012088570650760841257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62282698902855068695576685 23356012088570650760841257)
  ·
    refine ⟨17517009066427988070630943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23356012088570650760841257 17517009066427988070630943)
    ·
      refine ⟨26275513599641982105946415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17517009066427988070630943 26275513599641982105946415)
      ·
        refine ⟨39413270399462973158919623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26275513599641982105946415 39413270399462973158919623)
        ·
          refine ⟨59119905599194459738379435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39413270399462973158919623 59119905599194459738379435)
          ·
            refine ⟨88679858398791689607569153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59119905599194459738379435 88679858398791689607569153)
            ·
              refine ⟨66509893799093767205676865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88679858398791689607569153 66509893799093767205676865)
              ·
                refine ⟨49882420349320325404257649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66509893799093767205676865 49882420349320325404257649)
                ·
                  refine ⟨37411815261990244053193237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49882420349320325404257649 37411815261990244053193237)
                  ·
                    refine ⟨1753678840405792689993433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 37411815261990244053193237 1753678840405792689993433)
                    ·
                      refine ⟨1315259130304344517495075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1753678840405792689993433 1315259130304344517495075)
                      ·
                        rfl

theorem cell23_2561458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2].length) (baseStart_2561458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561458 prefixEnd_2561458 := by exact prefixLift 2561458
  have htrace : WordTrace (prefixWord ++ tailWord_2561458) baseStart_2561458 baseEnd_2561458 := by
    simpa [prefixWord, tailWord_2561458, baseEnd_2561458] using wordTrace_append hprefix tailTrace_2561458
  have hstable : (prefixWord ++ tailWord_2561458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561458).length < 2 ^ (prefixWord ++ tailWord_2561458).sum := by decide
  have hdescent : baseEnd_2561458 < baseStart_2561458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561471 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 4]
def baseStart_2561471 : Nat := 118140960795 + 2561471 * 2 ^ 59
def prefixEnd_2561471 : Nat := 4983230072969 + 3 ^ 40 * 2561471 * 2
def baseEnd_2561471 : Nat := 1315265805552852966632515

theorem tailTrace_2561471 : CollatzResearch.WordTrace tailWord_2561471 prefixEnd_2561471 1315265805552852966632515 := by
  unfold tailWord_2561471
  simp only [CollatzResearch.WordTrace]
  refine ⟨93424522503235506263588267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62283015002157004175725511 93424522503235506263588267)
  ·
    refine ⟨140136783754853259395382401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93424522503235506263588267 140136783754853259395382401)
    ·
      refine ⟨105102587816139944546536801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140136783754853259395382401 105102587816139944546536801)
      ·
        refine ⟨78826940862104958409902601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105102587816139944546536801 78826940862104958409902601)
        ·
          refine ⟨59120205646578718807426951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78826940862104958409902601 59120205646578718807426951)
          ·
            refine ⟨88680308469868078211140427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59120205646578718807426951 88680308469868078211140427)
            ·
              refine ⟨133020462704802117316710641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88680308469868078211140427 133020462704802117316710641)
              ·
                refine ⟨99765347028601587987532981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133020462704802117316710641 99765347028601587987532981)
                ·
                  refine ⟨9353001283931398873831217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 99765347028601587987532981 9353001283931398873831217)
                  ·
                    refine ⟨7014750962948549155373413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9353001283931398873831217 7014750962948549155373413)
                    ·
                      refine ⟨1315265805552852966632515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7014750962948549155373413 1315265805552852966632515)
                      ·
                        rfl

theorem cell23_2561471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 4].length) (baseStart_2561471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561471 prefixEnd_2561471 := by exact prefixLift 2561471
  have htrace : WordTrace (prefixWord ++ tailWord_2561471) baseStart_2561471 baseEnd_2561471 := by
    simpa [prefixWord, tailWord_2561471, baseEnd_2561471] using wordTrace_append hprefix tailTrace_2561471
  have hstable : (prefixWord ++ tailWord_2561471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561471).length < 2 ^ (prefixWord ++ tailWord_2561471).sum := by decide
  have hdescent : baseEnd_2561471 < baseStart_2561471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561475 : List Nat := [1, 1, 1, 3, 1, 1, 4, 4, 3, 2, 2]
def baseStart_2561475 : Nat := 118140960795 + 2561475 * 2 ^ 59
def prefixEnd_2561475 : Nat := 4983230072969 + 3 ^ 40 * 2561475 * 2
def baseEnd_2561475 : Nat := 1315267859475470950982497

theorem tailTrace_2561475 : CollatzResearch.WordTrace tailWord_2561475 prefixEnd_2561475 1315267859475470950982497 := by
  unfold tailWord_2561475
  simp only [CollatzResearch.WordTrace]
  refine ⟨93424668395221014946733879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62283112263480676631155919 93424668395221014946733879)
  ·
    refine ⟨140137002592831522420100819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93424668395221014946733879 140137002592831522420100819)
    ·
      refine ⟨210205503889247283630151229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140137002592831522420100819 210205503889247283630151229)
      ·
        refine ⟨78827063958467731361306711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210205503889247283630151229 78827063958467731361306711)
        ·
          refine ⟨118240595937701597041960067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78827063958467731361306711 118240595937701597041960067)
          ·
            refine ⟨177360893906552395562940101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118240595937701597041960067 177360893906552395562940101)
            ·
              refine ⟨33255167607478574168051269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 177360893906552395562940101 33255167607478574168051269)
              ·
                refine ⟨6235343926402232656509613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33255167607478574168051269 6235343926402232656509613)
                ·
                  refine ⟨2338253972400837246191105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6235343926402232656509613 2338253972400837246191105)
                  ·
                    refine ⟨1753690479300627934643329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2338253972400837246191105 1753690479300627934643329)
                    ·
                      refine ⟨1315267859475470950982497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1753690479300627934643329 1315267859475470950982497)
                      ·
                        rfl

theorem cell23_2561475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 3, 2, 2].length) (baseStart_2561475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561475 prefixEnd_2561475 := by exact prefixLift 2561475
  have htrace : WordTrace (prefixWord ++ tailWord_2561475) baseStart_2561475 baseEnd_2561475 := by
    simpa [prefixWord, tailWord_2561475, baseEnd_2561475] using wordTrace_append hprefix tailTrace_2561475
  have hstable : (prefixWord ++ tailWord_2561475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561475).length < 2 ^ (prefixWord ++ tailWord_2561475).sum := by decide
  have hdescent : baseEnd_2561475 < baseStart_2561475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561541 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 3, 8]
def baseStart_2561541 : Nat := 118140960795 + 2561541 * 2 ^ 59
def prefixEnd_2561541 : Nat := 4983230072969 + 3 ^ 40 * 2561541 * 2
def baseEnd_2561541 : Nat := 438433916399555897585731

theorem tailTrace_2561541 : CollatzResearch.WordTrace tailWord_2561541 prefixEnd_2561541 438433916399555897585731 := by
  unfold tailWord_2561541
  simp only [CollatzResearch.WordTrace]
  refine ⟨93427075612981908218636477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62284717075321272145757651 93427075612981908218636477)
  ·
    refine ⟨35035153354868215581988679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93427075612981908218636477 35035153354868215581988679)
    ·
      refine ⟨52552730032302323372983019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35035153354868215581988679 52552730032302323372983019)
      ·
        refine ⟨78829095048453485059474529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52552730032302323372983019 78829095048453485059474529)
        ·
          refine ⟨59121821286340113794605897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78829095048453485059474529 59121821286340113794605897)
          ·
            refine ⟨44341365964755085345954423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59121821286340113794605897 44341365964755085345954423)
            ·
              refine ⟨66512048947132628018931635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44341365964755085345954423 66512048947132628018931635)
              ·
                refine ⟨99768073420698942028397453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66512048947132628018931635 99768073420698942028397453)
                ·
                  refine ⟨37413027532762103260649045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99768073420698942028397453 37413027532762103260649045)
                  ·
                    refine ⟨438433916399555897585731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 37413027532762103260649045 438433916399555897585731)
                    ·
                      rfl

theorem cell23_2561541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 8].length) (baseStart_2561541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561541 prefixEnd_2561541 := by exact prefixLift 2561541
  have htrace : WordTrace (prefixWord ++ tailWord_2561541) baseStart_2561541 baseEnd_2561541 := by
    simpa [prefixWord, tailWord_2561541, baseEnd_2561541] using wordTrace_append hprefix tailTrace_2561541
  have hstable : (prefixWord ++ tailWord_2561541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561541).length < 2 ^ (prefixWord ++ tailWord_2561541).sum := by decide
  have hdescent : baseEnd_2561541 < baseStart_2561541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561561 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 1, 5, 6]
def baseStart_2561561 : Nat := 118140960795 + 2561561 * 2 ^ 59
def prefixEnd_2561561 : Nat := 4983230072969 + 3 ^ 40 * 2561561 * 2
def baseEnd_2561561 : Nat := 1315312018811757614507101

theorem tailTrace_2561561 : CollatzResearch.WordTrace tailWord_2561561 prefixEnd_2561561 1315312018811757614507101 := by
  unfold tailWord_2561561
  simp only [CollatzResearch.WordTrace]
  refine ⟨93427805072909451634364537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62285203381939634422909691 93427805072909451634364537)
  ·
    refine ⟨70070853804682088725773403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93427805072909451634364537 70070853804682088725773403)
    ·
      refine ⟨105106280707023133088660105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70070853804682088725773403 105106280707023133088660105)
      ·
        refine ⟨78829710530267349816495079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105106280707023133088660105 78829710530267349816495079)
        ·
          refine ⟨118244565795401024724742619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78829710530267349816495079 118244565795401024724742619)
          ·
            refine ⟨177366848693101537087113929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118244565795401024724742619 177366848693101537087113929)
            ·
              refine ⟨133025136519826152815335447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177366848693101537087113929 133025136519826152815335447)
              ·
                refine ⟨199537704779739229223003171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133025136519826152815335447 199537704779739229223003171)
                ·
                  refine ⟨299306557169608843834504757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 199537704779739229223003171 299306557169608843834504757)
                  ·
                    refine ⟨28059989734650829109484821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 299306557169608843834504757 28059989734650829109484821)
                    ·
                      refine ⟨1315312018811757614507101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28059989734650829109484821 1315312018811757614507101)
                      ·
                        rfl

theorem cell23_2561561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_2561561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561561 prefixEnd_2561561 := by exact prefixLift 2561561
  have htrace : WordTrace (prefixWord ++ tailWord_2561561) baseStart_2561561 baseEnd_2561561 := by
    simpa [prefixWord, tailWord_2561561, baseEnd_2561561] using wordTrace_append hprefix tailTrace_2561561
  have hstable : (prefixWord ++ tailWord_2561561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561561).length < 2 ^ (prefixWord ++ tailWord_2561561).sum := by decide
  have hdescent : baseEnd_2561561 < baseStart_2561561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561576 : List Nat := [2, 1, 5, 2, 2, 1, 3, 1, 2, 1, 3]
def baseStart_2561576 : Nat := 118140960795 + 2561576 * 2 ^ 59
def prefixEnd_2561576 : Nat := 4983230072969 + 3 ^ 40 * 2561576 * 2
def baseEnd_2561576 : Nat := 1315319721021575055819533

theorem tailTrace_2561576 : CollatzResearch.WordTrace tailWord_2561576 prefixEnd_2561576 1315319721021575055819533 := by
  unfold tailWord_2561576
  simp only [CollatzResearch.WordTrace]
  refine ⟨46714176083927554598080291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62285568111903406130773721 46714176083927554598080291)
  ·
    refine ⟨70071264125891331897120437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46714176083927554598080291 70071264125891331897120437)
    ·
      refine ⟨6569181011802312365355041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70071264125891331897120437 6569181011802312365355041)
      ·
        refine ⟨4926885758851734274016281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6569181011802312365355041 4926885758851734274016281)
        ·
          refine ⟨3695164319138800705512211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4926885758851734274016281 3695164319138800705512211)
          ·
            refine ⟨5542746478708201058268317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3695164319138800705512211 5542746478708201058268317)
            ·
              refine ⟨2078529929515575396850619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5542746478708201058268317 2078529929515575396850619)
              ·
                refine ⟨3117794894273363095275929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2078529929515575396850619 3117794894273363095275929)
                ·
                  refine ⟨2338346170705022321456947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3117794894273363095275929 2338346170705022321456947)
                  ·
                    refine ⟨3507519256057533482185421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2338346170705022321456947 3507519256057533482185421)
                    ·
                      refine ⟨1315319721021575055819533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3507519256057533482185421 1315319721021575055819533)
                      ·
                        rfl

theorem cell23_2561576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_2561576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561576 prefixEnd_2561576 := by exact prefixLift 2561576
  have htrace : WordTrace (prefixWord ++ tailWord_2561576) baseStart_2561576 baseEnd_2561576 := by
    simpa [prefixWord, tailWord_2561576, baseEnd_2561576] using wordTrace_append hprefix tailTrace_2561576
  have hstable : (prefixWord ++ tailWord_2561576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561576).length < 2 ^ (prefixWord ++ tailWord_2561576).sum := by decide
  have hdescent : baseEnd_2561576 < baseStart_2561576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561655 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 4, 4, 2]
def baseStart_2561655 : Nat := 118140960795 + 2561655 * 2 ^ 59
def prefixEnd_2561655 : Nat := 4983230072969 + 3 ^ 40 * 2561655 * 2
def baseEnd_2561655 : Nat := 1315360285993280246731669

theorem tailTrace_2561655 : CollatzResearch.WordTrace tailWord_2561655 prefixEnd_2561655 1315360285993280246731669 := by
  unfold tailWord_2561655
  simp only [CollatzResearch.WordTrace]
  refine ⟨93431233534568905688286419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62287489023045937125524279 93431233534568905688286419)
  ·
    refine ⟨140146850301853358532429629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93431233534568905688286419 140146850301853358532429629)
    ·
      refine ⟨52555068863195009449661111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140146850301853358532429629 52555068863195009449661111)
      ·
        refine ⟨78832603294792514174491667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52555068863195009449661111 78832603294792514174491667)
        ·
          refine ⟨118248904942188771261737501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78832603294792514174491667 118248904942188771261737501)
          ·
            refine ⟨44343339353320789223151563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118248904942188771261737501 44343339353320789223151563)
            ·
              refine ⟨66515009029981183834727345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44343339353320789223151563 66515009029981183834727345)
              ·
                refine ⟨49886256772485887876045509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66515009029981183834727345 49886256772485887876045509)
                ·
                  refine ⟨9353673144841103976758533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49886256772485887876045509 9353673144841103976758533)
                  ·
                    refine ⟨1753813714657706995642225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9353673144841103976758533 1753813714657706995642225)
                    ·
                      refine ⟨1315360285993280246731669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1753813714657706995642225 1315360285993280246731669)
                      ·
                        rfl

theorem cell23_2561655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 4, 2].length) (baseStart_2561655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561655 prefixEnd_2561655 := by exact prefixLift 2561655
  have htrace : WordTrace (prefixWord ++ tailWord_2561655) baseStart_2561655 baseEnd_2561655 := by
    simpa [prefixWord, tailWord_2561655, baseEnd_2561655] using wordTrace_append hprefix tailTrace_2561655
  have hstable : (prefixWord ++ tailWord_2561655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561655).length < 2 ^ (prefixWord ++ tailWord_2561655).sum := by decide
  have hdescent : baseEnd_2561655 < baseStart_2561655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561675 : List Nat := [1, 1, 1, 1, 4, 1, 3, 4, 2, 2, 3]
def baseStart_2561675 : Nat := 118140960795 + 2561675 * 2 ^ 59
def prefixEnd_2561675 : Nat := 4983230072969 + 3 ^ 40 * 2561675 * 2
def baseEnd_2561675 : Nat := 1315370555606370168481577

theorem tailTrace_2561675 : CollatzResearch.WordTrace tailWord_2561675 prefixEnd_2561675 1315370555606370168481577 := by
  unfold tailWord_2561675
  simp only [CollatzResearch.WordTrace]
  refine ⟨93431962994496449104014479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62287975329664299402676319 93431962994496449104014479)
  ·
    refine ⟨140147944491744673656021719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93431962994496449104014479 140147944491744673656021719)
    ·
      refine ⟨210221916737617010484032579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140147944491744673656021719 210221916737617010484032579)
      ·
        refine ⟨315332875106425515726048869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210221916737617010484032579 315332875106425515726048869)
        ·
          refine ⟨59124914082454784198634163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 315332875106425515726048869 59124914082454784198634163)
          ·
            refine ⟨88687371123682176297951245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59124914082454784198634163 88687371123682176297951245)
            ·
              refine ⟨33257764171380816111731717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88687371123682176297951245 33257764171380816111731717)
              ·
                refine ⟨6235830782133903020949697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33257764171380816111731717 6235830782133903020949697)
                ·
                  refine ⟨4676873086600427265712273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6235830782133903020949697 4676873086600427265712273)
                  ·
                    refine ⟨3507654814950320449284205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4676873086600427265712273 3507654814950320449284205)
                    ·
                      refine ⟨1315370555606370168481577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3507654814950320449284205 1315370555606370168481577)
                      ·
                        rfl

theorem cell23_2561675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 2, 3].length) (baseStart_2561675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561675 prefixEnd_2561675 := by exact prefixLift 2561675
  have htrace : WordTrace (prefixWord ++ tailWord_2561675) baseStart_2561675 baseEnd_2561675 := by
    simpa [prefixWord, tailWord_2561675, baseEnd_2561675] using wordTrace_append hprefix tailTrace_2561675
  have hstable : (prefixWord ++ tailWord_2561675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561675).length < 2 ^ (prefixWord ++ tailWord_2561675).sum := by decide
  have hdescent : baseEnd_2561675 < baseStart_2561675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561765 : List Nat := [1, 3, 1, 4, 1, 1, 1, 2, 3, 1, 5]
def baseStart_2561765 : Nat := 118140960795 + 2561765 * 2 ^ 59
def prefixEnd_2561765 : Nat := 4983230072969 + 3 ^ 40 * 2561765 * 2
def baseEnd_2561765 : Nat := 1315416768865274816356163

theorem tailTrace_2561765 : CollatzResearch.WordTrace tailWord_2561765 prefixEnd_2561765 1315416768865274816356163 := by
  unfold tailWord_2561765
  simp only [CollatzResearch.WordTrace]
  refine ⟨93435245564170394474790749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62290163709446929649860499 93435245564170394474790749)
  ·
    refine ⟨35038217086563897928046531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93435245564170394474790749 35038217086563897928046531)
    ·
      refine ⟨52557325629845846892069797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35038217086563897928046531 52557325629845846892069797)
      ·
        refine ⟨9854498555596096292263087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52557325629845846892069797 9854498555596096292263087)
        ·
          refine ⟨14781747833394144438394631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9854498555596096292263087 14781747833394144438394631)
          ·
            refine ⟨22172621750091216657591947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14781747833394144438394631 22172621750091216657591947)
            ·
              refine ⟨33258932625136824986387921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22172621750091216657591947 33258932625136824986387921)
              ·
                refine ⟨24944199468852618739790941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33258932625136824986387921 24944199468852618739790941)
                ·
                  refine ⟨9354074800819732027421603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24944199468852618739790941 9354074800819732027421603)
                  ·
                    refine ⟨14031112201229598041132405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9354074800819732027421603 14031112201229598041132405)
                    ·
                      refine ⟨1315416768865274816356163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14031112201229598041132405 1315416768865274816356163)
                      ·
                        rfl

theorem cell23_2561765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_2561765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561765 prefixEnd_2561765 := by exact prefixLift 2561765
  have htrace : WordTrace (prefixWord ++ tailWord_2561765) baseStart_2561765 baseEnd_2561765 := by
    simpa [prefixWord, tailWord_2561765, baseEnd_2561765] using wordTrace_append hprefix tailTrace_2561765
  have hstable : (prefixWord ++ tailWord_2561765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561765).length < 2 ^ (prefixWord ++ tailWord_2561765).sum := by decide
  have hdescent : baseEnd_2561765 < baseStart_2561765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561773 : List Nat := [1, 5, 1, 2, 1, 4, 1, 3, 1, 1, 3]
def baseStart_2561773 : Nat := 118140960795 + 2561773 * 2 ^ 59
def prefixEnd_2561773 : Nat := 4983230072969 + 3 ^ 40 * 2561773 * 2
def baseEnd_2561773 : Nat := 1315420876710510785056127

theorem tailTrace_2561773 : CollatzResearch.WordTrace tailWord_2561773 prefixEnd_2561773 1315420876710510785056127 := by
  unfold tailWord_2561773
  simp only [CollatzResearch.WordTrace]
  refine ⟨93435537348141411841081973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62290358232094274560721315 93435537348141411841081973)
  ·
    refine ⟨8759581626388257360101435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93435537348141411841081973 8759581626388257360101435)
    ·
      refine ⟨13139372439582386040152153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8759581626388257360101435 13139372439582386040152153)
      ·
        refine ⟨9854529329686789530114115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13139372439582386040152153 9854529329686789530114115)
        ·
          refine ⟨14781793994530184295171173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9854529329686789530114115 14781793994530184295171173)
          ·
            refine ⟨2771586373974409555344595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14781793994530184295171173 2771586373974409555344595)
            ·
              refine ⟨4157379560961614333016893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2771586373974409555344595 4157379560961614333016893)
              ·
                refine ⟨1559017335360605374881335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4157379560961614333016893 1559017335360605374881335)
                ·
                  refine ⟨2338526003040908062322003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1559017335360605374881335 2338526003040908062322003)
                  ·
                    refine ⟨3507789004561362093483005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2338526003040908062322003 3507789004561362093483005)
                    ·
                      refine ⟨1315420876710510785056127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3507789004561362093483005 1315420876710510785056127)
                      ·
                        rfl

theorem cell23_2561773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_2561773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561773 prefixEnd_2561773 := by exact prefixLift 2561773
  have htrace : WordTrace (prefixWord ++ tailWord_2561773) baseStart_2561773 baseEnd_2561773 := by
    simpa [prefixWord, tailWord_2561773, baseEnd_2561773] using wordTrace_append hprefix tailTrace_2561773
  have hstable : (prefixWord ++ tailWord_2561773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561773).length < 2 ^ (prefixWord ++ tailWord_2561773).sum := by decide
  have hdescent : baseEnd_2561773 < baseStart_2561773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561775 : List Nat := [1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 4]
def baseStart_2561775 : Nat := 118140960795 + 2561775 * 2 ^ 59
def prefixEnd_2561775 : Nat := 4983230072969 + 3 ^ 40 * 2561775 * 2
def baseEnd_2561775 : Nat := 1315421903671819777231117

theorem tailTrace_2561775 : CollatzResearch.WordTrace tailWord_2561775 prefixEnd_2561775 1315421903671819777231117 := by
  unfold tailWord_2561775
  simp only [CollatzResearch.WordTrace]
  refine ⟨93435610294134166182654779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62290406862756110788436519 93435610294134166182654779)
  ·
    refine ⟨140153415441201249273982169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93435610294134166182654779 140153415441201249273982169)
    ·
      refine ⟨105115061580900936955486627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140153415441201249273982169 105115061580900936955486627)
      ·
        refine ⟨157672592371351405433229941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105115061580900936955486627 157672592371351405433229941)
        ·
          refine ⟨14781805534814194259365307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 157672592371351405433229941 14781805534814194259365307)
          ·
            refine ⟨22172708302221291389047961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14781805534814194259365307 22172708302221291389047961)
            ·
              refine ⟨16629531226665968541785971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22172708302221291389047961 16629531226665968541785971)
              ·
                refine ⟨24944296839998952812678957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16629531226665968541785971 24944296839998952812678957)
                ·
                  refine ⟨9354111314999607304754609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24944296839998952812678957 9354111314999607304754609)
                  ·
                    refine ⟨7015583486249705478565957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9354111314999607304754609 7015583486249705478565957)
                    ·
                      refine ⟨1315421903671819777231117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7015583486249705478565957 1315421903671819777231117)
                      ·
                        rfl

theorem cell23_2561775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 4].length) (baseStart_2561775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561775 prefixEnd_2561775 := by exact prefixLift 2561775
  have htrace : WordTrace (prefixWord ++ tailWord_2561775) baseStart_2561775 baseEnd_2561775 := by
    simpa [prefixWord, tailWord_2561775, baseEnd_2561775] using wordTrace_append hprefix tailTrace_2561775
  have hstable : (prefixWord ++ tailWord_2561775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561775).length < 2 ^ (prefixWord ++ tailWord_2561775).sum := by decide
  have hdescent : baseEnd_2561775 < baseStart_2561775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561782 : List Nat := [5, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5]
def baseStart_2561782 : Nat := 118140960795 + 2561782 * 2 ^ 59
def prefixEnd_2561782 : Nat := 4983230072969 + 3 ^ 40 * 2561782 * 2
def baseEnd_2561782 : Nat := 1315425498036401249843585

theorem tailTrace_2561782 : CollatzResearch.WordTrace tailWord_2561782 prefixEnd_2561782 1315425498036401249843585 := by
  unfold tailWord_2561782
  simp only [CollatzResearch.WordTrace]
  refine ⟨5839741600319300398634975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62290577070072537585439733 5839741600319300398634975)
  ·
    refine ⟨8759612400478950597952463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5839741600319300398634975 8759612400478950597952463)
    ·
      refine ⟨13139418600718425896928695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8759612400478950597952463 13139418600718425896928695)
      ·
        refine ⟨19709127901077638845393043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13139418600718425896928695 19709127901077638845393043)
        ·
          refine ⟨29563691851616458268089565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19709127901077638845393043 29563691851616458268089565)
          ·
            refine ⟨11086384444356171850533587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29563691851616458268089565 11086384444356171850533587)
            ·
              refine ⟨16629576666534257775800381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11086384444356171850533587 16629576666534257775800381)
              ·
                refine ⟨6236091249950346665925143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16629576666534257775800381 6236091249950346665925143)
                ·
                  refine ⟨9354136874925519998887715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6236091249950346665925143 9354136874925519998887715)
                  ·
                    refine ⟨14031205312388279998331573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9354136874925519998887715 14031205312388279998331573)
                    ·
                      refine ⟨1315425498036401249843585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14031205312388279998331573 1315425498036401249843585)
                      ·
                        rfl

theorem cell23_2561782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_2561782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561782 prefixEnd_2561782 := by exact prefixLift 2561782
  have htrace : WordTrace (prefixWord ++ tailWord_2561782) baseStart_2561782 baseEnd_2561782 := by
    simpa [prefixWord, tailWord_2561782, baseEnd_2561782] using wordTrace_append hprefix tailTrace_2561782
  have hstable : (prefixWord ++ tailWord_2561782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561782).length < 2 ^ (prefixWord ++ tailWord_2561782).sum := by decide
  have hdescent : baseEnd_2561782 < baseStart_2561782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561790 : List Nat := [4, 2, 2, 1, 3, 1, 3, 2, 1, 1, 3]
def baseStart_2561790 : Nat := 118140960795 + 2561790 * 2 ^ 59
def prefixEnd_2561790 : Nat := 4983230072969 + 3 ^ 40 * 2561790 * 2
def baseEnd_2561790 : Nat := 1315429605881637218543549

theorem tailTrace_2561790 : CollatzResearch.WordTrace tailWord_2561790 prefixEnd_2561790 1315429605881637218543549 := by
  unfold tailWord_2561790
  simp only [CollatzResearch.WordTrace]
  refine ⟨11679519673634977968056353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62290771592719882496300549 11679519673634977968056353)
  ·
    refine ⟨8759639755226233476042265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11679519673634977968056353 8759639755226233476042265)
    ·
      refine ⟨6569729816419675107031699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8759639755226233476042265 6569729816419675107031699)
      ·
        refine ⟨9854594724629512660547549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6569729816419675107031699 9854594724629512660547549)
        ·
          refine ⟨3695473021736067247705331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9854594724629512660547549 3695473021736067247705331)
          ·
            refine ⟨5543209532604100871557997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3695473021736067247705331 5543209532604100871557997)
            ·
              refine ⟨2078703574726537826834249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5543209532604100871557997 2078703574726537826834249)
              ·
                refine ⟨1559027681044903370125687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2078703574726537826834249 1559027681044903370125687)
                ·
                  refine ⟨2338541521567355055188531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1559027681044903370125687 2338541521567355055188531)
                  ·
                    refine ⟨3507812282351032582782797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2338541521567355055188531 3507812282351032582782797)
                    ·
                      refine ⟨1315429605881637218543549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3507812282351032582782797 1315429605881637218543549)
                      ·
                        rfl

theorem cell23_2561790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_2561790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561790 prefixEnd_2561790 := by exact prefixLift 2561790
  have htrace : WordTrace (prefixWord ++ tailWord_2561790) baseStart_2561790 baseEnd_2561790 := by
    simpa [prefixWord, tailWord_2561790, baseEnd_2561790] using wordTrace_append hprefix tailTrace_2561790
  have hstable : (prefixWord ++ tailWord_2561790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561790).length < 2 ^ (prefixWord ++ tailWord_2561790).sum := by decide
  have hdescent : baseEnd_2561790 < baseStart_2561790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561796 : List Nat := [2, 3, 2, 2, 1, 2, 3, 1, 3, 2, 2]
def baseStart_2561796 : Nat := 118140960795 + 2561796 * 2 ^ 59
def prefixEnd_2561796 : Nat := 4983230072969 + 3 ^ 40 * 2561796 * 2
def baseEnd_2561796 : Nat := 1315432686765564195068521

theorem tailTrace_2561796 : CollatzResearch.WordTrace tailWord_2561796 prefixEnd_2561796 1315432686765564195068521 := by
  unfold tailWord_2561796
  simp only [CollatzResearch.WordTrace]
  refine ⟨46718188113529043384584621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62290917484705391179446161 46718188113529043384584621)
  ·
    refine ⟨17519320542573391269219233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46718188113529043384584621 17519320542573391269219233)
    ·
      refine ⟨13139490406930043451914425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17519320542573391269219233 13139490406930043451914425)
      ·
        refine ⟨9854617805197532588935819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13139490406930043451914425 9854617805197532588935819)
        ·
          refine ⟨14781926707796298883403729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9854617805197532588935819 14781926707796298883403729)
          ·
            refine ⟨11086445030847224162552797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14781926707796298883403729 11086445030847224162552797)
            ·
              refine ⟨4157416886567709060957299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11086445030847224162552797 4157416886567709060957299)
              ·
                refine ⟨6236125329851563591435949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4157416886567709060957299 6236125329851563591435949)
                ·
                  refine ⟨2338546998694336346788481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6236125329851563591435949 2338546998694336346788481)
                  ·
                    refine ⟨1753910249020752260091361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2338546998694336346788481 1753910249020752260091361)
                    ·
                      refine ⟨1315432686765564195068521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1753910249020752260091361 1315432686765564195068521)
                      ·
                        rfl

theorem cell23_2561796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_2561796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561796 prefixEnd_2561796 := by exact prefixLift 2561796
  have htrace : WordTrace (prefixWord ++ tailWord_2561796) baseStart_2561796 baseEnd_2561796 := by
    simpa [prefixWord, tailWord_2561796, baseEnd_2561796] using wordTrace_append hprefix tailTrace_2561796
  have hstable : (prefixWord ++ tailWord_2561796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561796).length < 2 ^ (prefixWord ++ tailWord_2561796).sum := by decide
  have hdescent : baseEnd_2561796 < baseStart_2561796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561890 : List Nat := [3, 3, 2, 1, 2, 3, 2, 1, 1, 3, 2]
def baseStart_2561890 : Nat := 118140960795 + 2561890 * 2 ^ 59
def prefixEnd_2561890 : Nat := 4983230072969 + 3 ^ 40 * 2561890 * 2
def baseEnd_2561890 : Nat := 1315480953947086827293089

theorem tailTrace_2561890 : CollatzResearch.WordTrace tailWord_2561890 prefixEnd_2561890 1315480953947086827293089 := by
  unfold tailWord_2561890
  simp only [CollatzResearch.WordTrace]
  refine ⟨23359951172179385205772781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62293203125811693882060749 23359951172179385205772781)
  ·
    refine ⟨8759981689567269452164793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23359951172179385205772781 8759981689567269452164793)
    ·
      refine ⟨6569986267175452089123595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8759981689567269452164793 6569986267175452089123595)
      ·
        refine ⟨9854979400763178133685393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6569986267175452089123595 9854979400763178133685393)
        ·
          refine ⟨7391234550572383600264045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9854979400763178133685393 7391234550572383600264045)
          ·
            refine ⟨2771712956464643850099017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7391234550572383600264045 2771712956464643850099017)
            ·
              refine ⟨2078784717348482887574263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2771712956464643850099017 2078784717348482887574263)
              ·
                refine ⟨3118177076022724331361395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2078784717348482887574263 3118177076022724331361395)
                ·
                  refine ⟨4677265614034086497042093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3118177076022724331361395 4677265614034086497042093)
                  ·
                    refine ⟨1753974605262782436390785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4677265614034086497042093 1753974605262782436390785)
                    ·
                      refine ⟨1315480953947086827293089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1753974605262782436390785 1315480953947086827293089)
                      ·
                        rfl

theorem cell23_2561890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_2561890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561890 prefixEnd_2561890 := by exact prefixLift 2561890
  have htrace : WordTrace (prefixWord ++ tailWord_2561890) baseStart_2561890 baseEnd_2561890 := by
    simpa [prefixWord, tailWord_2561890, baseEnd_2561890] using wordTrace_append hprefix tailTrace_2561890
  have hstable : (prefixWord ++ tailWord_2561890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561890).length < 2 ^ (prefixWord ++ tailWord_2561890).sum := by decide
  have hdescent : baseEnd_2561890 < baseStart_2561890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561909 : List Nat := [1, 3, 4, 1, 1, 1, 1, 6, 5]
def baseStart_2561909 : Nat := 118140960795 + 2561909 * 2 ^ 59
def prefixEnd_2561909 : Nat := 4983230072969 + 3 ^ 40 * 2561909 * 2
def baseEnd_2561909 : Nat := 146165634453280250328389

theorem tailTrace_2561909 : CollatzResearch.WordTrace tailWord_2561909 prefixEnd_2561909 146165634453280250328389 := by
  unfold tailWord_2561909
  simp only [CollatzResearch.WordTrace]
  refine ⟨93440497675648707068032781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62293665117099138045355187 93440497675648707068032781)
  ·
    refine ⟨35040186628368265150512293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93440497675648707068032781 35040186628368265150512293)
    ·
      refine ⟨6570034992819049715721055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35040186628368265150512293 6570034992819049715721055)
      ·
        refine ⟨9855052489228574573581583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6570034992819049715721055 9855052489228574573581583)
        ·
          refine ⟨14782578733842861860372375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9855052489228574573581583 14782578733842861860372375)
          ·
            refine ⟨22173868100764292790558563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14782578733842861860372375 22173868100764292790558563)
            ·
              refine ⟨33260802151146439185837845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22173868100764292790558563 33260802151146439185837845)
              ·
                refine ⟨1559100100834989336836149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33260802151146439185837845 1559100100834989336836149)
                ·
                  refine ⟨146165634453280250328389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1559100100834989336836149 146165634453280250328389)
                  ·
                    rfl

theorem cell23_2561909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 6, 5].length) (baseStart_2561909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561909 prefixEnd_2561909 := by exact prefixLift 2561909
  have htrace : WordTrace (prefixWord ++ tailWord_2561909) baseStart_2561909 baseEnd_2561909 := by
    simpa [prefixWord, tailWord_2561909, baseEnd_2561909] using wordTrace_append hprefix tailTrace_2561909
  have hstable : (prefixWord ++ tailWord_2561909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561909).length < 2 ^ (prefixWord ++ tailWord_2561909).sum := by decide
  have hdescent : baseEnd_2561909 < baseStart_2561909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561915 : List Nat := [1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 7]
def baseStart_2561915 : Nat := 118140960795 + 2561915 * 2 ^ 59
def prefixEnd_2561915 : Nat := 4983230072969 + 3 ^ 40 * 2561915 * 2
def baseEnd_2561915 : Nat := 1315493790963449229480473

theorem tailTrace_2561915 : CollatzResearch.WordTrace tailWord_2561915 prefixEnd_2561915 1315493790963449229480473 := by
  unfold tailWord_2561915
  simp only [CollatzResearch.WordTrace]
  refine ⟨93440716513626970092751199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62293811009084646728500799 93440716513626970092751199)
  ·
    refine ⟨140161074770440455139126799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93440716513626970092751199 140161074770440455139126799)
    ·
      refine ⟨210241612155660682708690199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140161074770440455139126799 210241612155660682708690199)
      ·
        refine ⟨315362418233491024063035299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210241612155660682708690199 315362418233491024063035299)
        ·
          refine ⟨473043627350236536094552949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315362418233491024063035299 473043627350236536094552949)
          ·
            refine ⟨44347840064084675258864339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 473043627350236536094552949 44347840064084675258864339)
            ·
              refine ⟨66521760096127012888296509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44347840064084675258864339 66521760096127012888296509)
              ·
                refine ⟨24945660036047629833111191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66521760096127012888296509 24945660036047629833111191)
                ·
                  refine ⟨37418490054071444749666787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24945660036047629833111191 37418490054071444749666787)
                  ·
                    refine ⟨56127735081107167124500181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37418490054071444749666787 56127735081107167124500181)
                    ·
                      refine ⟨1315493790963449229480473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 56127735081107167124500181 1315493790963449229480473)
                      ·
                        rfl

theorem cell23_2561915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 7].length) (baseStart_2561915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561915 prefixEnd_2561915 := by exact prefixLift 2561915
  have htrace : WordTrace (prefixWord ++ tailWord_2561915) baseStart_2561915 baseEnd_2561915 := by
    simpa [prefixWord, tailWord_2561915, baseEnd_2561915] using wordTrace_append hprefix tailTrace_2561915
  have hstable : (prefixWord ++ tailWord_2561915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561915).length < 2 ^ (prefixWord ++ tailWord_2561915).sum := by decide
  have hdescent : baseEnd_2561915 < baseStart_2561915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561959 : List Nat := [1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 4]
def baseStart_2561959 : Nat := 118140960795 + 2561959 * 2 ^ 59
def prefixEnd_2561959 : Nat := 4983230072969 + 3 ^ 40 * 2561959 * 2
def baseEnd_2561959 : Nat := 1315516384112247057330271

theorem tailTrace_2561959 : CollatzResearch.WordTrace tailWord_2561959 prefixEnd_2561959 1315516384112247057330271 := by
  unfold tailWord_2561959
  simp only [CollatzResearch.WordTrace]
  refine ⟨93442321325467565607352931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62294880883645043738235287 93442321325467565607352931)
  ·
    refine ⟨140163481988201348411029397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93442321325467565607352931 140163481988201348411029397)
    ·
      refine ⟨6570163218196938206767003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 140163481988201348411029397 6570163218196938206767003)
      ·
        refine ⟨9855244827295407310150505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6570163218196938206767003 9855244827295407310150505)
        ·
          refine ⟨7391433620471555482612879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9855244827295407310150505 7391433620471555482612879)
          ·
            refine ⟨11087150430707333223919319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7391433620471555482612879 11087150430707333223919319)
            ·
              refine ⟨16630725646060999835878979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11087150430707333223919319 16630725646060999835878979)
              ·
                refine ⟨24946088469091499753818469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16630725646060999835878979 24946088469091499753818469)
                ·
                  refine ⟨4677391587954656203840963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24946088469091499753818469 4677391587954656203840963)
                  ·
                    refine ⟨7016087381931984305761445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4677391587954656203840963 7016087381931984305761445)
                    ·
                      refine ⟨1315516384112247057330271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7016087381931984305761445 1315516384112247057330271)
                      ·
                        rfl

theorem cell23_2561959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_2561959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561959 prefixEnd_2561959 := by exact prefixLift 2561959
  have htrace : WordTrace (prefixWord ++ tailWord_2561959) baseStart_2561959 baseEnd_2561959 := by
    simpa [prefixWord, tailWord_2561959, baseEnd_2561959] using wordTrace_append hprefix tailTrace_2561959
  have hstable : (prefixWord ++ tailWord_2561959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561959).length < 2 ^ (prefixWord ++ tailWord_2561959).sum := by decide
  have hdescent : baseEnd_2561959 < baseStart_2561959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561960 : List Nat := [2, 1, 6, 2, 1, 1, 3, 2, 5]
def baseStart_2561960 : Nat := 118140960795 + 2561960 * 2 ^ 59
def prefixEnd_2561960 : Nat := 4983230072969 + 3 ^ 40 * 2561960 * 2
def baseEnd_2561960 : Nat := 146168544176989061490863

theorem tailTrace_2561960 : CollatzResearch.WordTrace tailWord_2561960 prefixEnd_2561960 146168544176989061490863 := by
  unfold tailWord_2561960
  simp only [CollatzResearch.WordTrace]
  refine ⟨46721178899231971389069667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62294905198975961852092889 46721178899231971389069667)
  ·
    refine ⟨70081768348847957083604501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46721178899231971389069667 70081768348847957083604501)
    ·
      refine ⟨3285082891352247988293961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 70081768348847957083604501 3285082891352247988293961)
      ·
        refine ⟨2463812168514185991220471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3285082891352247988293961 2463812168514185991220471)
        ·
          refine ⟨3695718252771278986830707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2463812168514185991220471 3695718252771278986830707)
          ·
            refine ⟨5543577379156918480246061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3695718252771278986830707 5543577379156918480246061)
            ·
              refine ⟨2078841517183844430092273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5543577379156918480246061 2078841517183844430092273)
              ·
                refine ⟨1559131137887883322569205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2078841517183844430092273 1559131137887883322569205)
                ·
                  refine ⟨146168544176989061490863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1559131137887883322569205 146168544176989061490863)
                  ·
                    rfl

theorem cell23_2561960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 2, 5].length) (baseStart_2561960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561960 prefixEnd_2561960 := by exact prefixLift 2561960
  have htrace : WordTrace (prefixWord ++ tailWord_2561960) baseStart_2561960 baseEnd_2561960 := by
    simpa [prefixWord, tailWord_2561960, baseEnd_2561960] using wordTrace_append hprefix tailTrace_2561960
  have hstable : (prefixWord ++ tailWord_2561960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561960).length < 2 ^ (prefixWord ++ tailWord_2561960).sum := by decide
  have hdescent : baseEnd_2561960 < baseStart_2561960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561996 : List Nat := [2, 2, 1, 4, 1, 3, 2, 1, 2, 2, 3]
def baseStart_2561996 : Nat := 118140960795 + 2561996 * 2 ^ 59
def prefixEnd_2561996 : Nat := 4983230072969 + 3 ^ 40 * 2561996 * 2
def baseEnd_2561996 : Nat := 1315535382896463412567601

theorem tailTrace_2561996 : CollatzResearch.WordTrace tailWord_2561996 prefixEnd_2561996 1315535382896463412567601 := by
  unfold tailWord_2561996
  simp only [CollatzResearch.WordTrace]
  refine ⟨46721835413166760463224921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62295780550889013950966561 46721835413166760463224921)
  ·
    refine ⟨35041376559875070347418691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46721835413166760463224921 35041376559875070347418691)
    ·
      refine ⟨52562064839812605521128037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35041376559875070347418691 52562064839812605521128037)
      ·
        refine ⟨9855387157464863535211507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52562064839812605521128037 9855387157464863535211507)
        ·
          refine ⟨14783080736197295302817261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9855387157464863535211507 14783080736197295302817261)
          ·
            refine ⟨5543655276073985738556473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14783080736197295302817261 5543655276073985738556473)
            ·
              refine ⟨4157741457055489303917355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5543655276073985738556473 4157741457055489303917355)
              ·
                refine ⟨6236612185583233955876033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4157741457055489303917355 6236612185583233955876033)
                ·
                  refine ⟨4677459139187425466907025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6236612185583233955876033 4677459139187425466907025)
                  ·
                    refine ⟨3508094354390569100180269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4677459139187425466907025 3508094354390569100180269)
                    ·
                      refine ⟨1315535382896463412567601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3508094354390569100180269 1315535382896463412567601)
                      ·
                        rfl

theorem cell23_2561996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_2561996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2561996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2561996 prefixEnd_2561996 := by exact prefixLift 2561996
  have htrace : WordTrace (prefixWord ++ tailWord_2561996) baseStart_2561996 baseEnd_2561996 := by
    simpa [prefixWord, tailWord_2561996, baseEnd_2561996] using wordTrace_append hprefix tailTrace_2561996
  have hstable : (prefixWord ++ tailWord_2561996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561996).length < 2 ^ (prefixWord ++ tailWord_2561996).sum := by decide
  have hdescent : baseEnd_2561996 < baseStart_2561996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562026 : List Nat := [3, 1, 3, 1, 2, 1, 2, 3, 3, 1, 3]
def baseStart_2562026 : Nat := 118140960795 + 2562026 * 2 ^ 59
def prefixEnd_2562026 : Nat := 4983230072969 + 3 ^ 40 * 2562026 * 2
def baseEnd_2562026 : Nat := 1315550787316098295192463

theorem tailTrace_2562026 : CollatzResearch.WordTrace tailWord_2562026 prefixEnd_2562026 1315550787316098295192463 := by
  unfold tailWord_2562026
  simp only [CollatzResearch.WordTrace]
  refine ⟨23361191254056209012510483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62296510010816557366694621 23361191254056209012510483)
  ·
    refine ⟨35041786881084313518765725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23361191254056209012510483 35041786881084313518765725)
    ·
      refine ⟨13140670080406617569537147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35041786881084313518765725 13140670080406617569537147)
      ·
        refine ⟨19711005120609926354305721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13140670080406617569537147 19711005120609926354305721)
        ·
          refine ⟨14783253840457444765729291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19711005120609926354305721 14783253840457444765729291)
          ·
            refine ⟨22174880760686167148593937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14783253840457444765729291 22174880760686167148593937)
            ·
              refine ⟨16631160570514625361445453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22174880760686167148593937 16631160570514625361445453)
              ·
                refine ⟨6236685213942984510542045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16631160570514625361445453 6236685213942984510542045)
                ·
                  refine ⟨2338756955228619191453267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6236685213942984510542045 2338756955228619191453267)
                  ·
                    refine ⟨3508135432842928787179901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2338756955228619191453267 3508135432842928787179901)
                    ·
                      refine ⟨1315550787316098295192463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3508135432842928787179901 1315550787316098295192463)
                      ·
                        rfl

theorem cell23_2562026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_2562026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562026 prefixEnd_2562026 := by exact prefixLift 2562026
  have htrace : WordTrace (prefixWord ++ tailWord_2562026) baseStart_2562026 baseEnd_2562026 := by
    simpa [prefixWord, tailWord_2562026, baseEnd_2562026] using wordTrace_append hprefix tailTrace_2562026
  have hstable : (prefixWord ++ tailWord_2562026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562026).length < 2 ^ (prefixWord ++ tailWord_2562026).sum := by decide
  have hdescent : baseEnd_2562026 < baseStart_2562026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562046 : List Nat := [4, 2, 2, 2, 1, 1, 2, 1, 3, 5]
def baseStart_2562046 : Nat := 118140960795 + 2562046 * 2 ^ 59
def prefixEnd_2562046 : Nat := 4983230072969 + 3 ^ 40 * 2562046 * 2
def baseEnd_2562046 : Nat := 438520352309729405647457

theorem tailTrace_2562046 : CollatzResearch.WordTrace tailWord_2562046 prefixEnd_2562046 438520352309729405647457 := by
  unfold tailWord_2562046
  simp only [CollatzResearch.WordTrace]
  refine ⟨11680686809519047433221249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62296996317434919643846661 11680686809519047433221249)
  ·
    refine ⟨8760515107139285574915937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11680686809519047433221249 8760515107139285574915937)
    ·
      refine ⟨6570386330354464181186953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8760515107139285574915937 6570386330354464181186953)
      ·
        refine ⟨4927789747765848135890215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6570386330354464181186953 4927789747765848135890215)
        ·
          refine ⟨7391684621648772203835323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4927789747765848135890215 7391684621648772203835323)
          ·
            refine ⟨11087526932473158305752985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7391684621648772203835323 11087526932473158305752985)
            ·
              refine ⟨8315645199354868729314739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11087526932473158305752985 8315645199354868729314739)
              ·
                refine ⟨12473467799032303093972109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8315645199354868729314739 12473467799032303093972109)
                ·
                  refine ⟨4677550424637113660239541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12473467799032303093972109 4677550424637113660239541)
                  ·
                    refine ⟨438520352309729405647457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4677550424637113660239541 438520352309729405647457)
                    ·
                      rfl

theorem cell23_2562046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_2562046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562046 prefixEnd_2562046 := by exact prefixLift 2562046
  have htrace : WordTrace (prefixWord ++ tailWord_2562046) baseStart_2562046 baseEnd_2562046 := by
    simpa [prefixWord, tailWord_2562046, baseEnd_2562046] using wordTrace_append hprefix tailTrace_2562046
  have hstable : (prefixWord ++ tailWord_2562046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562046).length < 2 ^ (prefixWord ++ tailWord_2562046).sum := by decide
  have hdescent : baseEnd_2562046 < baseStart_2562046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562049 : List Nat := [1, 2, 4, 1, 2, 1, 1, 3, 3, 1, 4]
def baseStart_2562049 : Nat := 118140960795 + 2562049 * 2 ^ 59
def prefixEnd_2562049 : Nat := 4983230072969 + 3 ^ 40 * 2562049 * 2
def baseEnd_2562049 : Nat := 1315562597371151705204857

theorem tailTrace_2562049 : CollatzResearch.WordTrace tailWord_2562049 prefixEnd_2562049 1315562597371151705204857 := by
  unfold tailWord_2562049
  simp only [CollatzResearch.WordTrace]
  refine ⟨93445603895141510978129201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62297069263427673985419467 93445603895141510978129201)
  ·
    refine ⟨70084202921356133233596901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93445603895141510978129201 70084202921356133233596901)
    ·
      refine ⟨13140788047754274981299419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70084202921356133233596901 13140788047754274981299419)
      ·
        refine ⟨19711182071631412471949129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13140788047754274981299419 19711182071631412471949129)
        ·
          refine ⟨14783386553723559353961847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19711182071631412471949129 14783386553723559353961847)
          ·
            refine ⟨22175079830585339030942771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14783386553723559353961847 22175079830585339030942771)
            ·
              refine ⟨33262619745878008546414157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22175079830585339030942771 33262619745878008546414157)
              ·
                refine ⟨12473482404704253204905309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33262619745878008546414157 12473482404704253204905309)
                ·
                  refine ⟨4677555901764094951839491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12473482404704253204905309 4677555901764094951839491)
                  ·
                    refine ⟨7016333852646142427759237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4677555901764094951839491 7016333852646142427759237)
                    ·
                      refine ⟨1315562597371151705204857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7016333852646142427759237 1315562597371151705204857)
                      ·
                        rfl

theorem cell23_2562049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_2562049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562049 prefixEnd_2562049 := by exact prefixLift 2562049
  have htrace : WordTrace (prefixWord ++ tailWord_2562049) baseStart_2562049 baseEnd_2562049 := by
    simpa [prefixWord, tailWord_2562049, baseEnd_2562049] using wordTrace_append hprefix tailTrace_2562049
  have hstable : (prefixWord ++ tailWord_2562049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562049).length < 2 ^ (prefixWord ++ tailWord_2562049).sum := by decide
  have hdescent : baseEnd_2562049 < baseStart_2562049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562053 : List Nat := [1, 3, 1, 1, 2, 6, 1, 1, 2, 3, 2]
def baseStart_2562053 : Nat := 118140960795 + 2562053 * 2 ^ 59
def prefixEnd_2562053 : Nat := 4983230072969 + 3 ^ 40 * 2562053 * 2
def baseEnd_2562053 : Nat := 1315564651293769689554839

theorem tailTrace_2562053 : CollatzResearch.WordTrace tailWord_2562053 prefixEnd_2562053 1315564651293769689554839 := by
  unfold tailWord_2562053
  simp only [CollatzResearch.WordTrace]
  refine ⟨93445749787127019661274813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62297166524751346440849875 93445749787127019661274813)
  ·
    refine ⟨35042156170172632372978055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93445749787127019661274813 35042156170172632372978055)
    ·
      refine ⟨52563234255258948559467083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35042156170172632372978055 52563234255258948559467083)
      ·
        refine ⟨78844851382888422839200625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52563234255258948559467083 78844851382888422839200625)
        ·
          refine ⟨59133638537166317129400469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78844851382888422839200625 59133638537166317129400469)
          ·
            refine ⟨2771889306429671115440647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 59133638537166317129400469 2771889306429671115440647)
            ·
              refine ⟨4157833959644506673160971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2771889306429671115440647 4157833959644506673160971)
              ·
                refine ⟨6236750939466760009741457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4157833959644506673160971 6236750939466760009741457)
                ·
                  refine ⟨4677563204600070007306093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6236750939466760009741457 4677563204600070007306093)
                  ·
                    refine ⟨1754086201725026252739785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4677563204600070007306093 1754086201725026252739785)
                    ·
                      refine ⟨1315564651293769689554839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1754086201725026252739785 1315564651293769689554839)
                      ·
                        rfl

theorem cell23_2562053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 3, 2].length) (baseStart_2562053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562053 prefixEnd_2562053 := by exact prefixLift 2562053
  have htrace : WordTrace (prefixWord ++ tailWord_2562053) baseStart_2562053 baseEnd_2562053 := by
    simpa [prefixWord, tailWord_2562053, baseEnd_2562053] using wordTrace_append hprefix tailTrace_2562053
  have hstable : (prefixWord ++ tailWord_2562053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562053).length < 2 ^ (prefixWord ++ tailWord_2562053).sum := by decide
  have hdescent : baseEnd_2562053 < baseStart_2562053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562059 : List Nat := [1, 1, 1, 1, 6, 1, 2, 2, 4, 4]
def baseStart_2562059 : Nat := 118140960795 + 2562059 * 2 ^ 59
def prefixEnd_2562059 : Nat := 4983230072969 + 3 ^ 40 * 2562059 * 2
def baseEnd_2562059 : Nat := 438522577392565555359937

theorem tailTrace_2562059 : CollatzResearch.WordTrace tailWord_2562059 prefixEnd_2562059 438522577392565555359937 := by
  unfold tailWord_2562059
  simp only [CollatzResearch.WordTrace]
  refine ⟨93445968625105282685993231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62297312416736855123995487 93445968625105282685993231)
  ·
    refine ⟨140168952937657924028989847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93445968625105282685993231 140168952937657924028989847)
    ·
      refine ⟨210253429406486886043484771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140168952937657924028989847 210253429406486886043484771)
      ·
        refine ⟨315380144109730329065227157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210253429406486886043484771 315380144109730329065227157)
        ·
          refine ⟨14783444255143609174932523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 315380144109730329065227157 14783444255143609174932523)
          ·
            refine ⟨22175166382715413762398785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14783444255143609174932523 22175166382715413762398785)
            ·
              refine ⟨16631374787036560321799089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22175166382715413762398785 16631374787036560321799089)
              ·
                refine ⟨12473531090277420241349317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16631374787036560321799089 12473531090277420241349317)
                ·
                  refine ⟨2338787079427016295252997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12473531090277420241349317 2338787079427016295252997)
                  ·
                    refine ⟨438522577392565555359937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2338787079427016295252997 438522577392565555359937)
                    ·
                      rfl

theorem cell23_2562059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 4, 4].length) (baseStart_2562059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562059 prefixEnd_2562059 := by exact prefixLift 2562059
  have htrace : WordTrace (prefixWord ++ tailWord_2562059) baseStart_2562059 baseEnd_2562059 := by
    simpa [prefixWord, tailWord_2562059, baseEnd_2562059] using wordTrace_append hprefix tailTrace_2562059
  have hstable : (prefixWord ++ tailWord_2562059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562059).length < 2 ^ (prefixWord ++ tailWord_2562059).sum := by decide
  have hdescent : baseEnd_2562059 < baseStart_2562059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562072 : List Nat := [2, 1, 2, 3, 2, 1, 12]
def baseStart_2562072 : Nat := 118140960795 + 2562072 * 2 ^ 59
def prefixEnd_2562072 : Nat := 4983230072969 + 3 ^ 40 * 2562072 * 2
def baseEnd_2562072 : Nat := 16241659350940803891571

theorem tailTrace_2562072 : CollatzResearch.WordTrace tailWord_2562072 prefixEnd_2562072 16241659350940803891571 := by
  unfold tailWord_2562072
  simp only [CollatzResearch.WordTrace]
  refine ⟨46723221387029092953108235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62297628516038790604144313 46723221387029092953108235)
  ·
    refine ⟨70084832080543639429662353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46723221387029092953108235 70084832080543639429662353)
    ·
      refine ⟨52563624060407729572246765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70084832080543639429662353 52563624060407729572246765)
      ·
        refine ⟨19711359022652898589592537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52563624060407729572246765 19711359022652898589592537)
        ·
          refine ⟨14783519266989673942194403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19711359022652898589592537 14783519266989673942194403)
          ·
            refine ⟨22175278900484510913291605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14783519266989673942194403 22175278900484510913291605)
            ·
              refine ⟨16241659350940803891571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 22175278900484510913291605 16241659350940803891571)
              ·
                rfl

theorem cell23_2562072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 12].length) (baseStart_2562072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562072 prefixEnd_2562072 := by exact prefixLift 2562072
  have htrace : WordTrace (prefixWord ++ tailWord_2562072) baseStart_2562072 baseEnd_2562072 := by
    simpa [prefixWord, tailWord_2562072, baseEnd_2562072] using wordTrace_append hprefix tailTrace_2562072
  have hstable : (prefixWord ++ tailWord_2562072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562072).length < 2 ^ (prefixWord ++ tailWord_2562072).sum := by decide
  have hdescent : baseEnd_2562072 < baseStart_2562072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562076 : List Nat := [2, 2, 3, 1, 3, 2, 1, 1, 4, 4]
def baseStart_2562076 : Nat := 118140960795 + 2562076 * 2 ^ 59
def prefixEnd_2562076 : Nat := 4983230072969 + 3 ^ 40 * 2562076 * 2
def baseEnd_2562076 : Nat := 438525487116274366522411

theorem tailTrace_2562076 : CollatzResearch.WordTrace tailWord_2562076 prefixEnd_2562076 438525487116274366522411 := by
  unfold tailWord_2562076
  simp only [CollatzResearch.WordTrace]
  refine ⟨46723294333021847294681041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62297725777362463059574721 46723294333021847294681041)
  ·
    refine ⟨35042470749766385471010781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46723294333021847294681041 35042470749766385471010781)
    ·
      refine ⟨13140926531162394551629043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35042470749766385471010781 13140926531162394551629043)
      ·
        refine ⟨19711389796743591827443565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13140926531162394551629043 19711389796743591827443565)
        ·
          refine ⟨7391771173778846935291337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19711389796743591827443565 7391771173778846935291337)
          ·
            refine ⟨5543828380334135201468503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7391771173778846935291337 5543828380334135201468503)
            ·
              refine ⟨8315742570501202802202755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5543828380334135201468503 8315742570501202802202755)
              ·
                refine ⟨12473613855751804203304133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8315742570501202802202755 12473613855751804203304133)
                ·
                  refine ⟨2338802597953463288119525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12473613855751804203304133 2338802597953463288119525)
                  ·
                    refine ⟨438525487116274366522411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2338802597953463288119525 438525487116274366522411)
                    ·
                      rfl

theorem cell23_2562076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_2562076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562076 prefixEnd_2562076 := by exact prefixLift 2562076
  have htrace : WordTrace (prefixWord ++ tailWord_2562076) baseStart_2562076 baseEnd_2562076 := by
    simpa [prefixWord, tailWord_2562076, baseEnd_2562076] using wordTrace_append hprefix tailTrace_2562076
  have hstable : (prefixWord ++ tailWord_2562076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562076).length < 2 ^ (prefixWord ++ tailWord_2562076).sum := by decide
  have hdescent : baseEnd_2562076 < baseStart_2562076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562083 : List Nat := [1, 1, 1, 4, 3, 1, 4, 1, 3, 2, 2]
def baseStart_2562083 : Nat := 118140960795 + 2562083 * 2 ^ 59
def prefixEnd_2562083 : Nat := 4983230072969 + 3 ^ 40 * 2562083 * 2
def baseEnd_2562083 : Nat := 1315580055713404572179701

theorem tailTrace_2562083 : CollatzResearch.WordTrace tailWord_2562083 prefixEnd_2562083 1315580055713404572179701 := by
  unfold tailWord_2562083
  simp only [CollatzResearch.WordTrace]
  refine ⟨93446843977018334784866903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62297895984678889856577935 93446843977018334784866903)
  ·
    refine ⟨140170265965527502177300355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93446843977018334784866903 140170265965527502177300355)
    ·
      refine ⟨210255398948291253265950533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140170265965527502177300355 210255398948291253265950533)
      ·
        refine ⟨39422887302804609987365725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 210255398948291253265950533 39422887302804609987365725)
        ·
          refine ⟨14783582738551728745262147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39422887302804609987365725 14783582738551728745262147)
          ·
            refine ⟨22175374107827593117893221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14783582738551728745262147 22175374107827593117893221)
            ·
              refine ⟨4157882645217673709604979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22175374107827593117893221 4157882645217673709604979)
              ·
                refine ⟨6236823967826510564407469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4157882645217673709604979 6236823967826510564407469)
                ·
                  refine ⟨2338808987934941461652801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6236823967826510564407469 2338808987934941461652801)
                  ·
                    refine ⟨1754106740951206096239601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2338808987934941461652801 1754106740951206096239601)
                    ·
                      refine ⟨1315580055713404572179701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1754106740951206096239601 1315580055713404572179701)
                      ·
                        rfl

theorem cell23_2562083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 3, 2, 2].length) (baseStart_2562083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562083 prefixEnd_2562083 := by exact prefixLift 2562083
  have htrace : WordTrace (prefixWord ++ tailWord_2562083) baseStart_2562083 baseEnd_2562083 := by
    simpa [prefixWord, tailWord_2562083, baseEnd_2562083] using wordTrace_append hprefix tailTrace_2562083
  have hstable : (prefixWord ++ tailWord_2562083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562083).length < 2 ^ (prefixWord ++ tailWord_2562083).sum := by decide
  have hdescent : baseEnd_2562083 < baseStart_2562083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562092 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 6]
def baseStart_2562092 : Nat := 118140960795 + 2562092 * 2 ^ 59
def prefixEnd_2562092 : Nat := 4983230072969 + 3 ^ 40 * 2562092 * 2
def baseEnd_2562092 : Nat := 1315584677039295036967159

theorem tailTrace_2562092 : CollatzResearch.WordTrace tailWord_2562092 prefixEnd_2562092 1315584677039295036967159 := by
  unfold tailWord_2562092
  simp only [CollatzResearch.WordTrace]
  refine ⟨46723586116992864660972265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62298114822657152881296353 46723586116992864660972265)
  ·
    refine ⟨35042689587744648495729199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46723586116992864660972265 35042689587744648495729199)
    ·
      refine ⟨52564034381616972743593799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35042689587744648495729199 52564034381616972743593799)
      ·
        refine ⟨78846051572425459115390699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52564034381616972743593799 78846051572425459115390699)
        ·
          refine ⟨118269077358638188673086049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78846051572425459115390699 118269077358638188673086049)
          ·
            refine ⟨88701808018978641504814537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118269077358638188673086049 88701808018978641504814537)
            ·
              refine ⟨66526356014233981128610903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88701808018978641504814537 66526356014233981128610903)
              ·
                refine ⟨99789534021350971692916355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66526356014233981128610903 99789534021350971692916355)
                ·
                  refine ⟨149684301032026457539374533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99789534021350971692916355 149684301032026457539374533)
                  ·
                    refine ⟨28065806443504960788632725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 149684301032026457539374533 28065806443504960788632725)
                    ·
                      refine ⟨1315584677039295036967159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28065806443504960788632725 1315584677039295036967159)
                      ·
                        rfl

theorem cell23_2562092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_2562092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562092 prefixEnd_2562092 := by exact prefixLift 2562092
  have htrace : WordTrace (prefixWord ++ tailWord_2562092) baseStart_2562092 baseEnd_2562092 := by
    simpa [prefixWord, tailWord_2562092, baseEnd_2562092] using wordTrace_append hprefix tailTrace_2562092
  have hstable : (prefixWord ++ tailWord_2562092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562092).length < 2 ^ (prefixWord ++ tailWord_2562092).sum := by decide
  have hdescent : baseEnd_2562092 < baseStart_2562092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562096 : List Nat := [2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 4]
def baseStart_2562096 : Nat := 118140960795 + 2562096 * 2 ^ 59
def prefixEnd_2562096 : Nat := 4983230072969 + 3 ^ 40 * 2562096 * 2
def baseEnd_2562096 : Nat := 1315586730961913021317141

theorem tailTrace_2562096 : CollatzResearch.WordTrace tailWord_2562096 prefixEnd_2562096 1315586730961913021317141 := by
  unfold tailWord_2562096
  simp only [CollatzResearch.WordTrace]
  refine ⟨46723659062985619002545071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62298212083980825336726761 46723659062985619002545071)
  ·
    refine ⟨70085488594478428503817607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46723659062985619002545071 70085488594478428503817607)
    ·
      refine ⟨105128232891717642755726411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70085488594478428503817607 105128232891717642755726411)
      ·
        refine ⟨157692349337576464133589617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105128232891717642755726411 157692349337576464133589617)
        ·
          refine ⟨118269262003182348100192213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157692349337576464133589617 118269262003182348100192213)
          ·
            refine ⟨2771935828199586283598255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 118269262003182348100192213 2771935828199586283598255)
            ·
              refine ⟨4157903742299379425397383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2771935828199586283598255 4157903742299379425397383)
              ·
                refine ⟨6236855613449069138096075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4157903742299379425397383 6236855613449069138096075)
                ·
                  refine ⟨9355283420173603707144113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6236855613449069138096075 9355283420173603707144113)
                  ·
                    refine ⟨7016462565130202780358085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9355283420173603707144113 7016462565130202780358085)
                    ·
                      refine ⟨1315586730961913021317141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7016462565130202780358085 1315586730961913021317141)
                      ·
                        rfl

theorem cell23_2562096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 4].length) (baseStart_2562096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562096 prefixEnd_2562096 := by exact prefixLift 2562096
  have htrace : WordTrace (prefixWord ++ tailWord_2562096) baseStart_2562096 baseEnd_2562096 := by
    simpa [prefixWord, tailWord_2562096, baseEnd_2562096] using wordTrace_append hprefix tailTrace_2562096
  have hstable : (prefixWord ++ tailWord_2562096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562096).length < 2 ^ (prefixWord ++ tailWord_2562096).sum := by decide
  have hdescent : baseEnd_2562096 < baseStart_2562096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562100 : List Nat := [2, 5, 1, 2, 2, 1, 2, 2, 1, 1, 4]
def baseStart_2562100 : Nat := 118140960795 + 2562100 * 2 ^ 59
def prefixEnd_2562100 : Nat := 4983230072969 + 3 ^ 40 * 2562100 * 2
def baseEnd_2562100 : Nat := 1315588784884531005667123

theorem tailTrace_2562100 : CollatzResearch.WordTrace tailWord_2562100 prefixEnd_2562100 1315588784884531005667123 := by
  unfold tailWord_2562100
  simp only [CollatzResearch.WordTrace]
  refine ⟨46723732008978373344117877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62298309345304497792157169 46723732008978373344117877)
  ·
    refine ⟨4380349875841722501011051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46723732008978373344117877 4380349875841722501011051)
    ·
      refine ⟨6570524813762583751516577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4380349875841722501011051 6570524813762583751516577)
      ·
        refine ⟨4927893610321937813637433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6570524813762583751516577 4927893610321937813637433)
        ·
          refine ⟨3695920207741453360228075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4927893610321937813637433 3695920207741453360228075)
          ·
            refine ⟨5543880311612180040342113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3695920207741453360228075 5543880311612180040342113)
            ·
              refine ⟨4157910233709135030256585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5543880311612180040342113 4157910233709135030256585)
              ·
                refine ⟨3118432675281851272692439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4157910233709135030256585 3118432675281851272692439)
                ·
                  refine ⟨4677649012922776909038659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3118432675281851272692439 4677649012922776909038659)
                  ·
                    refine ⟨7016473519384165363557989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4677649012922776909038659 7016473519384165363557989)
                    ·
                      refine ⟨1315588784884531005667123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7016473519384165363557989 1315588784884531005667123)
                      ·
                        rfl

theorem cell23_2562100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_2562100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562100 prefixEnd_2562100 := by exact prefixLift 2562100
  have htrace : WordTrace (prefixWord ++ tailWord_2562100) baseStart_2562100 baseEnd_2562100 := by
    simpa [prefixWord, tailWord_2562100, baseEnd_2562100] using wordTrace_append hprefix tailTrace_2562100
  have hstable : (prefixWord ++ tailWord_2562100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562100).length < 2 ^ (prefixWord ++ tailWord_2562100).sum := by decide
  have hdescent : baseEnd_2562100 < baseStart_2562100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562134 : List Nat := [5, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2]
def baseStart_2562134 : Nat := 118140960795 + 2562134 * 2 ^ 59
def prefixEnd_2562134 : Nat := 4983230072969 + 3 ^ 40 * 2562134 * 2
def baseEnd_2562134 : Nat := 1315606243226783872641967

theorem tailTrace_2562134 : CollatzResearch.WordTrace tailWord_2562134 prefixEnd_2562134 1315606243226783872641967 := by
  unfold tailWord_2562134
  simp only [CollatzResearch.WordTrace]
  refine ⟨5840544006239598155935841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62299136066555713663315637 5840544006239598155935841)
  ·
    refine ⟨4380408004679698616951881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5840544006239598155935841 4380408004679698616951881)
    ·
      refine ⟨3285306003509773962713911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4380408004679698616951881 3285306003509773962713911)
      ·
        refine ⟨4927959005264660944070867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3285306003509773962713911 4927959005264660944070867)
        ·
          refine ⟨7391938507896991416106301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4927959005264660944070867 7391938507896991416106301)
          ·
            refine ⟨2771976940461371781039863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7391938507896991416106301 2771976940461371781039863)
            ·
              refine ⟨4157965410692057671559795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2771976940461371781039863 4157965410692057671559795)
              ·
                refine ⟨6236948116038086507339693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4157965410692057671559795 6236948116038086507339693)
                ·
                  refine ⟨2338855543514282440252385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6236948116038086507339693 2338855543514282440252385)
                  ·
                    refine ⟨1754141657635711830189289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2338855543514282440252385 1754141657635711830189289)
                    ·
                      refine ⟨1315606243226783872641967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1754141657635711830189289 1315606243226783872641967)
                      ·
                        rfl

theorem cell23_2562134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_2562134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562134 prefixEnd_2562134 := by exact prefixLift 2562134
  have htrace : WordTrace (prefixWord ++ tailWord_2562134) baseStart_2562134 baseEnd_2562134 := by
    simpa [prefixWord, tailWord_2562134, baseEnd_2562134] using wordTrace_append hprefix tailTrace_2562134
  have hstable : (prefixWord ++ tailWord_2562134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562134).length < 2 ^ (prefixWord ++ tailWord_2562134).sum := by decide
  have hdescent : baseEnd_2562134 < baseStart_2562134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562159 : List Nat := [1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 5]
def baseStart_2562159 : Nat := 118140960795 + 2562159 * 2 ^ 59
def prefixEnd_2562159 : Nat := 4983230072969 + 3 ^ 40 * 2562159 * 2
def baseEnd_2562159 : Nat := 1315619080243146274829351

theorem tailTrace_2562159 : CollatzResearch.WordTrace tailWord_2562159 prefixEnd_2562159 1315619080243146274829351 := by
  unfold tailWord_2562159
  simp only [CollatzResearch.WordTrace]
  refine ⟨93449615924742999764633531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62299743949828666509755687 93449615924742999764633531)
  ·
    refine ⟨140174423887114499646950297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93449615924742999764633531 140174423887114499646950297)
    ·
      refine ⟨105130817915335874735212723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140174423887114499646950297 105130817915335874735212723)
      ·
        refine ⟨157696226873003812102819085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105130817915335874735212723 157696226873003812102819085)
        ·
          refine ⟨59136085077376429538557157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157696226873003812102819085 59136085077376429538557157)
          ·
            refine ⟨11088015952008080538479467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59136085077376429538557157 11088015952008080538479467)
            ·
              refine ⟨16632023928012120807719201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11088015952008080538479467 16632023928012120807719201)
              ·
                refine ⟨12474017946009090605789401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16632023928012120807719201 12474017946009090605789401)
                ·
                  refine ⟨9355513459506817954342051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12474017946009090605789401 9355513459506817954342051)
                  ·
                    refine ⟨14033270189260226931513077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9355513459506817954342051 14033270189260226931513077)
                    ·
                      refine ⟨1315619080243146274829351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14033270189260226931513077 1315619080243146274829351)
                      ·
                        rfl

theorem cell23_2562159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 5].length) (baseStart_2562159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562159 prefixEnd_2562159 := by exact prefixLift 2562159
  have htrace : WordTrace (prefixWord ++ tailWord_2562159) baseStart_2562159 baseEnd_2562159 := by
    simpa [prefixWord, tailWord_2562159, baseEnd_2562159] using wordTrace_append hprefix tailTrace_2562159
  have hstable : (prefixWord ++ tailWord_2562159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562159).length < 2 ^ (prefixWord ++ tailWord_2562159).sum := by decide
  have hdescent : baseEnd_2562159 < baseStart_2562159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562160 : List Nat := [2, 1, 1, 1, 5, 4, 1, 2, 1, 3, 2]
def baseStart_2562160 : Nat := 118140960795 + 2562160 * 2 ^ 59
def prefixEnd_2562160 : Nat := 4983230072969 + 3 ^ 40 * 2562160 * 2
def baseEnd_2562160 : Nat := 1315619593723800770916847

theorem tailTrace_2562160 : CollatzResearch.WordTrace tailWord_2562160 prefixEnd_2562160 1315619593723800770916847 := by
  unfold tailWord_2562160
  simp only [CollatzResearch.WordTrace]
  refine ⟨46724826198869688467709967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62299768265159584623613289 46724826198869688467709967)
  ·
    refine ⟨70087239298304532701564951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46724826198869688467709967 70087239298304532701564951)
    ·
      refine ⟨105130858947456799052347427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70087239298304532701564951 105130858947456799052347427)
      ·
        refine ⟨157696288421185198578521141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105130858947456799052347427 157696288421185198578521141)
        ·
          refine ⟨14784027039486112366736357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 157696288421185198578521141 14784027039486112366736357)
          ·
            refine ⟨2772005069903646068763067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14784027039486112366736357 2772005069903646068763067)
            ·
              refine ⟨4158007604855469103144601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2772005069903646068763067 4158007604855469103144601)
              ·
                refine ⟨3118505703641601827358451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4158007604855469103144601 3118505703641601827358451)
                ·
                  refine ⟨4677758555462402741037677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3118505703641601827358451 4677758555462402741037677)
                  ·
                    refine ⟨1754159458298401027889129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4677758555462402741037677 1754159458298401027889129)
                    ·
                      refine ⟨1315619593723800770916847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1754159458298401027889129 1315619593723800770916847)
                      ·
                        rfl

theorem cell23_2562160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 1, 3, 2].length) (baseStart_2562160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562160 prefixEnd_2562160 := by exact prefixLift 2562160
  have htrace : WordTrace (prefixWord ++ tailWord_2562160) baseStart_2562160 baseEnd_2562160 := by
    simpa [prefixWord, tailWord_2562160, baseEnd_2562160] using wordTrace_append hprefix tailTrace_2562160
  have hstable : (prefixWord ++ tailWord_2562160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562160).length < 2 ^ (prefixWord ++ tailWord_2562160).sum := by decide
  have hdescent : baseEnd_2562160 < baseStart_2562160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562173 : List Nat := [1, 4, 1, 1, 3, 3, 1, 2, 1, 4, 2]
def baseStart_2562173 : Nat := 118140960795 + 2562173 * 2 ^ 59
def prefixEnd_2562173 : Nat := 4983230072969 + 3 ^ 40 * 2562173 * 2
def baseEnd_2562173 : Nat := 1315626268972309220054287

theorem tailTrace_2562173 : CollatzResearch.WordTrace tailWord_2562173 prefixEnd_2562173 1315626268972309220054287 := by
  unfold tailWord_2562173
  simp only [CollatzResearch.WordTrace]
  refine ⟨93450126546692280155643173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62300084364461520103762115 93450126546692280155643173)
  ·
    refine ⟨17521898727504802529183095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93450126546692280155643173 17521898727504802529183095)
    ·
      refine ⟨26282848091257203793774643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17521898727504802529183095 26282848091257203793774643)
      ·
        refine ⟨39424272136885805690661965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26282848091257203793774643 39424272136885805690661965)
        ·
          refine ⟨14784102051332177133998237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39424272136885805690661965 14784102051332177133998237)
          ·
            refine ⟨5544038269249566425249339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14784102051332177133998237 5544038269249566425249339)
            ·
              refine ⟨8316057403874349637874009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5544038269249566425249339 8316057403874349637874009)
              ·
                refine ⟨6237043052905762228405507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8316057403874349637874009 6237043052905762228405507)
                ·
                  refine ⟨9355564579358643342608261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6237043052905762228405507 9355564579358643342608261)
                  ·
                    refine ⟨1754168358629745626739049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9355564579358643342608261 1754168358629745626739049)
                    ·
                      refine ⟨1315626268972309220054287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1754168358629745626739049 1315626268972309220054287)
                      ·
                        rfl

theorem cell23_2562173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 4, 2].length) (baseStart_2562173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562173 prefixEnd_2562173 := by exact prefixLift 2562173
  have htrace : WordTrace (prefixWord ++ tailWord_2562173) baseStart_2562173 baseEnd_2562173 := by
    simpa [prefixWord, tailWord_2562173, baseEnd_2562173] using wordTrace_append hprefix tailTrace_2562173
  have hstable : (prefixWord ++ tailWord_2562173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562173).length < 2 ^ (prefixWord ++ tailWord_2562173).sum := by decide
  have hdescent : baseEnd_2562173 < baseStart_2562173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562177 : List Nat := [1, 2, 4, 2, 3, 1, 3, 1, 1, 3, 2]
def baseStart_2562177 : Nat := 118140960795 + 2562177 * 2 ^ 59
def prefixEnd_2562177 : Nat := 4983230072969 + 3 ^ 40 * 2562177 * 2
def baseEnd_2562177 : Nat := 1315628322894927204404269

theorem tailTrace_2562177 : CollatzResearch.WordTrace tailWord_2562177 prefixEnd_2562177 1315628322894927204404269 := by
  unfold tailWord_2562177
  simp only [CollatzResearch.WordTrace]
  refine ⟨93450272438677788838788785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62300181625785192559192523 93450272438677788838788785)
  ·
    refine ⟨70087704329008341629091589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93450272438677788838788785 70087704329008341629091589)
    ·
      refine ⟨13141444561689064055454673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70087704329008341629091589 13141444561689064055454673)
      ·
        refine ⟨9856083421266798041591005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13141444561689064055454673 9856083421266798041591005)
        ·
          refine ⟨3696031282975049265596627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9856083421266798041591005 3696031282975049265596627)
          ·
            refine ⟨5544046924462573898394941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3696031282975049265596627 5544046924462573898394941)
            ·
              refine ⟨2079017596673465211898103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5544046924462573898394941 2079017596673465211898103)
              ·
                refine ⟨3118526395010197817847155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2079017596673465211898103 3118526395010197817847155)
                ·
                  refine ⟨4677789592515296726770733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3118526395010197817847155 4677789592515296726770733)
                  ·
                    refine ⟨1754171097193236272539025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4677789592515296726770733 1754171097193236272539025)
                    ·
                      refine ⟨1315628322894927204404269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1754171097193236272539025 1315628322894927204404269)
                      ·
                        rfl

theorem cell23_2562177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_2562177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562177 prefixEnd_2562177 := by exact prefixLift 2562177
  have htrace : WordTrace (prefixWord ++ tailWord_2562177) baseStart_2562177 baseEnd_2562177 := by
    simpa [prefixWord, tailWord_2562177, baseEnd_2562177] using wordTrace_append hprefix tailTrace_2562177
  have hstable : (prefixWord ++ tailWord_2562177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562177).length < 2 ^ (prefixWord ++ tailWord_2562177).sum := by decide
  have hdescent : baseEnd_2562177 < baseStart_2562177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562228 : List Nat := [2, 5, 3, 1, 1, 2, 2, 1, 1, 3, 2]
def baseStart_2562228 : Nat := 118140960795 + 2562228 * 2 ^ 59
def prefixEnd_2562228 : Nat := 4983230072969 + 3 ^ 40 * 2562228 * 2
def baseEnd_2562228 : Nat := 1315654510408306504866535

theorem tailTrace_2562228 : CollatzResearch.WordTrace tailWord_2562228 prefixEnd_2562228 1315654510408306504866535 := by
  unfold tailWord_2562228
  simp only [CollatzResearch.WordTrace]
  refine ⟨46726066280746512274447669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62301421707662016365930225 46726066280746512274447669)
  ·
    refine ⟨4380568713819985525729469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46726066280746512274447669 4380568713819985525729469)
    ·
      refine ⟨1642713267682494572148551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4380568713819985525729469 1642713267682494572148551)
      ·
        refine ⟨2464069901523741858222827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1642713267682494572148551 2464069901523741858222827)
        ·
          refine ⟨3696104852285612787334241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2464069901523741858222827 3696104852285612787334241)
          ·
            refine ⟨2772078639214209590500681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3696104852285612787334241 2772078639214209590500681)
            ·
              refine ⟨2079058979410657192875511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2772078639214209590500681 2079058979410657192875511)
              ·
                refine ⟨3118588469115985789313267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2079058979410657192875511 3118588469115985789313267)
                ·
                  refine ⟨4677882703673978683969901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3118588469115985789313267 4677882703673978683969901)
                  ·
                    refine ⟨1754206013877742006488713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4677882703673978683969901 1754206013877742006488713)
                    ·
                      refine ⟨1315654510408306504866535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1754206013877742006488713 1315654510408306504866535)
                      ·
                        rfl

theorem cell23_2562228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_2562228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562228 prefixEnd_2562228 := by exact prefixLift 2562228
  have htrace : WordTrace (prefixWord ++ tailWord_2562228) baseStart_2562228 baseEnd_2562228 := by
    simpa [prefixWord, tailWord_2562228, baseEnd_2562228] using wordTrace_append hprefix tailTrace_2562228
  have hstable : (prefixWord ++ tailWord_2562228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562228).length < 2 ^ (prefixWord ++ tailWord_2562228).sum := by decide
  have hdescent : baseEnd_2562228 < baseStart_2562228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562241 : List Nat := [1, 2, 6, 1, 3, 1, 1, 2, 2, 2, 2]
def baseStart_2562241 : Nat := 118140960795 + 2562241 * 2 ^ 59
def prefixEnd_2562241 : Nat := 4983230072969 + 3 ^ 40 * 2562241 * 2
def baseEnd_2562241 : Nat := 1315661185656814954003975

theorem tailTrace_2562241 : CollatzResearch.WordTrace tailWord_2562241 prefixEnd_2562241 1315661185656814954003975 := by
  unfold tailWord_2562241
  simp only [CollatzResearch.WordTrace]
  refine ⟨93452606710445927769118577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62301737806963951846079051 93452606710445927769118577)
  ·
    refine ⟨70089455032834445826838933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93452606710445927769118577 70089455032834445826838933)
    ·
      refine ⟨3285443204664114648133075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 70089455032834445826838933 3285443204664114648133075)
      ·
        refine ⟨4928164806996171972199613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3285443204664114648133075 4928164806996171972199613)
        ·
          refine ⟨1848061802623564489574855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4928164806996171972199613 1848061802623564489574855)
          ·
            refine ⟨2772092703935346734362283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1848061802623564489574855 2772092703935346734362283)
            ·
              refine ⟨4158139055903020101543425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2772092703935346734362283 4158139055903020101543425)
              ·
                refine ⟨3118604291927265076157569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4158139055903020101543425 3118604291927265076157569)
                ·
                  refine ⟨2338953218945448807118177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3118604291927265076157569 2338953218945448807118177)
                  ·
                    refine ⟨1754214914209086605338633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2338953218945448807118177 1754214914209086605338633)
                    ·
                      refine ⟨1315661185656814954003975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1754214914209086605338633 1315661185656814954003975)
                      ·
                        rfl

theorem cell23_2562241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_2562241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562241 prefixEnd_2562241 := by exact prefixLift 2562241
  have htrace : WordTrace (prefixWord ++ tailWord_2562241) baseStart_2562241 baseEnd_2562241 := by
    simpa [prefixWord, tailWord_2562241, baseEnd_2562241] using wordTrace_append hprefix tailTrace_2562241
  have hstable : (prefixWord ++ tailWord_2562241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562241).length < 2 ^ (prefixWord ++ tailWord_2562241).sum := by decide
  have hdescent : baseEnd_2562241 < baseStart_2562241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562259 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 4]
def baseStart_2562259 : Nat := 118140960795 + 2562259 * 2 ^ 59
def prefixEnd_2562259 : Nat := 4983230072969 + 3 ^ 40 * 2562259 * 2
def baseEnd_2562259 : Nat := 1315670428308595883578891

theorem tailTrace_2562259 : CollatzResearch.WordTrace tailWord_2562259 prefixEnd_2562259 1315670428308595883578891 := by
  unfold tailWord_2562259
  simp only [CollatzResearch.WordTrace]
  refine ⟨93453263224380716843273831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62302175482920477895515887 93453263224380716843273831)
  ·
    refine ⟨140179894836571075264910747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93453263224380716843273831 140179894836571075264910747)
    ·
      refine ⟨210269842254856612897366121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140179894836571075264910747 210269842254856612897366121)
      ·
        refine ⟨157702381691142459673024591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210269842254856612897366121 157702381691142459673024591)
        ·
          refine ⟨236553572536713689509536887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157702381691142459673024591 236553572536713689509536887)
          ·
            refine ⟨354830358805070534264305331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236553572536713689509536887 354830358805070534264305331)
            ·
              refine ⟨532245538207605801396457997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 354830358805070534264305331 532245538207605801396457997)
              ·
                refine ⟨199592076827852175523671749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 532245538207605801396457997 199592076827852175523671749)
                ·
                  refine ⟨37423514405222282910688453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 199592076827852175523671749 37423514405222282910688453)
                  ·
                    refine ⟨7016908950979178045754085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37423514405222282910688453 7016908950979178045754085)
                    ·
                      refine ⟨1315670428308595883578891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7016908950979178045754085 1315670428308595883578891)
                      ·
                        rfl

theorem cell23_2562259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 4].length) (baseStart_2562259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562259 prefixEnd_2562259 := by exact prefixLift 2562259
  have htrace : WordTrace (prefixWord ++ tailWord_2562259) baseStart_2562259 baseEnd_2562259 := by
    simpa [prefixWord, tailWord_2562259, baseEnd_2562259] using wordTrace_append hprefix tailTrace_2562259
  have hstable : (prefixWord ++ tailWord_2562259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562259).length < 2 ^ (prefixWord ++ tailWord_2562259).sum := by decide
  have hdescent : baseEnd_2562259 < baseStart_2562259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562266 : List Nat := [3, 1, 1, 2, 2, 1, 3, 2, 1, 4, 3]
def baseStart_2562266 : Nat := 118140960795 + 2562266 * 2 ^ 59
def prefixEnd_2562266 : Nat := 4983230072969 + 3 ^ 40 * 2562266 * 2
def baseEnd_2562266 : Nat := 1315674022673177356191359

theorem tailTrace_2562266 : CollatzResearch.WordTrace tailWord_2562266 prefixEnd_2562266 1315674022673177356191359 := by
  unfold tailWord_2562266
  simp only [CollatzResearch.WordTrace]
  refine ⟨23363379633838839259694663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62302345690236904692519101 23363379633838839259694663)
  ·
    refine ⟨35045069450758258889541995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23363379633838839259694663 35045069450758258889541995)
    ·
      refine ⟨52567604176137388334312993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35045069450758258889541995 52567604176137388334312993)
      ·
        refine ⟨39425703132103041250734745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52567604176137388334312993 39425703132103041250734745)
        ·
          refine ⟨29569277349077280938051059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39425703132103041250734745 29569277349077280938051059)
          ·
            refine ⟨44353916023615921407076589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29569277349077280938051059 44353916023615921407076589)
            ·
              refine ⟨16632718508855970527653721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44353916023615921407076589 16632718508855970527653721)
              ·
                refine ⟨12474538881641977895740291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16632718508855970527653721 12474538881641977895740291)
                ·
                  refine ⟨18711808322462966843610437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12474538881641977895740291 18711808322462966843610437)
                  ·
                    refine ⟨3508464060461806283176957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18711808322462966843610437 3508464060461806283176957)
                    ·
                      refine ⟨1315674022673177356191359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3508464060461806283176957 1315674022673177356191359)
                      ·
                        rfl

theorem cell23_2562266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 1, 4, 3].length) (baseStart_2562266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562266 prefixEnd_2562266 := by exact prefixLift 2562266
  have htrace : WordTrace (prefixWord ++ tailWord_2562266) baseStart_2562266 baseEnd_2562266 := by
    simpa [prefixWord, tailWord_2562266, baseEnd_2562266] using wordTrace_append hprefix tailTrace_2562266
  have hstable : (prefixWord ++ tailWord_2562266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562266).length < 2 ^ (prefixWord ++ tailWord_2562266).sum := by decide
  have hdescent : baseEnd_2562266 < baseStart_2562266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562316 : List Nat := [2, 2, 1, 2, 2, 2, 2, 2, 3, 5]
def baseStart_2562316 : Nat := 118140960795 + 2562316 * 2 ^ 59
def prefixEnd_2562316 : Nat := 4983230072969 + 3 ^ 40 * 2562316 * 2
def baseEnd_2562316 : Nat := 438566565568634053522043

theorem tailTrace_2562316 : CollatzResearch.WordTrace tailWord_2562316 prefixEnd_2562316 438566565568634053522043 := by
  unfold tailWord_2562316
  simp only [CollatzResearch.WordTrace]
  refine ⟨46727671092587107789049401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62303561456782810385399201 46727671092587107789049401)
  ·
    refine ⟨35045753319440330841787051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46727671092587107789049401 35045753319440330841787051)
    ·
      refine ⟨52568629979160496262680577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35045753319440330841787051 52568629979160496262680577)
      ·
        refine ⟨39426472484370372197010433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52568629979160496262680577 39426472484370372197010433)
        ·
          refine ⟨29569854363277779147757825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39426472484370372197010433 29569854363277779147757825)
          ·
            refine ⟨22177390772458334360818369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29569854363277779147757825 22177390772458334360818369)
            ·
              refine ⟨16633043079343750770613777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22177390772458334360818369 16633043079343750770613777)
              ·
                refine ⟨12474782309507813077960333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16633043079343750770613777 12474782309507813077960333)
                ·
                  refine ⟨4678043366065429904235125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12474782309507813077960333 4678043366065429904235125)
                  ·
                    refine ⟨438566565568634053522043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4678043366065429904235125 438566565568634053522043)
                    ·
                      rfl

theorem cell23_2562316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 3, 5].length) (baseStart_2562316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562316 prefixEnd_2562316 := by exact prefixLift 2562316
  have htrace : WordTrace (prefixWord ++ tailWord_2562316) baseStart_2562316 baseEnd_2562316 := by
    simpa [prefixWord, tailWord_2562316, baseEnd_2562316] using wordTrace_append hprefix tailTrace_2562316
  have hstable : (prefixWord ++ tailWord_2562316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562316).length < 2 ^ (prefixWord ++ tailWord_2562316).sum := by decide
  have hdescent : baseEnd_2562316 < baseStart_2562316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562340 : List Nat := [2, 3, 1, 3, 1, 2, 1, 3, 2, 3, 2]
def baseStart_2562340 : Nat := 118140960795 + 2562340 * 2 ^ 59
def prefixEnd_2562340 : Nat := 4983230072969 + 3 ^ 40 * 2562340 * 2
def baseEnd_2562340 : Nat := 1315712020241610066666019

theorem tailTrace_2562340 : CollatzResearch.WordTrace tailWord_2562340 prefixEnd_2562340 1315712020241610066666019 := by
  unfold tailWord_2562340
  simp only [CollatzResearch.WordTrace]
  refine ⟨46728108768543633838486237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62304145024724845117981649 46728108768543633838486237)
  ·
    refine ⟨17523040788203862689432339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46728108768543633838486237 17523040788203862689432339)
    ·
      refine ⟨26284561182305794034148509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17523040788203862689432339 26284561182305794034148509)
      ·
        refine ⟨9856710443364672762805691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26284561182305794034148509 9856710443364672762805691)
        ·
          refine ⟨14785065665047009144208537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9856710443364672762805691 14785065665047009144208537)
          ·
            refine ⟨11088799248785256858156403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14785065665047009144208537 11088799248785256858156403)
            ·
              refine ⟨16633198873177885287234605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11088799248785256858156403 16633198873177885287234605)
              ·
                refine ⟨6237449577441706982712977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16633198873177885287234605 6237449577441706982712977)
                ·
                  refine ⟨4678087183081280237034733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6237449577441706982712977 4678087183081280237034733)
                  ·
                    refine ⟨1754282693655480088888025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4678087183081280237034733 1754282693655480088888025)
                    ·
                      refine ⟨1315712020241610066666019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1754282693655480088888025 1315712020241610066666019)
                      ·
                        rfl

theorem cell23_2562340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_2562340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562340 prefixEnd_2562340 := by exact prefixLift 2562340
  have htrace : WordTrace (prefixWord ++ tailWord_2562340) baseStart_2562340 baseEnd_2562340 := by
    simpa [prefixWord, tailWord_2562340, baseEnd_2562340] using wordTrace_append hprefix tailTrace_2562340
  have hstable : (prefixWord ++ tailWord_2562340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562340).length < 2 ^ (prefixWord ++ tailWord_2562340).sum := by decide
  have hdescent : baseEnd_2562340 < baseStart_2562340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562376 : List Nat := [2, 1, 3, 1, 1, 2, 5, 8]
def baseStart_2562376 : Nat := 118140960795 + 2562376 * 2 ^ 59
def prefixEnd_2562376 : Nat := 4983230072969 + 3 ^ 40 * 2562376 * 2
def baseEnd_2562376 : Nat := 48730759464635997252439

theorem tailTrace_2562376 : CollatzResearch.WordTrace tailWord_2562376 prefixEnd_2562376 48730759464635997252439 := by
  unfold tailWord_2562376
  simp only [CollatzResearch.WordTrace]
  refine ⟨46728765282478422912641491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62305020376637897216855321 46728765282478422912641491)
  ·
    refine ⟨70093147923717634368962237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46728765282478422912641491 70093147923717634368962237)
    ·
      refine ⟨26284930471394112888360839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70093147923717634368962237 26284930471394112888360839)
      ·
        refine ⟨39427395707091169332541259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26284930471394112888360839 39427395707091169332541259)
        ·
          refine ⟨59141093560636753998811889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39427395707091169332541259 59141093560636753998811889)
          ·
            refine ⟨44355820170477565499108917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59141093560636753998811889 44355820170477565499108917)
            ·
              refine ⟨4158358140982271765541461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44355820170477565499108917 4158358140982271765541461)
              ·
                refine ⟨48730759464635997252439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4158358140982271765541461 48730759464635997252439)
                ·
                  rfl

theorem cell23_2562376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 8].length) (baseStart_2562376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562376 prefixEnd_2562376 := by exact prefixLift 2562376
  have htrace : WordTrace (prefixWord ++ tailWord_2562376) baseStart_2562376 baseEnd_2562376 := by
    simpa [prefixWord, tailWord_2562376, baseEnd_2562376] using wordTrace_append hprefix tailTrace_2562376
  have hstable : (prefixWord ++ tailWord_2562376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562376).length < 2 ^ (prefixWord ++ tailWord_2562376).sum := by decide
  have hdescent : baseEnd_2562376 < baseStart_2562376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562403 : List Nat := [1, 1, 1, 5, 2, 1, 1, 4, 1, 3, 3]
def baseStart_2562403 : Nat := 118140960795 + 2562403 * 2 ^ 59
def prefixEnd_2562403 : Nat := 4983230072969 + 3 ^ 40 * 2562403 * 2
def baseEnd_2562403 : Nat := 1315744369522843320178229

theorem tailTrace_2562403 : CollatzResearch.WordTrace tailWord_2562403 prefixEnd_2562403 1315744369522843320178229 := by
  unfold tailWord_2562403
  simp only [CollatzResearch.WordTrace]
  refine ⟨93458515335859029436515863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62305676890572686291010575 93458515335859029436515863)
  ·
    refine ⟨140187773003788544154773795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93458515335859029436515863 140187773003788544154773795)
    ·
      refine ⟨210281659505682816232160693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140187773003788544154773795 210281659505682816232160693)
      ·
        refine ⟨19713905578657764021765065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 210281659505682816232160693 19713905578657764021765065)
        ·
          refine ⟨14785429183993323016323799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19713905578657764021765065 14785429183993323016323799)
          ·
            refine ⟨22178143775989984524485699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14785429183993323016323799 22178143775989984524485699)
            ·
              refine ⟨33267215663984976786728549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22178143775989984524485699 33267215663984976786728549)
              ·
                refine ⟨6237602936997183147511603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33267215663984976786728549 6237602936997183147511603)
                ·
                  refine ⟨9356404405495774721267405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6237602936997183147511603 9356404405495774721267405)
                  ·
                    refine ⟨3508651652060915520475277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9356404405495774721267405 3508651652060915520475277)
                    ·
                      refine ⟨1315744369522843320178229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3508651652060915520475277 1315744369522843320178229)
                      ·
                        rfl

theorem cell23_2562403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_2562403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562403 prefixEnd_2562403 := by exact prefixLift 2562403
  have htrace : WordTrace (prefixWord ++ tailWord_2562403) baseStart_2562403 baseEnd_2562403 := by
    simpa [prefixWord, tailWord_2562403, baseEnd_2562403] using wordTrace_append hprefix tailTrace_2562403
  have hstable : (prefixWord ++ tailWord_2562403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562403).length < 2 ^ (prefixWord ++ tailWord_2562403).sum := by decide
  have hdescent : baseEnd_2562403 < baseStart_2562403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562404 : List Nat := [2, 3, 1, 1, 3, 1, 4, 3, 1, 2, 2]
def baseStart_2562404 : Nat := 118140960795 + 2562404 * 2 ^ 59
def prefixEnd_2562404 : Nat := 4983230072969 + 3 ^ 40 * 2562404 * 2
def baseEnd_2562404 : Nat := 1315744883003497816265725

theorem tailTrace_2562404 : CollatzResearch.WordTrace tailWord_2562404 prefixEnd_2562404 1315744883003497816265725 := by
  unfold tailWord_2562404
  simp only [CollatzResearch.WordTrace]
  refine ⟨46729275904427703303651133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62305701205903604404868177 46729275904427703303651133)
  ·
    refine ⟨17523478464160388738869175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46729275904427703303651133 17523478464160388738869175)
    ·
      refine ⟨26285217696240583108303763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17523478464160388738869175 26285217696240583108303763)
      ·
        refine ⟨39427826544360874662455645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26285217696240583108303763 39427826544360874662455645)
        ·
          refine ⟨14785434954135327998420867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39427826544360874662455645 14785434954135327998420867)
          ·
            refine ⟨22178152431202991997631301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14785434954135327998420867 22178152431202991997631301)
            ·
              refine ⟨4158403580850560999555869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22178152431202991997631301 4158403580850560999555869)
              ·
                refine ⟨1559401342818960374833451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4158403580850560999555869 1559401342818960374833451)
                ·
                  refine ⟨2339102014228440562250177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1559401342818960374833451 2339102014228440562250177)
                  ·
                    refine ⟨1754326510671330421687633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2339102014228440562250177 1754326510671330421687633)
                    ·
                      refine ⟨1315744883003497816265725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1754326510671330421687633 1315744883003497816265725)
                      ·
                        rfl

theorem cell23_2562404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 3, 1, 2, 2].length) (baseStart_2562404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562404 prefixEnd_2562404 := by exact prefixLift 2562404
  have htrace : WordTrace (prefixWord ++ tailWord_2562404) baseStart_2562404 baseEnd_2562404 := by
    simpa [prefixWord, tailWord_2562404, baseEnd_2562404] using wordTrace_append hprefix tailTrace_2562404
  have hstable : (prefixWord ++ tailWord_2562404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562404).length < 2 ^ (prefixWord ++ tailWord_2562404).sum := by decide
  have hdescent : baseEnd_2562404 < baseStart_2562404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562407 : List Nat := [1, 1, 5, 1, 3, 1, 4, 1, 1, 2, 3]
def baseStart_2562407 : Nat := 118140960795 + 2562407 * 2 ^ 59
def prefixEnd_2562407 : Nat := 4983230072969 + 3 ^ 40 * 2562407 * 2
def baseEnd_2562407 : Nat := 1315746423445461304528211

theorem tailTrace_2562407 : CollatzResearch.WordTrace tailWord_2562407 prefixEnd_2562407 1315746423445461304528211 := by
  unfold tailWord_2562407
  simp only [CollatzResearch.WordTrace]
  refine ⟨93458661227844538119661475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62305774151896358746440983 93458661227844538119661475)
  ·
    refine ⟨140187991841766807179492213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93458661227844538119661475 140187991841766807179492213)
    ·
      refine ⟨13142624235165638173077395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 140187991841766807179492213 13142624235165638173077395)
      ·
        refine ⟨19713936352748457259616093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13142624235165638173077395 19713936352748457259616093)
        ·
          refine ⟨7392726132280671472356035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19713936352748457259616093 7392726132280671472356035)
          ·
            refine ⟨11089089198421007208534053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7392726132280671472356035 11089089198421007208534053)
            ·
              refine ⟨2079204224703938851600135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11089089198421007208534053 2079204224703938851600135)
              ·
                refine ⟨3118806337055908277400203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2079204224703938851600135 3118806337055908277400203)
                ·
                  refine ⟨4678209505583862416100305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3118806337055908277400203 4678209505583862416100305)
                  ·
                    refine ⟨3508657129187896812075229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4678209505583862416100305 3508657129187896812075229)
                    ·
                      refine ⟨1315746423445461304528211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3508657129187896812075229 1315746423445461304528211)
                      ·
                        rfl

theorem cell23_2562407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_2562407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562407 prefixEnd_2562407 := by exact prefixLift 2562407
  have htrace : WordTrace (prefixWord ++ tailWord_2562407) baseStart_2562407 baseEnd_2562407 := by
    simpa [prefixWord, tailWord_2562407, baseEnd_2562407] using wordTrace_append hprefix tailTrace_2562407
  have hstable : (prefixWord ++ tailWord_2562407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562407).length < 2 ^ (prefixWord ++ tailWord_2562407).sum := by decide
  have hdescent : baseEnd_2562407 < baseStart_2562407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562434 : List Nat := [3, 4, 2, 1, 2, 2, 1, 1, 1, 2, 4]
def baseStart_2562434 : Nat := 118140960795 + 2562434 * 2 ^ 59
def prefixEnd_2562434 : Nat := 4983230072969 + 3 ^ 40 * 2562434 * 2
def baseEnd_2562434 : Nat := 1315760287423132698890587

theorem tailTrace_2562434 : CollatzResearch.WordTrace tailWord_2562434 prefixEnd_2562434 1315760287423132698890587 := by
  unfold tailWord_2562434
  simp only [CollatzResearch.WordTrace]
  refine ⟨23364911499686680432723589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62306430665831147820596237 23364911499686680432723589)
  ·
    refine ⟨4380920906191252581135673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23364911499686680432723589 4380920906191252581135673)
    ·
      refine ⟨3285690679643439435851755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4380920906191252581135673 3285690679643439435851755)
      ·
        refine ⟨4928536019465159153777633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3285690679643439435851755 4928536019465159153777633)
        ·
          refine ⟨3696402014598869365333225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4928536019465159153777633 3696402014598869365333225)
          ·
            refine ⟨2772301510949152023999919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3696402014598869365333225 2772301510949152023999919)
            ·
              refine ⟨4158452266423728035999879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2772301510949152023999919 4158452266423728035999879)
              ·
                refine ⟨6237678399635592053999819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4158452266423728035999879 6237678399635592053999819)
                ·
                  refine ⟨9356517599453388080999729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6237678399635592053999819 9356517599453388080999729)
                  ·
                    refine ⟨7017388199590041060749797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9356517599453388080999729 7017388199590041060749797)
                    ·
                      refine ⟨1315760287423132698890587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7017388199590041060749797 1315760287423132698890587)
                      ·
                        rfl

theorem cell23_2562434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_2562434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562434 prefixEnd_2562434 := by exact prefixLift 2562434
  have htrace : WordTrace (prefixWord ++ tailWord_2562434) baseStart_2562434 baseEnd_2562434 := by
    simpa [prefixWord, tailWord_2562434, baseEnd_2562434] using wordTrace_append hprefix tailTrace_2562434
  have hstable : (prefixWord ++ tailWord_2562434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562434).length < 2 ^ (prefixWord ++ tailWord_2562434).sum := by decide
  have hdescent : baseEnd_2562434 < baseStart_2562434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562463 : List Nat := [1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 5]
def baseStart_2562463 : Nat := 118140960795 + 2562463 * 2 ^ 59
def prefixEnd_2562463 : Nat := 4983230072969 + 3 ^ 40 * 2562463 * 2
def baseEnd_2562463 : Nat := 1315775178362113085427953

theorem tailTrace_2562463 : CollatzResearch.WordTrace tailWord_2562463 prefixEnd_2562463 1315775178362113085427953 := by
  unfold tailWord_2562463
  simp only [CollatzResearch.WordTrace]
  refine ⟨93460703715641659683700043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62307135810427773122466695 93460703715641659683700043)
  ·
    refine ⟨140191055573462489525550065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93460703715641659683700043 140191055573462489525550065)
    ·
      refine ⟨105143291680096867144162549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140191055573462489525550065 105143291680096867144162549)
      ·
        refine ⟨9857183595009081294765239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105143291680096867144162549 9857183595009081294765239)
        ·
          refine ⟨14785775392513621942147859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9857183595009081294765239 14785775392513621942147859)
          ·
            refine ⟨22178663088770432913221789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14785775392513621942147859 22178663088770432913221789)
            ·
              refine ⟨8316998658288912342458171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22178663088770432913221789 8316998658288912342458171)
              ·
                refine ⟨12475497987433368513687257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8316998658288912342458171 12475497987433368513687257)
                ·
                  refine ⟨9356623490575026385265443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12475497987433368513687257 9356623490575026385265443)
                  ·
                    refine ⟨14034935235862539577898165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9356623490575026385265443 14034935235862539577898165)
                    ·
                      refine ⟨1315775178362113085427953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14034935235862539577898165 1315775178362113085427953)
                      ·
                        rfl

theorem cell23_2562463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_2562463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562463 prefixEnd_2562463 := by exact prefixLift 2562463
  have htrace : WordTrace (prefixWord ++ tailWord_2562463) baseStart_2562463 baseEnd_2562463 := by
    simpa [prefixWord, tailWord_2562463, baseEnd_2562463] using wordTrace_append hprefix tailTrace_2562463
  have hstable : (prefixWord ++ tailWord_2562463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562463).length < 2 ^ (prefixWord ++ tailWord_2562463).sum := by decide
  have hdescent : baseEnd_2562463 < baseStart_2562463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562476 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 9]
def baseStart_2562476 : Nat := 118140960795 + 2562476 * 2 ^ 59
def prefixEnd_2562476 : Nat := 4983230072969 + 3 ^ 40 * 2562476 * 2
def baseEnd_2562476 : Nat := 1315781853610621534565393

theorem tailTrace_2562476 : CollatzResearch.WordTrace tailWord_2562476 prefixEnd_2562476 1315781853610621534565393 := by
  unfold tailWord_2562476
  simp only [CollatzResearch.WordTrace]
  refine ⟨46730588932297281451961641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62307451909729708602615521 46730588932297281451961641)
  ·
    refine ⟨35047941699222961088971231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46730588932297281451961641 35047941699222961088971231)
    ·
      refine ⟨52571912548834441633456847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35047941699222961088971231 52571912548834441633456847)
      ·
        refine ⟨78857868823251662450185271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52571912548834441633456847 78857868823251662450185271)
        ·
          refine ⟨118286803234877493675277907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78857868823251662450185271 118286803234877493675277907)
          ·
            refine ⟨177430204852316240512916861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118286803234877493675277907 177430204852316240512916861)
            ·
              refine ⟨66536326819618590192343823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 177430204852316240512916861 66536326819618590192343823)
              ·
                refine ⟨99804490229427885288515735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66536326819618590192343823 99804490229427885288515735)
                ·
                  refine ⟨149706735344141827932773603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99804490229427885288515735 149706735344141827932773603)
                  ·
                    refine ⟨224560103016212741899160405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 149706735344141827932773603 224560103016212741899160405)
                    ·
                      refine ⟨1315781853610621534565393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 224560103016212741899160405 1315781853610621534565393)
                      ·
                        rfl

theorem cell23_2562476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_2562476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562476 prefixEnd_2562476 := by exact prefixLift 2562476
  have htrace : WordTrace (prefixWord ++ tailWord_2562476) baseStart_2562476 baseEnd_2562476 := by
    simpa [prefixWord, tailWord_2562476, baseEnd_2562476] using wordTrace_append hprefix tailTrace_2562476
  have hstable : (prefixWord ++ tailWord_2562476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562476).length < 2 ^ (prefixWord ++ tailWord_2562476).sum := by decide
  have hdescent : baseEnd_2562476 < baseStart_2562476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562550 : List Nat := [5, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4]
def baseStart_2562550 : Nat := 118140960795 + 2562550 * 2 ^ 59
def prefixEnd_2562550 : Nat := 4983230072969 + 3 ^ 40 * 2562550 * 2
def baseEnd_2562550 : Nat := 1315819851179054245040053

theorem tailTrace_2562550 : CollatzResearch.WordTrace tailWord_2562550 prefixEnd_2562550 1315819851179054245040053 := by
  unfold tailWord_2562550
  simp only [CollatzResearch.WordTrace]
  refine ⟨5841492304145404596382319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62309251244217649028078069 5841492304145404596382319)
  ·
    refine ⟨8762238456218106894573479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5841492304145404596382319 8762238456218106894573479)
    ·
      refine ⟨13143357684327160341860219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8762238456218106894573479 13143357684327160341860219)
      ·
        refine ⟨19715036526490740512790329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13143357684327160341860219 19715036526490740512790329)
        ·
          refine ⟨14786277394868055384592747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19715036526490740512790329 14786277394868055384592747)
          ·
            refine ⟨22179416092302083076889121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14786277394868055384592747 22179416092302083076889121)
            ·
              refine ⟨16634562069226562307666841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22179416092302083076889121 16634562069226562307666841)
              ·
                refine ⟨12475921551919921730750131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16634562069226562307666841 12475921551919921730750131)
                ·
                  refine ⟨18713882327879882596125197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12475921551919921730750131 18713882327879882596125197)
                  ·
                    refine ⟨7017705872954955973546949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18713882327879882596125197 7017705872954955973546949)
                    ·
                      refine ⟨1315819851179054245040053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7017705872954955973546949 1315819851179054245040053)
                      ·
                        rfl

theorem cell23_2562550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_2562550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562550 prefixEnd_2562550 := by exact prefixLift 2562550
  have htrace : WordTrace (prefixWord ++ tailWord_2562550) baseStart_2562550 baseEnd_2562550 := by
    simpa [prefixWord, tailWord_2562550, baseEnd_2562550] using wordTrace_append hprefix tailTrace_2562550
  have hstable : (prefixWord ++ tailWord_2562550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562550).length < 2 ^ (prefixWord ++ tailWord_2562550).sum := by decide
  have hdescent : baseEnd_2562550 < baseStart_2562550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562570 : List Nat := [3, 1, 2, 2, 2, 1, 3, 1, 1, 4, 3]
def baseStart_2562570 : Nat := 118140960795 + 2562570 * 2 ^ 59
def prefixEnd_2562570 : Nat := 4983230072969 + 3 ^ 40 * 2562570 * 2
def baseEnd_2562570 : Nat := 1315830120792144166789961

theorem tailTrace_2562570 : CollatzResearch.WordTrace tailWord_2562570 prefixEnd_2562570 1315830120792144166789961 := by
  unfold tailWord_2562570
  simp only [CollatzResearch.WordTrace]
  refine ⟨23366151581563504239461291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62309737550836011305230109 23366151581563504239461291)
  ·
    refine ⟨35049227372345256359191937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23366151581563504239461291 35049227372345256359191937)
    ·
      refine ⟨26286920529258942269393953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35049227372345256359191937 26286920529258942269393953)
      ·
        refine ⟨19715190396944206702045465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26286920529258942269393953 19715190396944206702045465)
        ·
          refine ⟨14786392797708155026534099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19715190396944206702045465 14786392797708155026534099)
          ·
            refine ⟨22179589196562232539801149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14786392797708155026534099 22179589196562232539801149)
            ·
              refine ⟨8317345948710837202425431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22179589196562232539801149 8317345948710837202425431)
              ·
                refine ⟨12476018923066255803638147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8317345948710837202425431 12476018923066255803638147)
                ·
                  refine ⟨18714028384599383705457221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12476018923066255803638147 18714028384599383705457221)
                  ·
                    refine ⟨3508880322112384444773229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18714028384599383705457221 3508880322112384444773229)
                    ·
                      refine ⟨1315830120792144166789961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3508880322112384444773229 1315830120792144166789961)
                      ·
                        rfl

theorem cell23_2562570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_2562570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562570 prefixEnd_2562570 := by exact prefixLift 2562570
  have htrace : WordTrace (prefixWord ++ tailWord_2562570) baseStart_2562570 baseEnd_2562570 := by
    simpa [prefixWord, tailWord_2562570, baseEnd_2562570] using wordTrace_append hprefix tailTrace_2562570
  have hstable : (prefixWord ++ tailWord_2562570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562570).length < 2 ^ (prefixWord ++ tailWord_2562570).sum := by decide
  have hdescent : baseEnd_2562570 < baseStart_2562570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562593 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 1, 1, 8]
def baseStart_2562593 : Nat := 118140960795 + 2562593 * 2 ^ 59
def prefixEnd_2562593 : Nat := 4983230072969 + 3 ^ 40 * 2562593 * 2
def baseEnd_2562593 : Nat := 1315841930847197576802355

theorem tailTrace_2562593 : CollatzResearch.WordTrace tailWord_2562593 prefixEnd_2562593 1315841930847197576802355 := by
  unfold tailWord_2562593
  simp only [CollatzResearch.WordTrace]
  refine ⟨93465445205170691885932433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62310296803447127923954955 93465445205170691885932433)
  ·
    refine ⟨70099083903878018914449325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93465445205170691885932433 70099083903878018914449325)
    ·
      refine ⟨26287156463954257092918497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70099083903878018914449325 26287156463954257092918497)
      ·
        refine ⟨19715367347965692819688873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26287156463954257092918497 19715367347965692819688873)
        ·
          refine ⟨14786525510974269614766655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19715367347965692819688873 14786525510974269614766655)
          ·
            refine ⟨22179788266461404422149983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14786525510974269614766655 22179788266461404422149983)
            ·
              refine ⟨33269682399692106633224975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22179788266461404422149983 33269682399692106633224975)
              ·
                refine ⟨49904523599538159949837463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33269682399692106633224975 49904523599538159949837463)
                ·
                  refine ⟨74856785399307239924756195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49904523599538159949837463 74856785399307239924756195)
                  ·
                    refine ⟨112285178098960859887134293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 74856785399307239924756195 112285178098960859887134293)
                    ·
                      refine ⟨1315841930847197576802355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 112285178098960859887134293 1315841930847197576802355)
                      ·
                        rfl

theorem cell23_2562593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_2562593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562593 prefixEnd_2562593 := by exact prefixLift 2562593
  have htrace : WordTrace (prefixWord ++ tailWord_2562593) baseStart_2562593 baseEnd_2562593 := by
    simpa [prefixWord, tailWord_2562593, baseEnd_2562593] using wordTrace_append hprefix tailTrace_2562593
  have hstable : (prefixWord ++ tailWord_2562593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562593).length < 2 ^ (prefixWord ++ tailWord_2562593).sum := by decide
  have hdescent : baseEnd_2562593 < baseStart_2562593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562603 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 5, 5]
def baseStart_2562603 : Nat := 118140960795 + 2562603 * 2 ^ 59
def prefixEnd_2562603 : Nat := 4983230072969 + 3 ^ 40 * 2562603 * 2
def baseEnd_2562603 : Nat := 438615688551247512559103

theorem tailTrace_2562603 : CollatzResearch.WordTrace tailWord_2562603 prefixEnd_2562603 438615688551247512559103 := by
  unfold tailWord_2562603
  simp only [CollatzResearch.WordTrace]
  refine ⟨93465809935134463593796463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62310539956756309062530975 93465809935134463593796463)
  ·
    refine ⟨140198714902701695390694695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93465809935134463593796463 140198714902701695390694695)
    ·
      refine ⟨210298072354052543086042043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140198714902701695390694695 210298072354052543086042043)
      ·
        refine ⟨315447108531078814629063065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210298072354052543086042043 315447108531078814629063065)
        ·
          refine ⟨236585331398309110971797299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315447108531078814629063065 236585331398309110971797299)
          ·
            refine ⟨354877997097463666457695949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236585331398309110971797299 354877997097463666457695949)
            ·
              refine ⟨133079248911548874921635981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 354877997097463666457695949 133079248911548874921635981)
              ·
                refine ⟨49904718341830828095613493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133079248911548874921635981 49904718341830828095613493)
                ·
                  refine ⟨4678567344546640133963765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49904718341830828095613493 4678567344546640133963765)
                  ·
                    refine ⟨438615688551247512559103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4678567344546640133963765 438615688551247512559103)
                    ·
                      rfl

theorem cell23_2562603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 5].length) (baseStart_2562603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562603 prefixEnd_2562603 := by exact prefixLift 2562603
  have htrace : WordTrace (prefixWord ++ tailWord_2562603) baseStart_2562603 baseEnd_2562603 := by
    simpa [prefixWord, tailWord_2562603, baseEnd_2562603] using wordTrace_append hprefix tailTrace_2562603
  have hstable : (prefixWord ++ tailWord_2562603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562603).length < 2 ^ (prefixWord ++ tailWord_2562603).sum := by decide
  have hdescent : baseEnd_2562603 < baseStart_2562603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562617 : List Nat := [1, 2, 1, 5, 1, 1, 1, 4, 3, 1, 3]
def baseStart_2562617 : Nat := 118140960795 + 2562617 * 2 ^ 59
def prefixEnd_2562617 : Nat := 4983230072969 + 3 ^ 40 * 2562617 * 2
def baseEnd_2562617 : Nat := 1315854254382905482902245

theorem tailTrace_2562617 : CollatzResearch.WordTrace tailWord_2562617 prefixEnd_2562617 1315854254382905482902245 := by
  unfold tailWord_2562617
  simp only [CollatzResearch.WordTrace]
  refine ⟨93466320557083743984806105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62310880371389162656537403 93466320557083743984806105)
  ·
    refine ⟨70099740417812807988604579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93466320557083743984806105 70099740417812807988604579)
    ·
      refine ⟨105149610626719211982906869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70099740417812807988604579 105149610626719211982906869)
      ·
        refine ⟨9857775996254926123397519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105149610626719211982906869 9857775996254926123397519)
        ·
          refine ⟨14786663994382389185096279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9857775996254926123397519 14786663994382389185096279)
          ·
            refine ⟨22179995991573583777644419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14786663994382389185096279 22179995991573583777644419)
            ·
              refine ⟨33269993987360375666466629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22179995991573583777644419 33269993987360375666466629)
              ·
                refine ⟨6238123872630070437462493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33269993987360375666466629 6238123872630070437462493)
                ·
                  refine ⟨2339296452236276414048435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6238123872630070437462493 2339296452236276414048435)
                  ·
                    refine ⟨3508944678354414621072653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2339296452236276414048435 3508944678354414621072653)
                    ·
                      refine ⟨1315854254382905482902245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3508944678354414621072653 1315854254382905482902245)
                      ·
                        rfl

theorem cell23_2562617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_2562617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562617 prefixEnd_2562617 := by exact prefixLift 2562617
  have htrace : WordTrace (prefixWord ++ tailWord_2562617) baseStart_2562617 baseEnd_2562617 := by
    simpa [prefixWord, tailWord_2562617, baseEnd_2562617] using wordTrace_append hprefix tailTrace_2562617
  have hstable : (prefixWord ++ tailWord_2562617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562617).length < 2 ^ (prefixWord ++ tailWord_2562617).sum := by decide
  have hdescent : baseEnd_2562617 < baseStart_2562617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562644 : List Nat := [2, 4, 1, 1, 1, 4, 1, 2, 2, 3, 2]
def baseStart_2562644 : Nat := 118140960795 + 2562644 * 2 ^ 59
def prefixEnd_2562644 : Nat := 4983230072969 + 3 ^ 40 * 2562644 * 2
def baseEnd_2562644 : Nat := 1315868118360576877264621

theorem tailTrace_2562644 : CollatzResearch.WordTrace tailWord_2562644 prefixEnd_2562644 1315868118360576877264621 := by
  unfold tailWord_2562644
  simp only [CollatzResearch.WordTrace]
  refine ⟨46733652663992963798019493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62311536885323951730692657 46733652663992963798019493)
  ·
    refine ⟨8762559874498680712128655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46733652663992963798019493 8762559874498680712128655)
    ·
      refine ⟨13143839811748021068192983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8762559874498680712128655 13143839811748021068192983)
      ·
        refine ⟨19715759717622031602289475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13143839811748021068192983 19715759717622031602289475)
        ·
          refine ⟨29573639576433047403434213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19715759717622031602289475 29573639576433047403434213)
          ·
            refine ⟨5545057420581196388143915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29573639576433047403434213 5545057420581196388143915)
            ·
              refine ⟨8317586130871794582215873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5545057420581196388143915 8317586130871794582215873)
              ·
                refine ⟨6238189598153845936661905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8317586130871794582215873 6238189598153845936661905)
                ·
                  refine ⟨4678642198615384452496429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6238189598153845936661905 4678642198615384452496429)
                  ·
                    refine ⟨1754490824480769169686161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4678642198615384452496429 1754490824480769169686161)
                    ·
                      refine ⟨1315868118360576877264621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1754490824480769169686161 1315868118360576877264621)
                      ·
                        rfl

theorem cell23_2562644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_2562644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562644 prefixEnd_2562644 := by exact prefixLift 2562644
  have htrace : WordTrace (prefixWord ++ tailWord_2562644) baseStart_2562644 baseEnd_2562644 := by
    simpa [prefixWord, tailWord_2562644, baseEnd_2562644] using wordTrace_append hprefix tailTrace_2562644
  have hstable : (prefixWord ++ tailWord_2562644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562644).length < 2 ^ (prefixWord ++ tailWord_2562644).sum := by decide
  have hdescent : baseEnd_2562644 < baseStart_2562644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562658 : List Nat := [3, 3, 2, 3, 2, 1, 2, 1, 6]
def baseStart_2562658 : Nat := 118140960795 + 2562658 * 2 ^ 59
def prefixEnd_2562658 : Nat := 4983230072969 + 3 ^ 40 * 2562658 * 2
def baseEnd_2562658 : Nat := 146208367454415535832173

theorem tailTrace_2562658 : CollatzResearch.WordTrace tailWord_2562658 prefixEnd_2562658 146208367454415535832173 := by
  unfold tailWord_2562658
  simp only [CollatzResearch.WordTrace]
  refine ⟨23366953987483801996762157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62311877299956805324699085 23366953987483801996762157)
  ·
    refine ⟨8762607745306425748785809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23366953987483801996762157 8762607745306425748785809)
    ·
      refine ⟨6571955808979819311589357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8762607745306425748785809 6571955808979819311589357)
      ·
        refine ⟨2464483428367432241846009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6571955808979819311589357 2464483428367432241846009)
        ·
          refine ⟨1848362571275574181384507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2464483428367432241846009 1848362571275574181384507)
          ·
            refine ⟨2772543856913361272076761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1848362571275574181384507 2772543856913361272076761)
            ·
              refine ⟨2079407892685020954057571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2772543856913361272076761 2079407892685020954057571)
              ·
                refine ⟨3119111839027531431086357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2079407892685020954057571 3119111839027531431086357)
                ·
                  refine ⟨146208367454415535832173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3119111839027531431086357 146208367454415535832173)
                  ·
                    rfl

theorem cell23_2562658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_2562658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562658 prefixEnd_2562658 := by exact prefixLift 2562658
  have htrace : WordTrace (prefixWord ++ tailWord_2562658) baseStart_2562658 baseEnd_2562658 := by
    simpa [prefixWord, tailWord_2562658, baseEnd_2562658] using wordTrace_append hprefix tailTrace_2562658
  have hstable : (prefixWord ++ tailWord_2562658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562658).length < 2 ^ (prefixWord ++ tailWord_2562658).sum := by decide
  have hdescent : baseEnd_2562658 < baseStart_2562658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562660 : List Nat := [2, 3, 1, 1, 2, 2, 1, 4, 1, 1, 5]
def baseStart_2562660 : Nat := 118140960795 + 2562660 * 2 ^ 59
def prefixEnd_2562660 : Nat := 4983230072969 + 3 ^ 40 * 2562660 * 2
def baseEnd_2562660 : Nat := 1315876334051048814664547

theorem tailTrace_2562660 : CollatzResearch.WordTrace tailWord_2562660 prefixEnd_2562660 1315876334051048814664547 := by
  unfold tailWord_2562660
  simp only [CollatzResearch.WordTrace]
  refine ⟨46733944447963981164310717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62311925930618641552414289 46733944447963981164310717)
  ·
    refine ⟨17525229167986492936616519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46733944447963981164310717 17525229167986492936616519)
    ·
      refine ⟨26287843751979739404924779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17525229167986492936616519 26287843751979739404924779)
      ·
        refine ⟨39431765627969609107387169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26287843751979739404924779 39431765627969609107387169)
        ·
          refine ⟨29573824220977206830540377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39431765627969609107387169 29573824220977206830540377)
          ·
            refine ⟨22180368165732905122905283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29573824220977206830540377 22180368165732905122905283)
            ·
              refine ⟨33270552248599357684357925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22180368165732905122905283 33270552248599357684357925)
              ·
                refine ⟨6238228546612379565817111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33270552248599357684357925 6238228546612379565817111)
                ·
                  refine ⟨9357342819918569348725667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6238228546612379565817111 9357342819918569348725667)
                  ·
                    refine ⟨14036014229877854023088501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9357342819918569348725667 14036014229877854023088501)
                    ·
                      refine ⟨1315876334051048814664547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14036014229877854023088501 1315876334051048814664547)
                      ·
                        rfl

theorem cell23_2562660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_2562660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562660 prefixEnd_2562660 := by exact prefixLift 2562660
  have htrace : WordTrace (prefixWord ++ tailWord_2562660) baseStart_2562660 baseEnd_2562660 := by
    simpa [prefixWord, tailWord_2562660, baseEnd_2562660] using wordTrace_append hprefix tailTrace_2562660
  have hstable : (prefixWord ++ tailWord_2562660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562660).length < 2 ^ (prefixWord ++ tailWord_2562660).sum := by decide
  have hdescent : baseEnd_2562660 < baseStart_2562660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562714 : List Nat := [3, 1, 1, 6, 1, 2, 1, 8]
def baseStart_2562714 : Nat := 118140960795 + 2562714 * 2 ^ 59
def prefixEnd_2562714 : Nat := 4983230072969 + 3 ^ 40 * 2562714 * 2
def baseEnd_2562714 : Nat := 48737187481718207532937

theorem tailTrace_2562714 : CollatzResearch.WordTrace tailWord_2562714 prefixEnd_2562714 48737187481718207532937 := by
  unfold tailWord_2562714
  simp only [CollatzResearch.WordTrace]
  refine ⟨23367464609433082387771799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62313238958488219700724797 23367464609433082387771799)
  ·
    refine ⟨35051196914149623581657699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23367464609433082387771799 35051196914149623581657699)
    ·
      refine ⟨52576795371224435372486549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35051196914149623581657699 52576795371224435372486549)
      ·
        refine ⟨2464537283026145408085307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 52576795371224435372486549 2464537283026145408085307)
        ·
          refine ⟨3696805924539218112127961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2464537283026145408085307 3696805924539218112127961)
          ·
            refine ⟨2772604443404413584095971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3696805924539218112127961 2772604443404413584095971)
            ·
              refine ⟨4158906665106620376143957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2772604443404413584095971 4158906665106620376143957)
              ·
                refine ⟨48737187481718207532937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4158906665106620376143957 48737187481718207532937)
                ·
                  rfl

theorem cell23_2562714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 8].length) (baseStart_2562714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562714 prefixEnd_2562714 := by exact prefixLift 2562714
  have htrace : WordTrace (prefixWord ++ tailWord_2562714) baseStart_2562714 baseEnd_2562714 := by
    simpa [prefixWord, tailWord_2562714, baseEnd_2562714] using wordTrace_append hprefix tailTrace_2562714
  have hstable : (prefixWord ++ tailWord_2562714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562714).length < 2 ^ (prefixWord ++ tailWord_2562714).sum := by decide
  have hdescent : baseEnd_2562714 < baseStart_2562714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562724 : List Nat := [2, 3, 1, 2, 2, 1, 1, 5, 2, 1, 3]
def baseStart_2562724 : Nat := 118140960795 + 2562724 * 2 ^ 59
def prefixEnd_2562724 : Nat := 4983230072969 + 3 ^ 40 * 2562724 * 2
def baseEnd_2562724 : Nat := 1315909196812936564264253

theorem tailTrace_2562724 : CollatzResearch.WordTrace tailWord_2562724 prefixEnd_2562724 1315909196812936564264253 := by
  unfold tailWord_2562724
  simp only [CollatzResearch.WordTrace]
  refine ⟨46735111583848050629475613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62313482111797400839300817 46735111583848050629475613)
  ·
    refine ⟨17525666843943018986053355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46735111583848050629475613 17525666843943018986053355)
    ·
      refine ⟨26288500265914528479080033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17525666843943018986053355 26288500265914528479080033)
      ·
        refine ⟨19716375199435896359310025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26288500265914528479080033 19716375199435896359310025)
        ·
          refine ⟨14787281399576922269482519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19716375199435896359310025 14787281399576922269482519)
          ·
            refine ⟨22180922099365383404223779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14787281399576922269482519 22180922099365383404223779)
            ·
              refine ⟨33271383149048075106335669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22180922099365383404223779 33271383149048075106335669)
              ·
                refine ⟨3119192170223257041218969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33271383149048075106335669 3119192170223257041218969)
                ·
                  refine ⟨2339394127667442780914227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3119192170223257041218969 2339394127667442780914227)
                  ·
                    refine ⟨3509091191501164171371341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2339394127667442780914227 3509091191501164171371341)
                    ·
                      refine ⟨1315909196812936564264253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3509091191501164171371341 1315909196812936564264253)
                      ·
                        rfl

theorem cell23_2562724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_2562724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562724 prefixEnd_2562724 := by exact prefixLift 2562724
  have htrace : WordTrace (prefixWord ++ tailWord_2562724) baseStart_2562724 baseEnd_2562724 := by
    simpa [prefixWord, tailWord_2562724, baseEnd_2562724] using wordTrace_append hprefix tailTrace_2562724
  have hstable : (prefixWord ++ tailWord_2562724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562724).length < 2 ^ (prefixWord ++ tailWord_2562724).sum := by decide
  have hdescent : baseEnd_2562724 < baseStart_2562724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562742 : List Nat := [5, 1, 3, 1, 2, 1, 2, 3, 1, 2, 2]
def baseStart_2562742 : Nat := 118140960795 + 2562742 * 2 ^ 59
def prefixEnd_2562742 : Nat := 4983230072969 + 3 ^ 40 * 2562742 * 2
def baseEnd_2562742 : Nat := 1315918439464717493839171

theorem tailTrace_2562742 : CollatzResearch.WordTrace tailWord_2562742 prefixEnd_2562742 1315918439464717493839171 := by
  unfold tailWord_2562742
  simp only [CollatzResearch.WordTrace]
  refine ⟨5841929980101930645819155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62313919787753926888737653 5841929980101930645819155)
  ·
    refine ⟨8762894970152895968728733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5841929980101930645819155 8762894970152895968728733)
    ·
      refine ⟨3286085613807335988273275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8762894970152895968728733 3286085613807335988273275)
      ·
        refine ⟨4929128420711003982409913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3286085613807335988273275 4929128420711003982409913)
        ·
          refine ⟨3696846315533252986807435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4929128420711003982409913 3696846315533252986807435)
          ·
            refine ⟨5545269473299879480211153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3696846315533252986807435 5545269473299879480211153)
            ·
              refine ⟨4158952104974909610158365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5545269473299879480211153 4158952104974909610158365)
              ·
                refine ⟨1559607039365591103809387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4158952104974909610158365 1559607039365591103809387)
                ·
                  refine ⟨2339410559048386655714081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1559607039365591103809387 2339410559048386655714081)
                  ·
                    refine ⟨1754557919286289991785561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2339410559048386655714081 1754557919286289991785561)
                    ·
                      refine ⟨1315918439464717493839171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1754557919286289991785561 1315918439464717493839171)
                      ·
                        rfl

theorem cell23_2562742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_2562742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562742 prefixEnd_2562742 := by exact prefixLift 2562742
  have htrace : WordTrace (prefixWord ++ tailWord_2562742) baseStart_2562742 baseEnd_2562742 := by
    simpa [prefixWord, tailWord_2562742, baseEnd_2562742] using wordTrace_append hprefix tailTrace_2562742
  have hstable : (prefixWord ++ tailWord_2562742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562742).length < 2 ^ (prefixWord ++ tailWord_2562742).sum := by decide
  have hdescent : baseEnd_2562742 < baseStart_2562742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562751 : List Nat := [1, 1, 2, 2, 2, 4, 4, 1, 1, 3, 2]
def baseStart_2562751 : Nat := 118140960795 + 2562751 * 2 ^ 59
def prefixEnd_2562751 : Nat := 4983230072969 + 3 ^ 40 * 2562751 * 2
def baseEnd_2562751 : Nat := 1315923060790607958626629

theorem tailTrace_2562751 : CollatzResearch.WordTrace tailWord_2562751 prefixEnd_2562751 1315923060790607958626629 := by
  unfold tailWord_2562751
  simp only [CollatzResearch.WordTrace]
  refine ⟨93471207938598284870184107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62314138625732189913456071 93471207938598284870184107)
  ·
    refine ⟨140206811907897427305276161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93471207938598284870184107 140206811907897427305276161)
    ·
      refine ⟨105155108930923070478957121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140206811907897427305276161 105155108930923070478957121)
      ·
        refine ⟨78866331698192302859217841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105155108930923070478957121 78866331698192302859217841)
        ·
          refine ⟨59149748773644227144413381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78866331698192302859217841 59149748773644227144413381)
          ·
            refine ⟨11090577895058292589577509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59149748773644227144413381 11090577895058292589577509)
            ·
              refine ⟨2079483355323429860545783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11090577895058292589577509 2079483355323429860545783)
              ·
                refine ⟨3119225032985144790818675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2079483355323429860545783 3119225032985144790818675)
                ·
                  refine ⟨4678837549477717186228013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3119225032985144790818675 4678837549477717186228013)
                  ·
                    refine ⟨1754564081054143944835505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4678837549477717186228013 1754564081054143944835505)
                    ·
                      refine ⟨1315923060790607958626629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1754564081054143944835505 1315923060790607958626629)
                      ·
                        rfl

theorem cell23_2562751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 1, 3, 2].length) (baseStart_2562751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562751 prefixEnd_2562751 := by exact prefixLift 2562751
  have htrace : WordTrace (prefixWord ++ tailWord_2562751) baseStart_2562751 baseEnd_2562751 := by
    simpa [prefixWord, tailWord_2562751, baseEnd_2562751] using wordTrace_append hprefix tailTrace_2562751
  have hstable : (prefixWord ++ tailWord_2562751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562751).length < 2 ^ (prefixWord ++ tailWord_2562751).sum := by decide
  have hdescent : baseEnd_2562751 < baseStart_2562751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562787 : List Nat := [1, 1, 1, 7, 1, 1, 2, 2, 7]
def baseStart_2562787 : Nat := 118140960795 + 2562787 * 2 ^ 59
def prefixEnd_2562787 : Nat := 4983230072969 + 3 ^ 40 * 2562787 * 2
def baseEnd_2562787 : Nat := 146215727343796646419607

theorem tailTrace_2562787 : CollatzResearch.WordTrace tailWord_2562787 prefixEnd_2562787 146215727343796646419607 := by
  unfold tailWord_2562787
  simp only [CollatzResearch.WordTrace]
  refine ⟨93472520966467863018494615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62315013977645242012329743 93472520966467863018494615)
  ·
    refine ⟨140208781449701794527741923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93472520966467863018494615 140208781449701794527741923)
    ·
      refine ⟨210313172174552691791612885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140208781449701794527741923 210313172174552691791612885)
      ·
        refine ⟨4929214972841078713865927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 210313172174552691791612885 4929214972841078713865927)
        ·
          refine ⟨7393822459261618070798891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4929214972841078713865927 7393822459261618070798891)
          ·
            refine ⟨11090733688892427106198337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7393822459261618070798891 11090733688892427106198337)
            ·
              refine ⟨8318050266669320329648753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11090733688892427106198337 8318050266669320329648753)
              ·
                refine ⟨6238537700001990247236565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8318050266669320329648753 6238537700001990247236565)
                ·
                  refine ⟨146215727343796646419607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6238537700001990247236565 146215727343796646419607)
                  ·
                    rfl

theorem cell23_2562787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 7].length) (baseStart_2562787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562787 prefixEnd_2562787 := by exact prefixLift 2562787
  have htrace : WordTrace (prefixWord ++ tailWord_2562787) baseStart_2562787 baseEnd_2562787 := by
    simpa [prefixWord, tailWord_2562787, baseEnd_2562787] using wordTrace_append hprefix tailTrace_2562787
  have hstable : (prefixWord ++ tailWord_2562787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562787).length < 2 ^ (prefixWord ++ tailWord_2562787).sum := by decide
  have hdescent : baseEnd_2562787 < baseStart_2562787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562800 : List Nat := [2, 1, 1, 1, 3, 1, 3, 3, 1, 7]
def baseStart_2562800 : Nat := 118140960795 + 2562800 * 2 ^ 59
def prefixEnd_2562800 : Nat := 4983230072969 + 3 ^ 40 * 2562800 * 2
def baseEnd_2562800 : Nat := 438649407114226088971301

theorem tailTrace_2562800 : CollatzResearch.WordTrace tailWord_2562800 prefixEnd_2562800 438649407114226088971301 := by
  unfold tailWord_2562800
  simp only [CollatzResearch.WordTrace]
  refine ⟨46736497557710383119358927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62315330076947177492478569 46736497557710383119358927)
  ·
    refine ⟨70104746336565574679038391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46736497557710383119358927 70104746336565574679038391)
    ·
      refine ⟨105157119504848362018557587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70104746336565574679038391 105157119504848362018557587)
      ·
        refine ⟨157735679257272543027836381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105157119504848362018557587 157735679257272543027836381)
        ·
          refine ⟨59150879721477203635438643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157735679257272543027836381 59150879721477203635438643)
          ·
            refine ⟨88726319582215805453157965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59150879721477203635438643 88726319582215805453157965)
            ·
              refine ⟨33272369843330927044934237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88726319582215805453157965 33272369843330927044934237)
              ·
                refine ⟨12477138691249097641850339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33272369843330927044934237 12477138691249097641850339)
                ·
                  refine ⟨18715708036873646462775509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12477138691249097641850339 18715708036873646462775509)
                  ·
                    refine ⟨438649407114226088971301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18715708036873646462775509 438649407114226088971301)
                    ·
                      rfl

theorem cell23_2562800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 1, 7].length) (baseStart_2562800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562800 prefixEnd_2562800 := by exact prefixLift 2562800
  have htrace : WordTrace (prefixWord ++ tailWord_2562800) baseStart_2562800 baseEnd_2562800 := by
    simpa [prefixWord, tailWord_2562800, baseEnd_2562800] using wordTrace_append hprefix tailTrace_2562800
  have hstable : (prefixWord ++ tailWord_2562800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562800).length < 2 ^ (prefixWord ++ tailWord_2562800).sum := by decide
  have hdescent : baseEnd_2562800 < baseStart_2562800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562807 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 1, 7, 2]
def baseStart_2562807 : Nat := 118140960795 + 2562807 * 2 ^ 59
def prefixEnd_2562807 : Nat := 4983230072969 + 3 ^ 40 * 2562807 * 2
def baseEnd_2562807 : Nat := 1315951815707259739526371

theorem tailTrace_2562807 : CollatzResearch.WordTrace tailWord_2562807 prefixEnd_2562807 1315951815707259739526371 := by
  unfold tailWord_2562807
  simp only [CollatzResearch.WordTrace]
  refine ⟨93473250426395406434222675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62315500284263604289481783 93473250426395406434222675)
  ·
    refine ⟨140209875639593109651334013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93473250426395406434222675 140209875639593109651334013)
    ·
      refine ⟨52578703364847416119250255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140209875639593109651334013 52578703364847416119250255)
      ·
        refine ⟨78868055047271124178875383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52578703364847416119250255 78868055047271124178875383)
        ·
          refine ⟨118302082570906686268313075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78868055047271124178875383 118302082570906686268313075)
          ·
            refine ⟨177453123856360029402469613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118302082570906686268313075 177453123856360029402469613)
            ·
              refine ⟨66544921446135011025926105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 177453123856360029402469613 66544921446135011025926105)
              ·
                refine ⟨49908691084601258269444579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66544921446135011025926105 49908691084601258269444579)
                ·
                  refine ⟨74863036626901887404166869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49908691084601258269444579 74863036626901887404166869)
                  ·
                    refine ⟨1754602420943012986035161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 74863036626901887404166869 1754602420943012986035161)
                    ·
                      refine ⟨1315951815707259739526371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1754602420943012986035161 1315951815707259739526371)
                      ·
                        rfl

theorem cell23_2562807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 7, 2].length) (baseStart_2562807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562807 prefixEnd_2562807 := by exact prefixLift 2562807
  have htrace : WordTrace (prefixWord ++ tailWord_2562807) baseStart_2562807 baseEnd_2562807 := by
    simpa [prefixWord, tailWord_2562807, baseEnd_2562807] using wordTrace_append hprefix tailTrace_2562807
  have hstable : (prefixWord ++ tailWord_2562807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562807).length < 2 ^ (prefixWord ++ tailWord_2562807).sum := by decide
  have hdescent : baseEnd_2562807 < baseStart_2562807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562837 : List Nat := [1, 3, 2, 1, 2, 2, 1, 2, 4, 1, 4]
def baseStart_2562837 : Nat := 118140960795 + 2562837 * 2 ^ 59
def prefixEnd_2562837 : Nat := 4983230072969 + 3 ^ 40 * 2562837 * 2
def baseEnd_2562837 : Nat := 1315967220126894622151233

theorem tailTrace_2562837 : CollatzResearch.WordTrace tailWord_2562837 prefixEnd_2562837 1315967220126894622151233 := by
  unfold tailWord_2562837
  simp only [CollatzResearch.WordTrace]
  refine ⟨93474344616286721557814765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62316229744191147705209843 93474344616286721557814765)
  ·
    refine ⟨35052879231107520584180537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93474344616286721557814765 35052879231107520584180537)
    ·
      refine ⟨26289659423330640438135403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35052879231107520584180537 26289659423330640438135403)
      ·
        refine ⟨39434489134995960657203105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26289659423330640438135403 39434489134995960657203105)
        ·
          refine ⟨29575866851246970492902329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39434489134995960657203105 29575866851246970492902329)
          ·
            refine ⟨22181900138435227869676747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29575866851246970492902329 22181900138435227869676747)
            ·
              refine ⟨33272850207652841804515121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22181900138435227869676747 33272850207652841804515121)
              ·
                refine ⟨24954637655739631353386341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33272850207652841804515121 24954637655739631353386341)
                ·
                  refine ⟨4678994560451180878759939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24954637655739631353386341 4678994560451180878759939)
                  ·
                    refine ⟨7018491840676771318139909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4678994560451180878759939 7018491840676771318139909)
                    ·
                      refine ⟨1315967220126894622151233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7018491840676771318139909 1315967220126894622151233)
                      ·
                        rfl

theorem cell23_2562837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_2562837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562837 prefixEnd_2562837 := by exact prefixLift 2562837
  have htrace : WordTrace (prefixWord ++ tailWord_2562837) baseStart_2562837 baseEnd_2562837 := by
    simpa [prefixWord, tailWord_2562837, baseEnd_2562837] using wordTrace_append hprefix tailTrace_2562837
  have hstable : (prefixWord ++ tailWord_2562837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562837).length < 2 ^ (prefixWord ++ tailWord_2562837).sum := by decide
  have hdescent : baseEnd_2562837 < baseStart_2562837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562857 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 6, 2, 3]
def baseStart_2562857 : Nat := 118140960795 + 2562857 * 2 ^ 59
def prefixEnd_2562857 : Nat := 4983230072969 + 3 ^ 40 * 2562857 * 2
def baseEnd_2562857 : Nat := 1315977489739984543901141

theorem tailTrace_2562857 : CollatzResearch.WordTrace tailWord_2562857 prefixEnd_2562857 1315977489739984543901141 := by
  unfold tailWord_2562857
  simp only [CollatzResearch.WordTrace]
  refine ⟨93475074076214264973542825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62316716050809509982361883 93475074076214264973542825)
  ·
    refine ⟨70106305557160698730157119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93475074076214264973542825 70106305557160698730157119)
    ·
      refine ⟨105159458335741048095235679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70106305557160698730157119 105159458335741048095235679)
      ·
        refine ⟨157739187503611572142853519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105159458335741048095235679 157739187503611572142853519)
        ·
          refine ⟨236608781255417358214280279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157739187503611572142853519 236608781255417358214280279)
          ·
            refine ⟨354913171883126037321420419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236608781255417358214280279 354913171883126037321420419)
            ·
              refine ⟨532369757824689055982130629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 354913171883126037321420419 532369757824689055982130629)
              ·
                refine ⟨99819329592129197996649493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 532369757824689055982130629 99819329592129197996649493)
                ·
                  refine ⟨4679031074631056156092945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 99819329592129197996649493 4679031074631056156092945)
                  ·
                    refine ⟨3509273305973292117069709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4679031074631056156092945 3509273305973292117069709)
                    ·
                      refine ⟨1315977489739984543901141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3509273305973292117069709 1315977489739984543901141)
                      ·
                        rfl

theorem cell23_2562857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 2, 3].length) (baseStart_2562857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562857 prefixEnd_2562857 := by exact prefixLift 2562857
  have htrace : WordTrace (prefixWord ++ tailWord_2562857) baseStart_2562857 baseEnd_2562857 := by
    simpa [prefixWord, tailWord_2562857, baseEnd_2562857] using wordTrace_append hprefix tailTrace_2562857
  have hstable : (prefixWord ++ tailWord_2562857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562857).length < 2 ^ (prefixWord ++ tailWord_2562857).sum := by decide
  have hdescent : baseEnd_2562857 < baseStart_2562857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562887 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 2, 5, 3]
def baseStart_2562887 : Nat := 118140960795 + 2562887 * 2 ^ 59
def prefixEnd_2562887 : Nat := 4983230072969 + 3 ^ 40 * 2562887 * 2
def baseEnd_2562887 : Nat := 1315992894159619426526003

theorem tailTrace_2562887 : CollatzResearch.WordTrace tailWord_2562887 prefixEnd_2562887 1315992894159619426526003 := by
  unfold tailWord_2562887
  simp only [CollatzResearch.WordTrace]
  refine ⟨93476168266105580097134915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62317445510737053398089943 93476168266105580097134915)
  ·
    refine ⟨140214252399158370145702373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93476168266105580097134915 140214252399158370145702373)
    ·
      refine ⟨26290172324842194402319195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140214252399158370145702373 26290172324842194402319195)
      ·
        refine ⟨39435258487263291603478793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26290172324842194402319195 39435258487263291603478793)
        ·
          refine ⟨29576443865447468702609095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39435258487263291603478793 29576443865447468702609095)
          ·
            refine ⟨44364665798171203053913643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29576443865447468702609095 44364665798171203053913643)
            ·
              refine ⟨66546998697256804580870465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44364665798171203053913643 66546998697256804580870465)
              ·
                refine ⟨49910249022942603435652849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66546998697256804580870465 49910249022942603435652849)
                ·
                  refine ⟨37432686767206952576739637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49910249022942603435652849 37432686767206952576739637)
                  ·
                    refine ⟨3509314384425651804069341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37432686767206952576739637 3509314384425651804069341)
                    ·
                      refine ⟨1315992894159619426526003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3509314384425651804069341 1315992894159619426526003)
                      ·
                        rfl

theorem cell23_2562887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_2562887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562887 prefixEnd_2562887 := by exact prefixLift 2562887
  have htrace : WordTrace (prefixWord ++ tailWord_2562887) baseStart_2562887 baseEnd_2562887 := by
    simpa [prefixWord, tailWord_2562887, baseEnd_2562887] using wordTrace_append hprefix tailTrace_2562887
  have hstable : (prefixWord ++ tailWord_2562887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562887).length < 2 ^ (prefixWord ++ tailWord_2562887).sum := by decide
  have hdescent : baseEnd_2562887 < baseStart_2562887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562908 : List Nat := [2, 2, 4, 2, 1, 3, 1, 1, 2, 2, 3]
def baseStart_2562908 : Nat := 118140960795 + 2562908 * 2 ^ 59
def prefixEnd_2562908 : Nat := 4983230072969 + 3 ^ 40 * 2562908 * 2
def baseEnd_2562908 : Nat := 1316003677253363844363407

theorem tailTrace_2562908 : CollatzResearch.WordTrace tailWord_2562908 prefixEnd_2562908 1316003677253363844363407 := by
  unfold tailWord_2562908
  simp only [CollatzResearch.WordTrace]
  refine ⟨46738467099514750341824689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62317956132686333789099585 46738467099514750341824689)
  ·
    refine ⟨35053850324636062756368517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46738467099514750341824689 35053850324636062756368517)
    ·
      refine ⟨6572596935869261766819097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35053850324636062756368517 6572596935869261766819097)
      ·
        refine ⟨4929447701901946325114323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6572596935869261766819097 4929447701901946325114323)
        ·
          refine ⟨7394171552852919487671485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4929447701901946325114323 7394171552852919487671485)
          ·
            refine ⟨2772814332319844807876807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7394171552852919487671485 2772814332319844807876807)
            ·
              refine ⟨4159221498479767211815211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2772814332319844807876807 4159221498479767211815211)
              ·
                refine ⟨6238832247719650817722817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4159221498479767211815211 6238832247719650817722817)
                ·
                  refine ⟨4679124185789738113292113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6238832247719650817722817 4679124185789738113292113)
                  ·
                    refine ⟨3509343139342303584969085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4679124185789738113292113 3509343139342303584969085)
                    ·
                      refine ⟨1316003677253363844363407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3509343139342303584969085 1316003677253363844363407)
                      ·
                        rfl

theorem cell23_2562908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_2562908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562908 prefixEnd_2562908 := by exact prefixLift 2562908
  have htrace : WordTrace (prefixWord ++ tailWord_2562908) baseStart_2562908 baseEnd_2562908 := by
    simpa [prefixWord, tailWord_2562908, baseEnd_2562908] using wordTrace_append hprefix tailTrace_2562908
  have hstable : (prefixWord ++ tailWord_2562908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562908).length < 2 ^ (prefixWord ++ tailWord_2562908).sum := by decide
  have hdescent : baseEnd_2562908 < baseStart_2562908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562924 : List Nat := [2, 2, 1, 1, 4, 1, 3, 3, 1, 5]
def baseStart_2562924 : Nat := 118140960795 + 2562924 * 2 ^ 59
def prefixEnd_2562924 : Nat := 4983230072969 + 3 ^ 40 * 2562924 * 2
def baseEnd_2562924 : Nat := 438670630981278593921111

theorem tailTrace_2562924 : CollatzResearch.WordTrace tailWord_2562924 prefixEnd_2562924 438670630981278593921111 := by
  unfold tailWord_2562924
  simp only [CollatzResearch.WordTrace]
  refine ⟨46738758883485767708115913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62318345177981023610821217 46738758883485767708115913)
  ·
    refine ⟨35054069162614325781086935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46738758883485767708115913 35054069162614325781086935)
    ·
      refine ⟨52581103743921488671630403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35054069162614325781086935 52581103743921488671630403)
      ·
        refine ⟨78871655615882233007445605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52581103743921488671630403 78871655615882233007445605)
        ·
          refine ⟨14788435427977918688896051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78871655615882233007445605 14788435427977918688896051)
          ·
            refine ⟨22182653141966878033344077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14788435427977918688896051 22182653141966878033344077)
            ·
              refine ⟨8318494928237579262504029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22182653141966878033344077 8318494928237579262504029)
              ·
                refine ⟨3119435598089092223439011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8318494928237579262504029 3119435598089092223439011)
                ·
                  refine ⟨4679153397133638335158517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3119435598089092223439011 4679153397133638335158517)
                  ·
                    refine ⟨438670630981278593921111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4679153397133638335158517 438670630981278593921111)
                    ·
                      rfl

theorem cell23_2562924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 5].length) (baseStart_2562924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562924 prefixEnd_2562924 := by exact prefixLift 2562924
  have htrace : WordTrace (prefixWord ++ tailWord_2562924) baseStart_2562924 baseEnd_2562924 := by
    simpa [prefixWord, tailWord_2562924, baseEnd_2562924] using wordTrace_append hprefix tailTrace_2562924
  have hstable : (prefixWord ++ tailWord_2562924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562924).length < 2 ^ (prefixWord ++ tailWord_2562924).sum := by decide
  have hdescent : baseEnd_2562924 < baseStart_2562924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562964 : List Nat := [2, 4, 2, 1, 1, 1, 1, 2, 3, 1, 5]
def baseStart_2562964 : Nat := 118140960795 + 2562964 * 2 ^ 59
def prefixEnd_2562964 : Nat := 4983230072969 + 3 ^ 40 * 2562964 * 2
def baseEnd_2562964 : Nat := 1316032432170015625263149

theorem tailTrace_2562964 : CollatzResearch.WordTrace tailWord_2562964 prefixEnd_2562964 1316032432170015625263149 := by
  unfold tailWord_2562964
  simp only [CollatzResearch.WordTrace]
  refine ⟨46739488343413311123843973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62319317791217748165125297 46739488343413311123843973)
  ·
    refine ⟨8763654064389995835720745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46739488343413311123843973 8763654064389995835720745)
    ·
      refine ⟨6572740548292496876790559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8763654064389995835720745 6572740548292496876790559)
      ·
        refine ⟨9859110822438745315185839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6572740548292496876790559 9859110822438745315185839)
        ·
          refine ⟨14788666233658117972778759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9859110822438745315185839 14788666233658117972778759)
          ·
            refine ⟨22182999350487176959168139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14788666233658117972778759 22182999350487176959168139)
            ·
              refine ⟨33274499025730765438752209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22182999350487176959168139 33274499025730765438752209)
              ·
                refine ⟨24955874269298074079064157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33274499025730765438752209 24955874269298074079064157)
                ·
                  refine ⟨9358452850986777779649059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24955874269298074079064157 9358452850986777779649059)
                  ·
                    refine ⟨14037679276480166669473589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9358452850986777779649059 14037679276480166669473589)
                    ·
                      refine ⟨1316032432170015625263149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14037679276480166669473589 1316032432170015625263149)
                      ·
                        rfl

theorem cell23_2562964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_2562964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562964 prefixEnd_2562964 := by exact prefixLift 2562964
  have htrace : WordTrace (prefixWord ++ tailWord_2562964) baseStart_2562964 baseEnd_2562964 := by
    simpa [prefixWord, tailWord_2562964, baseEnd_2562964] using wordTrace_append hprefix tailTrace_2562964
  have hstable : (prefixWord ++ tailWord_2562964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562964).length < 2 ^ (prefixWord ++ tailWord_2562964).sum := by decide
  have hdescent : baseEnd_2562964 < baseStart_2562964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562967 : List Nat := [1, 1, 3, 3, 1, 2, 3, 9]
def baseStart_2562967 : Nat := 118140960795 + 2562967 * 2 ^ 59
def prefixEnd_2562967 : Nat := 4983230072969 + 3 ^ 40 * 2562967 * 2
def baseEnd_2562967 : Nat := 48741998985628856056505

theorem tailTrace_2562967 : CollatzResearch.WordTrace tailWord_2562967 prefixEnd_2562967 48741998985628856056505 := by
  unfold tailWord_2562967
  simp only [CollatzResearch.WordTrace]
  refine ⟨93479086105815753760047155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62319390737210502506698103 93479086105815753760047155)
  ·
    refine ⟨140218629158723630640070733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93479086105815753760047155 140218629158723630640070733)
    ·
      refine ⟨52581985934521361490026525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140218629158723630640070733 52581985934521361490026525)
      ·
        refine ⟨19718244725445510558759947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52581985934521361490026525 19718244725445510558759947)
        ·
          refine ⟨29577367088168265838139921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19718244725445510558759947 29577367088168265838139921)
          ·
            refine ⟨22183025316126199378604941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29577367088168265838139921 22183025316126199378604941)
            ·
              refine ⟨8318634493547324766976853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22183025316126199378604941 8318634493547324766976853)
              ·
                refine ⟨48741998985628856056505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8318634493547324766976853 48741998985628856056505)
                ·
                  rfl

theorem cell23_2562967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 9].length) (baseStart_2562967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562967 prefixEnd_2562967 := by exact prefixLift 2562967
  have htrace : WordTrace (prefixWord ++ tailWord_2562967) baseStart_2562967 baseEnd_2562967 := by
    simpa [prefixWord, tailWord_2562967, baseEnd_2562967] using wordTrace_append hprefix tailTrace_2562967
  have hstable : (prefixWord ++ tailWord_2562967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562967).length < 2 ^ (prefixWord ++ tailWord_2562967).sum := by decide
  have hdescent : baseEnd_2562967 < baseStart_2562967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562972 : List Nat := [2, 2, 3, 3, 2, 2, 1, 3, 1, 1, 3]
def baseStart_2562972 : Nat := 118140960795 + 2562972 * 2 ^ 59
def prefixEnd_2562972 : Nat := 4983230072969 + 3 ^ 40 * 2562972 * 2
def baseEnd_2562972 : Nat := 1316036540015251593963113

theorem tailTrace_2562972 : CollatzResearch.WordTrace tailWord_2562972 prefixEnd_2562972 1316036540015251593963113 := by
  unfold tailWord_2562972
  simp only [CollatzResearch.WordTrace]
  refine ⟨46739634235398819806989585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62319512313865093075986113 46739634235398819806989585)
  ·
    refine ⟨35054725676549114855242189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46739634235398819806989585 35054725676549114855242189)
    ·
      refine ⟨13145522128705918070715821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35054725676549114855242189 13145522128705918070715821)
      ·
        refine ⟨4929570798264719276518433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13145522128705918070715821 4929570798264719276518433)
        ·
          refine ⟨3697178098698539457388825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4929570798264719276518433 3697178098698539457388825)
          ·
            refine ⟨2772883574023904593041619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3697178098698539457388825 2772883574023904593041619)
            ·
              refine ⟨4159325361035856889562429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2772883574023904593041619 4159325361035856889562429)
              ·
                refine ⟨1559747010388446333585911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4159325361035856889562429 1559747010388446333585911)
                ·
                  refine ⟨2339620515582669500378867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1559747010388446333585911 2339620515582669500378867)
                  ·
                    refine ⟨3509430773374004250568301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2339620515582669500378867 3509430773374004250568301)
                    ·
                      refine ⟨1316036540015251593963113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3509430773374004250568301 1316036540015251593963113)
                      ·
                        rfl

theorem cell23_2562972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_2562972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562972 prefixEnd_2562972 := by exact prefixLift 2562972
  have htrace : WordTrace (prefixWord ++ tailWord_2562972) baseStart_2562972 baseEnd_2562972 := by
    simpa [prefixWord, tailWord_2562972, baseEnd_2562972] using wordTrace_append hprefix tailTrace_2562972
  have hstable : (prefixWord ++ tailWord_2562972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562972).length < 2 ^ (prefixWord ++ tailWord_2562972).sum := by decide
  have hdescent : baseEnd_2562972 < baseStart_2562972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562989 : List Nat := [1, 5, 2, 3, 1, 1, 3, 2, 1, 1, 3]
def baseStart_2562989 : Nat := 118140960795 + 2562989 * 2 ^ 59
def prefixEnd_2562989 : Nat := 4983230072969 + 3 ^ 40 * 2562989 * 2
def baseEnd_2562989 : Nat := 1316045269186378027450535

theorem tailTrace_2562989 : CollatzResearch.WordTrace tailWord_2562989 prefixEnd_2562989 1316045269186378027450535 := by
  unfold tailWord_2562989
  simp only [CollatzResearch.WordTrace]
  refine ⟨93479888511736051517348021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62319925674490701011565347 93479888511736051517348021)
  ·
    refine ⟨8763739547975254829751377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93479888511736051517348021 8763739547975254829751377)
    ·
      refine ⟨6572804660981441122313533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8763739547975254829751377 6572804660981441122313533)
      ·
        refine ⟨2464801747868040420867575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6572804660981441122313533 2464801747868040420867575)
        ·
          refine ⟨3697202621802060631301363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2464801747868040420867575 3697202621802060631301363)
          ·
            refine ⟨5545803932703090946952045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3697202621802060631301363 5545803932703090946952045)
            ·
              refine ⟨2079676474763659105107017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5545803932703090946952045 2079676474763659105107017)
              ·
                refine ⟨1559757356072744328830263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2079676474763659105107017 1559757356072744328830263)
                ·
                  refine ⟨2339636034109116493245395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1559757356072744328830263 2339636034109116493245395)
                  ·
                    refine ⟨3509454051163674739868093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2339636034109116493245395 3509454051163674739868093)
                    ·
                      refine ⟨1316045269186378027450535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3509454051163674739868093 1316045269186378027450535)
                      ·
                        rfl

theorem cell23_2562989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_2562989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2562989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2562989 prefixEnd_2562989 := by exact prefixLift 2562989
  have htrace : WordTrace (prefixWord ++ tailWord_2562989) baseStart_2562989 baseEnd_2562989 := by
    simpa [prefixWord, tailWord_2562989, baseEnd_2562989] using wordTrace_append hprefix tailTrace_2562989
  have hstable : (prefixWord ++ tailWord_2562989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562989).length < 2 ^ (prefixWord ++ tailWord_2562989).sum := by decide
  have hdescent : baseEnd_2562989 < baseStart_2562989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563005 : List Nat := [1, 4, 1, 2, 4, 2, 2, 1, 2, 4]
def baseStart_2563005 : Nat := 118140960795 + 2563005 * 2 ^ 59
def prefixEnd_2563005 : Nat := 4983230072969 + 3 ^ 40 * 2563005 * 2
def baseEnd_2563005 : Nat := 438684494958949988283487

theorem tailTrace_2563005 : CollatzResearch.WordTrace tailWord_2563005 prefixEnd_2563005 438684494958949988283487 := by
  unfold tailWord_2563005
  simp only [CollatzResearch.WordTrace]
  refine ⟨93480472079678086249930469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62320314719785390833286979 93480472079678086249930469)
  ·
    refine ⟨17527588514939641171861963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93480472079678086249930469 17527588514939641171861963)
    ·
      refine ⟨26291382772409461757792945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17527588514939641171861963 26291382772409461757792945)
      ·
        refine ⟨19718537079307096318344709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26291382772409461757792945 19718537079307096318344709)
        ·
          refine ⟨3697225702370080559689633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19718537079307096318344709 3697225702370080559689633)
          ·
            refine ⟨2772919276777560419767225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3697225702370080559689633 2772919276777560419767225)
            ·
              refine ⟨2079689457583170314825419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2772919276777560419767225 2079689457583170314825419)
              ·
                refine ⟨3119534186374755472238129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2079689457583170314825419 3119534186374755472238129)
                ·
                  refine ⟨2339650639781066604178597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3119534186374755472238129 2339650639781066604178597)
                  ·
                    refine ⟨438684494958949988283487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2339650639781066604178597 438684494958949988283487)
                    ·
                      rfl

theorem cell23_2563005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 2, 4].length) (baseStart_2563005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563005 prefixEnd_2563005 := by exact prefixLift 2563005
  have htrace : WordTrace (prefixWord ++ tailWord_2563005) baseStart_2563005 baseEnd_2563005 := by
    simpa [prefixWord, tailWord_2563005, baseEnd_2563005] using wordTrace_append hprefix tailTrace_2563005
  have hstable : (prefixWord ++ tailWord_2563005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563005).length < 2 ^ (prefixWord ++ tailWord_2563005).sum := by decide
  have hdescent : baseEnd_2563005 < baseStart_2563005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563007 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 5]
def baseStart_2563007 : Nat := 118140960795 + 2563007 * 2 ^ 59
def prefixEnd_2563007 : Nat := 4983230072969 + 3 ^ 40 * 2563007 * 2
def baseEnd_2563007 : Nat := 1316054511838158957025451

theorem tailTrace_2563007 : CollatzResearch.WordTrace tailWord_2563007 prefixEnd_2563007 1316054511838158957025451 := by
  unfold tailWord_2563007
  simp only [CollatzResearch.WordTrace]
  refine ⟨93480545025670840591503275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62320363350447227061002183 93480545025670840591503275)
  ·
    refine ⟨140220817538506260887254913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93480545025670840591503275 140220817538506260887254913)
    ·
      refine ⟨105165613153879695665441185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140220817538506260887254913 105165613153879695665441185)
      ·
        refine ⟨78874209865409771749080889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105165613153879695665441185 78874209865409771749080889)
        ·
          refine ⟨59155657399057328811810667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78874209865409771749080889 59155657399057328811810667)
          ·
            refine ⟨88733486098585993217716001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59155657399057328811810667 88733486098585993217716001)
            ·
              refine ⟨66550114573939494913287001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88733486098585993217716001 66550114573939494913287001)
              ·
                refine ⟨49912585930454621184965251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66550114573939494913287001 49912585930454621184965251)
                ·
                  refine ⟨74868878895681931777447877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49912585930454621184965251 74868878895681931777447877)
                  ·
                    refine ⟨14037914792940362208271477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74868878895681931777447877 14037914792940362208271477)
                    ·
                      refine ⟨1316054511838158957025451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14037914792940362208271477 1316054511838158957025451)
                      ·
                        rfl

theorem cell23_2563007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_2563007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563007 prefixEnd_2563007 := by exact prefixLift 2563007
  have htrace : WordTrace (prefixWord ++ tailWord_2563007) baseStart_2563007 baseEnd_2563007 := by
    simpa [prefixWord, tailWord_2563007, baseEnd_2563007] using wordTrace_append hprefix tailTrace_2563007
  have hstable : (prefixWord ++ tailWord_2563007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563007).length < 2 ^ (prefixWord ++ tailWord_2563007).sum := by decide
  have hdescent : baseEnd_2563007 < baseStart_2563007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563011 : List Nat := [1, 1, 1, 3, 1, 1, 2, 7, 2, 1, 3]
def baseStart_2563011 : Nat := 118140960795 + 2563011 * 2 ^ 59
def prefixEnd_2563011 : Nat := 4983230072969 + 3 ^ 40 * 2563011 * 2
def baseEnd_2563011 : Nat := 1316056565760776941375433

theorem tailTrace_2563011 : CollatzResearch.WordTrace tailWord_2563011 prefixEnd_2563011 1316056565760776941375433 := by
  unfold tailWord_2563011
  simp only [CollatzResearch.WordTrace]
  refine ⟨93480690917656349274648887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62320460611770899516432591 93480690917656349274648887)
  ·
    refine ⟨140221036376484523911973331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93480690917656349274648887 140221036376484523911973331)
    ·
      refine ⟨210331554564726785867959997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140221036376484523911973331 210331554564726785867959997)
      ·
        refine ⟨78874332961772544700484999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210331554564726785867959997 78874332961772544700484999)
        ·
          refine ⟨118311499442658817050727499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78874332961772544700484999 118311499442658817050727499)
          ·
            refine ⟨177467249163988225576091249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118311499442658817050727499 177467249163988225576091249)
            ·
              refine ⟨133100436872991169182068437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177467249163988225576091249 133100436872991169182068437)
              ·
                refine ⟨3119541489210730527704729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 133100436872991169182068437 3119541489210730527704729)
                ·
                  refine ⟨2339656116908047895778547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3119541489210730527704729 2339656116908047895778547)
                  ·
                    refine ⟨3509484175362071843667821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2339656116908047895778547 3509484175362071843667821)
                    ·
                      refine ⟨1316056565760776941375433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3509484175362071843667821 1316056565760776941375433)
                      ·
                        rfl

theorem cell23_2563011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 2, 1, 3].length) (baseStart_2563011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563011 prefixEnd_2563011 := by exact prefixLift 2563011
  have htrace : WordTrace (prefixWord ++ tailWord_2563011) baseStart_2563011 baseEnd_2563011 := by
    simpa [prefixWord, tailWord_2563011, baseEnd_2563011] using wordTrace_append hprefix tailTrace_2563011
  have hstable : (prefixWord ++ tailWord_2563011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563011).length < 2 ^ (prefixWord ++ tailWord_2563011).sum := by decide
  have hdescent : baseEnd_2563011 < baseStart_2563011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563012 : List Nat := [2, 3, 3, 3, 2, 1, 1, 2, 1, 1, 4]
def baseStart_2563012 : Nat := 118140960795 + 2563012 * 2 ^ 59
def prefixEnd_2563012 : Nat := 4983230072969 + 3 ^ 40 * 2563012 * 2
def baseEnd_2563012 : Nat := 1316057079241431437462929

theorem tailTrace_2563012 : CollatzResearch.WordTrace tailWord_2563012 prefixEnd_2563012 1316057079241431437462929 := by
  unfold tailWord_2563012
  simp only [CollatzResearch.WordTrace]
  refine ⟨46740363695326363222717645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62320484927101817630290193 46740363695326363222717645)
  ·
    refine ⟨17527636385747386208519117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46740363695326363222717645 17527636385747386208519117)
    ·
      refine ⟨6572863644655269828194669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17527636385747386208519117 6572863644655269828194669)
      ·
        refine ⟨2464823866745726185573001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6572863644655269828194669 2464823866745726185573001)
        ·
          refine ⟨1848617900059294639179751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2464823866745726185573001 1848617900059294639179751)
          ·
            refine ⟨2772926850088941958769627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1848617900059294639179751 2772926850088941958769627)
            ·
              refine ⟨4159390275133412938154441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2772926850088941958769627 4159390275133412938154441)
              ·
                refine ⟨3119542706350059703615831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4159390275133412938154441 3119542706350059703615831)
                ·
                  refine ⟨4679314059525089555423747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3119542706350059703615831 4679314059525089555423747)
                  ·
                    refine ⟨7018971089287634333135621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4679314059525089555423747 7018971089287634333135621)
                    ·
                      refine ⟨1316057079241431437462929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7018971089287634333135621 1316057079241431437462929)
                      ·
                        rfl

theorem cell23_2563012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_2563012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563012 prefixEnd_2563012 := by exact prefixLift 2563012
  have htrace : WordTrace (prefixWord ++ tailWord_2563012) baseStart_2563012 baseEnd_2563012 := by
    simpa [prefixWord, tailWord_2563012, baseEnd_2563012] using wordTrace_append hprefix tailTrace_2563012
  have hstable : (prefixWord ++ tailWord_2563012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563012).length < 2 ^ (prefixWord ++ tailWord_2563012).sum := by decide
  have hdescent : baseEnd_2563012 < baseStart_2563012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563068 : List Nat := [2, 2, 2, 1, 2, 4, 2, 1, 1, 4, 2]
def baseStart_2563068 : Nat := 118140960795 + 2563068 * 2 ^ 59
def prefixEnd_2563068 : Nat := 4983230072969 + 3 ^ 40 * 2563068 * 2
def baseEnd_2563068 : Nat := 1316085834158083218362671

theorem tailTrace_2563068 : CollatzResearch.WordTrace tailWord_2563068 prefixEnd_2563068 1316085834158083218362671 := by
  unfold tailWord_2563068
  simp only [CollatzResearch.WordTrace]
  refine ⟨46741384939224924004736929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62321846585633232006315905 46741384939224924004736929)
  ·
    refine ⟨35056038704418693003552697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46741384939224924004736929 35056038704418693003552697)
    ·
      refine ⟨26292029028314019752664523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35056038704418693003552697 26292029028314019752664523)
      ·
        refine ⟨39438043542471029628996785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26292029028314019752664523 39438043542471029628996785)
        ·
          refine ⟨29578532656853272221747589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39438043542471029628996785 29578532656853272221747589)
          ·
            refine ⟨5545974873159988541577673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29578532656853272221747589 5545974873159988541577673)
            ·
              refine ⟨4159481154869991406183255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5545974873159988541577673 4159481154869991406183255)
              ·
                refine ⟨6239221732304987109274883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4159481154869991406183255 6239221732304987109274883)
                ·
                  refine ⟨9358832598457480663912325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6239221732304987109274883 9358832598457480663912325)
                  ·
                    refine ⟨1754781112210777624483561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9358832598457480663912325 1754781112210777624483561)
                    ·
                      refine ⟨1316085834158083218362671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1754781112210777624483561 1316085834158083218362671)
                      ·
                        rfl

theorem cell23_2563068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 1, 4, 2].length) (baseStart_2563068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563068 prefixEnd_2563068 := by exact prefixLift 2563068
  have htrace : WordTrace (prefixWord ++ tailWord_2563068) baseStart_2563068 baseEnd_2563068 := by
    simpa [prefixWord, tailWord_2563068, baseEnd_2563068] using wordTrace_append hprefix tailTrace_2563068
  have hstable : (prefixWord ++ tailWord_2563068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563068).length < 2 ^ (prefixWord ++ tailWord_2563068).sum := by decide
  have hdescent : baseEnd_2563068 < baseStart_2563068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563108 : List Nat := [2, 3, 1, 4, 1, 1, 2, 4, 5]
def baseStart_2563108 : Nat := 118140960795 + 2563108 * 2 ^ 59
def prefixEnd_2563108 : Nat := 4983230072969 + 3 ^ 40 * 2563108 * 2
def baseEnd_2563108 : Nat := 146234041487140340206943

theorem tailTrace_2563108 : CollatzResearch.WordTrace tailWord_2563108 prefixEnd_2563108 146234041487140340206943 := by
  unfold tailWord_2563108
  simp only [CollatzResearch.WordTrace]
  refine ⟨46742114399152467420464989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62322819198869956560619985 46742114399152467420464989)
  ·
    refine ⟨17528292899682175282674371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46742114399152467420464989 17528292899682175282674371)
    ·
      refine ⟨26292439349523262924011557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17528292899682175282674371 26292439349523262924011557)
      ·
        refine ⟨4929832378035611798252167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26292439349523262924011557 4929832378035611798252167)
        ·
          refine ⟨7394748567053417697378251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4929832378035611798252167 7394748567053417697378251)
          ·
            refine ⟨11092122850580126546067377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7394748567053417697378251 11092122850580126546067377)
            ·
              refine ⟨8319092137935094909550533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11092122850580126546067377 8319092137935094909550533)
              ·
                refine ⟨1559829775862830295540725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8319092137935094909550533 1559829775862830295540725)
                ·
                  refine ⟨146234041487140340206943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1559829775862830295540725 146234041487140340206943)
                  ·
                    rfl

theorem cell23_2563108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 4, 5].length) (baseStart_2563108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563108 prefixEnd_2563108 := by exact prefixLift 2563108
  have htrace : WordTrace (prefixWord ++ tailWord_2563108) baseStart_2563108 baseEnd_2563108 := by
    simpa [prefixWord, tailWord_2563108, baseEnd_2563108] using wordTrace_append hprefix tailTrace_2563108
  have hstable : (prefixWord ++ tailWord_2563108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563108).length < 2 ^ (prefixWord ++ tailWord_2563108).sum := by decide
  have hdescent : baseEnd_2563108 < baseStart_2563108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563141 : List Nat := [1, 3, 1, 1, 1, 3, 2, 2, 1, 6, 2]
def baseStart_2563141 : Nat := 118140960795 + 2563141 * 2 ^ 59
def prefixEnd_2563141 : Nat := 4983230072969 + 3 ^ 40 * 2563141 * 2
def baseEnd_2563141 : Nat := 1316123318245861432749835

theorem tailTrace_2563141 : CollatzResearch.WordTrace tailWord_2563141 prefixEnd_2563141 1316123318245861432749835 := by
  unfold tailWord_2563141
  simp only [CollatzResearch.WordTrace]
  refine ⟨93485432407185381476881277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62323621604790254317920851 93485432407185381476881277)
  ·
    refine ⟨35057037152694518053830479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93485432407185381476881277 35057037152694518053830479)
    ·
      refine ⟨52585555729041777080745719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35057037152694518053830479 52585555729041777080745719)
      ·
        refine ⟨78878333593562665621118579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52585555729041777080745719 78878333593562665621118579)
        ·
          refine ⟨118317500390343998431677869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78878333593562665621118579 118317500390343998431677869)
          ·
            refine ⟨44369062646378999411879201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118317500390343998431677869 44369062646378999411879201)
            ·
              refine ⟨33276796984784249558909401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44369062646378999411879201 33276796984784249558909401)
              ·
                refine ⟨24957597738588187169182051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33276796984784249558909401 24957597738588187169182051)
                ·
                  refine ⟨37436396607882280753773077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24957597738588187169182051 37436396607882280753773077)
                  ·
                    refine ⟨1754831090994481910333113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 37436396607882280753773077 1754831090994481910333113)
                    ·
                      refine ⟨1316123318245861432749835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1754831090994481910333113 1316123318245861432749835)
                      ·
                        rfl

theorem cell23_2563141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 6, 2].length) (baseStart_2563141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563141 prefixEnd_2563141 := by exact prefixLift 2563141
  have htrace : WordTrace (prefixWord ++ tailWord_2563141) baseStart_2563141 baseEnd_2563141 := by
    simpa [prefixWord, tailWord_2563141, baseEnd_2563141] using wordTrace_append hprefix tailTrace_2563141
  have hstable : (prefixWord ++ tailWord_2563141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563141).length < 2 ^ (prefixWord ++ tailWord_2563141).sum := by decide
  have hdescent : baseEnd_2563141 < baseStart_2563141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563142 : List Nat := [6, 1, 1, 1, 1, 4, 1, 3, 5]
def baseStart_2563142 : Nat := 118140960795 + 2563142 * 2 ^ 59
def prefixEnd_2563142 : Nat := 4983230072969 + 3 ^ 40 * 2563142 * 2
def baseEnd_2563142 : Nat := 146235981302946214315259

theorem tailTrace_2563142 : CollatzResearch.WordTrace tailWord_2563142 prefixEnd_2563142 146235981302946214315259 := by
  unfold tailWord_2563142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2921420902505679957739615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 62323645920121172431778453 2921420902505679957739615)
  ·
    refine ⟨4382131353758519936609423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2921420902505679957739615 4382131353758519936609423)
    ·
      refine ⟨6573197030637779904914135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4382131353758519936609423 6573197030637779904914135)
      ·
        refine ⟨9859795545956669857371203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6573197030637779904914135 9859795545956669857371203)
        ·
          refine ⟨14789693318935004786056805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9859795545956669857371203 14789693318935004786056805)
          ·
            refine ⟨2773067497300313397385651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14789693318935004786056805 2773067497300313397385651)
            ·
              refine ⟨4159601245950470096078477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2773067497300313397385651 4159601245950470096078477)
              ·
                refine ⟨1559850467231426286029429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4159601245950470096078477 1559850467231426286029429)
                ·
                  refine ⟨146235981302946214315259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1559850467231426286029429 146235981302946214315259)
                  ·
                    rfl

theorem cell23_2563142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_2563142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563142 prefixEnd_2563142 := by exact prefixLift 2563142
  have htrace : WordTrace (prefixWord ++ tailWord_2563142) baseStart_2563142 baseEnd_2563142 := by
    simpa [prefixWord, tailWord_2563142, baseEnd_2563142] using wordTrace_append hprefix tailTrace_2563142
  have hstable : (prefixWord ++ tailWord_2563142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563142).length < 2 ^ (prefixWord ++ tailWord_2563142).sum := by decide
  have hdescent : baseEnd_2563142 < baseStart_2563142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563211 : List Nat := [1, 1, 1, 1, 4, 1, 1, 7, 1, 5]
def baseStart_2563211 : Nat := 118140960795 + 2563211 * 2 ^ 59
def prefixEnd_2563211 : Nat := 4983230072969 + 3 ^ 40 * 2563211 * 2
def baseEnd_2563211 : Nat := 438719753963892052958171

theorem tailTrace_2563211 : CollatzResearch.WordTrace tailWord_2563211 prefixEnd_2563211 438719753963892052958171 := by
  unfold tailWord_2563211
  simp only [CollatzResearch.WordTrace]
  refine ⟨93487985516931783431929487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62325323677954522287952991 93487985516931783431929487)
  ·
    refine ⟨140231978275397675147894231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93487985516931783431929487 140231978275397675147894231)
    ·
      refine ⟨210347967413096512721841347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140231978275397675147894231 210347967413096512721841347)
      ·
        refine ⟨315521951119644769082762021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210347967413096512721841347 315521951119644769082762021)
        ·
          refine ⟨59160365834933394203017879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 315521951119644769082762021 59160365834933394203017879)
          ·
            refine ⟨88740548752400091304526819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59160365834933394203017879 88740548752400091304526819)
            ·
              refine ⟨133110823128600136956790229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88740548752400091304526819 133110823128600136956790229)
              ·
                refine ⟨3119784917076565709924771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 133110823128600136956790229 3119784917076565709924771)
                ·
                  refine ⟨4679677375614848564887157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3119784917076565709924771 4679677375614848564887157)
                  ·
                    refine ⟨438719753963892052958171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4679677375614848564887157 438719753963892052958171)
                    ·
                      rfl

theorem cell23_2563211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 5].length) (baseStart_2563211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563211 prefixEnd_2563211 := by exact prefixLift 2563211
  have htrace : WordTrace (prefixWord ++ tailWord_2563211) baseStart_2563211 baseEnd_2563211 := by
    simpa [prefixWord, tailWord_2563211, baseEnd_2563211] using wordTrace_append hprefix tailTrace_2563211
  have hstable : (prefixWord ++ tailWord_2563211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563211).length < 2 ^ (prefixWord ++ tailWord_2563211).sum := by decide
  have hdescent : baseEnd_2563211 < baseStart_2563211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563242 : List Nat := [3, 1, 5, 1, 1, 2, 1, 2, 3, 1, 3]
def baseStart_2563242 : Nat := 118140960795 + 2563242 * 2 ^ 59
def prefixEnd_2563242 : Nat := 4983230072969 + 3 ^ 40 * 2563242 * 2
def baseEnd_2563242 : Nat := 1316175179791965537586871

theorem tailTrace_2563242 : CollatzResearch.WordTrace tailWord_2563242 prefixEnd_2563242 1316175179791965537586871 := by
  unfold tailWord_2563242
  simp only [CollatzResearch.WordTrace]
  refine ⟨23372279044954868931576995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62326077453212983817538653 23372279044954868931576995)
  ·
    refine ⟨35058418567432303397365493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23372279044954868931576995 35058418567432303397365493)
    ·
      refine ⟨3286726740696778443503015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35058418567432303397365493 3286726740696778443503015)
      ·
        refine ⟨4930090111045167665254523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3286726740696778443503015 4930090111045167665254523)
        ·
          refine ⟨7395135166567751497881785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4930090111045167665254523 7395135166567751497881785)
          ·
            refine ⟨5546351374925813623411339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7395135166567751497881785 5546351374925813623411339)
            ·
              refine ⟨8319527062388720435117009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5546351374925813623411339 8319527062388720435117009)
              ·
                refine ⟨6239645296791540326337757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8319527062388720435117009 6239645296791540326337757)
                ·
                  refine ⟨2339866986296827622376659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6239645296791540326337757 2339866986296827622376659)
                  ·
                    refine ⟨3509800479445241433564989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2339866986296827622376659 3509800479445241433564989)
                    ·
                      refine ⟨1316175179791965537586871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3509800479445241433564989 1316175179791965537586871)
                      ·
                        rfl

theorem cell23_2563242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_2563242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563242 prefixEnd_2563242 := by exact prefixLift 2563242
  have htrace : WordTrace (prefixWord ++ tailWord_2563242) baseStart_2563242 baseEnd_2563242 := by
    simpa [prefixWord, tailWord_2563242, baseEnd_2563242] using wordTrace_append hprefix tailTrace_2563242
  have hstable : (prefixWord ++ tailWord_2563242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563242).length < 2 ^ (prefixWord ++ tailWord_2563242).sum := by decide
  have hdescent : baseEnd_2563242 < baseStart_2563242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563262 : List Nat := [4, 2, 1, 1, 3, 3, 2, 1, 1, 5]
def baseStart_2563262 : Nat := 118140960795 + 2563262 * 2 ^ 59
def prefixEnd_2563262 : Nat := 4983230072969 + 3 ^ 40 * 2563262 * 2
def baseEnd_2563262 : Nat := 438728483135018486445593

theorem tailTrace_2563262 : CollatzResearch.WordTrace tailWord_2563262 prefixEnd_2563262 438728483135018486445593 := by
  unfold tailWord_2563262
  simp only [CollatzResearch.WordTrace]
  refine ⟨11686230704968377392754505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62326563759831346094690693 11686230704968377392754505)
  ·
    refine ⟨8764673028726283044565879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11686230704968377392754505 8764673028726283044565879)
    ·
      refine ⟨13147009543089424566848819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8764673028726283044565879 13147009543089424566848819)
      ·
        refine ⟨19720514314634136850273229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13147009543089424566848819 19720514314634136850273229)
        ·
          refine ⟨7395192867987801318852461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19720514314634136850273229 7395192867987801318852461)
          ·
            refine ⟨2773197325495425494569673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7395192867987801318852461 2773197325495425494569673)
            ·
              refine ⟨2079897994121569120927255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2773197325495425494569673 2079897994121569120927255)
              ·
                refine ⟨3119846991182353681390883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2079897994121569120927255 3119846991182353681390883)
                ·
                  refine ⟨4679770486773530522086325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3119846991182353681390883 4679770486773530522086325)
                  ·
                    refine ⟨438728483135018486445593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4679770486773530522086325 438728483135018486445593)
                    ·
                      rfl

theorem cell23_2563262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_2563262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563262 prefixEnd_2563262 := by exact prefixLift 2563262
  have htrace : WordTrace (prefixWord ++ tailWord_2563262) baseStart_2563262 baseEnd_2563262 := by
    simpa [prefixWord, tailWord_2563262, baseEnd_2563262] using wordTrace_append hprefix tailTrace_2563262
  have hstable : (prefixWord ++ tailWord_2563262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563262).length < 2 ^ (prefixWord ++ tailWord_2563262).sum := by decide
  have hdescent : baseEnd_2563262 < baseStart_2563262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563282 : List Nat := [3, 2, 2, 2, 1, 1, 4, 1, 3, 2, 2]
def baseStart_2563282 : Nat := 118140960795 + 2563282 * 2 ^ 59
def prefixEnd_2563282 : Nat := 4983230072969 + 3 ^ 40 * 2563282 * 2
def baseEnd_2563282 : Nat := 1316195719018145381086687

theorem tailTrace_2563282 : CollatzResearch.WordTrace tailWord_2563282 prefixEnd_2563282 1316195719018145381086687 := by
  unfold tailWord_2563282
  simp only [CollatzResearch.WordTrace]
  refine ⟨23372643774918640639441025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62327050066449708371842733 23372643774918640639441025)
  ·
    refine ⟨17529482831188980479580769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23372643774918640639441025 17529482831188980479580769)
    ·
      refine ⟨13147112123391735359685577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17529482831188980479580769 13147112123391735359685577)
      ·
        refine ⟨9860334092543801519764183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13147112123391735359685577 9860334092543801519764183)
        ·
          refine ⟨14790501138815702279646275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9860334092543801519764183 14790501138815702279646275)
          ·
            refine ⟨22185751708223553419469413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14790501138815702279646275 22185751708223553419469413)
            ·
              refine ⟨4159828445291916266150515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22185751708223553419469413 4159828445291916266150515)
              ·
                refine ⟨6239742667937874399225773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4159828445291916266150515 6239742667937874399225773)
                ·
                  refine ⟨2339903500476702899709665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6239742667937874399225773 2339903500476702899709665)
                  ·
                    refine ⟨1754927625357527174782249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2339903500476702899709665 1754927625357527174782249)
                    ·
                      refine ⟨1316195719018145381086687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1754927625357527174782249 1316195719018145381086687)
                      ·
                        rfl

theorem cell23_2563282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_2563282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563282 prefixEnd_2563282 := by exact prefixLift 2563282
  have htrace : WordTrace (prefixWord ++ tailWord_2563282) baseStart_2563282 baseEnd_2563282 := by
    simpa [prefixWord, tailWord_2563282, baseEnd_2563282] using wordTrace_append hprefix tailTrace_2563282
  have hstable : (prefixWord ++ tailWord_2563282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563282).length < 2 ^ (prefixWord ++ tailWord_2563282).sum := by decide
  have hdescent : baseEnd_2563282 < baseStart_2563282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563359 : List Nat := [1, 1, 2, 4, 4, 2, 1, 2, 1, 3, 2]
def baseStart_2563359 : Nat := 118140960795 + 2563359 * 2 ^ 59
def prefixEnd_2563359 : Nat := 4983230072969 + 3 ^ 40 * 2563359 * 2
def baseEnd_2563359 : Nat := 1316235257028541579823833

theorem tailTrace_2563359 : CollatzResearch.WordTrace tailWord_2563359 prefixEnd_2563359 1316235257028541579823833 := by
  unfold tailWord_2563359
  simp only [CollatzResearch.WordTrace]
  refine ⟨93493383520395604708317131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62328922346930403138878087 93493383520395604708317131)
  ·
    refine ⟨140240075280593407062475697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93493383520395604708317131 140240075280593407062475697)
    ·
      refine ⟨105180056460445055296856773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140240075280593407062475697 105180056460445055296856773)
      ·
        refine ⟨19721260586333447868160645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105180056460445055296856773 19721260586333447868160645)
        ·
          refine ⟨3697736359937521475280121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19721260586333447868160645 3697736359937521475280121)
          ·
            refine ⟨2773302269953141106460091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3697736359937521475280121 2773302269953141106460091)
            ·
              refine ⟨4159953404929711659690137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2773302269953141106460091 4159953404929711659690137)
              ·
                refine ⟨3119965053697283744767603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4159953404929711659690137 3119965053697283744767603)
                ·
                  refine ⟨4679947580545925617151405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3119965053697283744767603 4679947580545925617151405)
                  ·
                    refine ⟨1754980342704722106431777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4679947580545925617151405 1754980342704722106431777)
                    ·
                      refine ⟨1316235257028541579823833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1754980342704722106431777 1316235257028541579823833)
                      ·
                        rfl

theorem cell23_2563359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_2563359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563359 prefixEnd_2563359 := by exact prefixLift 2563359
  have htrace : WordTrace (prefixWord ++ tailWord_2563359) baseStart_2563359 baseEnd_2563359 := by
    simpa [prefixWord, tailWord_2563359, baseEnd_2563359] using wordTrace_append hprefix tailTrace_2563359
  have hstable : (prefixWord ++ tailWord_2563359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563359).length < 2 ^ (prefixWord ++ tailWord_2563359).sum := by decide
  have hdescent : baseEnd_2563359 < baseStart_2563359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563361 : List Nat := [1, 2, 3, 2, 1, 1, 1, 3, 9]
def baseStart_2563361 : Nat := 118140960795 + 2563361 * 2 ^ 59
def prefixEnd_2563361 : Nat := 4983230072969 + 3 ^ 40 * 2563361 * 2
def baseEnd_2563361 : Nat := 146248475998872285777647

theorem tailTrace_2563361 : CollatzResearch.WordTrace tailWord_2563361 prefixEnd_2563361 146248475998872285777647 := by
  unfold tailWord_2563361
  simp only [CollatzResearch.WordTrace]
  refine ⟨93493456466388359049889937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62328970977592239366593291 93493456466388359049889937)
  ·
    refine ⟨70120092349791269287417453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93493456466388359049889937 70120092349791269287417453)
    ·
      refine ⟨26295034631171725982781545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70120092349791269287417453 26295034631171725982781545)
      ·
        refine ⟨19721275973378794487086159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26295034631171725982781545 19721275973378794487086159)
        ·
          refine ⟨29581913960068191730629239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19721275973378794487086159 29581913960068191730629239)
          ·
            refine ⟨44372870940102287595943859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29581913960068191730629239 44372870940102287595943859)
            ·
              refine ⟨66559306410153431393915789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44372870940102287595943859 66559306410153431393915789)
              ·
                refine ⟨24959739903807536772718421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66559306410153431393915789 24959739903807536772718421)
                ·
                  refine ⟨146248475998872285777647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 24959739903807536772718421 146248475998872285777647)
                  ·
                    rfl

theorem cell23_2563361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 9].length) (baseStart_2563361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563361 prefixEnd_2563361 := by exact prefixLift 2563361
  have htrace : WordTrace (prefixWord ++ tailWord_2563361) baseStart_2563361 baseEnd_2563361 := by
    simpa [prefixWord, tailWord_2563361, baseEnd_2563361] using wordTrace_append hprefix tailTrace_2563361
  have hstable : (prefixWord ++ tailWord_2563361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563361).length < 2 ^ (prefixWord ++ tailWord_2563361).sum := by decide
  have hdescent : baseEnd_2563361 < baseStart_2563361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563512 : List Nat := [2, 1, 2, 1, 2, 2, 5, 1, 3, 1, 3]
def baseStart_2563512 : Nat := 118140960795 + 2563512 * 2 ^ 59
def prefixEnd_2563512 : Nat := 4983230072969 + 3 ^ 40 * 2563512 * 2
def baseEnd_2563512 : Nat := 1316313819568679481210629

theorem tailTrace_2563512 : CollatzResearch.WordTrace tailWord_2563512 prefixEnd_2563512 1316313819568679481210629 := by
  unfold tailWord_2563512
  simp only [CollatzResearch.WordTrace]
  refine ⟨46749481944420655919318395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62332642592560874559091193 46749481944420655919318395)
  ·
    refine ⟨70124222916630983878977593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46749481944420655919318395 70124222916630983878977593)
    ·
      refine ⟨52593167187473237909233195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70124222916630983878977593 52593167187473237909233195)
      ·
        refine ⟨78889750781209856863849793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52593167187473237909233195 78889750781209856863849793)
        ·
          refine ⟨59167313085907392647887345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78889750781209856863849793 59167313085907392647887345)
          ·
            refine ⟨44375484814430544485915509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59167313085907392647887345 44375484814430544485915509)
            ·
              refine ⟨4160201701352863545554579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44375484814430544485915509 4160201701352863545554579)
              ·
                refine ⟨6240302552029295318331869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4160201701352863545554579 6240302552029295318331869)
                ·
                  refine ⟨2340113457010985744374451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6240302552029295318331869 2340113457010985744374451)
                  ·
                    refine ⟨3510170185516478616561677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2340113457010985744374451 3510170185516478616561677)
                    ·
                      refine ⟨1316313819568679481210629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3510170185516478616561677 1316313819568679481210629)
                      ·
                        rfl

theorem cell23_2563512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 3, 1, 3].length) (baseStart_2563512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563512 prefixEnd_2563512 := by exact prefixLift 2563512
  have htrace : WordTrace (prefixWord ++ tailWord_2563512) baseStart_2563512 baseEnd_2563512 := by
    simpa [prefixWord, tailWord_2563512, baseEnd_2563512] using wordTrace_append hprefix tailTrace_2563512
  have hstable : (prefixWord ++ tailWord_2563512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563512).length < 2 ^ (prefixWord ++ tailWord_2563512).sum := by decide
  have hdescent : baseEnd_2563512 < baseStart_2563512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563532 : List Nat := [2, 2, 1, 4, 2, 1, 3, 2, 1, 5]
def baseStart_2563532 : Nat := 118140960795 + 2563532 * 2 ^ 59
def prefixEnd_2563532 : Nat := 4983230072969 + 3 ^ 40 * 2563532 * 2
def baseEnd_2563532 : Nat := 438774696393923134320179

theorem tailTrace_2563532 : CollatzResearch.WordTrace tailWord_2563532 prefixEnd_2563532 438774696393923134320179 := by
  unfold tailWord_2563532
  simp only [CollatzResearch.WordTrace]
  refine ⟨46749846674384427627182425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62333128899179236836243233 46749846674384427627182425)
  ·
    refine ⟨35062385005788320720386819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46749846674384427627182425 35062385005788320720386819)
    ·
      refine ⟨52593577508682481080580229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35062385005788320720386819 52593577508682481080580229)
      ·
        refine ⟨9861295782877965202608793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52593577508682481080580229 9861295782877965202608793)
        ·
          refine ⟨7395971837158473901956595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9861295782877965202608793 7395971837158473901956595)
          ·
            refine ⟨11093957755737710852934893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7395971837158473901956595 11093957755737710852934893)
            ·
              refine ⟨4160234158401641569850585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11093957755737710852934893 4160234158401641569850585)
              ·
                refine ⟨3120175618801231177387939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4160234158401641569850585 3120175618801231177387939)
                ·
                  refine ⟨4680263428201846766081909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3120175618801231177387939 4680263428201846766081909)
                  ·
                    refine ⟨438774696393923134320179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4680263428201846766081909 438774696393923134320179)
                    ·
                      rfl

theorem cell23_2563532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 1, 5].length) (baseStart_2563532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563532 prefixEnd_2563532 := by exact prefixLift 2563532
  have htrace : WordTrace (prefixWord ++ tailWord_2563532) baseStart_2563532 baseEnd_2563532 := by
    simpa [prefixWord, tailWord_2563532, baseEnd_2563532] using wordTrace_append hprefix tailTrace_2563532
  have hstable : (prefixWord ++ tailWord_2563532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563532).length < 2 ^ (prefixWord ++ tailWord_2563532).sum := by decide
  have hdescent : baseEnd_2563532 < baseStart_2563532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563535 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 2, 6, 2]
def baseStart_2563535 : Nat := 118140960795 + 2563535 * 2 ^ 59
def prefixEnd_2563535 : Nat := 4983230072969 + 3 ^ 40 * 2563535 * 2
def baseEnd_2563535 : Nat := 1316325629623732891223023

theorem tailTrace_2563535 : CollatzResearch.WordTrace tailWord_2563535 prefixEnd_2563535 1316325629623732891223023 := by
  unfold tailWord_2563535
  simp only [CollatzResearch.WordTrace]
  refine ⟨93499802767757986766724059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62333201845171991177816039 93499802767757986766724059)
  ·
    refine ⟨140249704151636980150086089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93499802767757986766724059 140249704151636980150086089)
    ·
      refine ⟨105187278113727735112564567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140249704151636980150086089 105187278113727735112564567)
      ·
        refine ⟨157780917170591602668846851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105187278113727735112564567 157780917170591602668846851)
        ·
          refine ⟨236671375755887404003270277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157780917170591602668846851 236671375755887404003270277)
          ·
            refine ⟨44375882954228888250613177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 236671375755887404003270277 44375882954228888250613177)
            ·
              refine ⟨33281912215671666187959883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44375882954228888250613177 33281912215671666187959883)
              ·
                refine ⟨49922868323507499281939825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33281912215671666187959883 49922868323507499281939825)
                ·
                  refine ⟨37442151242630624461454869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49922868323507499281939825 37442151242630624461454869)
                  ·
                    refine ⟨1755100839498310521630697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 37442151242630624461454869 1755100839498310521630697)
                    ·
                      refine ⟨1316325629623732891223023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1755100839498310521630697 1316325629623732891223023)
                      ·
                        rfl

theorem cell23_2563535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 6, 2].length) (baseStart_2563535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563535 prefixEnd_2563535 := by exact prefixLift 2563535
  have htrace : WordTrace (prefixWord ++ tailWord_2563535) baseStart_2563535 baseEnd_2563535 := by
    simpa [prefixWord, tailWord_2563535, baseEnd_2563535] using wordTrace_append hprefix tailTrace_2563535
  have hstable : (prefixWord ++ tailWord_2563535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563535).length < 2 ^ (prefixWord ++ tailWord_2563535).sum := by decide
  have hdescent : baseEnd_2563535 < baseStart_2563535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563545 : List Nat := [1, 2, 1, 2, 4, 3, 1, 2, 1, 6]
def baseStart_2563545 : Nat := 118140960795 + 2563545 * 2 ^ 59
def prefixEnd_2563545 : Nat := 4983230072969 + 3 ^ 40 * 2563545 * 2
def baseEnd_2563545 : Nat := 438776921476759284032659

theorem tailTrace_2563545 : CollatzResearch.WordTrace tailWord_2563545 prefixEnd_2563545 438776921476759284032659 := by
  unfold tailWord_2563545
  simp only [CollatzResearch.WordTrace]
  refine ⟨93500167497721758474588089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62333444998481172316392059 93500167497721758474588089)
  ·
    refine ⟨70125125623291318855941067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93500167497721758474588089 70125125623291318855941067)
    ·
      refine ⟨105187688434936978283911601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70125125623291318855941067 105187688434936978283911601)
      ·
        refine ⟨78890766326202733712933701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105187688434936978283911601 78890766326202733712933701)
        ·
          refine ⟨14792018686163012571175069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78890766326202733712933701 14792018686163012571175069)
          ·
            refine ⟨5547007007311129714190651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14792018686163012571175069 5547007007311129714190651)
            ·
              refine ⟨8320510510966694571285977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5547007007311129714190651 8320510510966694571285977)
              ·
                refine ⟨6240382883225020928464483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8320510510966694571285977 6240382883225020928464483)
                ·
                  refine ⟨9360574324837531392696725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6240382883225020928464483 9360574324837531392696725)
                  ·
                    refine ⟨438776921476759284032659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9360574324837531392696725 438776921476759284032659)
                    ·
                      rfl

theorem cell23_2563545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 6].length) (baseStart_2563545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563545 prefixEnd_2563545 := by exact prefixLift 2563545
  have htrace : WordTrace (prefixWord ++ tailWord_2563545) baseStart_2563545 baseEnd_2563545 := by
    simpa [prefixWord, tailWord_2563545, baseEnd_2563545] using wordTrace_append hprefix tailTrace_2563545
  have hstable : (prefixWord ++ tailWord_2563545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563545).length < 2 ^ (prefixWord ++ tailWord_2563545).sum := by decide
  have hdescent : baseEnd_2563545 < baseStart_2563545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563549 : List Nat := [1, 4, 3, 1, 1, 3, 3, 1, 1, 5]
def baseStart_2563549 : Nat := 118140960795 + 2563549 * 2 ^ 59
def prefixEnd_2563549 : Nat := 4983230072969 + 3 ^ 40 * 2563549 * 2
def baseEnd_2563549 : Nat := 438777606117631945482653

theorem tailTrace_2563549 : CollatzResearch.WordTrace tailWord_2563549 prefixEnd_2563549 438777606117631945482653 := by
  unfold tailWord_2563549
  simp only [CollatzResearch.WordTrace]
  refine ⟨93500313389707267157733701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62333542259804844771822467 93500313389707267157733701)
  ·
    refine ⟨17531308760570112592075069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93500313389707267157733701 17531308760570112592075069)
    ·
      refine ⟨6574240785213792222028151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17531308760570112592075069 6574240785213792222028151)
      ·
        refine ⟨9861361177820688333042227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6574240785213792222028151 9861361177820688333042227)
        ·
          refine ⟨14792041766731032499563341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9861361177820688333042227 14792041766731032499563341)
          ·
            refine ⟨5547015662524137187336253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14792041766731032499563341 5547015662524137187336253)
            ·
              refine ⟨2080130873446551445251095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5547015662524137187336253 2080130873446551445251095)
              ·
                refine ⟨3120196310169827167876643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2080130873446551445251095 3120196310169827167876643)
                ·
                  refine ⟨4680294465254740751814965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3120196310169827167876643 4680294465254740751814965)
                  ·
                    refine ⟨438777606117631945482653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4680294465254740751814965 438777606117631945482653)
                    ·
                      rfl

theorem cell23_2563549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_2563549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563549 prefixEnd_2563549 := by exact prefixLift 2563549
  have htrace : WordTrace (prefixWord ++ tailWord_2563549) baseStart_2563549 baseEnd_2563549 := by
    simpa [prefixWord, tailWord_2563549, baseEnd_2563549] using wordTrace_append hprefix tailTrace_2563549
  have hstable : (prefixWord ++ tailWord_2563549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563549).length < 2 ^ (prefixWord ++ tailWord_2563549).sum := by decide
  have hdescent : baseEnd_2563549 < baseStart_2563549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563552 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 7, 2, 2]
def baseStart_2563552 : Nat := 118140960795 + 2563552 * 2 ^ 59
def prefixEnd_2563552 : Nat := 4983230072969 + 3 ^ 40 * 2563552 * 2
def baseEnd_2563552 : Nat := 1316334358794859324710445

theorem tailTrace_2563552 : CollatzResearch.WordTrace tailWord_2563552 prefixEnd_2563552 1316334358794859324710445 := by
  unfold tailWord_2563552
  simp only [CollatzResearch.WordTrace]
  refine ⟨46750211404348199335046455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62333615205797599113395273 46750211404348199335046455)
  ·
    refine ⟨70125317106522299002569683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46750211404348199335046455 70125317106522299002569683)
    ·
      refine ⟨105187975659783448503854525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70125317106522299002569683 105187975659783448503854525)
      ·
        refine ⟨39445490872418793188945447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105187975659783448503854525 39445490872418793188945447)
        ·
          refine ⟨59168236308628189783418171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39445490872418793188945447 59168236308628189783418171)
          ·
            refine ⟨88752354462942284675127257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59168236308628189783418171 88752354462942284675127257)
            ·
              refine ⟨66564265847206713506345443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88752354462942284675127257 66564265847206713506345443)
              ·
                refine ⟨99846398770810070259518165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66564265847206713506345443 99846398770810070259518165)
                ·
                  refine ⟨2340149971190861021707457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 99846398770810070259518165 2340149971190861021707457)
                  ·
                    refine ⟨1755112478393145766280593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2340149971190861021707457 1755112478393145766280593)
                    ·
                      refine ⟨1316334358794859324710445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1755112478393145766280593 1316334358794859324710445)
                      ·
                        rfl

theorem cell23_2563552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 7, 2, 2].length) (baseStart_2563552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563552 prefixEnd_2563552 := by exact prefixLift 2563552
  have htrace : WordTrace (prefixWord ++ tailWord_2563552) baseStart_2563552 baseEnd_2563552 := by
    simpa [prefixWord, tailWord_2563552, baseEnd_2563552] using wordTrace_append hprefix tailTrace_2563552
  have hstable : (prefixWord ++ tailWord_2563552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563552).length < 2 ^ (prefixWord ++ tailWord_2563552).sum := by decide
  have hdescent : baseEnd_2563552 < baseStart_2563552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563586 : List Nat := [3, 4, 1, 2, 1, 1, 1, 1, 5, 2, 2]
def baseStart_2563586 : Nat := 118140960795 + 2563586 * 2 ^ 59
def prefixEnd_2563586 : Nat := 4983230072969 + 3 ^ 40 * 2563586 * 2
def baseEnd_2563586 : Nat := 1316351817137112191685289

theorem tailTrace_2563586 : CollatzResearch.WordTrace tailWord_2563586 prefixEnd_2563586 1316351817137112191685289 := by
  unfold tailWord_2563586
  simp only [CollatzResearch.WordTrace]
  refine ⟨23375415722643305619207653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62334441927048814984553741 23375415722643305619207653)
  ·
    refine ⟨4382890447995619803601435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23375415722643305619207653 4382890447995619803601435)
    ·
      refine ⟨6574335671993429705402153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4382890447995619803601435 6574335671993429705402153)
      ·
        refine ⟨4930751753995072279051615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6574335671993429705402153 4930751753995072279051615)
        ·
          refine ⟨7396127630992608418577423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4930751753995072279051615 7396127630992608418577423)
          ·
            refine ⟨11094191446488912627866135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7396127630992608418577423 11094191446488912627866135)
            ·
              refine ⟨16641287169733368941799203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11094191446488912627866135 16641287169733368941799203)
              ·
                refine ⟨24961930754600053412698805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16641287169733368941799203 24961930754600053412698805)
                ·
                  refine ⟨2340181008243755007440513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24961930754600053412698805 2340181008243755007440513)
                  ·
                    refine ⟨1755135756182816255580385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2340181008243755007440513 1755135756182816255580385)
                    ·
                      refine ⟨1316351817137112191685289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1755135756182816255580385 1316351817137112191685289)
                      ·
                        rfl

theorem cell23_2563586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_2563586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563586 prefixEnd_2563586 := by exact prefixLift 2563586
  have htrace : WordTrace (prefixWord ++ tailWord_2563586) baseStart_2563586 baseEnd_2563586 := by
    simpa [prefixWord, tailWord_2563586, baseEnd_2563586] using wordTrace_append hprefix tailTrace_2563586
  have hstable : (prefixWord ++ tailWord_2563586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563586).length < 2 ^ (prefixWord ++ tailWord_2563586).sum := by decide
  have hdescent : baseEnd_2563586 < baseStart_2563586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563619 : List Nat := [1, 1, 1, 4, 5, 1, 1, 1, 4, 1, 3]
def baseStart_2563619 : Nat := 118140960795 + 2563619 * 2 ^ 59
def prefixEnd_2563619 : Nat := 4983230072969 + 3 ^ 40 * 2563619 * 2
def baseEnd_2563619 : Nat := 1316368761998710562572637

theorem tailTrace_2563619 : CollatzResearch.WordTrace tailWord_2563619 prefixEnd_2563619 1316368761998710562572637 := by
  unfold tailWord_2563619
  simp only [CollatzResearch.WordTrace]
  refine ⟨93502866499453669112781911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62335244332969112741854607 93502866499453669112781911)
  ·
    refine ⟨140254299749180503669172867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93502866499453669112781911 140254299749180503669172867)
    ·
      refine ⟨210381449623770755503759301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140254299749180503669172867 210381449623770755503759301)
      ·
        refine ⟨39446521804457016656954869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 210381449623770755503759301 39446521804457016656954869)
        ·
          refine ⟨3698111419167845311589519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39446521804457016656954869 3698111419167845311589519)
          ·
            refine ⟨5547167128751767967384279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3698111419167845311589519 5547167128751767967384279)
            ·
              refine ⟨8320750693127651951076419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5547167128751767967384279 8320750693127651951076419)
              ·
                refine ⟨12481126039691477926614629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8320750693127651951076419 12481126039691477926614629)
                ·
                  refine ⟨2340211132442152111240243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12481126039691477926614629 2340211132442152111240243)
                  ·
                    refine ⟨3510316698663228166860365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2340211132442152111240243 3510316698663228166860365)
                    ·
                      refine ⟨1316368761998710562572637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3510316698663228166860365 1316368761998710562572637)
                      ·
                        rfl

theorem cell23_2563619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 4, 1, 3].length) (baseStart_2563619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563619 prefixEnd_2563619 := by exact prefixLift 2563619
  have htrace : WordTrace (prefixWord ++ tailWord_2563619) baseStart_2563619 baseEnd_2563619 := by
    simpa [prefixWord, tailWord_2563619, baseEnd_2563619] using wordTrace_append hprefix tailTrace_2563619
  have hstable : (prefixWord ++ tailWord_2563619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563619).length < 2 ^ (prefixWord ++ tailWord_2563619).sum := by decide
  have hdescent : baseEnd_2563619 < baseStart_2563619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563635 : List Nat := [1, 1, 1, 2, 4, 3, 2, 1, 2, 6]
def baseStart_2563635 : Nat := 118140960795 + 2563635 * 2 ^ 59
def prefixEnd_2563635 : Nat := 4983230072969 + 3 ^ 40 * 2563635 * 2
def baseEnd_2563635 : Nat := 438792325896394166657521

theorem tailTrace_2563635 : CollatzResearch.WordTrace tailWord_2563635 prefixEnd_2563635 438792325896394166657521 := by
  unfold tailWord_2563635
  simp only [CollatzResearch.WordTrace]
  refine ⟨93503450067395703845364359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62335633378263802563576239 93503450067395703845364359)
  ·
    refine ⟨140255175101093555768046539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93503450067395703845364359 140255175101093555768046539)
    ·
      refine ⟨210382762651640333652069809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140255175101093555768046539 210382762651640333652069809)
      ·
        refine ⟨157787071988730250239052357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210382762651640333652069809 157787071988730250239052357)
        ·
          refine ⟨29585075997886921919822317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 157787071988730250239052357 29585075997886921919822317)
          ·
            refine ⟨11094403499207595719933369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29585075997886921919822317 11094403499207595719933369)
            ·
              refine ⟨8320802624405696789950027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11094403499207595719933369 8320802624405696789950027)
              ·
                refine ⟨12481203936608545184925041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8320802624405696789950027 12481203936608545184925041)
                ·
                  refine ⟨9360902952456408888693781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12481203936608545184925041 9360902952456408888693781)
                  ·
                    refine ⟨438792325896394166657521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9360902952456408888693781 438792325896394166657521)
                    ·
                      rfl

theorem cell23_2563635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 6].length) (baseStart_2563635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563635 prefixEnd_2563635 := by exact prefixLift 2563635
  have htrace : WordTrace (prefixWord ++ tailWord_2563635) baseStart_2563635 baseEnd_2563635 := by
    simpa [prefixWord, tailWord_2563635, baseEnd_2563635] using wordTrace_append hprefix tailTrace_2563635
  have hstable : (prefixWord ++ tailWord_2563635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563635).length < 2 ^ (prefixWord ++ tailWord_2563635).sum := by decide
  have hdescent : baseEnd_2563635 < baseStart_2563635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563654 : List Nat := [6, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2]
def baseStart_2563654 : Nat := 118140960795 + 2563654 * 2 ^ 59
def prefixEnd_2563654 : Nat := 4983230072969 + 3 ^ 40 * 2563654 * 2
def baseEnd_2563654 : Nat := 1316386733821617925634977

theorem tailTrace_2563654 : CollatzResearch.WordTrace tailWord_2563654 prefixEnd_2563654 1316386733821617925634977 := by
  unfold tailWord_2563654
  simp only [CollatzResearch.WordTrace]
  refine ⟨2922004470447714690322063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 62336095369551246726870677 2922004470447714690322063)
  ·
    refine ⟨4383006705671572035483095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2922004470447714690322063 4383006705671572035483095)
    ·
      refine ⟨6574510058507358053224643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4383006705671572035483095 6574510058507358053224643)
      ·
        refine ⟨9861765087761037079836965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6574510058507358053224643 9861765087761037079836965)
        ·
          refine ⟨1849080953955194452469431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9861765087761037079836965 1849080953955194452469431)
          ·
            refine ⟨2773621430932791678704147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1849080953955194452469431 2773621430932791678704147)
            ·
              refine ⟨4160432146399187518056221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2773621430932791678704147 4160432146399187518056221)
              ·
                refine ⟨1560162054899695319271083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4160432146399187518056221 1560162054899695319271083)
                ·
                  refine ⟨2340243082349542978906625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1560162054899695319271083 2340243082349542978906625)
                  ·
                    refine ⟨1755182311762157234179969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2340243082349542978906625 1755182311762157234179969)
                    ·
                      refine ⟨1316386733821617925634977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1755182311762157234179969 1316386733821617925634977)
                      ·
                        rfl

theorem cell23_2563654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_2563654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563654 prefixEnd_2563654 := by exact prefixLift 2563654
  have htrace : WordTrace (prefixWord ++ tailWord_2563654) baseStart_2563654 baseEnd_2563654 := by
    simpa [prefixWord, tailWord_2563654, baseEnd_2563654] using wordTrace_append hprefix tailTrace_2563654
  have hstable : (prefixWord ++ tailWord_2563654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563654).length < 2 ^ (prefixWord ++ tailWord_2563654).sum := by decide
  have hdescent : baseEnd_2563654 < baseStart_2563654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563676 : List Nat := [2, 2, 4, 1, 2, 1, 2, 1, 4, 2, 2]
def baseStart_2563676 : Nat := 118140960795 + 2563676 * 2 ^ 59
def prefixEnd_2563676 : Nat := 4983230072969 + 3 ^ 40 * 2563676 * 2
def baseEnd_2563676 : Nat := 1316398030396016839559875

theorem tailTrace_2563676 : CollatzResearch.WordTrace tailWord_2563676 prefixEnd_2563676 1316398030396016839559875 := by
  unfold tailWord_2563676
  simp only [CollatzResearch.WordTrace]
  refine ⟨46752472730123583923803441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62336630306831445231737921 46752472730123583923803441)
  ·
    refine ⟨35064354547592687942852581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46752472730123583923803441 35064354547592687942852581)
    ·
      refine ⟨6574566477673628989284859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35064354547592687942852581 6574566477673628989284859)
      ·
        refine ⟨9861849716510443483927289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6574566477673628989284859 9861849716510443483927289)
        ·
          refine ⟨7396387287382832612945467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9861849716510443483927289 7396387287382832612945467)
          ·
            refine ⟨11094580931074248919418201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7396387287382832612945467 11094580931074248919418201)
            ·
              refine ⟨8320935698305686689563651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11094580931074248919418201 8320935698305686689563651)
              ·
                refine ⟨12481403547458530034345477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8320935698305686689563651 12481403547458530034345477)
                ·
                  refine ⟨2340263165148474381439777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12481403547458530034345477 2340263165148474381439777)
                  ·
                    refine ⟨1755197373861355786079833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2340263165148474381439777 1755197373861355786079833)
                    ·
                      refine ⟨1316398030396016839559875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1755197373861355786079833 1316398030396016839559875)
                      ·
                        rfl

theorem cell23_2563676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_2563676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563676 prefixEnd_2563676 := by exact prefixLift 2563676
  have htrace : WordTrace (prefixWord ++ tailWord_2563676) baseStart_2563676 baseEnd_2563676 := by
    simpa [prefixWord, tailWord_2563676, baseEnd_2563676] using wordTrace_append hprefix tailTrace_2563676
  have hstable : (prefixWord ++ tailWord_2563676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563676).length < 2 ^ (prefixWord ++ tailWord_2563676).sum := by decide
  have hdescent : baseEnd_2563676 < baseStart_2563676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563693 : List Nat := [1, 5, 1, 1, 4, 1, 1, 3, 2, 2, 2]
def baseStart_2563693 : Nat := 118140960795 + 2563693 * 2 ^ 59
def prefixEnd_2563693 : Nat := 4983230072969 + 3 ^ 40 * 2563693 * 2
def baseEnd_2563693 : Nat := 1316406759567143273047297

theorem tailTrace_2563693 : CollatzResearch.WordTrace tailWord_2563693 prefixEnd_2563693 1316406759567143273047297 := by
  unfold tailWord_2563693
  simp only [CollatzResearch.WordTrace]
  refine ⟨93505565501185579750975733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62337043667457053167317155 93505565501185579750975733)
  ·
    refine ⟨8766146765736148101653975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93505565501185579750975733 8766146765736148101653975)
    ·
      refine ⟨13149220148604222152480963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8766146765736148101653975 13149220148604222152480963)
      ·
        refine ⟨19723830222906333228721445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13149220148604222152480963 19723830222906333228721445)
        ·
          refine ⟨3698218166794937480385271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19723830222906333228721445 3698218166794937480385271)
          ·
            refine ⟨5547327250192406220577907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3698218166794937480385271 5547327250192406220577907)
            ·
              refine ⟨8320990875288609330866861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5547327250192406220577907 8320990875288609330866861)
              ·
                refine ⟨3120371578233228499075073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8320990875288609330866861 3120371578233228499075073)
                ·
                  refine ⟨2340278683674921374306305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3120371578233228499075073 2340278683674921374306305)
                  ·
                    refine ⟨1755209012756191030729729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2340278683674921374306305 1755209012756191030729729)
                    ·
                      refine ⟨1316406759567143273047297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1755209012756191030729729 1316406759567143273047297)
                      ·
                        rfl

theorem cell23_2563693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_2563693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563693 prefixEnd_2563693 := by exact prefixLift 2563693
  have htrace : WordTrace (prefixWord ++ tailWord_2563693) baseStart_2563693 baseEnd_2563693 := by
    simpa [prefixWord, tailWord_2563693, baseEnd_2563693] using wordTrace_append hprefix tailTrace_2563693
  have hstable : (prefixWord ++ tailWord_2563693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563693).length < 2 ^ (prefixWord ++ tailWord_2563693).sum := by decide
  have hdescent : baseEnd_2563693 < baseStart_2563693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563695 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 6, 5]
def baseStart_2563695 : Nat := 118140960795 + 2563695 * 2 ^ 59
def prefixEnd_2563695 : Nat := 4983230072969 + 3 ^ 40 * 2563695 * 2
def baseEnd_2563695 : Nat := 438802595509484088407429

theorem tailTrace_2563695 : CollatzResearch.WordTrace tailWord_2563695 prefixEnd_2563695 438802595509484088407429 := by
  unfold tailWord_2563695
  simp only [CollatzResearch.WordTrace]
  refine ⟨93505638447178334092548539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62337092298118889395032359 93505638447178334092548539)
  ·
    refine ⟨140258457670767501138822809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93505638447178334092548539 140258457670767501138822809)
    ·
      refine ⟨105193843253075625854117107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140258457670767501138822809 105193843253075625854117107)
      ·
        refine ⟨157790764879613438781175661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105193843253075625854117107 157790764879613438781175661)
        ·
          refine ⟨59171536829855039542940873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157790764879613438781175661 59171536829855039542940873)
          ·
            refine ⟨44378652622391279657205655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59171536829855039542940873 44378652622391279657205655)
            ·
              refine ⟨66567978933586919485808483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44378652622391279657205655 66567978933586919485808483)
              ·
                refine ⟨99851968400380379228712725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66567978933586919485808483 99851968400380379228712725)
                ·
                  refine ⟨4680561018767830276345909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 99851968400380379228712725 4680561018767830276345909)
                  ·
                    refine ⟨438802595509484088407429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4680561018767830276345909 438802595509484088407429)
                    ·
                      rfl

theorem cell23_2563695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 5].length) (baseStart_2563695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563695 prefixEnd_2563695 := by exact prefixLift 2563695
  have htrace : WordTrace (prefixWord ++ tailWord_2563695) baseStart_2563695 baseEnd_2563695 := by
    simpa [prefixWord, tailWord_2563695, baseEnd_2563695] using wordTrace_append hprefix tailTrace_2563695
  have hstable : (prefixWord ++ tailWord_2563695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563695).length < 2 ^ (prefixWord ++ tailWord_2563695).sum := by decide
  have hdescent : baseEnd_2563695 < baseStart_2563695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563705 : List Nat := [1, 2, 1, 3, 3, 1, 1, 2, 1, 1, 7]
def baseStart_2563705 : Nat := 118140960795 + 2563705 * 2 ^ 59
def prefixEnd_2563705 : Nat := 4983230072969 + 3 ^ 40 * 2563705 * 2
def baseEnd_2563705 : Nat := 1316412921334997226097241

theorem tailTrace_2563705 : CollatzResearch.WordTrace tailWord_2563705 prefixEnd_2563705 1316412921334997226097241 := by
  unfold tailWord_2563705
  simp only [CollatzResearch.WordTrace]
  refine ⟨93506003177142105800412569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62337335451428070533608379 93506003177142105800412569)
  ·
    refine ⟨70129502382856579350309427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93506003177142105800412569 70129502382856579350309427)
    ·
      refine ⟨105194253574284869025464141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70129502382856579350309427 105194253574284869025464141)
      ·
        refine ⟨39447845090356825884549053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105194253574284869025464141 39447845090356825884549053)
        ·
          refine ⟨14792941908883809706705895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39447845090356825884549053 14792941908883809706705895)
          ·
            refine ⟨22189412863325714560058843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14792941908883809706705895 22189412863325714560058843)
            ·
              refine ⟨33284119294988571840088265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22189412863325714560058843 33284119294988571840088265)
              ·
                refine ⟨24963089471241428880066199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33284119294988571840088265 24963089471241428880066199)
                ·
                  refine ⟨37444634206862143320099299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24963089471241428880066199 37444634206862143320099299)
                  ·
                    refine ⟨56166951310293214980148949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37444634206862143320099299 56166951310293214980148949)
                    ·
                      refine ⟨1316412921334997226097241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 56166951310293214980148949 1316412921334997226097241)
                      ·
                        rfl

theorem cell23_2563705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_2563705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563705 prefixEnd_2563705 := by exact prefixLift 2563705
  have htrace : WordTrace (prefixWord ++ tailWord_2563705) baseStart_2563705 baseEnd_2563705 := by
    simpa [prefixWord, tailWord_2563705, baseEnd_2563705] using wordTrace_append hprefix tailTrace_2563705
  have hstable : (prefixWord ++ tailWord_2563705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563705).length < 2 ^ (prefixWord ++ tailWord_2563705).sum := by decide
  have hdescent : baseEnd_2563705 < baseStart_2563705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563712 : List Nat := [2, 1, 1, 2, 1, 4, 4, 1, 2, 5]
def baseStart_2563712 : Nat := 118140960795 + 2563712 * 2 ^ 59
def prefixEnd_2563712 : Nat := 4983230072969 + 3 ^ 40 * 2563712 * 2
def baseEnd_2563712 : Nat := 438805505233192899569903

theorem tailTrace_2563712 : CollatzResearch.WordTrace tailWord_2563712 prefixEnd_2563712 438805505233192899569903 := by
  unfold tailWord_2563712
  simp only [CollatzResearch.WordTrace]
  refine ⟨46753129244058372997958695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62337505658744497330611593 46753129244058372997958695)
  ·
    refine ⟨70129693866087559496938043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46753129244058372997958695 70129693866087559496938043)
    ·
      refine ⟨105194540799131339245407065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70129693866087559496938043 105194540799131339245407065)
      ·
        refine ⟨78895905599348504434055299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105194540799131339245407065 78895905599348504434055299)
        ·
          refine ⟨118343858399022756651082949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78895905599348504434055299 118343858399022756651082949)
          ·
            refine ⟨22189473449816766872078053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118343858399022756651082949 22189473449816766872078053)
            ·
              refine ⟨4160526271840643788514635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22189473449816766872078053 4160526271840643788514635)
              ·
                refine ⟨6240789407760965682771953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4160526271840643788514635 6240789407760965682771953)
                ·
                  refine ⟨4680592055820724262078965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6240789407760965682771953 4680592055820724262078965)
                  ·
                    refine ⟨438805505233192899569903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4680592055820724262078965 438805505233192899569903)
                    ·
                      rfl

theorem cell23_2563712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 2, 5].length) (baseStart_2563712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563712 prefixEnd_2563712 := by exact prefixLift 2563712
  have htrace : WordTrace (prefixWord ++ tailWord_2563712) baseStart_2563712 baseEnd_2563712 := by
    simpa [prefixWord, tailWord_2563712, baseEnd_2563712] using wordTrace_append hprefix tailTrace_2563712
  have hstable : (prefixWord ++ tailWord_2563712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563712).length < 2 ^ (prefixWord ++ tailWord_2563712).sum := by decide
  have hdescent : baseEnd_2563712 < baseStart_2563712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563722 : List Nat := [3, 1, 2, 3, 2, 1, 1, 2, 1, 2, 5]
def baseStart_2563722 : Nat := 118140960795 + 2563722 * 2 ^ 59
def prefixEnd_2563722 : Nat := 4983230072969 + 3 ^ 40 * 2563722 * 2
def baseEnd_2563722 : Nat := 1316421650506123659584663

theorem tailTrace_2563722 : CollatzResearch.WordTrace tailWord_2563722 prefixEnd_2563722 1316421650506123659584663 := by
  unfold tailWord_2563722
  simp only [CollatzResearch.WordTrace]
  refine ⟨23376655804520129425945355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62337748812053678469187613 23376655804520129425945355)
  ·
    refine ⟨35064983706780194138918033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23376655804520129425945355 35064983706780194138918033)
    ·
      refine ⟨26298737780085145604188525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35064983706780194138918033 26298737780085145604188525)
      ·
        refine ⟨9862026667531929601570697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26298737780085145604188525 9862026667531929601570697)
        ·
          refine ⟨7396520000648947201178023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9862026667531929601570697 7396520000648947201178023)
          ·
            refine ⟨11094780000973420801767035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7396520000648947201178023 11094780000973420801767035)
            ·
              refine ⟨16642170001460131202650553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11094780000973420801767035 16642170001460131202650553)
              ·
                refine ⟨12481627501095098401987915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16642170001460131202650553 12481627501095098401987915)
                ·
                  refine ⟨18722441251642647602981873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12481627501095098401987915 18722441251642647602981873)
                  ·
                    refine ⟨14041830938731985702236405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18722441251642647602981873 14041830938731985702236405)
                    ·
                      refine ⟨1316421650506123659584663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14041830938731985702236405 1316421650506123659584663)
                      ·
                        rfl

theorem cell23_2563722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_2563722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563722 prefixEnd_2563722 := by exact prefixLift 2563722
  have htrace : WordTrace (prefixWord ++ tailWord_2563722) baseStart_2563722 baseEnd_2563722 := by
    simpa [prefixWord, tailWord_2563722, baseEnd_2563722] using wordTrace_append hprefix tailTrace_2563722
  have hstable : (prefixWord ++ tailWord_2563722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563722).length < 2 ^ (prefixWord ++ tailWord_2563722).sum := by decide
  have hdescent : baseEnd_2563722 < baseStart_2563722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563766 : List Nat := [5, 1, 3, 1, 1, 2, 1, 1, 1, 3, 4]
def baseStart_2563766 : Nat := 118140960795 + 2563766 * 2 ^ 59
def prefixEnd_2563766 : Nat := 4983230072969 + 3 ^ 40 * 2563766 * 2
def baseEnd_2563766 : Nat := 1316444243654921487434461

theorem tailTrace_2563766 : CollatzResearch.WordTrace tailWord_2563766 prefixEnd_2563766 1316444243654921487434461 := by
  unfold tailWord_2563766
  simp only [CollatzResearch.WordTrace]
  refine ⟨5844264251870069576148947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62338818686614075478922101 5844264251870069576148947)
  ·
    refine ⟨8766396377805104364223421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5844264251870069576148947 8766396377805104364223421)
    ·
      refine ⟨3287398641676914136583783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8766396377805104364223421 3287398641676914136583783)
      ·
        refine ⟨4931097962515371204875675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3287398641676914136583783 4931097962515371204875675)
        ·
          refine ⟨7396646943773056807313513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4931097962515371204875675 7396646943773056807313513)
          ·
            refine ⟨5547485207829792605485135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7396646943773056807313513 5547485207829792605485135)
            ·
              refine ⟨8321227811744688908227703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5547485207829792605485135 8321227811744688908227703)
              ·
                refine ⟨12481841717617033362341555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8321227811744688908227703 12481841717617033362341555)
                ·
                  refine ⟨18722762576425550043512333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12481841717617033362341555 18722762576425550043512333)
                  ·
                    refine ⟨7021035966159581266317125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18722762576425550043512333 7021035966159581266317125)
                    ·
                      refine ⟨1316444243654921487434461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7021035966159581266317125 1316444243654921487434461)
                      ·
                        rfl

theorem cell23_2563766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_2563766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563766 prefixEnd_2563766 := by exact prefixLift 2563766
  have htrace : WordTrace (prefixWord ++ tailWord_2563766) baseStart_2563766 baseEnd_2563766 := by
    simpa [prefixWord, tailWord_2563766, baseEnd_2563766] using wordTrace_append hprefix tailTrace_2563766
  have hstable : (prefixWord ++ tailWord_2563766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563766).length < 2 ^ (prefixWord ++ tailWord_2563766).sum := by decide
  have hdescent : baseEnd_2563766 < baseStart_2563766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563769 : List Nat := [1, 2, 1, 4, 1, 1, 5, 1, 2, 2, 3]
def baseStart_2563769 : Nat := 118140960795 + 2563769 * 2 ^ 59
def prefixEnd_2563769 : Nat := 4983230072969 + 3 ^ 40 * 2563769 * 2
def baseEnd_2563769 : Nat := 1316445784096884975696947

theorem tailTrace_2563769 : CollatzResearch.WordTrace tailWord_2563769 prefixEnd_2563769 1316445784096884975696947 := by
  unfold tailWord_2563769
  simp only [CollatzResearch.WordTrace]
  refine ⟨93508337448910244730742361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62338891632606829820494907 93508337448910244730742361)
  ·
    refine ⟨70131253086682683548056771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93508337448910244730742361 70131253086682683548056771)
    ·
      refine ⟨105196879630024025322085157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70131253086682683548056771 105196879630024025322085157)
      ·
        refine ⟨19724414930629504747890967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105196879630024025322085157 19724414930629504747890967)
        ·
          refine ⟨29586622395944257121836451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19724414930629504747890967 29586622395944257121836451)
          ·
            refine ⟨44379933593916385682754677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29586622395944257121836451 44379933593916385682754677)
            ·
              refine ⟨4160618774429661157758251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44379933593916385682754677 4160618774429661157758251)
              ·
                refine ⟨6240928161644491736637377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4160618774429661157758251 6240928161644491736637377)
                ·
                  refine ⟨4680696121233368802478033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6240928161644491736637377 4680696121233368802478033)
                  ·
                    refine ⟨3510522090925026601858525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4680696121233368802478033 3510522090925026601858525)
                    ·
                      refine ⟨1316445784096884975696947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3510522090925026601858525 1316445784096884975696947)
                      ·
                        rfl

theorem cell23_2563769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_2563769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563769 prefixEnd_2563769 := by exact prefixLift 2563769
  have htrace : WordTrace (prefixWord ++ tailWord_2563769) baseStart_2563769 baseEnd_2563769 := by
    simpa [prefixWord, tailWord_2563769, baseEnd_2563769] using wordTrace_append hprefix tailTrace_2563769
  have hstable : (prefixWord ++ tailWord_2563769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563769).length < 2 ^ (prefixWord ++ tailWord_2563769).sum := by decide
  have hdescent : baseEnd_2563769 < baseStart_2563769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563776 : List Nat := [2, 1, 1, 2, 4, 1, 4, 3, 1, 4]
def baseStart_2563776 : Nat := 118140960795 + 2563776 * 2 ^ 59
def prefixEnd_2563776 : Nat := 4983230072969 + 3 ^ 40 * 2563776 * 2
def baseEnd_2563776 : Nat := 438816459487155482769805

theorem tailTrace_2563776 : CollatzResearch.WordTrace tailWord_2563776 prefixEnd_2563776 438816459487155482769805 := by
  unfold tailWord_2563776
  simp only [CollatzResearch.WordTrace]
  refine ⟨46754296379942442463123591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62339061839923256617498121 46754296379942442463123591)
  ·
    refine ⟨70131444569913663694685387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46754296379942442463123591 70131444569913663694685387)
    ·
      refine ⟨105197166854870495542028081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70131444569913663694685387 105197166854870495542028081)
      ·
        refine ⟨78897875141152871656521061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105197166854870495542028081 78897875141152871656521061)
        ·
          refine ⟨14793351588966163435597699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78897875141152871656521061 14793351588966163435597699)
          ·
            refine ⟨22190027383449245153396549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14793351588966163435597699 22190027383449245153396549)
            ·
              refine ⟨4160630134396733466261853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22190027383449245153396549 4160630134396733466261853)
              ·
                refine ⟨1560236300398775049848195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4160630134396733466261853 1560236300398775049848195)
                ·
                  refine ⟨2340354450598162574772293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1560236300398775049848195 2340354450598162574772293)
                  ·
                    refine ⟨438816459487155482769805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2340354450598162574772293 438816459487155482769805)
                    ·
                      rfl

theorem cell23_2563776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 3, 1, 4].length) (baseStart_2563776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563776 prefixEnd_2563776 := by exact prefixLift 2563776
  have htrace : WordTrace (prefixWord ++ tailWord_2563776) baseStart_2563776 baseEnd_2563776 := by
    simpa [prefixWord, tailWord_2563776, baseEnd_2563776] using wordTrace_append hprefix tailTrace_2563776
  have hstable : (prefixWord ++ tailWord_2563776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563776).length < 2 ^ (prefixWord ++ tailWord_2563776).sum := by decide
  have hdescent : baseEnd_2563776 < baseStart_2563776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563795 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 7]
def baseStart_2563795 : Nat := 118140960795 + 2563795 * 2 ^ 59
def prefixEnd_2563795 : Nat := 4983230072969 + 3 ^ 40 * 2563795 * 2
def baseEnd_2563795 : Nat := 1316459134593901873971827

theorem tailTrace_2563795 : CollatzResearch.WordTrace tailWord_2563795 prefixEnd_2563795 1316459134593901873971827 := by
  unfold tailWord_2563795
  simp only [CollatzResearch.WordTrace]
  refine ⟨93509285746816051171188839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62339523831210700780792559 93509285746816051171188839)
  ·
    refine ⟨140263928620224076756783259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93509285746816051171188839 140263928620224076756783259)
    ·
      refine ⟨210395892930336115135174889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140263928620224076756783259 210395892930336115135174889)
      ·
        refine ⟨157796919697752086351381167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210395892930336115135174889 157796919697752086351381167)
        ·
          refine ⟨236695379546628129527071751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157796919697752086351381167 236695379546628129527071751)
          ·
            refine ⟨355043069319942194290607627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236695379546628129527071751 355043069319942194290607627)
            ·
              refine ⟨532564603979913291435911441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355043069319942194290607627 532564603979913291435911441)
              ·
                refine ⟨399423452984934968576933581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 532564603979913291435911441 399423452984934968576933581)
                ·
                  refine ⟨149783794869350613216350093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 399423452984934968576933581 149783794869350613216350093)
                  ·
                    refine ⟨56168923076006479956131285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 149783794869350613216350093 56168923076006479956131285)
                    ·
                      refine ⟨1316459134593901873971827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 56168923076006479956131285 1316459134593901873971827)
                      ·
                        rfl

theorem cell23_2563795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 7].length) (baseStart_2563795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563795 prefixEnd_2563795 := by exact prefixLift 2563795
  have htrace : WordTrace (prefixWord ++ tailWord_2563795) baseStart_2563795 baseEnd_2563795 := by
    simpa [prefixWord, tailWord_2563795, baseEnd_2563795] using wordTrace_append hprefix tailTrace_2563795
  have hstable : (prefixWord ++ tailWord_2563795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563795).length < 2 ^ (prefixWord ++ tailWord_2563795).sum := by decide
  have hdescent : baseEnd_2563795 < baseStart_2563795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563816 : List Nat := [2, 1, 4, 1, 3, 1, 2, 2, 3, 1, 3]
def baseStart_2563816 : Nat := 118140960795 + 2563816 * 2 ^ 59
def prefixEnd_2563816 : Nat := 4983230072969 + 3 ^ 40 * 2563816 * 2
def baseEnd_2563816 : Nat := 1316469917687646291809231

theorem tailTrace_2563816 : CollatzResearch.WordTrace tailWord_2563816 prefixEnd_2563816 1316469917687646291809231 := by
  unfold tailWord_2563816
  simp only [CollatzResearch.WordTrace]
  refine ⟨46755025839869985878851651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62340034453159981171802201 46755025839869985878851651)
  ·
    refine ⟨70132538759804978818277477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46755025839869985878851651 70132538759804978818277477)
    ·
      refine ⟨13149851017463433528427027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70132538759804978818277477 13149851017463433528427027)
      ·
        refine ⟨19724776526195150292640541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13149851017463433528427027 19724776526195150292640541)
        ·
          refine ⟨7396791197323181359740203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19724776526195150292640541 7396791197323181359740203)
          ·
            refine ⟨11095186795984772039610305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7396791197323181359740203 11095186795984772039610305)
            ·
              refine ⟨8321390096988579029707729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11095186795984772039610305 8321390096988579029707729)
              ·
                refine ⟨6241042572741434272280797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8321390096988579029707729 6241042572741434272280797)
                ·
                  refine ⟨2340390964778037852105299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6241042572741434272280797 2340390964778037852105299)
                  ·
                    refine ⟨3510586447167056778157949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2340390964778037852105299 3510586447167056778157949)
                    ·
                      refine ⟨1316469917687646291809231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3510586447167056778157949 1316469917687646291809231)
                      ·
                        rfl

theorem cell23_2563816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_2563816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563816 prefixEnd_2563816 := by exact prefixLift 2563816
  have htrace : WordTrace (prefixWord ++ tailWord_2563816) baseStart_2563816 baseEnd_2563816 := by
    simpa [prefixWord, tailWord_2563816, baseEnd_2563816] using wordTrace_append hprefix tailTrace_2563816
  have hstable : (prefixWord ++ tailWord_2563816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563816).length < 2 ^ (prefixWord ++ tailWord_2563816).sum := by decide
  have hdescent : baseEnd_2563816 < baseStart_2563816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563826 : List Nat := [3, 2, 1, 3, 1, 1, 2, 3, 2, 3, 2]
def baseStart_2563826 : Nat := 118140960795 + 2563826 * 2 ^ 59
def prefixEnd_2563826 : Nat := 4983230072969 + 3 ^ 40 * 2563826 * 2
def baseEnd_2563826 : Nat := 1316475052494191252684185

theorem tailTrace_2563826 : CollatzResearch.WordTrace tailWord_2563826 prefixEnd_2563826 1316475052494191252684185 := by
  unfold tailWord_2563826
  simp only [CollatzResearch.WordTrace]
  refine ⟨23377604102425935866391833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62340277606469162310378221 23377604102425935866391833)
  ·
    refine ⟨17533203076819451899793875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23377604102425935866391833 17533203076819451899793875)
    ·
      refine ⟨26299804615229177849690813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17533203076819451899793875 26299804615229177849690813)
      ·
        refine ⟨9862426730710941693634055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26299804615229177849690813 9862426730710941693634055)
        ·
          refine ⟨14793640096066412540451083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9862426730710941693634055 14793640096066412540451083)
          ·
            refine ⟨22190460144099618810676625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14793640096066412540451083 22190460144099618810676625)
            ·
              refine ⟨16642845108074714108007469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22190460144099618810676625 16642845108074714108007469)
              ·
                refine ⟨6241066915528017790502801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16642845108074714108007469 6241066915528017790502801)
                ·
                  refine ⟨4680800186646013342877101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6241066915528017790502801 4680800186646013342877101)
                  ·
                    refine ⟨1755300069992255003578913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4680800186646013342877101 1755300069992255003578913)
                    ·
                      refine ⟨1316475052494191252684185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1755300069992255003578913 1316475052494191252684185)
                      ·
                        rfl

theorem cell23_2563826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_2563826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563826 prefixEnd_2563826 := by exact prefixLift 2563826
  have htrace : WordTrace (prefixWord ++ tailWord_2563826) baseStart_2563826 baseEnd_2563826 := by
    simpa [prefixWord, tailWord_2563826, baseEnd_2563826] using wordTrace_append hprefix tailTrace_2563826
  have hstable : (prefixWord ++ tailWord_2563826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563826).length < 2 ^ (prefixWord ++ tailWord_2563826).sum := by decide
  have hdescent : baseEnd_2563826 < baseStart_2563826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563839 : List Nat := [1, 1, 2, 2, 1, 3, 4, 3, 1, 1, 4]
def baseStart_2563839 : Nat := 118140960795 + 2563839 * 2 ^ 59
def prefixEnd_2563839 : Nat := 4983230072969 + 3 ^ 40 * 2563839 * 2
def baseEnd_2563839 : Nat := 1316481727742699701821625

theorem tailTrace_2563839 : CollatzResearch.WordTrace tailWord_2563839 prefixEnd_2563839 1316481727742699701821625 := by
  unfold tailWord_2563839
  simp only [CollatzResearch.WordTrace]
  refine ⟨93510890558656646685790571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62340593705771097790527047 93510890558656646685790571)
  ·
    refine ⟨140266335837984970028685857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93510890558656646685790571 140266335837984970028685857)
    ·
      refine ⟨105199751878488727521514393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140266335837984970028685857 105199751878488727521514393)
      ·
        refine ⟨78899813908866545641135795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105199751878488727521514393 78899813908866545641135795)
        ·
          refine ⟨118349720863299818461703693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78899813908866545641135795 118349720863299818461703693)
          ·
            refine ⟨44381145323737431923138885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118349720863299818461703693 44381145323737431923138885)
            ·
              refine ⟨8321464748200768485588541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44381145323737431923138885 8321464748200768485588541)
              ·
                refine ⟨3120549280575288182095703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8321464748200768485588541 3120549280575288182095703)
                ·
                  refine ⟨4680823920862932273143555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3120549280575288182095703 4680823920862932273143555)
                  ·
                    refine ⟨7021235881294398409715333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4680823920862932273143555 7021235881294398409715333)
                    ·
                      refine ⟨1316481727742699701821625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7021235881294398409715333 1316481727742699701821625)
                      ·
                        rfl

theorem cell23_2563839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 1, 4].length) (baseStart_2563839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563839 prefixEnd_2563839 := by exact prefixLift 2563839
  have htrace : WordTrace (prefixWord ++ tailWord_2563839) baseStart_2563839 baseEnd_2563839 := by
    simpa [prefixWord, tailWord_2563839, baseEnd_2563839] using wordTrace_append hprefix tailTrace_2563839
  have hstable : (prefixWord ++ tailWord_2563839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563839).length < 2 ^ (prefixWord ++ tailWord_2563839).sum := by decide
  have hdescent : baseEnd_2563839 < baseStart_2563839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563849 : List Nat := [1, 2, 1, 1, 3, 2, 1, 6, 2, 4]
def baseStart_2563849 : Nat := 118140960795 + 2563849 * 2 ^ 59
def prefixEnd_2563849 : Nat := 4983230072969 + 3 ^ 40 * 2563849 * 2
def baseEnd_2563849 : Nat := 438828954183081554232193

theorem tailTrace_2563849 : CollatzResearch.WordTrace tailWord_2563849 prefixEnd_2563849 438828954183081554232193 := by
  unfold tailWord_2563849
  simp only [CollatzResearch.WordTrace]
  refine ⟨93511255288620418393654601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62340836859080278929103067 93511255288620418393654601)
  ·
    refine ⟨70133441466465313795240951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93511255288620418393654601 70133441466465313795240951)
    ·
      refine ⟨105200162199697970692861427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70133441466465313795240951 105200162199697970692861427)
      ·
        refine ⟨157800243299546956039292141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105200162199697970692861427 157800243299546956039292141)
        ·
          refine ⟨59175091237330108514734553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157800243299546956039292141 59175091237330108514734553)
          ·
            refine ⟨44381318427997581386050915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59175091237330108514734553 44381318427997581386050915)
            ·
              refine ⟨66571977641996372079076373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44381318427997581386050915 66571977641996372079076373)
              ·
                refine ⟨3120561451968579941206705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 66571977641996372079076373 3120561451968579941206705)
                ·
                  refine ⟨2340421088976434955905029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3120561451968579941206705 2340421088976434955905029)
                  ·
                    refine ⟨438828954183081554232193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2340421088976434955905029 438828954183081554232193)
                    ·
                      rfl

theorem cell23_2563849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 2, 4].length) (baseStart_2563849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563849 prefixEnd_2563849 := by exact prefixLift 2563849
  have htrace : WordTrace (prefixWord ++ tailWord_2563849) baseStart_2563849 baseEnd_2563849 := by
    simpa [prefixWord, tailWord_2563849, baseEnd_2563849] using wordTrace_append hprefix tailTrace_2563849
  have hstable : (prefixWord ++ tailWord_2563849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563849).length < 2 ^ (prefixWord ++ tailWord_2563849).sum := by decide
  have hdescent : baseEnd_2563849 < baseStart_2563849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563850 : List Nat := [3, 1, 2, 2, 1, 4, 3, 2, 1, 1, 3]
def baseStart_2563850 : Nat := 118140960795 + 2563850 * 2 ^ 59
def prefixEnd_2563850 : Nat := 4983230072969 + 3 ^ 40 * 2563850 * 2
def baseEnd_2563850 : Nat := 1316487376029899158784075

theorem tailTrace_2563850 : CollatzResearch.WordTrace tailWord_2563850 prefixEnd_2563850 1316487376029899158784075 := by
  unfold tailWord_2563850
  simp only [CollatzResearch.WordTrace]
  refine ⟨23377822940404198891110251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62340861174411197042960669 23377822940404198891110251)
  ·
    refine ⟨35066734410606298336665377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23377822940404198891110251 35066734410606298336665377)
    ·
      refine ⟨26300050807954723752499033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35066734410606298336665377 26300050807954723752499033)
      ·
        refine ⟨19725038105966042814374275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26300050807954723752499033 19725038105966042814374275)
        ·
          refine ⟨29587557158949064221561413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19725038105966042814374275 29587557158949064221561413)
          ·
            refine ⟨5547666967302949541542765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29587557158949064221561413 5547666967302949541542765)
            ·
              refine ⟨2080375112738606078078537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5547666967302949541542765 2080375112738606078078537)
              ·
                refine ⟨1560281334553954558558903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2080375112738606078078537 1560281334553954558558903)
                ·
                  refine ⟨2340422001830931837838355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1560281334553954558558903 2340422001830931837838355)
                  ·
                    refine ⟨3510633002746397756757533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2340422001830931837838355 3510633002746397756757533)
                    ·
                      refine ⟨1316487376029899158784075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3510633002746397756757533 1316487376029899158784075)
                      ·
                        rfl

theorem cell23_2563850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 2, 1, 1, 3].length) (baseStart_2563850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563850 prefixEnd_2563850 := by exact prefixLift 2563850
  have htrace : WordTrace (prefixWord ++ tailWord_2563850) baseStart_2563850 baseEnd_2563850 := by
    simpa [prefixWord, tailWord_2563850, baseEnd_2563850] using wordTrace_append hprefix tailTrace_2563850
  have hstable : (prefixWord ++ tailWord_2563850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563850).length < 2 ^ (prefixWord ++ tailWord_2563850).sum := by decide
  have hdescent : baseEnd_2563850 < baseStart_2563850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563852 : List Nat := [2, 2, 1, 2, 2, 1, 3, 2, 1, 1, 6]
def baseStart_2563852 : Nat := 118140960795 + 2563852 * 2 ^ 59
def prefixEnd_2563852 : Nat := 4983230072969 + 3 ^ 40 * 2563852 * 2
def baseEnd_2563852 : Nat := 1316488402991208150959065

theorem tailTrace_2563852 : CollatzResearch.WordTrace tailWord_2563852 prefixEnd_2563852 1316488402991208150959065 := by
  unfold tailWord_2563852
  simp only [CollatzResearch.WordTrace]
  refine ⟨46755682353804774953006905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62340909805073033270675873 46755682353804774953006905)
  ·
    refine ⟨35066761765353581214755179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46755682353804774953006905 35066761765353581214755179)
    ·
      refine ⟨52600142648030371822132769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35066761765353581214755179 52600142648030371822132769)
      ·
        refine ⟨39450106986022778866599577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52600142648030371822132769 39450106986022778866599577)
        ·
          refine ⟨29587580239517084149949683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39450106986022778866599577 29587580239517084149949683)
          ·
            refine ⟨44381370359275626224924525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29587580239517084149949683 44381370359275626224924525)
            ·
              refine ⟨16643013884728359834346697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44381370359275626224924525 16643013884728359834346697)
              ·
                refine ⟨12482260413546269875760023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16643013884728359834346697 12482260413546269875760023)
                ·
                  refine ⟨18723390620319404813640035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12482260413546269875760023 18723390620319404813640035)
                  ·
                    refine ⟨28085085930479107220460053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18723390620319404813640035 28085085930479107220460053)
                    ·
                      refine ⟨1316488402991208150959065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28085085930479107220460053 1316488402991208150959065)
                      ·
                        rfl

theorem cell23_2563852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_2563852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563852 prefixEnd_2563852 := by exact prefixLift 2563852
  have htrace : WordTrace (prefixWord ++ tailWord_2563852) baseStart_2563852 baseEnd_2563852 := by
    simpa [prefixWord, tailWord_2563852, baseEnd_2563852] using wordTrace_append hprefix tailTrace_2563852
  have hstable : (prefixWord ++ tailWord_2563852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563852).length < 2 ^ (prefixWord ++ tailWord_2563852).sum := by decide
  have hdescent : baseEnd_2563852 < baseStart_2563852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563866 : List Nat := [3, 1, 1, 3, 2, 3, 1, 3, 2, 4]
def baseStart_2563866 : Nat := 118140960795 + 2563866 * 2 ^ 59
def prefixEnd_2563866 : Nat := 4983230072969 + 3 ^ 40 * 2563866 * 2
def baseEnd_2563866 : Nat := 438831863906790365394667

theorem tailTrace_2563866 : CollatzResearch.WordTrace tailWord_2563866 prefixEnd_2563866 438831863906790365394667 := by
  unfold tailWord_2563866
  simp only [CollatzResearch.WordTrace]
  refine ⟨23377968832389707574255863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62341250219705886864682301 23377968832389707574255863)
  ·
    refine ⟨35066953248584561361383795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23377968832389707574255863 35066953248584561361383795)
    ·
      refine ⟨52600429872876842042075693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35066953248584561361383795 52600429872876842042075693)
      ·
        refine ⟨19725161202328815765778385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52600429872876842042075693 19725161202328815765778385)
        ·
          refine ⟨14793870901746611824333789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19725161202328815765778385 14793870901746611824333789)
          ·
            refine ⟨5547701588154979434125171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14793870901746611824333789 5547701588154979434125171)
            ·
              refine ⟨8321552382232469151187757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5547701588154979434125171 8321552382232469151187757)
              ·
                refine ⟨3120582143337175931695409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8321552382232469151187757 3120582143337175931695409)
                ·
                  refine ⟨2340436607502881948771557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3120582143337175931695409 2340436607502881948771557)
                  ·
                    refine ⟨438831863906790365394667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2340436607502881948771557 438831863906790365394667)
                    ·
                      rfl

theorem cell23_2563866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 2, 4].length) (baseStart_2563866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563866 prefixEnd_2563866 := by exact prefixLift 2563866
  have htrace : WordTrace (prefixWord ++ tailWord_2563866) baseStart_2563866 baseEnd_2563866 := by
    simpa [prefixWord, tailWord_2563866, baseEnd_2563866] using wordTrace_append hprefix tailTrace_2563866
  have hstable : (prefixWord ++ tailWord_2563866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563866).length < 2 ^ (prefixWord ++ tailWord_2563866).sum := by decide
  have hdescent : baseEnd_2563866 < baseStart_2563866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563876 : List Nat := [2, 3, 1, 3, 2, 2, 1, 1, 3, 2, 3]
def baseStart_2563876 : Nat := 118140960795 + 2563876 * 2 ^ 59
def prefixEnd_2563876 : Nat := 4983230072969 + 3 ^ 40 * 2563876 * 2
def baseEnd_2563876 : Nat := 1316500726526916057058955

theorem tailTrace_2563876 : CollatzResearch.WordTrace tailWord_2563876 prefixEnd_2563876 1316500726526916057058955 := by
  unfold tailWord_2563876
  simp only [CollatzResearch.WordTrace]
  refine ⟨46756120029761301002443741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62341493373015068003258321 46756120029761301002443741)
  ·
    refine ⟨17533545011160487875916403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46756120029761301002443741 17533545011160487875916403)
    ·
      refine ⟨26300317516740731813874605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17533545011160487875916403 26300317516740731813874605)
      ·
        refine ⟨9862619068777774430202977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26300317516740731813874605 9862619068777774430202977)
        ·
          refine ⟨7396964301583330822652233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9862619068777774430202977 7396964301583330822652233)
          ·
            refine ⟨5547723226187498116989175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7396964301583330822652233 5547723226187498116989175)
            ·
              refine ⟨8321584839281247175483763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5547723226187498116989175 8321584839281247175483763)
              ·
                refine ⟨12482377258921870763225645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8321584839281247175483763 12482377258921870763225645)
                ·
                  refine ⟨4680891472095701536209617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12482377258921870763225645 4680891472095701536209617)
                  ·
                    refine ⟨3510668604071776152157213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4680891472095701536209617 3510668604071776152157213)
                    ·
                      refine ⟨1316500726526916057058955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3510668604071776152157213 1316500726526916057058955)
                      ·
                        rfl

theorem cell23_2563876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_2563876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563876 prefixEnd_2563876 := by exact prefixLift 2563876
  have htrace : WordTrace (prefixWord ++ tailWord_2563876) baseStart_2563876 baseEnd_2563876 := by
    simpa [prefixWord, tailWord_2563876, baseEnd_2563876] using wordTrace_append hprefix tailTrace_2563876
  have hstable : (prefixWord ++ tailWord_2563876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563876).length < 2 ^ (prefixWord ++ tailWord_2563876).sum := by decide
  have hdescent : baseEnd_2563876 < baseStart_2563876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563889 : List Nat := [1, 2, 2, 3, 2, 2, 1, 1, 3, 3, 3]
def baseStart_2563889 : Nat := 118140960795 + 2563889 * 2 ^ 59
def prefixEnd_2563889 : Nat := 4983230072969 + 3 ^ 40 * 2563889 * 2
def baseEnd_2563889 : Nat := 1316507401775424506196395

theorem tailTrace_2563889 : CollatzResearch.WordTrace tailWord_2563889 prefixEnd_2563889 1316507401775424506196395 := by
  unfold tailWord_2563889
  simp only [CollatzResearch.WordTrace]
  refine ⟨93512714208475505225110721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62341809472317003483407147 93512714208475505225110721)
  ·
    refine ⟨70134535656356628918833041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93512714208475505225110721 70134535656356628918833041)
    ·
      refine ⟨52600901742267471689124781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70134535656356628918833041 52600901742267471689124781)
      ·
        refine ⟨19725338153350301883421793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52600901742267471689124781 19725338153350301883421793)
        ·
          refine ⟨14794003615012726412566345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19725338153350301883421793 14794003615012726412566345)
          ·
            refine ⟨11095502711259544809424759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14794003615012726412566345 11095502711259544809424759)
            ·
              refine ⟨16643254066889317214137139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11095502711259544809424759 16643254066889317214137139)
              ·
                refine ⟨24964881100333975821205709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16643254066889317214137139 24964881100333975821205709)
                ·
                  refine ⟨9361830412625240932952141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24964881100333975821205709 9361830412625240932952141)
                  ·
                    refine ⟨3510686404734465349857053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9361830412625240932952141 3510686404734465349857053)
                    ·
                      refine ⟨1316507401775424506196395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3510686404734465349857053 1316507401775424506196395)
                      ·
                        rfl

theorem cell23_2563889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_2563889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563889 prefixEnd_2563889 := by exact prefixLift 2563889
  have htrace : WordTrace (prefixWord ++ tailWord_2563889) baseStart_2563889 baseEnd_2563889 := by
    simpa [prefixWord, tailWord_2563889, baseEnd_2563889] using wordTrace_append hprefix tailTrace_2563889
  have hstable : (prefixWord ++ tailWord_2563889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563889).length < 2 ^ (prefixWord ++ tailWord_2563889).sum := by decide
  have hdescent : baseEnd_2563889 < baseStart_2563889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563893 : List Nat := [1, 3, 3, 1, 5, 1, 1, 1, 1, 1, 5]
def baseStart_2563893 : Nat := 118140960795 + 2563893 * 2 ^ 59
def prefixEnd_2563893 : Nat := 4983230072969 + 3 ^ 40 * 2563893 * 2
def baseEnd_2563893 : Nat := 1316509455698042490546377

theorem tailTrace_2563893 : CollatzResearch.WordTrace tailWord_2563893 prefixEnd_2563893 1316509455698042490546377 := by
  unfold tailWord_2563893
  simp only [CollatzResearch.WordTrace]
  refine ⟨93512860100461013908256333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62341906733640675938837555 93512860100461013908256333)
  ·
    refine ⟨35067322537672880215596125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93512860100461013908256333 35067322537672880215596125)
    ·
      refine ⟨13150245951627330080848547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35067322537672880215596125 13150245951627330080848547)
      ·
        refine ⟨19725368927440995121272821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13150245951627330080848547 19725368927440995121272821)
        ·
          refine ⟨1849253336947593292619327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19725368927440995121272821 1849253336947593292619327)
          ·
            refine ⟨2773880005421389938928991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1849253336947593292619327 2773880005421389938928991)
            ·
              refine ⟨4160820008132084908393487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2773880005421389938928991 4160820008132084908393487)
              ·
                refine ⟨6241230012198127362590231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4160820008132084908393487 6241230012198127362590231)
                ·
                  refine ⟨9361845018297191043885347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6241230012198127362590231 9361845018297191043885347)
                  ·
                    refine ⟨14042767527445786565828021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9361845018297191043885347 14042767527445786565828021)
                    ·
                      refine ⟨1316509455698042490546377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14042767527445786565828021 1316509455698042490546377)
                      ·
                        rfl

theorem cell23_2563893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_2563893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563893 prefixEnd_2563893 := by exact prefixLift 2563893
  have htrace : WordTrace (prefixWord ++ tailWord_2563893) baseStart_2563893 baseEnd_2563893 := by
    simpa [prefixWord, tailWord_2563893, baseEnd_2563893] using wordTrace_append hprefix tailTrace_2563893
  have hstable : (prefixWord ++ tailWord_2563893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563893).length < 2 ^ (prefixWord ++ tailWord_2563893).sum := by decide
  have hdescent : baseEnd_2563893 < baseStart_2563893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563907 : List Nat := [1, 1, 1, 3, 1, 7, 2, 2, 1, 2, 2]
def baseStart_2563907 : Nat := 118140960795 + 2563907 * 2 ^ 59
def prefixEnd_2563907 : Nat := 4983230072969 + 3 ^ 40 * 2563907 * 2
def baseEnd_2563907 : Nat := 1316516644427205435771313

theorem tailTrace_2563907 : CollatzResearch.WordTrace tailWord_2563907 prefixEnd_2563907 1316516644427205435771313 := by
  unfold tailWord_2563907
  simp only [CollatzResearch.WordTrace]
  refine ⟨93513370722410294299265975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62342247148273529532843983 93513370722410294299265975)
  ·
    refine ⟨140270056083615441448898963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93513370722410294299265975 140270056083615441448898963)
    ·
      refine ⟨210405084125423162173348445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140270056083615441448898963 210405084125423162173348445)
      ·
        refine ⟨78901906547033685815005667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210405084125423162173348445 78901906547033685815005667)
        ·
          refine ⟨118352859820550528722508501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78901906547033685815005667 118352859820550528722508501)
          ·
            refine ⟨2773895152044153016933793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 118352859820550528722508501 2773895152044153016933793)
            ·
              refine ⟨2080421364033114762700345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2773895152044153016933793 2080421364033114762700345)
              ·
                refine ⟨1560316023024836072025259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2080421364033114762700345 1560316023024836072025259)
                ·
                  refine ⟨2340474034537254108037889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1560316023024836072025259 2340474034537254108037889)
                  ·
                    refine ⟨1755355525902940581028417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2340474034537254108037889 1755355525902940581028417)
                    ·
                      refine ⟨1316516644427205435771313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1755355525902940581028417 1316516644427205435771313)
                      ·
                        rfl

theorem cell23_2563907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 2, 1, 2, 2].length) (baseStart_2563907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563907 prefixEnd_2563907 := by exact prefixLift 2563907
  have htrace : WordTrace (prefixWord ++ tailWord_2563907) baseStart_2563907 baseEnd_2563907 := by
    simpa [prefixWord, tailWord_2563907, baseEnd_2563907] using wordTrace_append hprefix tailTrace_2563907
  have hstable : (prefixWord ++ tailWord_2563907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563907).length < 2 ^ (prefixWord ++ tailWord_2563907).sum := by decide
  have hdescent : baseEnd_2563907 < baseStart_2563907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563949 : List Nat := [1, 5, 1, 1, 1, 1, 2, 3, 2, 1, 5]
def baseStart_2563949 : Nat := 118140960795 + 2563949 * 2 ^ 59
def prefixEnd_2563949 : Nat := 4983230072969 + 3 ^ 40 * 2563949 * 2
def baseEnd_2563949 : Nat := 1316538210614694271446119

theorem tailTrace_2563949 : CollatzResearch.WordTrace tailWord_2563949 prefixEnd_2563949 1316538210614694271446119 := by
  unfold tailWord_2563949
  simp only [CollatzResearch.WordTrace]
  refine ⟨93514902588258135472294901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62343268392172090314863267 93514902588258135472294901)
  ·
    refine ⟨8767022117649200200527647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93514902588258135472294901 8767022117649200200527647)
    ·
      refine ⟨13150533176473800300791471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8767022117649200200527647 13150533176473800300791471)
      ·
        refine ⟨19725799764710700451187207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13150533176473800300791471 19725799764710700451187207)
        ·
          refine ⟨29588699647066050676780811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19725799764710700451187207 29588699647066050676780811)
          ·
            refine ⟨44383049470599076015171217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29588699647066050676780811 44383049470599076015171217)
            ·
              refine ⟨33287287102949307011378413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44383049470599076015171217 33287287102949307011378413)
              ·
                refine ⟨12482732663605990129266905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33287287102949307011378413 12482732663605990129266905)
                ·
                  refine ⟨9362049497704492596950179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12482732663605990129266905 9362049497704492596950179)
                  ·
                    refine ⟨14043074246556738895425269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9362049497704492596950179 14043074246556738895425269)
                    ·
                      refine ⟨1316538210614694271446119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14043074246556738895425269 1316538210614694271446119)
                      ·
                        rfl

theorem cell23_2563949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_2563949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563949 prefixEnd_2563949 := by exact prefixLift 2563949
  have htrace : WordTrace (prefixWord ++ tailWord_2563949) baseStart_2563949 baseEnd_2563949 := by
    simpa [prefixWord, tailWord_2563949, baseEnd_2563949] using wordTrace_append hprefix tailTrace_2563949
  have hstable : (prefixWord ++ tailWord_2563949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563949).length < 2 ^ (prefixWord ++ tailWord_2563949).sum := by decide
  have hdescent : baseEnd_2563949 < baseStart_2563949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563950 : List Nat := [4, 1, 2, 3, 1, 2, 1, 3, 1, 3, 2]
def baseStart_2563950 : Nat := 118140960795 + 2563950 * 2 ^ 59
def prefixEnd_2563950 : Nat := 4983230072969 + 3 ^ 40 * 2563950 * 2
def baseEnd_2563950 : Nat := 1316538724095348767533615

theorem tailTrace_2563950 : CollatzResearch.WordTrace tailWord_2563950 prefixEnd_2563950 1316538724095348767533615 := by
  unfold tailWord_2563950
  simp only [CollatzResearch.WordTrace]
  refine ⟨11689367382656814080385163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62343292707503008428720869 11689367382656814080385163)
  ·
    refine ⟨17534051073985221120577745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11689367382656814080385163 17534051073985221120577745)
    ·
      refine ⟨13150538305488915840433309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17534051073985221120577745 13150538305488915840433309)
      ·
        refine ⟨4931451864558343440162491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13150538305488915840433309 4931451864558343440162491)
        ·
          refine ⟨7397177796837515160243737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4931451864558343440162491 7397177796837515160243737)
          ·
            refine ⟨5547883347628136370182803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7397177796837515160243737 5547883347628136370182803)
            ·
              refine ⟨8321825021442204555274205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5547883347628136370182803 8321825021442204555274205)
              ·
                refine ⟨3120684383040826708227827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8321825021442204555274205 3120684383040826708227827)
                ·
                  refine ⟨4681026574561240062341741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3120684383040826708227827 4681026574561240062341741)
                  ·
                    refine ⟨1755384965460465023378153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4681026574561240062341741 1755384965460465023378153)
                    ·
                      refine ⟨1316538724095348767533615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1755384965460465023378153 1316538724095348767533615)
                      ·
                        rfl

theorem cell23_2563950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_2563950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563950 prefixEnd_2563950 := by exact prefixLift 2563950
  have htrace : WordTrace (prefixWord ++ tailWord_2563950) baseStart_2563950 baseEnd_2563950 := by
    simpa [prefixWord, tailWord_2563950, baseEnd_2563950] using wordTrace_append hprefix tailTrace_2563950
  have hstable : (prefixWord ++ tailWord_2563950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563950).length < 2 ^ (prefixWord ++ tailWord_2563950).sum := by decide
  have hdescent : baseEnd_2563950 < baseStart_2563950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563952 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 11]
def baseStart_2563952 : Nat := 118140960795 + 2563952 * 2 ^ 59
def prefixEnd_2563952 : Nat := 4983230072969 + 3 ^ 40 * 2563952 * 2
def baseEnd_2563952 : Nat := 146282194561850862189845

theorem tailTrace_2563952 : CollatzResearch.WordTrace tailWord_2563952 prefixEnd_2563952 146282194561850862189845 := by
  unfold tailWord_2563952
  simp only [CollatzResearch.WordTrace]
  refine ⟨46757506003623633492327055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62343341338164844656436073 46757506003623633492327055)
  ·
    refine ⟨70136259005435450238490583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46757506003623633492327055 70136259005435450238490583)
    ·
      refine ⟨105204388508153175357735875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70136259005435450238490583 105204388508153175357735875)
      ·
        refine ⟨157806582762229763036603813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105204388508153175357735875 157806582762229763036603813)
        ·
          refine ⟨29588734267918080569363215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 157806582762229763036603813 29588734267918080569363215)
          ·
            refine ⟨44383101401877120854044823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29588734267918080569363215 44383101401877120854044823)
            ·
              refine ⟨66574652102815681281067235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44383101401877120854044823 66574652102815681281067235)
              ·
                refine ⟨99861978154223521921600853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66574652102815681281067235 99861978154223521921600853)
                ·
                  refine ⟨146282194561850862189845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 99861978154223521921600853 146282194561850862189845)
                  ·
                    rfl

theorem cell23_2563952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 11].length) (baseStart_2563952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563952 prefixEnd_2563952 := by exact prefixLift 2563952
  have htrace : WordTrace (prefixWord ++ tailWord_2563952) baseStart_2563952 baseEnd_2563952 := by
    simpa [prefixWord, tailWord_2563952, baseEnd_2563952] using wordTrace_append hprefix tailTrace_2563952
  have hstable : (prefixWord ++ tailWord_2563952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563952).length < 2 ^ (prefixWord ++ tailWord_2563952).sum := by decide
  have hdescent : baseEnd_2563952 < baseStart_2563952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563986 : List Nat := [3, 2, 3, 2, 1, 1, 2, 2, 7]
def baseStart_2563986 : Nat := 118140960795 + 2563986 * 2 ^ 59
def prefixEnd_2563986 : Nat := 4983230072969 + 3 ^ 40 * 2563986 * 2
def baseEnd_2563986 : Nat := 146284134377656736298161

theorem tailTrace_2563986 : CollatzResearch.WordTrace tailWord_2563986 prefixEnd_2563986 146284134377656736298161 := by
  unfold tailWord_2563986
  simp only [CollatzResearch.WordTrace]
  refine ⟨23379063022281022697847953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62344168059416060527594541 23379063022281022697847953)
  ·
    refine ⟨17534297266710767023385965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23379063022281022697847953 17534297266710767023385965)
    ·
      refine ⟨6575361475016537633769737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17534297266710767023385965 6575361475016537633769737)
      ·
        refine ⟨4931521106262403225327303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6575361475016537633769737 4931521106262403225327303)
        ·
          refine ⟨7397281659393604837990955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4931521106262403225327303 7397281659393604837990955)
          ·
            refine ⟨11095922489090407256986433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7397281659393604837990955 11095922489090407256986433)
            ·
              refine ⟨8321941866817805442739825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11095922489090407256986433 8321941866817805442739825)
              ·
                refine ⟨6241456400113354082054869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8321941866817805442739825 6241456400113354082054869)
                ·
                  refine ⟨146284134377656736298161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6241456400113354082054869 146284134377656736298161)
                  ·
                    rfl

theorem cell23_2563986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 7].length) (baseStart_2563986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2563986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2563986 prefixEnd_2563986 := by exact prefixLift 2563986
  have htrace : WordTrace (prefixWord ++ tailWord_2563986) baseStart_2563986 baseEnd_2563986 := by
    simpa [prefixWord, tailWord_2563986, baseEnd_2563986] using wordTrace_append hprefix tailTrace_2563986
  have hstable : (prefixWord ++ tailWord_2563986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563986).length < 2 ^ (prefixWord ++ tailWord_2563986).sum := by decide
  have hdescent : baseEnd_2563986 < baseStart_2563986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564020 : List Nat := [2, 5, 2, 1, 2, 2, 1, 1, 7]
def baseStart_2564020 : Nat := 118140960795 + 2564020 * 2 ^ 59
def prefixEnd_2564020 : Nat := 4983230072969 + 3 ^ 40 * 2564020 * 2
def baseEnd_2564020 : Nat := 146286074193462610406477

theorem tailTrace_2564020 : CollatzResearch.WordTrace tailWord_2564020 prefixEnd_2564020 146286074193462610406477 := by
  unfold tailWord_2564020
  simp only [CollatzResearch.WordTrace]
  refine ⟨46758746085500457299064757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62344994780667276398753009 46758746085500457299064757)
  ·
    refine ⟨4383632445515667871787321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46758746085500457299064757 4383632445515667871787321)
    ·
      refine ⟨3287724334136750903840491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4383632445515667871787321 3287724334136750903840491)
      ·
        refine ⟨4931586501205126355760737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3287724334136750903840491 4931586501205126355760737)
        ·
          refine ⟨3698689875903844766820553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4931586501205126355760737 3698689875903844766820553)
          ·
            refine ⟨2774017406927883575115415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3698689875903844766820553 2774017406927883575115415)
            ·
              refine ⟨4161026110391825362673123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2774017406927883575115415 4161026110391825362673123)
              ·
                refine ⟨6241539165587738044009685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4161026110391825362673123 6241539165587738044009685)
                ·
                  refine ⟨146286074193462610406477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6241539165587738044009685 146286074193462610406477)
                  ·
                    rfl

theorem cell23_2564020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_2564020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564020 prefixEnd_2564020 := by exact prefixLift 2564020
  have htrace : WordTrace (prefixWord ++ tailWord_2564020) baseStart_2564020 baseEnd_2564020 := by
    simpa [prefixWord, tailWord_2564020, baseEnd_2564020] using wordTrace_append hprefix tailTrace_2564020
  have hstable : (prefixWord ++ tailWord_2564020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564020).length < 2 ^ (prefixWord ++ tailWord_2564020).sum := by decide
  have hdescent : baseEnd_2564020 < baseStart_2564020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564046 : List Nat := [4, 1, 1, 1, 2, 2, 2, 1, 5, 4]
def baseStart_2564046 : Nat := 118140960795 + 2564046 * 2 ^ 59
def prefixEnd_2564046 : Nat := 4983230072969 + 3 ^ 40 * 2564046 * 2
def baseEnd_2564046 : Nat := 438862672746060130644391

theorem tailTrace_2564046 : CollatzResearch.WordTrace tailWord_2564046 prefixEnd_2564046 438862672746060130644391 := by
  unfold tailWord_2564046
  simp only [CollatzResearch.WordTrace]
  refine ⟨11689805058613340129821999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62345626979271147359050661 11689805058613340129821999)
  ·
    refine ⟨17534707587920010194732999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11689805058613340129821999 17534707587920010194732999)
    ·
      refine ⟨26302061381880015292099499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17534707587920010194732999 26302061381880015292099499)
      ·
        refine ⟨39453092072820022938149249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26302061381880015292099499 39453092072820022938149249)
        ·
          refine ⟨29589819054615017203611937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39453092072820022938149249 29589819054615017203611937)
          ·
            refine ⟨22192364290961262902708953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29589819054615017203611937 22192364290961262902708953)
            ·
              refine ⟨16644273218220947177031715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22192364290961262902708953 16644273218220947177031715)
              ·
                refine ⟨24966409827331420765547573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16644273218220947177031715 24966409827331420765547573)
                ·
                  refine ⟨2340600921312320696770085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24966409827331420765547573 2340600921312320696770085)
                  ·
                    refine ⟨438862672746060130644391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2340600921312320696770085 438862672746060130644391)
                    ·
                      rfl

theorem cell23_2564046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 5, 4].length) (baseStart_2564046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564046 prefixEnd_2564046 := by exact prefixLift 2564046
  have htrace : WordTrace (prefixWord ++ tailWord_2564046) baseStart_2564046 baseEnd_2564046 := by
    simpa [prefixWord, tailWord_2564046, baseEnd_2564046] using wordTrace_append hprefix tailTrace_2564046
  have hstable : (prefixWord ++ tailWord_2564046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564046).length < 2 ^ (prefixWord ++ tailWord_2564046).sum := by decide
  have hdescent : baseEnd_2564046 < baseStart_2564046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564053 : List Nat := [1, 3, 2, 3, 2, 2, 2, 1, 2, 1, 4]
def baseStart_2564053 : Nat := 118140960795 + 2564053 * 2 ^ 59
def prefixEnd_2564053 : Nat := 4983230072969 + 3 ^ 40 * 2564053 * 2
def baseEnd_2564053 : Nat := 1316591612602761864545641

theorem tailTrace_2564053 : CollatzResearch.WordTrace tailWord_2564053 prefixEnd_2564053 1316591612602761864545641 := by
  unfold tailWord_2564053
  simp only [CollatzResearch.WordTrace]
  refine ⟨93518695779881361234080813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62345797186587574156053875 93518695779881361234080813)
  ·
    refine ⟨35069510917455510462780305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93518695779881361234080813 35069510917455510462780305)
    ·
      refine ⟨26302133188091632847085229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35069510917455510462780305 26302133188091632847085229)
      ·
        refine ⟨9863299945534362317656961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26302133188091632847085229 9863299945534362317656961)
        ·
          refine ⟨7397474959150771738242721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9863299945534362317656961 7397474959150771738242721)
          ·
            refine ⟨5548106219363078803682041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7397474959150771738242721 5548106219363078803682041)
            ·
              refine ⟨4161079664522309102761531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5548106219363078803682041 4161079664522309102761531)
              ·
                refine ⟨6241619496783463654142297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4161079664522309102761531 6241619496783463654142297)
                ·
                  refine ⟨4681214622587597740606723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6241619496783463654142297 4681214622587597740606723)
                  ·
                    refine ⟨7021821933881396610910085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4681214622587597740606723 7021821933881396610910085)
                    ·
                      refine ⟨1316591612602761864545641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7021821933881396610910085 1316591612602761864545641)
                      ·
                        rfl

theorem cell23_2564053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_2564053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564053 prefixEnd_2564053 := by exact prefixLift 2564053
  have htrace : WordTrace (prefixWord ++ tailWord_2564053) baseStart_2564053 baseEnd_2564053 := by
    simpa [prefixWord, tailWord_2564053, baseEnd_2564053] using wordTrace_append hprefix tailTrace_2564053
  have hstable : (prefixWord ++ tailWord_2564053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564053).length < 2 ^ (prefixWord ++ tailWord_2564053).sum := by decide
  have hdescent : baseEnd_2564053 < baseStart_2564053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564079 : List Nat := [1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 6]
def baseStart_2564079 : Nat := 118140960795 + 2564079 * 2 ^ 59
def prefixEnd_2564079 : Nat := 4983230072969 + 3 ^ 40 * 2564079 * 2
def baseEnd_2564079 : Nat := 1316604963099778762820521

theorem tailTrace_2564079 : CollatzResearch.WordTrace tailWord_2564079 prefixEnd_2564079 1316604963099778762820521 := by
  unfold tailWord_2564079
  simp only [CollatzResearch.WordTrace]
  refine ⟨93519644077787167674527291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62346429385191445116351527 93519644077787167674527291)
  ·
    refine ⟨140279466116680751511790937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93519644077787167674527291 140279466116680751511790937)
    ·
      refine ⟨105209599587510563633843203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140279466116680751511790937 105209599587510563633843203)
      ·
        refine ⟨157814399381265845450764805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105209599587510563633843203 157814399381265845450764805)
        ·
          refine ⟨29590199883987346022018401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 157814399381265845450764805 29590199883987346022018401)
          ·
            refine ⟨22192649912990509516513801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29590199883987346022018401 22192649912990509516513801)
            ·
              refine ⟨16644487434742882137385351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22192649912990509516513801 16644487434742882137385351)
              ·
                refine ⟨24966731152114323206078027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16644487434742882137385351 24966731152114323206078027)
                ·
                  refine ⟨37450096728171484809117041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24966731152114323206078027 37450096728171484809117041)
                  ·
                    refine ⟨28087572546128613606837781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37450096728171484809117041 28087572546128613606837781)
                    ·
                      refine ⟨1316604963099778762820521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28087572546128613606837781 1316604963099778762820521)
                      ·
                        rfl

theorem cell23_2564079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 6].length) (baseStart_2564079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564079 prefixEnd_2564079 := by exact prefixLift 2564079
  have htrace : WordTrace (prefixWord ++ tailWord_2564079) baseStart_2564079 baseEnd_2564079 := by
    simpa [prefixWord, tailWord_2564079, baseEnd_2564079] using wordTrace_append hprefix tailTrace_2564079
  have hstable : (prefixWord ++ tailWord_2564079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564079).length < 2 ^ (prefixWord ++ tailWord_2564079).sum := by decide
  have hdescent : baseEnd_2564079 < baseStart_2564079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564080 : List Nat := [2, 1, 1, 1, 3, 2, 6, 2, 1, 4]
def baseStart_2564080 : Nat := 118140960795 + 2564080 * 2 ^ 59
def prefixEnd_2564080 : Nat := 4983230072969 + 3 ^ 40 * 2564080 * 2
def baseEnd_2564080 : Nat := 438868492193477752969339

theorem tailTrace_2564080 : CollatzResearch.WordTrace tailWord_2564080 prefixEnd_2564080 438868492193477752969339 := by
  unfold tailWord_2564080
  simp only [CollatzResearch.WordTrace]
  refine ⟨46759840275391772422656847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62346453700522363230209129 46759840275391772422656847)
  ·
    refine ⟨70139760413087658633985271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46759840275391772422656847 70139760413087658633985271)
    ·
      refine ⟨105209640619631487950977907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70139760413087658633985271 105209640619631487950977907)
      ·
        refine ⟨157814460929447231926466861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105209640619631487950977907 157814460929447231926466861)
        ·
          refine ⟨59180422848542711972425073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157814460929447231926466861 59180422848542711972425073)
          ·
            refine ⟨44385317136407033979318805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59180422848542711972425073 44385317136407033979318805)
            ·
              refine ⟨2080561740769079717780569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 44385317136407033979318805 2080561740769079717780569)
              ·
                refine ⟨1560421305576809788335427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2080561740769079717780569 1560421305576809788335427)
                ·
                  refine ⟨2340631958365214682503141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1560421305576809788335427 2340631958365214682503141)
                  ·
                    refine ⟨438868492193477752969339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2340631958365214682503141 438868492193477752969339)
                    ·
                      rfl

theorem cell23_2564080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 2, 1, 4].length) (baseStart_2564080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564080 prefixEnd_2564080 := by exact prefixLift 2564080
  have htrace : WordTrace (prefixWord ++ tailWord_2564080) baseStart_2564080 baseEnd_2564080 := by
    simpa [prefixWord, tailWord_2564080, baseEnd_2564080] using wordTrace_append hprefix tailTrace_2564080
  have hstable : (prefixWord ++ tailWord_2564080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564080).length < 2 ^ (prefixWord ++ tailWord_2564080).sum := by decide
  have hdescent : baseEnd_2564080 < baseStart_2564080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564103 : List Nat := [1, 1, 4, 3, 1, 2, 1, 1, 5, 1, 3]
def baseStart_2564103 : Nat := 118140960795 + 2564103 * 2 ^ 59
def prefixEnd_2564103 : Nat := 4983230072969 + 3 ^ 40 * 2564103 * 2
def baseEnd_2564103 : Nat := 1316617286635486668920411

theorem tailTrace_2564103 : CollatzResearch.WordTrace tailWord_2564103 prefixEnd_2564103 1316617286635486668920411 := by
  unfold tailWord_2564103
  simp only [CollatzResearch.WordTrace]
  refine ⟨93520519429700219773400963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62347012953133479848933975 93520519429700219773400963)
  ·
    refine ⟨140280779144550329660101445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93520519429700219773400963 140280779144550329660101445)
    ·
      refine ⟨26302646089603186811269021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140280779144550329660101445 26302646089603186811269021)
      ·
        refine ⟨9863492283601195054225883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26302646089603186811269021 9863492283601195054225883)
        ·
          refine ⟨14795238425401792581338825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9863492283601195054225883 14795238425401792581338825)
          ·
            refine ⟨11096428819051344436004119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14795238425401792581338825 11096428819051344436004119)
            ·
              refine ⟨16644643228577016654006179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11096428819051344436004119 16644643228577016654006179)
              ·
                refine ⟨24966964842865524981009269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16644643228577016654006179 24966964842865524981009269)
                ·
                  refine ⟨2340652954018642966969619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24966964842865524981009269 2340652954018642966969619)
                  ·
                    refine ⟨3510979431027964450454429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2340652954018642966969619 3510979431027964450454429)
                    ·
                      refine ⟨1316617286635486668920411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3510979431027964450454429 1316617286635486668920411)
                      ·
                        rfl

theorem cell23_2564103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_2564103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564103 prefixEnd_2564103 := by exact prefixLift 2564103
  have htrace : WordTrace (prefixWord ++ tailWord_2564103) baseStart_2564103 baseEnd_2564103 := by
    simpa [prefixWord, tailWord_2564103, baseEnd_2564103] using wordTrace_append hprefix tailTrace_2564103
  have hstable : (prefixWord ++ tailWord_2564103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564103).length < 2 ^ (prefixWord ++ tailWord_2564103).sum := by decide
  have hdescent : baseEnd_2564103 < baseStart_2564103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564146 : List Nat := [3, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5]
def baseStart_2564146 : Nat := 118140960795 + 2564146 * 2 ^ 59
def prefixEnd_2564146 : Nat := 4983230072969 + 3 ^ 40 * 2564146 * 2
def baseEnd_2564146 : Nat := 1316639366303630000682713

theorem tailTrace_2564146 : CollatzResearch.WordTrace tailWord_2564146 prefixEnd_2564146 1316639366303630000682713 := by
  unfold tailWord_2564146
  simp only [CollatzResearch.WordTrace]
  refine ⟨23380521942136109529304073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62348058512362958744810861 23380521942136109529304073)
  ·
    refine ⟨17535391456602082146978055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23380521942136109529304073 17535391456602082146978055)
    ·
      refine ⟨26303087184903123220467083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17535391456602082146978055 26303087184903123220467083)
      ·
        refine ⟨39454630777354684830700625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26303087184903123220467083 39454630777354684830700625)
        ·
          refine ⟨29590973083016013623025469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39454630777354684830700625 29590973083016013623025469)
          ·
            refine ⟨11096614906131005108634551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29590973083016013623025469 11096614906131005108634551)
            ·
              refine ⟨16644922359196507662951827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11096614906131005108634551 16644922359196507662951827)
              ·
                refine ⟨24967383538794761494427741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16644922359196507662951827 24967383538794761494427741)
                ·
                  refine ⟨9362768827048035560410403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24967383538794761494427741 9362768827048035560410403)
                  ·
                    refine ⟨14044153240572053340615605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9362768827048035560410403 14044153240572053340615605)
                    ·
                      refine ⟨1316639366303630000682713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14044153240572053340615605 1316639366303630000682713)
                      ·
                        rfl

theorem cell23_2564146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_2564146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564146 prefixEnd_2564146 := by exact prefixLift 2564146
  have htrace : WordTrace (prefixWord ++ tailWord_2564146) baseStart_2564146 baseEnd_2564146 := by
    simpa [prefixWord, tailWord_2564146, baseEnd_2564146] using wordTrace_append hprefix tailTrace_2564146
  have hstable : (prefixWord ++ tailWord_2564146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564146).length < 2 ^ (prefixWord ++ tailWord_2564146).sum := by decide
  have hdescent : baseEnd_2564146 < baseStart_2564146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564156 : List Nat := [2, 2, 2, 2, 2, 1, 3, 1, 1, 1, 6]
def baseStart_2564156 : Nat := 118140960795 + 2564156 * 2 ^ 59
def prefixEnd_2564156 : Nat := 4983230072969 + 3 ^ 40 * 2564156 * 2
def baseEnd_2564156 : Nat := 1316644501110174961557667

theorem tailTrace_2564156 : CollatzResearch.WordTrace tailWord_2564156 prefixEnd_2564156 1316644501110174961557667 := by
  unfold tailWord_2564156
  simp only [CollatzResearch.WordTrace]
  refine ⟨46761226249254104912540161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62348301665672139883386881 46761226249254104912540161)
  ·
    refine ⟨35070919686940578684405121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46761226249254104912540161 35070919686940578684405121)
    ·
      refine ⟨26303189765205434013303841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35070919686940578684405121 26303189765205434013303841)
      ·
        refine ⟨19727392323904075509977881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26303189765205434013303841 19727392323904075509977881)
        ·
          refine ⟨14795544242928056632483411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19727392323904075509977881 14795544242928056632483411)
          ·
            refine ⟨22193316364392084948725117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14795544242928056632483411 22193316364392084948725117)
            ·
              refine ⟨8322493636647031855771919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22193316364392084948725117 8322493636647031855771919)
              ·
                refine ⟨12483740454970547783657879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8322493636647031855771919 12483740454970547783657879)
                ·
                  refine ⟨18725610682455821675486819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12483740454970547783657879 18725610682455821675486819)
                  ·
                    refine ⟨28088416023683732513230229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18725610682455821675486819 28088416023683732513230229)
                    ·
                      refine ⟨1316644501110174961557667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28088416023683732513230229 1316644501110174961557667)
                      ·
                        rfl

theorem cell23_2564156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_2564156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564156 prefixEnd_2564156 := by exact prefixLift 2564156
  have htrace : WordTrace (prefixWord ++ tailWord_2564156) baseStart_2564156 baseEnd_2564156 := by
    simpa [prefixWord, tailWord_2564156, baseEnd_2564156] using wordTrace_append hprefix tailTrace_2564156
  have hstable : (prefixWord ++ tailWord_2564156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564156).length < 2 ^ (prefixWord ++ tailWord_2564156).sum := by decide
  have hdescent : baseEnd_2564156 < baseStart_2564156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564160 : List Nat := [2, 1, 1, 2, 2, 4, 2, 2, 3, 2, 2]
def baseStart_2564160 : Nat := 118140960795 + 2564160 * 2 ^ 59
def prefixEnd_2564160 : Nat := 4983230072969 + 3 ^ 40 * 2564160 * 2
def baseEnd_2564160 : Nat := 1316646555032792945907649

theorem tailTrace_2564160 : CollatzResearch.WordTrace tailWord_2564160 prefixEnd_2564160 1316646555032792945907649 := by
  unfold tailWord_2564160
  simp only [CollatzResearch.WordTrace]
  refine ⟨46761299195246859254112967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62348398926995812338817289 46761299195246859254112967)
  ·
    refine ⟨70141948792870288881169451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46761299195246859254112967 70141948792870288881169451)
    ·
      refine ⟨105212923189305433321754177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70141948792870288881169451 105212923189305433321754177)
      ·
        refine ⟨78909692391979074991315633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105212923189305433321754177 78909692391979074991315633)
        ·
          refine ⟨59182269293984306243486725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78909692391979074991315633 59182269293984306243486725)
          ·
            refine ⟨11096675492622057420653761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59182269293984306243486725 11096675492622057420653761)
            ·
              refine ⟨8322506619466543065490321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11096675492622057420653761 8322506619466543065490321)
              ·
                refine ⟨6241879964599907299117741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8322506619466543065490321 6241879964599907299117741)
                ·
                  refine ⟨2340704986724965237169153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6241879964599907299117741 2340704986724965237169153)
                  ·
                    refine ⟨1755528740043723927876865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2340704986724965237169153 1755528740043723927876865)
                    ·
                      refine ⟨1316646555032792945907649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1755528740043723927876865 1316646555032792945907649)
                      ·
                        rfl

theorem cell23_2564160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 3, 2, 2].length) (baseStart_2564160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564160 prefixEnd_2564160 := by exact prefixLift 2564160
  have htrace : WordTrace (prefixWord ++ tailWord_2564160) baseStart_2564160 baseEnd_2564160 := by
    simpa [prefixWord, tailWord_2564160, baseEnd_2564160] using wordTrace_append hprefix tailTrace_2564160
  have hstable : (prefixWord ++ tailWord_2564160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564160).length < 2 ^ (prefixWord ++ tailWord_2564160).sum := by decide
  have hdescent : baseEnd_2564160 < baseStart_2564160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564173 : List Nat := [1, 6, 1, 1, 1, 1, 2, 1, 3, 2, 4]
def baseStart_2564173 : Nat := 118140960795 + 2564173 * 2 ^ 59
def prefixEnd_2564173 : Nat := 4983230072969 + 3 ^ 40 * 2564173 * 2
def baseEnd_2564173 : Nat := 1316653230281301395045089

theorem tailTrace_2564173 : CollatzResearch.WordTrace tailWord_2564173 prefixEnd_2564173 1316653230281301395045089 := by
  unfold tailWord_2564173
  simp only [CollatzResearch.WordTrace]
  refine ⟨93523072539446621728449173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62348715026297747818966115 93523072539446621728449173)
  ·
    refine ⟨4383894025286560393521055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 93523072539446621728449173 4383894025286560393521055)
    ·
      refine ⟨6575841037929840590281583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4383894025286560393521055 6575841037929840590281583)
      ·
        refine ⟨9863761556894760885422375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6575841037929840590281583 9863761556894760885422375)
        ·
          refine ⟨14795642335342141328133563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9863761556894760885422375 14795642335342141328133563)
          ·
            refine ⟨22193463503013211992200345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14795642335342141328133563 22193463503013211992200345)
            ·
              refine ⟨16645097627259908994150259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22193463503013211992200345 16645097627259908994150259)
              ·
                refine ⟨24967646440889863491225389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16645097627259908994150259 24967646440889863491225389)
                ·
                  refine ⟨9362867415333698809209521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24967646440889863491225389 9362867415333698809209521)
                  ·
                    refine ⟨7022150561500274106907141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9362867415333698809209521 7022150561500274106907141)
                    ·
                      refine ⟨1316653230281301395045089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7022150561500274106907141 1316653230281301395045089)
                      ·
                        rfl

theorem cell23_2564173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_2564173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564173 prefixEnd_2564173 := by exact prefixLift 2564173
  have htrace : WordTrace (prefixWord ++ tailWord_2564173) baseStart_2564173 baseEnd_2564173 := by
    simpa [prefixWord, tailWord_2564173, baseEnd_2564173] using wordTrace_append hprefix tailTrace_2564173
  have hstable : (prefixWord ++ tailWord_2564173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564173).length < 2 ^ (prefixWord ++ tailWord_2564173).sum := by decide
  have hdescent : baseEnd_2564173 < baseStart_2564173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564220 : List Nat := [2, 2, 2, 1, 1, 5, 1, 1, 3, 3, 2]
def baseStart_2564220 : Nat := 118140960795 + 2564220 * 2 ^ 59
def prefixEnd_2564220 : Nat := 4983230072969 + 3 ^ 40 * 2564220 * 2
def baseEnd_2564220 : Nat := 1316677363872062711157373

theorem tailTrace_2564220 : CollatzResearch.WordTrace tailWord_2564220 prefixEnd_2564220 1316677363872062711157373 := by
  unfold tailWord_2564220
  simp only [CollatzResearch.WordTrace]
  refine ⟨46762393385138174377705057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62349857846850899170273409 46762393385138174377705057)
  ·
    refine ⟨35071795038853630783278793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46762393385138174377705057 35071795038853630783278793)
    ·
      refine ⟨26303846279140223087459095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35071795038853630783278793 26303846279140223087459095)
      ·
        refine ⟨39455769418710334631188643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26303846279140223087459095 39455769418710334631188643)
        ·
          refine ⟨59183654128065501946782965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39455769418710334631188643 59183654128065501946782965)
          ·
            refine ⟨5548467574506140807510903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59183654128065501946782965 5548467574506140807510903)
            ·
              refine ⟨8322701361759211211266355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5548467574506140807510903 8322701361759211211266355)
              ·
                refine ⟨12484052042638816816899533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8322701361759211211266355 12484052042638816816899533)
                ·
                  refine ⟨4681519515989556306337325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12484052042638816816899533 4681519515989556306337325)
                  ·
                    refine ⟨1755569818496083614876497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4681519515989556306337325 1755569818496083614876497)
                    ·
                      refine ⟨1316677363872062711157373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1755569818496083614876497 1316677363872062711157373)
                      ·
                        rfl

theorem cell23_2564220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 3, 3, 2].length) (baseStart_2564220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564220 prefixEnd_2564220 := by exact prefixLift 2564220
  have htrace : WordTrace (prefixWord ++ tailWord_2564220) baseStart_2564220 baseEnd_2564220 := by
    simpa [prefixWord, tailWord_2564220, baseEnd_2564220] using wordTrace_append hprefix tailTrace_2564220
  have hstable : (prefixWord ++ tailWord_2564220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564220).length < 2 ^ (prefixWord ++ tailWord_2564220).sum := by decide
  have hdescent : baseEnd_2564220 < baseStart_2564220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564253 : List Nat := [1, 4, 2, 1, 1, 3, 1, 1, 2, 4, 3]
def baseStart_2564253 : Nat := 118140960795 + 2564253 * 2 ^ 59
def prefixEnd_2564253 : Nat := 4983230072969 + 3 ^ 40 * 2564253 * 2
def baseEnd_2564253 : Nat := 1316694308733661082044721

theorem tailTrace_2564253 : CollatzResearch.WordTrace tailWord_2564253 prefixEnd_2564253 1316694308733661082044721 := by
  unfold tailWord_2564253
  simp only [CollatzResearch.WordTrace]
  refine ⟨93525990379156795391361413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62350660252771196927574275 93525990379156795391361413)
  ·
    refine ⟨17536123196091899135880265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93525990379156795391361413 17536123196091899135880265)
    ·
      refine ⟨13152092397068924351910199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17536123196091899135880265 13152092397068924351910199)
      ·
        refine ⟨19728138595603386527865299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13152092397068924351910199 19728138595603386527865299)
        ·
          refine ⟨29592207893405079791797949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19728138595603386527865299 29592207893405079791797949)
          ·
            refine ⟨11097077960026904921924231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29592207893405079791797949 11097077960026904921924231)
            ·
              refine ⟨16645616940040357382886347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11097077960026904921924231 16645616940040357382886347)
              ·
                refine ⟨24968425410060536074329521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16645616940040357382886347 24968425410060536074329521)
                ·
                  refine ⟨18726319057545402055747141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24968425410060536074329521 18726319057545402055747141)
                  ·
                    refine ⟨3511184823289762885452589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18726319057545402055747141 3511184823289762885452589)
                    ·
                      refine ⟨1316694308733661082044721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3511184823289762885452589 1316694308733661082044721)
                      ·
                        rfl

theorem cell23_2564253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_2564253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564253 prefixEnd_2564253 := by exact prefixLift 2564253
  have htrace : WordTrace (prefixWord ++ tailWord_2564253) baseStart_2564253 baseEnd_2564253 := by
    simpa [prefixWord, tailWord_2564253, baseEnd_2564253] using wordTrace_append hprefix tailTrace_2564253
  have hstable : (prefixWord ++ tailWord_2564253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564253).length < 2 ^ (prefixWord ++ tailWord_2564253).sum := by decide
  have hdescent : baseEnd_2564253 < baseStart_2564253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564360 : List Nat := [2, 1, 3, 2, 3, 1, 1, 1, 4, 2, 3]
def baseStart_2564360 : Nat := 118140960795 + 2564360 * 2 ^ 59
def prefixEnd_2564360 : Nat := 4983230072969 + 3 ^ 40 * 2564360 * 2
def baseEnd_2564360 : Nat := 1316749251163692163406729

theorem tailTrace_2564360 : CollatzResearch.WordTrace tailWord_2564360 prefixEnd_2564360 1316749251163692163406729 := by
  unfold tailWord_2564360
  simp only [CollatzResearch.WordTrace]
  refine ⟨46764946494884576332753267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62353261993179435110337689 46764946494884576332753267)
  ·
    refine ⟨70147419742326864499129901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46764946494884576332753267 70147419742326864499129901)
    ·
      refine ⟨26305282403372574187173713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70147419742326864499129901 26305282403372574187173713)
      ·
        refine ⟨19728961802529430640380285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26305282403372574187173713 19728961802529430640380285)
        ·
          refine ⟨7398360675948536490142607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19728961802529430640380285 7398360675948536490142607)
          ·
            refine ⟨11097541013922804735213911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7398360675948536490142607 11097541013922804735213911)
            ·
              refine ⟨16646311520884207102820867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11097541013922804735213911 16646311520884207102820867)
              ·
                refine ⟨24969467281326310654231301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16646311520884207102820867 24969467281326310654231301)
                ·
                  refine ⟨4681775115248683247668369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24969467281326310654231301 4681775115248683247668369)
                  ·
                    refine ⟨3511331336436512435751277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4681775115248683247668369 3511331336436512435751277)
                    ·
                      refine ⟨1316749251163692163406729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3511331336436512435751277 1316749251163692163406729)
                      ·
                        rfl

theorem cell23_2564360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_2564360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564360 prefixEnd_2564360 := by exact prefixLift 2564360
  have htrace : WordTrace (prefixWord ++ tailWord_2564360) baseStart_2564360 baseEnd_2564360 := by
    simpa [prefixWord, tailWord_2564360, baseEnd_2564360] using wordTrace_append hprefix tailTrace_2564360
  have hstable : (prefixWord ++ tailWord_2564360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564360).length < 2 ^ (prefixWord ++ tailWord_2564360).sum := by decide
  have hdescent : baseEnd_2564360 < baseStart_2564360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564363 : List Nat := [1, 1, 1, 1, 5, 2, 2, 4, 6]
def baseStart_2564363 : Nat := 118140960795 + 2564363 * 2 ^ 59
def prefixEnd_2564363 : Nat := 4983230072969 + 3 ^ 40 * 2564363 * 2
def baseEnd_2564363 : Nat := 146305643511739516852135

theorem tailTrace_2564363 : CollatzResearch.WordTrace tailWord_2564363 prefixEnd_2564363 146305643511739516852135 := by
  unfold tailWord_2564363
  simp only [CollatzResearch.WordTrace]
  refine ⟨93530002408758284177865743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62353334939172189451910495 93530002408758284177865743)
  ·
    refine ⟨140295003613137426266798615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93530002408758284177865743 140295003613137426266798615)
    ·
      refine ⟨210442505419706139400197923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140295003613137426266798615 210442505419706139400197923)
      ·
        refine ⟨315663758129559209100296885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210442505419706139400197923 315663758129559209100296885)
        ·
          refine ⟨29593477324646175853152833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 315663758129559209100296885 29593477324646175853152833)
          ·
            refine ⟨22195107993484631889864625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29593477324646175853152833 22195107993484631889864625)
            ·
              refine ⟨16646330995113473917398469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22195107993484631889864625 16646330995113473917398469)
              ·
                refine ⟨3121187061583776359512213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16646330995113473917398469 3121187061583776359512213)
                ·
                  refine ⟨146305643511739516852135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3121187061583776359512213 146305643511739516852135)
                  ·
                    rfl

theorem cell23_2564363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 6].length) (baseStart_2564363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564363 prefixEnd_2564363 := by exact prefixLift 2564363
  have htrace : WordTrace (prefixWord ++ tailWord_2564363) baseStart_2564363 baseEnd_2564363 := by
    simpa [prefixWord, tailWord_2564363, baseEnd_2564363] using wordTrace_append hprefix tailTrace_2564363
  have hstable : (prefixWord ++ tailWord_2564363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564363).length < 2 ^ (prefixWord ++ tailWord_2564363).sum := by decide
  have hdescent : baseEnd_2564363 < baseStart_2564363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564391 : List Nat := [1, 1, 8, 1, 1, 1, 2, 1, 2, 1, 4]
def baseStart_2564391 : Nat := 118140960795 + 2564391 * 2 ^ 59
def prefixEnd_2564391 : Nat := 4983230072969 + 3 ^ 40 * 2564391 * 2
def baseEnd_2564391 : Nat := 1316765169063981542119087

theorem tailTrace_2564391 : CollatzResearch.WordTrace tailWord_2564391 prefixEnd_2564391 1316765169063981542119087 := by
  unfold tailWord_2564391
  simp only [CollatzResearch.WordTrace]
  refine ⟨93531023652656844959885027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62354015768437896639923351 93531023652656844959885027)
  ·
    refine ⟨140296535478985267439827541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93531023652656844959885027 140296535478985267439827541)
    ·
      refine ⟨1644100025144358602810479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 140296535478985267439827541 1644100025144358602810479)
      ·
        refine ⟨2466150037716537904215719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1644100025144358602810479 2466150037716537904215719)
        ·
          refine ⟨3699225056574806856323579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2466150037716537904215719 3699225056574806856323579)
          ·
            refine ⟨5548837584862210284485369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3699225056574806856323579 5548837584862210284485369)
            ·
              refine ⟨4161628188646657713364027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5548837584862210284485369 4161628188646657713364027)
              ·
                refine ⟨6242442282969986570046041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4161628188646657713364027 6242442282969986570046041)
                ·
                  refine ⟨4681831712227489927534531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6242442282969986570046041 4681831712227489927534531)
                  ·
                    refine ⟨7022747568341234891301797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4681831712227489927534531 7022747568341234891301797)
                    ·
                      refine ⟨1316765169063981542119087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7022747568341234891301797 1316765169063981542119087)
                      ·
                        rfl

theorem cell23_2564391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_2564391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564391 prefixEnd_2564391 := by exact prefixLift 2564391
  have htrace : WordTrace (prefixWord ++ tailWord_2564391) baseStart_2564391 baseEnd_2564391 := by
    simpa [prefixWord, tailWord_2564391, baseEnd_2564391] using wordTrace_append hprefix tailTrace_2564391
  have hstable : (prefixWord ++ tailWord_2564391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564391).length < 2 ^ (prefixWord ++ tailWord_2564391).sum := by decide
  have hdescent : baseEnd_2564391 < baseStart_2564391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564394 : List Nat := [3, 1, 4, 2, 2, 1, 2, 1, 2, 2, 3]
def baseStart_2564394 : Nat := 118140960795 + 2564394 * 2 ^ 59
def prefixEnd_2564394 : Nat := 4983230072969 + 3 ^ 40 * 2564394 * 2
def baseEnd_2564394 : Nat := 1316766709505945030381573

theorem tailTrace_2564394 : CollatzResearch.WordTrace tailWord_2564394 prefixEnd_2564394 1316766709505945030381573 := by
  unfold tailWord_2564394
  simp only [CollatzResearch.WordTrace]
  refine ⟨23382783267911494118061059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62354088714430650981496157 23382783267911494118061059)
  ·
    refine ⟨35074174901867241177091589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23382783267911494118061059 35074174901867241177091589)
    ·
      refine ⟨6576407794100107720704673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35074174901867241177091589 6576407794100107720704673)
      ·
        refine ⟨4932305845575080790528505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6576407794100107720704673 4932305845575080790528505)
        ·
          refine ⟨3699229384181310592896379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4932305845575080790528505 3699229384181310592896379)
          ·
            refine ⟨5548844076271965889344569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3699229384181310592896379 5548844076271965889344569)
            ·
              refine ⟨4161633057203974417008427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5548844076271965889344569 4161633057203974417008427)
              ·
                refine ⟨6242449585805961625512641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4161633057203974417008427 6242449585805961625512641)
                ·
                  refine ⟨4681837189354471219134481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6242449585805961625512641 4681837189354471219134481)
                  ·
                    refine ⟨3511377892015853414350861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4681837189354471219134481 3511377892015853414350861)
                    ·
                      refine ⟨1316766709505945030381573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3511377892015853414350861 1316766709505945030381573)
                      ·
                        rfl

theorem cell23_2564394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_2564394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564394 prefixEnd_2564394 := by exact prefixLift 2564394
  have htrace : WordTrace (prefixWord ++ tailWord_2564394) baseStart_2564394 baseEnd_2564394 := by
    simpa [prefixWord, tailWord_2564394, baseEnd_2564394] using wordTrace_append hprefix tailTrace_2564394
  have hstable : (prefixWord ++ tailWord_2564394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564394).length < 2 ^ (prefixWord ++ tailWord_2564394).sum := by decide
  have hdescent : baseEnd_2564394 < baseStart_2564394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564423 : List Nat := [1, 1, 4, 1, 2, 2, 1, 2, 3, 6]
def baseStart_2564423 : Nat := 118140960795 + 2564423 * 2 ^ 59
def prefixEnd_2564423 : Nat := 4983230072969 + 3 ^ 40 * 2564423 * 2
def baseEnd_2564423 : Nat := 438927200148308472306313

theorem tailTrace_2564423 : CollatzResearch.WordTrace tailWord_2564423 prefixEnd_2564423 438927200148308472306313 := by
  unfold tailWord_2564423
  simp only [CollatzResearch.WordTrace]
  refine ⟨93532190788540914425049923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62354793859027276283366615 93532190788540914425049923)
  ·
    refine ⟨140298286182811371637574885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93532190788540914425049923 140298286182811371637574885)
    ·
      refine ⟨26305928659277132182045291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140298286182811371637574885 26305928659277132182045291)
      ·
        refine ⟨39458892988915698273067937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26305928659277132182045291 39458892988915698273067937)
        ·
          refine ⟨29594169741686773704800953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39458892988915698273067937 29594169741686773704800953)
          ·
            refine ⟨22195627306265080278600715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29594169741686773704800953 22195627306265080278600715)
            ·
              refine ⟨33293440959397620417901073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22195627306265080278600715 33293440959397620417901073)
              ·
                refine ⟨24970080719548215313425805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33293440959397620417901073 24970080719548215313425805)
                ·
                  refine ⟨9363780269830580742534677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24970080719548215313425805 9363780269830580742534677)
                  ·
                    refine ⟨438927200148308472306313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9363780269830580742534677 438927200148308472306313)
                    ·
                      rfl

theorem cell23_2564423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_2564423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564423 prefixEnd_2564423 := by exact prefixLift 2564423
  have htrace : WordTrace (prefixWord ++ tailWord_2564423) baseStart_2564423 baseEnd_2564423 := by
    simpa [prefixWord, tailWord_2564423, baseEnd_2564423] using wordTrace_append hprefix tailTrace_2564423
  have hstable : (prefixWord ++ tailWord_2564423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564423).length < 2 ^ (prefixWord ++ tailWord_2564423).sum := by decide
  have hdescent : baseEnd_2564423 < baseStart_2564423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564447 : List Nat := [1, 1, 2, 3, 1, 2, 3, 1, 5, 2, 2]
def baseStart_2564447 : Nat := 118140960795 + 2564447 * 2 ^ 59
def prefixEnd_2564447 : Nat := 4983230072969 + 3 ^ 40 * 2564447 * 2
def baseEnd_2564447 : Nat := 1316793923980633323018829

theorem tailTrace_2564447 : CollatzResearch.WordTrace tailWord_2564447 prefixEnd_2564447 1316793923980633323018829 := by
  unfold tailWord_2564447
  simp only [CollatzResearch.WordTrace]
  refine ⟨93533066140453966523923595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62355377426969311015949063 93533066140453966523923595)
  ·
    refine ⟨140299599210680949785885393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93533066140453966523923595 140299599210680949785885393)
    ·
      refine ⟨105224699408010712339414045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140299599210680949785885393 105224699408010712339414045)
      ·
        refine ⟨39459262278004017127280267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105224699408010712339414045 39459262278004017127280267)
        ·
          refine ⟨59188893417006025690920401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39459262278004017127280267 59188893417006025690920401)
          ·
            refine ⟨44391670062754519268190301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59188893417006025690920401 44391670062754519268190301)
            ·
              refine ⟨16646876273532944725571363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44391670062754519268190301 16646876273532944725571363)
              ·
                refine ⟨24970314410299417088357045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16646876273532944725571363 24970314410299417088357045)
                ·
                  refine ⟨2340966975965570352033473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24970314410299417088357045 2340966975965570352033473)
                  ·
                    refine ⟨1755725231974177764025105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2340966975965570352033473 1755725231974177764025105)
                    ·
                      refine ⟨1316793923980633323018829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1755725231974177764025105 1316793923980633323018829)
                      ·
                        rfl

theorem cell23_2564447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 5, 2, 2].length) (baseStart_2564447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564447 prefixEnd_2564447 := by exact prefixLift 2564447
  have htrace : WordTrace (prefixWord ++ tailWord_2564447) baseStart_2564447 baseEnd_2564447 := by
    simpa [prefixWord, tailWord_2564447, baseEnd_2564447] using wordTrace_append hprefix tailTrace_2564447
  have hstable : (prefixWord ++ tailWord_2564447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564447).length < 2 ^ (prefixWord ++ tailWord_2564447).sum := by decide
  have hdescent : baseEnd_2564447 < baseStart_2564447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564464 : List Nat := [2, 1, 1, 1, 4, 5, 2, 1, 1, 1, 4]
def baseStart_2564464 : Nat := 118140960795 + 2564464 * 2 ^ 59
def prefixEnd_2564464 : Nat := 4983230072969 + 3 ^ 40 * 2564464 * 2
def baseEnd_2564464 : Nat := 1316802653151759756506251

theorem tailTrace_2564464 : CollatzResearch.WordTrace tailWord_2564464 prefixEnd_2564464 1316802653151759756506251 := by
  unfold tailWord_2564464
  simp only [CollatzResearch.WordTrace]
  refine ⟨46766843090696189213646223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62355790787594918951528297 46766843090696189213646223)
  ·
    refine ⟨70150264636044283820469335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46766843090696189213646223 70150264636044283820469335)
    ·
      refine ⟨105225396954066425730704003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70150264636044283820469335 105225396954066425730704003)
      ·
        refine ⟨157838095431099638596056005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105225396954066425730704003 157838095431099638596056005)
        ·
          refine ⟨29594642893331182236760501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 157838095431099638596056005 29594642893331182236760501)
          ·
            refine ⟨2774497771249798334696297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29594642893331182236760501 2774497771249798334696297)
            ·
              refine ⟨2080873328437348751022223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2774497771249798334696297 2080873328437348751022223)
              ·
                refine ⟨3121309992656023126533335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2080873328437348751022223 3121309992656023126533335)
                ·
                  refine ⟨4681964988984034689800003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3121309992656023126533335 4681964988984034689800003)
                  ·
                    refine ⟨7022947483476052034700005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4681964988984034689800003 7022947483476052034700005)
                    ·
                      refine ⟨1316802653151759756506251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7022947483476052034700005 1316802653151759756506251)
                      ·
                        rfl

theorem cell23_2564464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 1, 1, 4].length) (baseStart_2564464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564464 prefixEnd_2564464 := by exact prefixLift 2564464
  have htrace : WordTrace (prefixWord ++ tailWord_2564464) baseStart_2564464 baseEnd_2564464 := by
    simpa [prefixWord, tailWord_2564464, baseEnd_2564464] using wordTrace_append hprefix tailTrace_2564464
  have hstable : (prefixWord ++ tailWord_2564464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564464).length < 2 ^ (prefixWord ++ tailWord_2564464).sum := by decide
  have hdescent : baseEnd_2564464 < baseStart_2564464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564473 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 2, 2, 6]
def baseStart_2564473 : Nat := 118140960795 + 2564473 * 2 ^ 59
def prefixEnd_2564473 : Nat := 4983230072969 + 3 ^ 40 * 2564473 * 2
def baseEnd_2564473 : Nat := 1316807274477650221293709

theorem tailTrace_2564473 : CollatzResearch.WordTrace tailWord_2564473 prefixEnd_2564473 1316807274477650221293709 := by
  unfold tailWord_2564473
  simp only [CollatzResearch.WordTrace]
  refine ⟨93534014438359772964370073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62356009625573181976246715 93534014438359772964370073)
  ·
    refine ⟨70150510828769829723277555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93534014438359772964370073 70150510828769829723277555)
    ·
      refine ⟨105225766243154744584916333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70150510828769829723277555 105225766243154744584916333)
      ·
        refine ⟨39459662341183029219343625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105225766243154744584916333 39459662341183029219343625)
        ·
          refine ⟨29594746755887271914507719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39459662341183029219343625 29594746755887271914507719)
          ·
            refine ⟨44392120133830907871761579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29594746755887271914507719 44392120133830907871761579)
            ·
              refine ⟨66588180200746361807642369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44392120133830907871761579 66588180200746361807642369)
              ·
                refine ⟨49941135150559771355731777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66588180200746361807642369 49941135150559771355731777)
                ·
                  refine ⟨37455851362919828516798833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49941135150559771355731777 37455851362919828516798833)
                  ·
                    refine ⟨28091888522189871387599125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37455851362919828516798833 28091888522189871387599125)
                    ·
                      refine ⟨1316807274477650221293709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28091888522189871387599125 1316807274477650221293709)
                      ·
                        rfl

theorem cell23_2564473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_2564473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564473 prefixEnd_2564473 := by exact prefixLift 2564473
  have htrace : WordTrace (prefixWord ++ tailWord_2564473) baseStart_2564473 baseEnd_2564473 := by
    simpa [prefixWord, tailWord_2564473, baseEnd_2564473] using wordTrace_append hprefix tailTrace_2564473
  have hstable : (prefixWord ++ tailWord_2564473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564473).length < 2 ^ (prefixWord ++ tailWord_2564473).sum := by decide
  have hdescent : baseEnd_2564473 < baseStart_2564473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564481 : List Nat := [1, 2, 4, 3, 1, 2, 2, 1, 3, 2, 2]
def baseStart_2564481 : Nat := 118140960795 + 2564481 * 2 ^ 59
def prefixEnd_2564481 : Nat := 4983230072969 + 3 ^ 40 * 2564481 * 2
def baseEnd_2564481 : Nat := 1316811382322886189993673

theorem tailTrace_2564481 : CollatzResearch.WordTrace tailWord_2564481 prefixEnd_2564481 1316811382322886189993673 := by
  unfold tailWord_2564481
  simp only [CollatzResearch.WordTrace]
  refine ⟨93534306222330790330661297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62356204148220526887107531 93534306222330790330661297)
  ·
    refine ⟨70150729666748092747995973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93534306222330790330661297 70150729666748092747995973)
    ·
      refine ⟨13153261812515267390249245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70150729666748092747995973 13153261812515267390249245)
      ·
        refine ⟨4932473179693225271343467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13153261812515267390249245 4932473179693225271343467)
        ·
          refine ⟨7398709769539837907015201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4932473179693225271343467 7398709769539837907015201)
          ·
            refine ⟨5549032327154878430261401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7398709769539837907015201 5549032327154878430261401)
            ·
              refine ⟨4161774245366158822696051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5549032327154878430261401 4161774245366158822696051)
              ·
                refine ⟨6242661368049238234044077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4161774245366158822696051 6242661368049238234044077)
                ·
                  refine ⟨2340998013018464337766529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6242661368049238234044077 2340998013018464337766529)
                  ·
                    refine ⟨1755748509763848253324897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2340998013018464337766529 1755748509763848253324897)
                    ·
                      refine ⟨1316811382322886189993673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1755748509763848253324897 1316811382322886189993673)
                      ·
                        rfl

theorem cell23_2564481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_2564481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564481 prefixEnd_2564481 := by exact prefixLift 2564481
  have htrace : WordTrace (prefixWord ++ tailWord_2564481) baseStart_2564481 baseEnd_2564481 := by
    simpa [prefixWord, tailWord_2564481, baseEnd_2564481] using wordTrace_append hprefix tailTrace_2564481
  have hstable : (prefixWord ++ tailWord_2564481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564481).length < 2 ^ (prefixWord ++ tailWord_2564481).sum := by decide
  have hdescent : baseEnd_2564481 < baseStart_2564481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564494 : List Nat := [4, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4]
def baseStart_2564494 : Nat := 118140960795 + 2564494 * 2 ^ 59
def prefixEnd_2564494 : Nat := 4983230072969 + 3 ^ 40 * 2564494 * 2
def baseEnd_2564494 : Nat := 1316818057571394639131113

theorem tailTrace_2564494 : CollatzResearch.WordTrace tailWord_2564494 prefixEnd_2564494 1316818057571394639131113 := by
  unfold tailWord_2564494
  simp only [CollatzResearch.WordTrace]
  refine ⟨11691847546410461693860567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62356520247522462367256357 11691847546410461693860567)
  ·
    refine ⟨17537771319615692540790851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11691847546410461693860567 17537771319615692540790851)
    ·
      refine ⟨26306656979423538811186277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17537771319615692540790851 26306656979423538811186277)
      ·
        refine ⟨4932498183641913527097427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26306656979423538811186277 4932498183641913527097427)
        ·
          refine ⟨7398747275462870290646141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4932498183641913527097427 7398747275462870290646141)
          ·
            refine ⟨2774530228298576358992303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7398747275462870290646141 2774530228298576358992303)
            ·
              refine ⟨4161795342447864538488455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2774530228298576358992303 4161795342447864538488455)
              ·
                refine ⟨6242693013671796807732683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4161795342447864538488455 6242693013671796807732683)
                ·
                  refine ⟨9364039520507695211599025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6242693013671796807732683 9364039520507695211599025)
                  ·
                    refine ⟨7023029640380771408699269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9364039520507695211599025 7023029640380771408699269)
                    ·
                      refine ⟨1316818057571394639131113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7023029640380771408699269 1316818057571394639131113)
                      ·
                        rfl

theorem cell23_2564494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_2564494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564494 prefixEnd_2564494 := by exact prefixLift 2564494
  have htrace : WordTrace (prefixWord ++ tailWord_2564494) baseStart_2564494 baseEnd_2564494 := by
    simpa [prefixWord, tailWord_2564494, baseEnd_2564494] using wordTrace_append hprefix tailTrace_2564494
  have hstable : (prefixWord ++ tailWord_2564494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564494).length < 2 ^ (prefixWord ++ tailWord_2564494).sum := by decide
  have hdescent : baseEnd_2564494 < baseStart_2564494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564532 : List Nat := [2, 5, 2, 2, 2, 1, 1, 1, 3, 2, 2]
def baseStart_2564532 : Nat := 118140960795 + 2564532 * 2 ^ 59
def prefixEnd_2564532 : Nat := 4983230072969 + 3 ^ 40 * 2564532 * 2
def baseEnd_2564532 : Nat := 1316837569836265490455939

theorem tailTrace_2564532 : CollatzResearch.WordTrace tailWord_2564532 prefixEnd_2564532 1316837569836265490455939 := by
  unfold tailWord_2564532
  simp only [CollatzResearch.WordTrace]
  refine ⟨46768083172573013020383925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62357444230097350693845233 46768083172573013020383925)
  ·
    refine ⟨4384507797428719970660993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46768083172573013020383925 4384507797428719970660993)
    ·
      refine ⟨3288380848071539977995745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4384507797428719970660993 3288380848071539977995745)
      ·
        refine ⟨2466285636053654983496809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3288380848071539977995745 2466285636053654983496809)
        ·
          refine ⟨1849714227040241237622607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2466285636053654983496809 1849714227040241237622607)
          ·
            refine ⟨2774571340560361856433911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1849714227040241237622607 2774571340560361856433911)
            ·
              refine ⟨4161857010840542784650867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2774571340560361856433911 4161857010840542784650867)
              ·
                refine ⟨6242785516260814176976301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4161857010840542784650867 6242785516260814176976301)
                ·
                  refine ⟨2341044568597805316366113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6242785516260814176976301 2341044568597805316366113)
                  ·
                    refine ⟨1755783426448353987274585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2341044568597805316366113 1755783426448353987274585)
                    ·
                      refine ⟨1316837569836265490455939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1755783426448353987274585 1316837569836265490455939)
                      ·
                        rfl

theorem cell23_2564532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_2564532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564532 prefixEnd_2564532 := by exact prefixLift 2564532
  have htrace : WordTrace (prefixWord ++ tailWord_2564532) baseStart_2564532 baseEnd_2564532 := by
    simpa [prefixWord, tailWord_2564532, baseEnd_2564532] using wordTrace_append hprefix tailTrace_2564532
  have hstable : (prefixWord ++ tailWord_2564532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564532).length < 2 ^ (prefixWord ++ tailWord_2564532).sum := by decide
  have hdescent : baseEnd_2564532 < baseStart_2564532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564577 : List Nat := [1, 2, 3, 1, 2, 2, 2, 5, 5]
def baseStart_2564577 : Nat := 118140960795 + 2564577 * 2 ^ 59
def prefixEnd_2564577 : Nat := 4983230072969 + 3 ^ 40 * 2564577 * 2
def baseEnd_2564577 : Nat := 146317852940635312710359

theorem tailTrace_2564577 : CollatzResearch.WordTrace tailWord_2564577 prefixEnd_2564577 146317852940635312710359 := by
  unfold tailWord_2564577
  simp only [CollatzResearch.WordTrace]
  refine ⟨93537807629982998726155985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62358538419988665817437323 93537807629982998726155985)
  ·
    refine ⟨70153355722487249044616989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93537807629982998726155985 70153355722487249044616989)
    ·
      refine ⟨26307508395932718391731371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70153355722487249044616989 26307508395932718391731371)
      ·
        refine ⟨39461262593899077587597057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26307508395932718391731371 39461262593899077587597057)
        ·
          refine ⟨29595946945424308190697793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39461262593899077587597057 29595946945424308190697793)
          ·
            refine ⟨22196960209068231143023345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29595946945424308190697793 22196960209068231143023345)
            ·
              refine ⟨16647720156801173357267509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22196960209068231143023345 16647720156801173357267509)
              ·
                refine ⟨1560723764700110002243829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16647720156801173357267509 1560723764700110002243829)
                ·
                  refine ⟨146317852940635312710359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1560723764700110002243829 146317852940635312710359)
                  ·
                    rfl

theorem cell23_2564577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 5, 5].length) (baseStart_2564577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564577 prefixEnd_2564577 := by exact prefixLift 2564577
  have htrace : WordTrace (prefixWord ++ tailWord_2564577) baseStart_2564577 baseEnd_2564577 := by
    simpa [prefixWord, tailWord_2564577, baseEnd_2564577] using wordTrace_append hprefix tailTrace_2564577
  have hstable : (prefixWord ++ tailWord_2564577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564577).length < 2 ^ (prefixWord ++ tailWord_2564577).sum := by decide
  have hdescent : baseEnd_2564577 < baseStart_2564577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564600 : List Nat := [2, 1, 2, 1, 1, 4, 1, 3, 1, 2, 5]
def baseStart_2564600 : Nat := 118140960795 + 2564600 * 2 ^ 59
def prefixEnd_2564600 : Nat := 4983230072969 + 3 ^ 40 * 2564600 * 2
def baseEnd_2564600 : Nat := 1316872486520771224405625

theorem tailTrace_2564600 : CollatzResearch.WordTrace tailWord_2564600 prefixEnd_2564600 1316872486520771224405625 := by
  unfold tailWord_2564600
  simp only [CollatzResearch.WordTrace]
  refine ⟨46769323254449836827121627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62359097672599782436162169 46769323254449836827121627)
  ·
    refine ⟨70153984881674755240682441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46769323254449836827121627 70153984881674755240682441)
    ·
      refine ⟨52615488661256066430511831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70153984881674755240682441 52615488661256066430511831)
      ·
        refine ⟨78923232991884099645767747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52615488661256066430511831 78923232991884099645767747)
        ·
          refine ⟨118384849487826149468651621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78923232991884099645767747 118384849487826149468651621)
          ·
            refine ⟨22197159278967403025372179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118384849487826149468651621 22197159278967403025372179)
            ·
              refine ⟨33295738918451104538058269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22197159278967403025372179 33295738918451104538058269)
              ·
                refine ⟨12485902094419164201771851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33295738918451104538058269 12485902094419164201771851)
                ·
                  refine ⟨18728853141628746302657777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12485902094419164201771851 18728853141628746302657777)
                  ·
                    refine ⟨14046639856221559726993333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18728853141628746302657777 14046639856221559726993333)
                    ·
                      refine ⟨1316872486520771224405625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14046639856221559726993333 1316872486520771224405625)
                      ·
                        rfl

theorem cell23_2564600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 1, 2, 5].length) (baseStart_2564600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564600 prefixEnd_2564600 := by exact prefixLift 2564600
  have htrace : WordTrace (prefixWord ++ tailWord_2564600) baseStart_2564600 baseEnd_2564600 := by
    simpa [prefixWord, tailWord_2564600, baseEnd_2564600] using wordTrace_append hprefix tailTrace_2564600
  have hstable : (prefixWord ++ tailWord_2564600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564600).length < 2 ^ (prefixWord ++ tailWord_2564600).sum := by decide
  have hdescent : baseEnd_2564600 < baseStart_2564600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564627 : List Nat := [1, 1, 1, 2, 1, 5, 1, 2, 1, 6, 2]
def baseStart_2564627 : Nat := 118140960795 + 2564627 * 2 ^ 59
def prefixEnd_2564627 : Nat := 4983230072969 + 3 ^ 40 * 2564627 * 2
def baseEnd_2564627 : Nat := 1316886350498442618768001

theorem tailTrace_2564627 : CollatzResearch.WordTrace tailWord_2564627 prefixEnd_2564627 1316886350498442618768001 := by
  unfold tailWord_2564627
  simp only [CollatzResearch.WordTrace]
  refine ⟨93539631279801857265476135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62359754186534571510317423 93539631279801857265476135)
  ·
    refine ⟨140309446919702785898214203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93539631279801857265476135 140309446919702785898214203)
    ·
      refine ⟨210464170379554178847321305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140309446919702785898214203 210464170379554178847321305)
      ·
        refine ⟨157848127784665634135490979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210464170379554178847321305 157848127784665634135490979)
        ·
          refine ⟨236772191676998451203236469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157848127784665634135490979 236772191676998451203236469)
          ·
            refine ⟨22197392969718604800303419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 236772191676998451203236469 22197392969718604800303419)
            ·
              refine ⟨33296089454577907200455129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22197392969718604800303419 33296089454577907200455129)
              ·
                refine ⟨24972067090933430400341347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33296089454577907200455129 24972067090933430400341347)
                ·
                  refine ⟨37458100636400145600512021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24972067090933430400341347 37458100636400145600512021)
                  ·
                    refine ⟨1755848467331256825024001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 37458100636400145600512021 1755848467331256825024001)
                    ·
                      refine ⟨1316886350498442618768001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1755848467331256825024001 1316886350498442618768001)
                      ·
                        rfl

theorem cell23_2564627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 6, 2].length) (baseStart_2564627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564627 prefixEnd_2564627 := by exact prefixLift 2564627
  have htrace : WordTrace (prefixWord ++ tailWord_2564627) baseStart_2564627 baseEnd_2564627 := by
    simpa [prefixWord, tailWord_2564627, baseEnd_2564627] using wordTrace_append hprefix tailTrace_2564627
  have hstable : (prefixWord ++ tailWord_2564627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564627).length < 2 ^ (prefixWord ++ tailWord_2564627).sum := by decide
  have hdescent : baseEnd_2564627 < baseStart_2564627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564680 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 2, 9]
def baseStart_2564680 : Nat := 118140960795 + 2564680 * 2 ^ 59
def prefixEnd_2564680 : Nat := 4983230072969 + 3 ^ 40 * 2564680 * 2
def baseEnd_2564680 : Nat := 438971188324376970468419

theorem tailTrace_2564680 : CollatzResearch.WordTrace tailWord_2564680 prefixEnd_2564680 438971188324376970468419 := by
  unfold tailWord_2564680
  simp only [CollatzResearch.WordTrace]
  refine ⟨46770782174304923658577747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62361042899073231544770329 46770782174304923658577747)
  ·
    refine ⟨70156173261457385487866621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46770782174304923658577747 70156173261457385487866621)
    ·
      refine ⟨26308564973046519557949983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70156173261457385487866621 26308564973046519557949983)
      ·
        refine ⟨39462847459569779336924975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26308564973046519557949983 39462847459569779336924975)
        ·
          refine ⟨59194271189354669005387463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39462847459569779336924975 59194271189354669005387463)
          ·
            refine ⟨88791406784032003508081195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59194271189354669005387463 88791406784032003508081195)
            ·
              refine ⟨133187110176048005262121793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88791406784032003508081195 133187110176048005262121793)
              ·
                refine ⟨99890332632036003946591345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133187110176048005262121793 99890332632036003946591345)
                ·
                  refine ⟨74917749474027002959943509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99890332632036003946591345 74917749474027002959943509)
                  ·
                    refine ⟨438971188324376970468419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 74917749474027002959943509 438971188324376970468419)
                    ·
                      rfl

theorem cell23_2564680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_2564680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564680 prefixEnd_2564680 := by exact prefixLift 2564680
  have htrace : WordTrace (prefixWord ++ tailWord_2564680) baseStart_2564680 baseEnd_2564680 := by
    simpa [prefixWord, tailWord_2564680, baseEnd_2564680] using wordTrace_append hprefix tailTrace_2564680
  have hstable : (prefixWord ++ tailWord_2564680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564680).length < 2 ^ (prefixWord ++ tailWord_2564680).sum := by decide
  have hdescent : baseEnd_2564680 < baseStart_2564680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564704 : List Nat := [2, 1, 1, 3, 2, 1, 3, 1, 4, 3, 2]
def baseStart_2564704 : Nat := 118140960795 + 2564704 * 2 ^ 59
def prefixEnd_2564704 : Nat := 4983230072969 + 3 ^ 40 * 2564704 * 2
def baseEnd_2564704 : Nat := 1316925888508838817505147

theorem tailTrace_2564704 : CollatzResearch.WordTrace tailWord_2564704 prefixEnd_2564704 1316925888508838817505147 := by
  unfold tailWord_2564704
  simp only [CollatzResearch.WordTrace]
  refine ⟨46771219850261449708014583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62361626467015266277352777 46771219850261449708014583)
  ·
    refine ⟨70156829775392174562021875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46771219850261449708014583 70156829775392174562021875)
    ·
      refine ⟨105235244663088261843032813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70156829775392174562021875 105235244663088261843032813)
      ·
        refine ⟨39463216748658098191137305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105235244663088261843032813 39463216748658098191137305)
        ·
          refine ⟨29597412561493573643352979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39463216748658098191137305 29597412561493573643352979)
          ·
            refine ⟨44396118842240360465029469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29597412561493573643352979 44396118842240360465029469)
            ·
              refine ⟨16648544565840135174386051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44396118842240360465029469 16648544565840135174386051)
              ·
                refine ⟨24972816848760202761579077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16648544565840135174386051 24972816848760202761579077)
                ·
                  refine ⟨4682403159142538017796077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24972816848760202761579077 4682403159142538017796077)
                  ·
                    refine ⟨1755901184678451756673529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4682403159142538017796077 1755901184678451756673529)
                    ·
                      refine ⟨1316925888508838817505147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1755901184678451756673529 1316925888508838817505147)
                      ·
                        rfl

theorem cell23_2564704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 4, 3, 2].length) (baseStart_2564704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564704 prefixEnd_2564704 := by exact prefixLift 2564704
  have htrace : WordTrace (prefixWord ++ tailWord_2564704) baseStart_2564704 baseEnd_2564704 := by
    simpa [prefixWord, tailWord_2564704, baseEnd_2564704] using wordTrace_append hprefix tailTrace_2564704
  have hstable : (prefixWord ++ tailWord_2564704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564704).length < 2 ^ (prefixWord ++ tailWord_2564704).sum := by decide
  have hdescent : baseEnd_2564704 < baseStart_2564704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564778 : List Nat := [3, 1, 5, 2, 1, 1, 2, 1, 1, 6]
def baseStart_2564778 : Nat := 118140960795 + 2564778 * 2 ^ 59
def prefixEnd_2564778 : Nat := 4983230072969 + 3 ^ 40 * 2564778 * 2
def baseEnd_2564778 : Nat := 438987962025757175993269

theorem tailTrace_2564778 : CollatzResearch.WordTrace tailWord_2564778 prefixEnd_2564778 438987962025757175993269 := by
  unfold tailWord_2564778
  simp only [CollatzResearch.WordTrace]
  refine ⟨23386284675563702513555747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62363425801503206702815325 23386284675563702513555747)
  ·
    refine ⟨35079427013345553770333621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23386284675563702513555747 35079427013345553770333621)
    ·
      refine ⟨3288696282501145665968777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35079427013345553770333621 3288696282501145665968777)
      ·
        refine ⟨2466522211875859249476583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3288696282501145665968777 2466522211875859249476583)
        ·
          refine ⟨3699783317813788874214875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2466522211875859249476583 3699783317813788874214875)
          ·
            refine ⟨5549674976720683311322313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3699783317813788874214875 5549674976720683311322313)
            ·
              refine ⟨4162256232540512483491735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5549674976720683311322313 4162256232540512483491735)
              ·
                refine ⟨6243384348810768725237603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4162256232540512483491735 6243384348810768725237603)
                ·
                  refine ⟨9365076523216153087856405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6243384348810768725237603 9365076523216153087856405)
                  ·
                    refine ⟨438987962025757175993269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9365076523216153087856405 438987962025757175993269)
                    ·
                      rfl

theorem cell23_2564778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_2564778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564778 prefixEnd_2564778 := by exact prefixLift 2564778
  have htrace : WordTrace (prefixWord ++ tailWord_2564778) baseStart_2564778 baseEnd_2564778 := by
    simpa [prefixWord, tailWord_2564778, baseEnd_2564778] using wordTrace_append hprefix tailTrace_2564778
  have hstable : (prefixWord ++ tailWord_2564778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564778).length < 2 ^ (prefixWord ++ tailWord_2564778).sum := by decide
  have hdescent : baseEnd_2564778 < baseStart_2564778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564781 : List Nat := [1, 5, 2, 1, 1, 3, 2, 1, 1, 2, 4]
def baseStart_2564781 : Nat := 118140960795 + 2564781 * 2 ^ 59
def prefixEnd_2564781 : Nat := 4983230072969 + 3 ^ 40 * 2564781 * 2
def baseEnd_2564781 : Nat := 1316965426519235016242293

theorem tailTrace_2564781 : CollatzResearch.WordTrace tailWord_2564781 prefixEnd_2564781 1316965426519235016242293 := by
  unfold tailWord_2564781
  simp only [CollatzResearch.WordTrace]
  refine ⟨93545248121243941566582197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62363498747495961044388131 93545248121243941566582197)
  ·
    refine ⟨8769867011366619521867081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93545248121243941566582197 8769867011366619521867081)
    ·
      refine ⟨6577400258524964641400311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8769867011366619521867081 6577400258524964641400311)
      ·
        refine ⟨9866100387787446962100467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6577400258524964641400311 9866100387787446962100467)
        ·
          refine ⟨14799150581681170443150701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9866100387787446962100467 14799150581681170443150701)
          ·
            refine ⟨5549681468130438916181513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14799150581681170443150701 5549681468130438916181513)
            ·
              refine ⟨4162261101097829187136135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5549681468130438916181513 4162261101097829187136135)
              ·
                refine ⟨6243391651646743780704203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4162261101097829187136135 6243391651646743780704203)
                ·
                  refine ⟨9365087477470115671056305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6243391651646743780704203 9365087477470115671056305)
                  ·
                    refine ⟨7023815608102586753292229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9365087477470115671056305 7023815608102586753292229)
                    ·
                      refine ⟨1316965426519235016242293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7023815608102586753292229 1316965426519235016242293)
                      ·
                        rfl

theorem cell23_2564781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_2564781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564781 prefixEnd_2564781 := by exact prefixLift 2564781
  have htrace : WordTrace (prefixWord ++ tailWord_2564781) baseStart_2564781 baseEnd_2564781 := by
    simpa [prefixWord, tailWord_2564781, baseEnd_2564781] using wordTrace_append hprefix tailTrace_2564781
  have hstable : (prefixWord ++ tailWord_2564781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564781).length < 2 ^ (prefixWord ++ tailWord_2564781).sum := by decide
  have hdescent : baseEnd_2564781 < baseStart_2564781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564784 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 6, 1, 3]
def baseStart_2564784 : Nat := 118140960795 + 2564784 * 2 ^ 59
def prefixEnd_2564784 : Nat := 4983230072969 + 3 ^ 40 * 2564784 * 2
def baseEnd_2564784 : Nat := 1316966966961198504504779

theorem tailTrace_2564784 : CollatzResearch.WordTrace tailWord_2564784 prefixEnd_2564784 1316966966961198504504779 := by
  unfold tailWord_2564784
  simp only [CollatzResearch.WordTrace]
  refine ⟨46772678770116536539470703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62363571693488715385960937 46772678770116536539470703)
  ·
    refine ⟨70159018155174804809206055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46772678770116536539470703 70159018155174804809206055)
    ·
      refine ⟨105238527232762207213809083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70159018155174804809206055 105238527232762207213809083)
      ·
        refine ⟨157857790849143310820713625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105238527232762207213809083 157857790849143310820713625)
        ·
          refine ⟨118393343136857483115535219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157857790849143310820713625 118393343136857483115535219)
          ·
            refine ⟨177590014705286224673302829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118393343136857483115535219 177590014705286224673302829)
            ·
              refine ⟨66596255514482334252488561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 177590014705286224673302829 66596255514482334252488561)
              ·
                refine ⟨49947191635861750689366421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66596255514482334252488561 49947191635861750689366421)
                ·
                  refine ⟨2341274607931019563564051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 49947191635861750689366421 2341274607931019563564051)
                  ·
                    refine ⟨3511911911896529345346077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2341274607931019563564051 3511911911896529345346077)
                    ·
                      refine ⟨1316966966961198504504779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3511911911896529345346077 1316966966961198504504779)
                      ·
                        rfl

theorem cell23_2564784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 6, 1, 3].length) (baseStart_2564784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564784 prefixEnd_2564784 := by exact prefixLift 2564784
  have htrace : WordTrace (prefixWord ++ tailWord_2564784) baseStart_2564784 baseEnd_2564784 := by
    simpa [prefixWord, tailWord_2564784, baseEnd_2564784] using wordTrace_append hprefix tailTrace_2564784
  have hstable : (prefixWord ++ tailWord_2564784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564784).length < 2 ^ (prefixWord ++ tailWord_2564784).sum := by decide
  have hdescent : baseEnd_2564784 < baseStart_2564784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564785 : List Nat := [1, 2, 2, 6, 1, 1, 1, 2, 3, 2, 2]
def baseStart_2564785 : Nat := 118140960795 + 2564785 * 2 ^ 59
def prefixEnd_2564785 : Nat := 4983230072969 + 3 ^ 40 * 2564785 * 2
def baseEnd_2564785 : Nat := 1316967480441853000592275

theorem tailTrace_2564785 : CollatzResearch.WordTrace tailWord_2564785 prefixEnd_2564785 1316967480441853000592275 := by
  unfold tailWord_2564785
  simp only [CollatzResearch.WordTrace]
  refine ⟨93545394013229450249727809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62363596008819633499818539 93545394013229450249727809)
  ·
    refine ⟨70159045509922087687295857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93545394013229450249727809 70159045509922087687295857)
    ·
      refine ⟨52619284132441565765471893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70159045509922087687295857 52619284132441565765471893)
      ·
        refine ⟨2466528943708198395256495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 52619284132441565765471893 2466528943708198395256495)
        ·
          refine ⟨3699793415562297592884743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2466528943708198395256495 3699793415562297592884743)
          ·
            refine ⟨5549690123343446389327115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3699793415562297592884743 5549690123343446389327115)
            ·
              refine ⟨8324535185015169583990673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5549690123343446389327115 8324535185015169583990673)
              ·
                refine ⟨6243401388761377187993005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8324535185015169583990673 6243401388761377187993005)
                ·
                  refine ⟨2341275520785516445497377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6243401388761377187993005 2341275520785516445497377)
                  ·
                    refine ⟨1755956640589137334123033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2341275520785516445497377 1755956640589137334123033)
                    ·
                      refine ⟨1316967480441853000592275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1755956640589137334123033 1316967480441853000592275)
                      ·
                        rfl

theorem cell23_2564785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_2564785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564785 prefixEnd_2564785 := by exact prefixLift 2564785
  have htrace : WordTrace (prefixWord ++ tailWord_2564785) baseStart_2564785 baseEnd_2564785 := by
    simpa [prefixWord, tailWord_2564785, baseEnd_2564785] using wordTrace_append hprefix tailTrace_2564785
  have hstable : (prefixWord ++ tailWord_2564785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564785).length < 2 ^ (prefixWord ++ tailWord_2564785).sum := by decide
  have hdescent : baseEnd_2564785 < baseStart_2564785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564807 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 4]
def baseStart_2564807 : Nat := 118140960795 + 2564807 * 2 ^ 59
def prefixEnd_2564807 : Nat := 4983230072969 + 3 ^ 40 * 2564807 * 2
def baseEnd_2564807 : Nat := 1316978777016251914517173

theorem tailTrace_2564807 : CollatzResearch.WordTrace tailWord_2564807 prefixEnd_2564807 1316978777016251914517173 := by
  unfold tailWord_2564807
  simp only [CollatzResearch.WordTrace]
  refine ⟨93546196419149748007028675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62364130946099832004685783 93546196419149748007028675)
  ·
    refine ⟨140319294628724622010543013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93546196419149748007028675 140319294628724622010543013)
    ·
      refine ⟨26309867742885866626976815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140319294628724622010543013 26309867742885866626976815)
      ·
        refine ⟨39464801614328799940465223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26309867742885866626976815 39464801614328799940465223)
        ·
          refine ⟨59197202421493199910697835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39464801614328799940465223 59197202421493199910697835)
          ·
            refine ⟨88795803632239799866046753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59197202421493199910697835 88795803632239799866046753)
            ·
              refine ⟨66596852724179849899535065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88795803632239799866046753 66596852724179849899535065)
              ·
                refine ⟨49947639543134887424651299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66596852724179849899535065 49947639543134887424651299)
                ·
                  refine ⟨74921459314702331136976949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49947639543134887424651299 74921459314702331136976949)
                  ·
                    refine ⟨7023886810753343544091589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 74921459314702331136976949 7023886810753343544091589)
                    ·
                      refine ⟨1316978777016251914517173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7023886810753343544091589 1316978777016251914517173)
                      ·
                        rfl

theorem cell23_2564807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_2564807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564807 prefixEnd_2564807 := by exact prefixLift 2564807
  have htrace : WordTrace (prefixWord ++ tailWord_2564807) baseStart_2564807 baseEnd_2564807 := by
    simpa [prefixWord, tailWord_2564807, baseEnd_2564807] using wordTrace_append hprefix tailTrace_2564807
  have hstable : (prefixWord ++ tailWord_2564807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564807).length < 2 ^ (prefixWord ++ tailWord_2564807).sum := by decide
  have hdescent : baseEnd_2564807 < baseStart_2564807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564817 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 4, 6]
def baseStart_2564817 : Nat := 118140960795 + 2564817 * 2 ^ 59
def prefixEnd_2564817 : Nat := 4983230072969 + 3 ^ 40 * 2564817 * 2
def baseEnd_2564817 : Nat := 438994637274265625130709

theorem tailTrace_2564817 : CollatzResearch.WordTrace tailWord_2564817 prefixEnd_2564817 438994637274265625130709 := by
  unfold tailWord_2564817
  simp only [CollatzResearch.WordTrace]
  refine ⟨93546561149113519714892705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62364374099409013143261803 93546561149113519714892705)
  ·
    refine ⟨70159920861835139786169529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93546561149113519714892705 70159920861835139786169529)
    ·
      refine ⟨52619940646376354839627147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70159920861835139786169529 52619940646376354839627147)
      ·
        refine ⟨78929910969564532259440721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52619940646376354839627147 78929910969564532259440721)
        ·
          refine ⟨59197433227173399194580541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78929910969564532259440721 59197433227173399194580541)
          ·
            refine ⟨22199037460190024697967703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59197433227173399194580541 22199037460190024697967703)
            ·
              refine ⟨33298556190285037046951555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22199037460190024697967703 33298556190285037046951555)
              ·
                refine ⟨49947834285427555570427333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33298556190285037046951555 49947834285427555570427333)
                ·
                  refine ⟨9365218928517666669455125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49947834285427555570427333 9365218928517666669455125)
                  ·
                    refine ⟨438994637274265625130709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9365218928517666669455125 438994637274265625130709)
                    ·
                      rfl

theorem cell23_2564817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 6].length) (baseStart_2564817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564817 prefixEnd_2564817 := by exact prefixLift 2564817
  have htrace : WordTrace (prefixWord ++ tailWord_2564817) baseStart_2564817 baseEnd_2564817 := by
    simpa [prefixWord, tailWord_2564817, baseEnd_2564817] using wordTrace_append hprefix tailTrace_2564817
  have hstable : (prefixWord ++ tailWord_2564817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564817).length < 2 ^ (prefixWord ++ tailWord_2564817).sum := by decide
  have hdescent : baseEnd_2564817 < baseStart_2564817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564818 : List Nat := [3, 2, 2, 2, 3, 1, 1, 1, 4, 1, 3]
def baseStart_2564818 : Nat := 118140960795 + 2564818 * 2 ^ 59
def prefixEnd_2564818 : Nat := 4983230072969 + 3 ^ 40 * 2564818 * 2
def baseEnd_2564818 : Nat := 1316984425303451371479623

theorem tailTrace_2564818 : CollatzResearch.WordTrace tailWord_2564818 prefixEnd_2564818 1316984425303451371479623 := by
  unfold tailWord_2564818
  simp only [CollatzResearch.WordTrace]
  refine ⟨23386649405527474221419777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62364398414739931257119405 23386649405527474221419777)
  ·
    refine ⟨17539987054145605666064833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23386649405527474221419777 17539987054145605666064833)
    ·
      refine ⟨13154990290609204249548625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17539987054145605666064833 13154990290609204249548625)
      ·
        refine ⟨9866242717956903187161469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13154990290609204249548625 9866242717956903187161469)
        ·
          refine ⟨3699841019233838695185551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9866242717956903187161469 3699841019233838695185551)
          ·
            refine ⟨5549761528850758042778327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3699841019233838695185551 5549761528850758042778327)
            ·
              refine ⟨8324642293276137064167491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5549761528850758042778327 8324642293276137064167491)
              ·
                refine ⟨12486963439914205596251237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8324642293276137064167491 12486963439914205596251237)
                ·
                  refine ⟨2341305644983913549297107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12486963439914205596251237 2341305644983913549297107)
                  ·
                    refine ⟨3511958467475870323945661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2341305644983913549297107 3511958467475870323945661)
                    ·
                      refine ⟨1316984425303451371479623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3511958467475870323945661 1316984425303451371479623)
                      ·
                        rfl

theorem cell23_2564818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_2564818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564818 prefixEnd_2564818 := by exact prefixLift 2564818
  have htrace : WordTrace (prefixWord ++ tailWord_2564818) baseStart_2564818 baseEnd_2564818 := by
    simpa [prefixWord, tailWord_2564818, baseEnd_2564818] using wordTrace_append hprefix tailTrace_2564818
  have hstable : (prefixWord ++ tailWord_2564818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564818).length < 2 ^ (prefixWord ++ tailWord_2564818).sum := by decide
  have hdescent : baseEnd_2564818 < baseStart_2564818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564835 : List Nat := [1, 1, 1, 7, 1, 2, 3, 1, 2, 1, 3]
def baseStart_2564835 : Nat := 118140960795 + 2564835 * 2 ^ 59
def prefixEnd_2564835 : Nat := 4983230072969 + 3 ^ 40 * 2564835 * 2
def baseEnd_2564835 : Nat := 1316993154474577804967045

theorem tailTrace_2564835 : CollatzResearch.WordTrace tailWord_2564835 prefixEnd_2564835 1316993154474577804967045 := by
  unfold tailWord_2564835
  simp only [CollatzResearch.WordTrace]
  refine ⟨93547217663048308789047959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62364811775365539192698639 93547217663048308789047959)
  ·
    refine ⟨140320826494572463183571939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93547217663048308789047959 140320826494572463183571939)
    ·
      refine ⟨210481239741858694775357909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140320826494572463183571939 210481239741858694775357909)
      ·
        refine ⟨4933154056449813158797451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 210481239741858694775357909 4933154056449813158797451)
        ·
          refine ⟨7399731084674719738196177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4933154056449813158797451 7399731084674719738196177)
          ·
            refine ⟨5549798313506039803647133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7399731084674719738196177 5549798313506039803647133)
            ·
              refine ⟨2081174367564764926367675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5549798313506039803647133 2081174367564764926367675)
              ·
                refine ⟨3121761551347147389551513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2081174367564764926367675 3121761551347147389551513)
                ·
                  refine ⟨2341321163510360542163635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3121761551347147389551513 2341321163510360542163635)
                  ·
                    refine ⟨3511981745265540813245453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2341321163510360542163635 3511981745265540813245453)
                    ·
                      refine ⟨1316993154474577804967045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3511981745265540813245453 1316993154474577804967045)
                      ·
                        rfl

theorem cell23_2564835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_2564835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564835 prefixEnd_2564835 := by exact prefixLift 2564835
  have htrace : WordTrace (prefixWord ++ tailWord_2564835) baseStart_2564835 baseEnd_2564835 := by
    simpa [prefixWord, tailWord_2564835, baseEnd_2564835] using wordTrace_append hprefix tailTrace_2564835
  have hstable : (prefixWord ++ tailWord_2564835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564835).length < 2 ^ (prefixWord ++ tailWord_2564835).sum := by decide
  have hdescent : baseEnd_2564835 < baseStart_2564835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564841 : List Nat := [1, 2, 1, 1, 1, 2, 7, 1, 1, 4, 2]
def baseStart_2564841 : Nat := 118140960795 + 2564841 * 2 ^ 59
def prefixEnd_2564841 : Nat := 4983230072969 + 3 ^ 40 * 2564841 * 2
def baseEnd_2564841 : Nat := 1316996235358504781492017

theorem tailTrace_2564841 : CollatzResearch.WordTrace tailWord_2564841 prefixEnd_2564841 1316996235358504781492017 := by
  unfold tailWord_2564841
  simp only [CollatzResearch.WordTrace]
  refine ⟨93547436501026571813766377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62364957667351047875844251 93547436501026571813766377)
  ·
    refine ⟨70160577375769928860324783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93547436501026571813766377 70160577375769928860324783)
    ·
      refine ⟨105240866063654893290487175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70160577375769928860324783 105240866063654893290487175)
      ·
        refine ⟨157861299095482339935730763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105240866063654893290487175 157861299095482339935730763)
        ·
          refine ⟨236791948643223509903596145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157861299095482339935730763 236791948643223509903596145)
          ·
            refine ⟨177593961482417632427697109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236791948643223509903596145 177593961482417632427697109)
            ·
              refine ⟨4162358472244163260024151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 177593961482417632427697109 4162358472244163260024151)
              ·
                refine ⟨6243537708366244890036227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4162358472244163260024151 6243537708366244890036227)
                ·
                  refine ⟨9365306562549367335054341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6243537708366244890036227 9365306562549367335054341)
                  ·
                    refine ⟨1755994980478006375322689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9365306562549367335054341 1755994980478006375322689)
                    ·
                      refine ⟨1316996235358504781492017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1755994980478006375322689 1316996235358504781492017)
                      ·
                        rfl

theorem cell23_2564841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 4, 2].length) (baseStart_2564841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564841 prefixEnd_2564841 := by exact prefixLift 2564841
  have htrace : WordTrace (prefixWord ++ tailWord_2564841) baseStart_2564841 baseEnd_2564841 := by
    simpa [prefixWord, tailWord_2564841, baseEnd_2564841] using wordTrace_append hprefix tailTrace_2564841
  have hstable : (prefixWord ++ tailWord_2564841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564841).length < 2 ^ (prefixWord ++ tailWord_2564841).sum := by decide
  have hdescent : baseEnd_2564841 < baseStart_2564841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564853 : List Nat := [1, 3, 6, 1, 2, 1, 1, 3, 1, 2, 2]
def baseStart_2564853 : Nat := 118140960795 + 2564853 * 2 ^ 59
def prefixEnd_2564853 : Nat := 4983230072969 + 3 ^ 40 * 2564853 * 2
def baseEnd_2564853 : Nat := 1317002397126358734541963

theorem tailTrace_2564853 : CollatzResearch.WordTrace tailWord_2564853 prefixEnd_2564853 1317002397126358734541963 := by
  unfold tailWord_2564853
  simp only [CollatzResearch.WordTrace]
  refine ⟨93547874176983097863203213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62365249451322065242135475 93547874176983097863203213)
  ·
    refine ⟨35080452816368661698701205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93547874176983097863203213 35080452816368661698701205)
    ·
      refine ⟨1644396225767281017126619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 35080452816368661698701205 1644396225767281017126619)
      ·
        refine ⟨2466594338650921525689929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1644396225767281017126619 2466594338650921525689929)
        ·
          refine ⟨1849945753988191144267447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2466594338650921525689929 1849945753988191144267447)
          ·
            refine ⟨2774918630982286716401171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1849945753988191144267447 2774918630982286716401171)
            ·
              refine ⟨4162377946473430074601757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2774918630982286716401171 4162377946473430074601757)
              ·
                refine ⟨1560891729927536277975659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4162377946473430074601757 1560891729927536277975659)
                ·
                  refine ⟨2341337594891304416963489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1560891729927536277975659 2341337594891304416963489)
                  ·
                    refine ⟨1756003196168478312722617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2341337594891304416963489 1756003196168478312722617)
                    ·
                      refine ⟨1317002397126358734541963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1756003196168478312722617 1317002397126358734541963)
                      ·
                        rfl

theorem cell23_2564853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_2564853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564853 prefixEnd_2564853 := by exact prefixLift 2564853
  have htrace : WordTrace (prefixWord ++ tailWord_2564853) baseStart_2564853 baseEnd_2564853 := by
    simpa [prefixWord, tailWord_2564853, baseEnd_2564853] using wordTrace_append hprefix tailTrace_2564853
  have hstable : (prefixWord ++ tailWord_2564853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564853).length < 2 ^ (prefixWord ++ tailWord_2564853).sum := by decide
  have hdescent : baseEnd_2564853 < baseStart_2564853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564892 : List Nat := [2, 2, 3, 1, 1, 5, 2, 1, 2, 2, 2]
def baseStart_2564892 : Nat := 118140960795 + 2564892 * 2 ^ 59
def prefixEnd_2564892 : Nat := 4983230072969 + 3 ^ 40 * 2564892 * 2
def baseEnd_2564892 : Nat := 1317022422871884081954283

theorem tailTrace_2564892 : CollatzResearch.WordTrace tailWord_2564892 prefixEnd_2564892 1317022422871884081954283 := by
  unfold tailWord_2564892
  simp only [CollatzResearch.WordTrace]
  refine ⟨46774648311920903761936465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62366197749227871682581953 46774648311920903761936465)
  ·
    refine ⟨35080986233940677821452349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46774648311920903761936465 35080986233940677821452349)
    ·
      refine ⟨13155369837727754183044631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35080986233940677821452349 13155369837727754183044631)
      ·
        refine ⟨19733054756591631274566947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13155369837727754183044631 19733054756591631274566947)
        ·
          refine ⟨29599582134887446911850421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19733054756591631274566947 29599582134887446911850421)
          ·
            refine ⟨2774960825145698147985977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29599582134887446911850421 2774960825145698147985977)
            ·
              refine ⟨2081220618859273610989483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2774960825145698147985977 2081220618859273610989483)
              ·
                refine ⟨3121830928288910416484225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2081220618859273610989483 3121830928288910416484225)
                ·
                  refine ⟨2341373196216682812363169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3121830928288910416484225 2341373196216682812363169)
                  ·
                    refine ⟨1756029897162512109272377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2341373196216682812363169 1756029897162512109272377)
                    ·
                      refine ⟨1317022422871884081954283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1756029897162512109272377 1317022422871884081954283)
                      ·
                        rfl

theorem cell23_2564892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_2564892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564892 prefixEnd_2564892 := by exact prefixLift 2564892
  have htrace : WordTrace (prefixWord ++ tailWord_2564892) baseStart_2564892 baseEnd_2564892 := by
    simpa [prefixWord, tailWord_2564892, baseEnd_2564892] using wordTrace_append hprefix tailTrace_2564892
  have hstable : (prefixWord ++ tailWord_2564892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564892).length < 2 ^ (prefixWord ++ tailWord_2564892).sum := by decide
  have hdescent : baseEnd_2564892 < baseStart_2564892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564904 : List Nat := [2, 1, 5, 1, 1, 1, 1, 2, 1, 1, 7]
def baseStart_2564904 : Nat := 118140960795 + 2564904 * 2 ^ 59
def prefixEnd_2564904 : Nat := 4983230072969 + 3 ^ 40 * 2564904 * 2
def baseEnd_2564904 : Nat := 1317028584639738035004227

theorem tailTrace_2564904 : CollatzResearch.WordTrace tailWord_2564904 prefixEnd_2564904 1317028584639738035004227 := by
  unfold tailWord_2564904
  simp only [CollatzResearch.WordTrace]
  refine ⟨46774867149899166786654883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62366489533198889048873177 46774867149899166786654883)
  ·
    refine ⟨70162300724848750179982325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46774867149899166786654883 70162300724848750179982325)
    ·
      refine ⟨6577715692954570329373343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70162300724848750179982325 6577715692954570329373343)
      ·
        refine ⟨9866573539431855494060015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6577715692954570329373343 9866573539431855494060015)
        ·
          refine ⟨14799860309147783241090023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9866573539431855494060015 14799860309147783241090023)
          ·
            refine ⟨22199790463721674861635035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14799860309147783241090023 22199790463721674861635035)
            ·
              refine ⟨33299685695582512292452553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22199790463721674861635035 33299685695582512292452553)
              ·
                refine ⟨24974764271686884219339415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33299685695582512292452553 24974764271686884219339415)
                ·
                  refine ⟨37462146407530326329009123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24974764271686884219339415 37462146407530326329009123)
                  ·
                    refine ⟨56193219611295489493513685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37462146407530326329009123 56193219611295489493513685)
                    ·
                      refine ⟨1317028584639738035004227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 56193219611295489493513685 1317028584639738035004227)
                      ·
                        rfl

theorem cell23_2564904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_2564904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564904 prefixEnd_2564904 := by exact prefixLift 2564904
  have htrace : WordTrace (prefixWord ++ tailWord_2564904) baseStart_2564904 baseEnd_2564904 := by
    simpa [prefixWord, tailWord_2564904, baseEnd_2564904] using wordTrace_append hprefix tailTrace_2564904
  have hstable : (prefixWord ++ tailWord_2564904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564904).length < 2 ^ (prefixWord ++ tailWord_2564904).sum := by decide
  have hdescent : baseEnd_2564904 < baseStart_2564904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564907 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 1, 10]
def baseStart_2564907 : Nat := 118140960795 + 2564907 * 2 ^ 59
def prefixEnd_2564907 : Nat := 4983230072969 + 3 ^ 40 * 2564907 * 2
def baseEnd_2564907 : Nat := 439010041693900507755571

theorem tailTrace_2564907 : CollatzResearch.WordTrace tailWord_2564907 prefixEnd_2564907 439010041693900507755571 := by
  unfold tailWord_2564907
  simp only [CollatzResearch.WordTrace]
  refine ⟨93549843718787465085668975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62366562479191643390445983 93549843718787465085668975)
  ·
    refine ⟨140324765578181197628503463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93549843718787465085668975 140324765578181197628503463)
    ·
      refine ⟨210487148367271796442755195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140324765578181197628503463 210487148367271796442755195)
      ·
        refine ⟨315730722550907694664132793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210487148367271796442755195 315730722550907694664132793)
        ·
          refine ⟨236798041913180770998099595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315730722550907694664132793 236798041913180770998099595)
          ·
            refine ⟨355197062869771156497149393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236798041913180770998099595 355197062869771156497149393)
            ·
              refine ⟨266397797152328367372862045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 355197062869771156497149393 266397797152328367372862045)
              ·
                refine ⟨99899173932123137764823267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 266397797152328367372862045 99899173932123137764823267)
                ·
                  refine ⟨149848760898184706647234901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99899173932123137764823267 149848760898184706647234901)
                  ·
                    refine ⟨439010041693900507755571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 149848760898184706647234901 439010041693900507755571)
                    ·
                      rfl

theorem cell23_2564907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 10].length) (baseStart_2564907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564907 prefixEnd_2564907 := by exact prefixLift 2564907
  have htrace : WordTrace (prefixWord ++ tailWord_2564907) baseStart_2564907 baseEnd_2564907 := by
    simpa [prefixWord, tailWord_2564907, baseEnd_2564907] using wordTrace_append hprefix tailTrace_2564907
  have hstable : (prefixWord ++ tailWord_2564907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564907).length < 2 ^ (prefixWord ++ tailWord_2564907).sum := by decide
  have hdescent : baseEnd_2564907 < baseStart_2564907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564931 : List Nat := [1, 1, 1, 3, 1, 4, 2, 2, 2, 4, 2]
def baseStart_2564931 : Nat := 118140960795 + 2564931 * 2 ^ 59
def prefixEnd_2564931 : Nat := 4983230072969 + 3 ^ 40 * 2564931 * 2
def baseEnd_2564931 : Nat := 1317042448617409429366603

theorem tailTrace_2564931 : CollatzResearch.WordTrace tailWord_2564931 prefixEnd_2564931 1317042448617409429366603 := by
  unfold tailWord_2564931
  simp only [CollatzResearch.WordTrace]
  refine ⟨93550719070700517184542647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62367146047133678123028431 93550719070700517184542647)
  ·
    refine ⟨140326078606050775776813971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93550719070700517184542647 140326078606050775776813971)
    ·
      refine ⟨210489117909076163665220957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140326078606050775776813971 210489117909076163665220957)
      ·
        refine ⟨78933419215903561374457859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210489117909076163665220957 78933419215903561374457859)
        ·
          refine ⟨118400128823855342061686789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78933419215903561374457859 118400128823855342061686789)
          ·
            refine ⟨22200024154472876636566273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118400128823855342061686789 22200024154472876636566273)
            ·
              refine ⟨16650018115854657477424705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22200024154472876636566273 16650018115854657477424705)
              ·
                refine ⟨12487513586890993108068529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16650018115854657477424705 12487513586890993108068529)
                ·
                  refine ⟨9365635190168244831051397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12487513586890993108068529 9365635190168244831051397)
                  ·
                    refine ⟨1756056598156545905822137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9365635190168244831051397 1756056598156545905822137)
                    ·
                      refine ⟨1317042448617409429366603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1756056598156545905822137 1317042448617409429366603)
                      ·
                        rfl

theorem cell23_2564931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 4, 2].length) (baseStart_2564931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564931 prefixEnd_2564931 := by exact prefixLift 2564931
  have htrace : WordTrace (prefixWord ++ tailWord_2564931) baseStart_2564931 baseEnd_2564931 := by
    simpa [prefixWord, tailWord_2564931, baseEnd_2564931] using wordTrace_append hprefix tailTrace_2564931
  have hstable : (prefixWord ++ tailWord_2564931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564931).length < 2 ^ (prefixWord ++ tailWord_2564931).sum := by decide
  have hdescent : baseEnd_2564931 < baseStart_2564931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564968 : List Nat := [2, 1, 4, 2, 1, 2, 3, 1, 2, 2, 3]
def baseStart_2564968 : Nat := 118140960795 + 2564968 * 2 ^ 59
def prefixEnd_2564968 : Nat := 4983230072969 + 3 ^ 40 * 2564968 * 2
def baseEnd_2564968 : Nat := 1317061447401625784603933

theorem tailTrace_2564968 : CollatzResearch.WordTrace tailWord_2564968 prefixEnd_2564968 1317061447401625784603933 := by
  unfold tailWord_2564968
  simp only [CollatzResearch.WordTrace]
  refine ⟨46776034285783236251819779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62368045714377648335759705 46776034285783236251819779)
  ·
    refine ⟨70164051428674854377729669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46776034285783236251819779 70164051428674854377729669)
    ·
      refine ⟨13155759642876535195824313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70164051428674854377729669 13155759642876535195824313)
      ·
        refine ⟨9866819732157401396868235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13155759642876535195824313 9866819732157401396868235)
        ·
          refine ⟨14800229598236102095302353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9866819732157401396868235 14800229598236102095302353)
          ·
            refine ⟨11100172198677076571476765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14800229598236102095302353 11100172198677076571476765)
            ·
              refine ⟨4162564574503903714303787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11100172198677076571476765 4162564574503903714303787)
              ·
                refine ⟨6243846861755855571455681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4162564574503903714303787 6243846861755855571455681)
                ·
                  refine ⟨4682885146316891678591761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6243846861755855571455681 4682885146316891678591761)
                  ·
                    refine ⟨3512163859737668758943821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4682885146316891678591761 3512163859737668758943821)
                    ·
                      refine ⟨1317061447401625784603933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3512163859737668758943821 1317061447401625784603933)
                      ·
                        rfl

theorem cell23_2564968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_2564968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564968 prefixEnd_2564968 := by exact prefixLift 2564968
  have htrace : WordTrace (prefixWord ++ tailWord_2564968) baseStart_2564968 baseEnd_2564968 := by
    simpa [prefixWord, tailWord_2564968, baseEnd_2564968] using wordTrace_append hprefix tailTrace_2564968
  have hstable : (prefixWord ++ tailWord_2564968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564968).length < 2 ^ (prefixWord ++ tailWord_2564968).sum := by decide
  have hdescent : baseEnd_2564968 < baseStart_2564968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564984 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 5, 5]
def baseStart_2564984 : Nat := 118140960795 + 2564984 * 2 ^ 59
def prefixEnd_2564984 : Nat := 4983230072969 + 3 ^ 40 * 2564984 * 2
def baseEnd_2564984 : Nat := 439023221030699240667953

theorem tailTrace_2564984 : CollatzResearch.WordTrace tailWord_2564984 prefixEnd_2564984 439023221030699240667953 := by
  unfold tailWord_2564984
  simp only [CollatzResearch.WordTrace]
  refine ⟨46776326069754253618111003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62368434759672338157481337 46776326069754253618111003)
  ·
    refine ⟨70164489104631380427166505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46776326069754253618111003 70164489104631380427166505)
    ·
      refine ⟨52623366828473535320374879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70164489104631380427166505 52623366828473535320374879)
      ·
        refine ⟨78935050242710302980562319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52623366828473535320374879 78935050242710302980562319)
        ·
          refine ⟨118402575364065454470843479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78935050242710302980562319 118402575364065454470843479)
          ·
            refine ⟨177603863046098181706265219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118402575364065454470843479 177603863046098181706265219)
            ·
              refine ⟨266405794569147272559397829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177603863046098181706265219 266405794569147272559397829)
              ·
                refine ⟨49951086481715113604887093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 266405794569147272559397829 49951086481715113604887093)
                ·
                  refine ⟨4682914357660791900458165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49951086481715113604887093 4682914357660791900458165)
                  ·
                    refine ⟨439023221030699240667953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4682914357660791900458165 439023221030699240667953)
                    ·
                      rfl

theorem cell23_2564984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 5, 5].length) (baseStart_2564984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2564984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2564984 prefixEnd_2564984 := by exact prefixLift 2564984
  have htrace : WordTrace (prefixWord ++ tailWord_2564984) baseStart_2564984 baseEnd_2564984 := by
    simpa [prefixWord, tailWord_2564984, baseEnd_2564984] using wordTrace_append hprefix tailTrace_2564984
  have hstable : (prefixWord ++ tailWord_2564984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564984).length < 2 ^ (prefixWord ++ tailWord_2564984).sum := by decide
  have hdescent : baseEnd_2564984 < baseStart_2564984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565078 : List Nat := [5, 2, 1, 1, 2, 1, 2, 9]
def baseStart_2565078 : Nat := 118140960795 + 2565078 * 2 ^ 59
def prefixEnd_2565078 : Nat := 4983230072969 + 3 ^ 40 * 2565078 * 2
def baseEnd_2565078 : Nat := 48782145565689642749201

theorem tailTrace_2565078 : CollatzResearch.WordTrace tailWord_2565078 prefixEnd_2565078 48782145565689642749201 := by
  unfold tailWord_2565078
  simp only [CollatzResearch.WordTrace]
  refine ⟨5847255037572997580633993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62370720400778640860095925 5847255037572997580633993)
  ·
    refine ⟨4385441278179748185475495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5847255037572997580633993 4385441278179748185475495)
    ·
      refine ⟨6578161917269622278213243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4385441278179748185475495 6578161917269622278213243)
      ·
        refine ⟨9867242875904433417319865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6578161917269622278213243 9867242875904433417319865)
        ·
          refine ⟨7400432156928325062989899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9867242875904433417319865 7400432156928325062989899)
          ·
            refine ⟨11100648235392487594484849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7400432156928325062989899 11100648235392487594484849)
            ·
              refine ⟨8325486176544365695863637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11100648235392487594484849 8325486176544365695863637)
              ·
                refine ⟨48782145565689642749201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8325486176544365695863637 48782145565689642749201)
                ·
                  rfl

theorem cell23_2565078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 9].length) (baseStart_2565078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565078 prefixEnd_2565078 := by exact prefixLift 2565078
  have htrace : WordTrace (prefixWord ++ tailWord_2565078) baseStart_2565078 baseEnd_2565078 := by
    simpa [prefixWord, tailWord_2565078, baseEnd_2565078] using wordTrace_append hprefix tailTrace_2565078
  have hstable : (prefixWord ++ tailWord_2565078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565078).length < 2 ^ (prefixWord ++ tailWord_2565078).sum := by decide
  have hdescent : baseEnd_2565078 < baseStart_2565078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565105 : List Nat := [1, 2, 2, 2, 4, 1, 1, 4, 2, 1, 3]
def baseStart_2565105 : Nat := 118140960795 + 2565105 * 2 ^ 59
def prefixEnd_2565105 : Nat := 4983230072969 + 3 ^ 40 * 2565105 * 2
def baseEnd_2565105 : Nat := 1317131794251291748590803

theorem tailTrace_2565105 : CollatzResearch.WordTrace tailWord_2565105 prefixEnd_2565105 1317131794251291748590803 := by
  unfold tailWord_2565105
  simp only [CollatzResearch.WordTrace]
  refine ⟨93557065372070144901376769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62371376914713429934251179 93557065372070144901376769)
  ·
    refine ⟨70167799029052608676032577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93557065372070144901376769 70167799029052608676032577)
    ·
      refine ⟨52625849271789456507024433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70167799029052608676032577 52625849271789456507024433)
      ·
        refine ⟨39469386953842092380268325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52625849271789456507024433 39469386953842092380268325)
        ·
          refine ⟨7400510053845392321300311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39469386953842092380268325 7400510053845392321300311)
          ·
            refine ⟨11100765080768088481950467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7400510053845392321300311 11100765080768088481950467)
            ·
              refine ⟨16651147621152132722925701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11100765080768088481950467 16651147621152132722925701)
              ·
                refine ⟨3122090178966024885548569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16651147621152132722925701 3122090178966024885548569)
                ·
                  refine ⟨2341567634224518664161427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3122090178966024885548569 2341567634224518664161427)
                  ·
                    refine ⟨3512351451336777996242141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2341567634224518664161427 3512351451336777996242141)
                    ·
                      refine ⟨1317131794251291748590803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3512351451336777996242141 1317131794251291748590803)
                      ·
                        rfl

theorem cell23_2565105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 2, 1, 3].length) (baseStart_2565105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565105 prefixEnd_2565105 := by exact prefixLift 2565105
  have htrace : WordTrace (prefixWord ++ tailWord_2565105) baseStart_2565105 baseEnd_2565105 := by
    simpa [prefixWord, tailWord_2565105, baseEnd_2565105] using wordTrace_append hprefix tailTrace_2565105
  have hstable : (prefixWord ++ tailWord_2565105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565105).length < 2 ^ (prefixWord ++ tailWord_2565105).sum := by decide
  have hdescent : baseEnd_2565105 < baseStart_2565105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565106 : List Nat := [3, 2, 1, 5, 1, 1, 1, 4, 1, 2, 2]
def baseStart_2565106 : Nat := 118140960795 + 2565106 * 2 ^ 59
def prefixEnd_2565106 : Nat := 4983230072969 + 3 ^ 40 * 2565106 * 2
def baseEnd_2565106 : Nat := 1317132307731946244678299

theorem tailTrace_2565106 : CollatzResearch.WordTrace tailWord_2565106 prefixEnd_2565106 1317132307731946244678299 := by
  unfold tailWord_2565106
  simp only [CollatzResearch.WordTrace]
  refine ⟨23389275461266630518040793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62371401230044348048108781 23389275461266630518040793)
  ·
    refine ⟨17541956595949972888530595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23389275461266630518040793 17541956595949972888530595)
    ·
      refine ⟨26312934893924959332795893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17541956595949972888530595 26312934893924959332795893)
      ·
        refine ⟨2466837646305464937449615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26312934893924959332795893 2466837646305464937449615)
        ·
          refine ⟨3700256469458197406174423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2466837646305464937449615 3700256469458197406174423)
          ·
            refine ⟨5550384704187296109261635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3700256469458197406174423 5550384704187296109261635)
            ·
              refine ⟨8325577056280944163892453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5550384704187296109261635 8325577056280944163892453)
              ·
                refine ⟨1561045698052677030729835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8325577056280944163892453 1561045698052677030729835)
                ·
                  refine ⟨2341568547079015546094753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1561045698052677030729835 2341568547079015546094753)
                  ·
                    refine ⟨1756176410309261659571065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2341568547079015546094753 1756176410309261659571065)
                    ·
                      refine ⟨1317132307731946244678299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1756176410309261659571065 1317132307731946244678299)
                      ·
                        rfl

theorem cell23_2565106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_2565106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565106 prefixEnd_2565106 := by exact prefixLift 2565106
  have htrace : WordTrace (prefixWord ++ tailWord_2565106) baseStart_2565106 baseEnd_2565106 := by
    simpa [prefixWord, tailWord_2565106, baseEnd_2565106] using wordTrace_append hprefix tailTrace_2565106
  have hstable : (prefixWord ++ tailWord_2565106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565106).length < 2 ^ (prefixWord ++ tailWord_2565106).sum := by decide
  have hdescent : baseEnd_2565106 < baseStart_2565106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565121 : List Nat := [1, 2, 4, 1, 2, 2, 1, 1, 1, 8]
def baseStart_2565121 : Nat := 118140960795 + 2565121 * 2 ^ 59
def prefixEnd_2565121 : Nat := 4983230072969 + 3 ^ 40 * 2565121 * 2
def baseEnd_2565121 : Nat := 439046669980587895330243

theorem tailTrace_2565121 : CollatzResearch.WordTrace tailWord_2565121 prefixEnd_2565121 439046669980587895330243 := by
  unfold tailWord_2565121
  simp only [CollatzResearch.WordTrace]
  refine ⟨93557648940012179633959217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62371765960008119755972811 93557648940012179633959217)
  ·
    refine ⟨70168236705009134725469413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93557648940012179633959217 70168236705009134725469413)
    ·
      refine ⟨13156544382189212761025515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70168236705009134725469413 13156544382189212761025515)
      ·
        refine ⟨19734816573283819141538273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13156544382189212761025515 19734816573283819141538273)
        ·
          refine ⟨14801112429962864356153705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19734816573283819141538273 14801112429962864356153705)
          ·
            refine ⟨11100834322472148267115279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14801112429962864356153705 11100834322472148267115279)
            ·
              refine ⟨16651251483708222400672919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11100834322472148267115279 16651251483708222400672919)
              ·
                refine ⟨24976877225562333601009379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16651251483708222400672919 24976877225562333601009379)
                ·
                  refine ⟨37465315838343500401514069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24976877225562333601009379 37465315838343500401514069)
                  ·
                    refine ⟨439046669980587895330243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 37465315838343500401514069 439046669980587895330243)
                    ·
                      rfl

theorem cell23_2565121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_2565121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565121 prefixEnd_2565121 := by exact prefixLift 2565121
  have htrace : WordTrace (prefixWord ++ tailWord_2565121) baseStart_2565121 baseEnd_2565121 := by
    simpa [prefixWord, tailWord_2565121, baseEnd_2565121] using wordTrace_append hprefix tailTrace_2565121
  have hstable : (prefixWord ++ tailWord_2565121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565121).length < 2 ^ (prefixWord ++ tailWord_2565121).sum := by decide
  have hdescent : baseEnd_2565121 < baseStart_2565121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565161 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 2, 9, 3]
def baseStart_2565161 : Nat := 118140960795 + 2565161 * 2 ^ 59
def prefixEnd_2565161 : Nat := 4983230072969 + 3 ^ 40 * 2565161 * 2
def baseEnd_2565161 : Nat := 1317160549167943529490545

theorem tailTrace_2565161 : CollatzResearch.WordTrace tailWord_2565161 prefixEnd_2565161 1317160549167943529490545 := by
  unfold tailWord_2565161
  simp only [CollatzResearch.WordTrace]
  refine ⟨93559107859867266465415337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62372738573244844310276891 93559107859867266465415337)
  ·
    refine ⟨70169330894900449849061503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93559107859867266465415337 70169330894900449849061503)
    ·
      refine ⟨105253996342350674773592255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70169330894900449849061503 105253996342350674773592255)
      ·
        refine ⟨157880994513526012160388383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105253996342350674773592255 157880994513526012160388383)
        ·
          refine ⟨236821491770289018240582575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157880994513526012160388383 236821491770289018240582575)
          ·
            refine ⟨355232237655433527360873863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236821491770289018240582575 355232237655433527360873863)
            ·
              refine ⟨532848356483150291041310795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355232237655433527360873863 532848356483150291041310795)
              ·
                refine ⟨799272534724725436561966193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 532848356483150291041310795 799272534724725436561966193)
                ·
                  refine ⟨599454401043544077421474645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 799272534724725436561966193 599454401043544077421474645)
                  ·
                    refine ⟨3512428131114516078641453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 599454401043544077421474645 3512428131114516078641453)
                    ·
                      refine ⟨1317160549167943529490545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3512428131114516078641453 1317160549167943529490545)
                      ·
                        rfl

theorem cell23_2565161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 9, 3].length) (baseStart_2565161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565161 prefixEnd_2565161 := by exact prefixLift 2565161
  have htrace : WordTrace (prefixWord ++ tailWord_2565161) baseStart_2565161 baseEnd_2565161 := by
    simpa [prefixWord, tailWord_2565161, baseEnd_2565161] using wordTrace_append hprefix tailTrace_2565161
  have hstable : (prefixWord ++ tailWord_2565161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565161).length < 2 ^ (prefixWord ++ tailWord_2565161).sum := by decide
  have hdescent : baseEnd_2565161 < baseStart_2565161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565168 : List Nat := [2, 1, 1, 1, 2, 4, 1, 6, 5]
def baseStart_2565168 : Nat := 118140960795 + 2565168 * 2 ^ 59
def prefixEnd_2565168 : Nat := 4983230072969 + 3 ^ 40 * 2565168 * 2
def baseEnd_2565168 : Nat := 146351571503613889122557

theorem tailTrace_2565168 : CollatzResearch.WordTrace tailWord_2565168 prefixEnd_2565168 146351571503613889122557 := by
  unfold tailWord_2565168
  simp only [CollatzResearch.WordTrace]
  refine ⟨46779681585420953330460079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62372908780561271107280105 46779681585420953330460079)
  ·
    refine ⟨70169522378131429995690119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46779681585420953330460079 70169522378131429995690119)
    ·
      refine ⟨105254283567197144993535179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70169522378131429995690119 105254283567197144993535179)
      ·
        refine ⟨157881425350795717490302769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105254283567197144993535179 157881425350795717490302769)
        ·
          refine ⟨118411069013096788117727077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157881425350795717490302769 118411069013096788117727077)
          ·
            refine ⟨22202075439955647772073827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118411069013096788117727077 22202075439955647772073827)
            ·
              refine ⟨33303113159933471658110741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22202075439955647772073827 33303113159933471658110741)
              ·
                refine ⟨1561083429371881483973941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33303113159933471658110741 1561083429371881483973941)
                ·
                  refine ⟨146351571503613889122557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1561083429371881483973941 146351571503613889122557)
                  ·
                    rfl

theorem cell23_2565168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 6, 5].length) (baseStart_2565168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565168 prefixEnd_2565168 := by exact prefixLift 2565168
  have htrace : WordTrace (prefixWord ++ tailWord_2565168) baseStart_2565168 baseEnd_2565168 := by
    simpa [prefixWord, tailWord_2565168, baseEnd_2565168] using wordTrace_append hprefix tailTrace_2565168
  have hstable : (prefixWord ++ tailWord_2565168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565168).length < 2 ^ (prefixWord ++ tailWord_2565168).sum := by decide
  have hdescent : baseEnd_2565168 < baseStart_2565168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565178 : List Nat := [3, 1, 1, 1, 3, 1, 4, 1, 2, 3, 3]
def baseStart_2565178 : Nat := 118140960795 + 2565178 * 2 ^ 59
def prefixEnd_2565178 : Nat := 4983230072969 + 3 ^ 40 * 2565178 * 2
def baseEnd_2565178 : Nat := 1317169278339069962977967

theorem tailTrace_2565178 : CollatzResearch.WordTrace tailWord_2565178 prefixEnd_2565178 1317169278339069962977967 := by
  unfold tailWord_2565178
  simp only [CollatzResearch.WordTrace]
  refine ⟨23389931975201419592196047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62373151933870452245856125 23389931975201419592196047)
  ·
    refine ⟨35084897962802129388294071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23389931975201419592196047 35084897962802129388294071)
    ·
      refine ⟨52627346944203194082441107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35084897962802129388294071 52627346944203194082441107)
      ·
        refine ⟨78941020416304791123661661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52627346944203194082441107 78941020416304791123661661)
        ·
          refine ⟨29602882656114296671373123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78941020416304791123661661 29602882656114296671373123)
          ·
            refine ⟨44404323984171445007059685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29602882656114296671373123 44404323984171445007059685)
            ·
              refine ⟨8325810747032145938823691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44404323984171445007059685 8325810747032145938823691)
              ·
                refine ⟨12488716120548218908235537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8325810747032145938823691 12488716120548218908235537)
                ·
                  refine ⟨9366537090411164181176653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12488716120548218908235537 9366537090411164181176653)
                  ·
                    refine ⟨3512451408904186567941245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9366537090411164181176653 3512451408904186567941245)
                    ·
                      refine ⟨1317169278339069962977967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3512451408904186567941245 1317169278339069962977967)
                      ·
                        rfl

theorem cell23_2565178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 2, 3, 3].length) (baseStart_2565178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565178 prefixEnd_2565178 := by exact prefixLift 2565178
  have htrace : WordTrace (prefixWord ++ tailWord_2565178) baseStart_2565178 baseEnd_2565178 := by
    simpa [prefixWord, tailWord_2565178, baseEnd_2565178] using wordTrace_append hprefix tailTrace_2565178
  have hstable : (prefixWord ++ tailWord_2565178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565178).length < 2 ^ (prefixWord ++ tailWord_2565178).sum := by decide
  have hdescent : baseEnd_2565178 < baseStart_2565178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565198 : List Nat := [4, 1, 1, 1, 1, 3, 2, 3, 2, 5]
def baseStart_2565198 : Nat := 118140960795 + 2565198 * 2 ^ 59
def prefixEnd_2565198 : Nat := 4983230072969 + 3 ^ 40 * 2565198 * 2
def baseEnd_2565198 : Nat := 439059849317386628242625

theorem tailTrace_2565198 : CollatzResearch.WordTrace tailWord_2565198 prefixEnd_2565198 439059849317386628242625 := by
  unfold tailWord_2565198
  simp only [CollatzResearch.WordTrace]
  refine ⟨11695057170091652723064031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62373638240488814523008165 11695057170091652723064031)
  ·
    refine ⟨17542585755137479084596047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11695057170091652723064031 17542585755137479084596047)
    ·
      refine ⟨26313878632706218626894071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17542585755137479084596047 26313878632706218626894071)
      ·
        refine ⟨39470817949059327940341107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26313878632706218626894071 39470817949059327940341107)
        ·
          refine ⟨59206226923588991910511661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39470817949059327940341107 59206226923588991910511661)
          ·
            refine ⟨22202335096345871966441873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59206226923588991910511661 22202335096345871966441873)
            ·
              refine ⟨16651751322259403974831405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22202335096345871966441873 16651751322259403974831405)
              ·
                refine ⟨6244406745847276490561777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16651751322259403974831405 6244406745847276490561777)
                ·
                  refine ⟨4683305059385457367921333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6244406745847276490561777 4683305059385457367921333)
                  ·
                    refine ⟨439059849317386628242625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4683305059385457367921333 439059849317386628242625)
                    ·
                      rfl

theorem cell23_2565198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_2565198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565198 prefixEnd_2565198 := by exact prefixLift 2565198
  have htrace : WordTrace (prefixWord ++ tailWord_2565198) baseStart_2565198 baseEnd_2565198 := by
    simpa [prefixWord, tailWord_2565198, baseEnd_2565198] using wordTrace_append hprefix tailTrace_2565198
  have hstable : (prefixWord ++ tailWord_2565198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565198).length < 2 ^ (prefixWord ++ tailWord_2565198).sum := by decide
  have hdescent : baseEnd_2565198 < baseStart_2565198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565202 : List Nat := [3, 2, 2, 1, 3, 3, 1, 3, 5]
def baseStart_2565202 : Nat := 118140960795 + 2565202 * 2 ^ 59
def prefixEnd_2565202 : Nat := 4983230072969 + 3 ^ 40 * 2565202 * 2
def baseEnd_2565202 : Nat := 146353511319419763230873

theorem tailTrace_2565202 : CollatzResearch.WordTrace tailWord_2565202 prefixEnd_2565202 146353511319419763230873 := by
  unfold tailWord_2565202
  simp only [CollatzResearch.WordTrace]
  refine ⟨23390150813179682616914465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62373735501812486978438573 23390150813179682616914465)
  ·
    refine ⟨17542613109884761962685849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23390150813179682616914465 17542613109884761962685849)
    ·
      refine ⟨13156959832413571472014387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17542613109884761962685849 13156959832413571472014387)
      ·
        refine ⟨19735439748620357208021581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13156959832413571472014387 19735439748620357208021581)
        ·
          refine ⟨7400789905732633953008093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19735439748620357208021581 7400789905732633953008093)
          ·
            refine ⟨2775296214649737732378035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7400789905732633953008093 2775296214649737732378035)
            ·
              refine ⟨4162944321974606598567053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2775296214649737732378035 4162944321974606598567053)
              ·
                refine ⟨1561104120740477474462645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4162944321974606598567053 1561104120740477474462645)
                ·
                  refine ⟨146353511319419763230873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1561104120740477474462645 146353511319419763230873)
                  ·
                    rfl

theorem cell23_2565202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 3, 5].length) (baseStart_2565202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565202 prefixEnd_2565202 := by exact prefixLift 2565202
  have htrace : WordTrace (prefixWord ++ tailWord_2565202) baseStart_2565202 baseEnd_2565202 := by
    simpa [prefixWord, tailWord_2565202, baseEnd_2565202] using wordTrace_append hprefix tailTrace_2565202
  have hstable : (prefixWord ++ tailWord_2565202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565202).length < 2 ^ (prefixWord ++ tailWord_2565202).sum := by decide
  have hdescent : baseEnd_2565202 < baseStart_2565202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565279 : List Nat := [1, 1, 2, 6, 2, 1, 1, 4, 1, 4]
def baseStart_2565279 : Nat := 118140960795 + 2565279 * 2 ^ 59
def prefixEnd_2565279 : Nat := 4983230072969 + 3 ^ 40 * 2565279 * 2
def baseEnd_2565279 : Nat := 439073713295058022605001

theorem tailTrace_2565279 : CollatzResearch.WordTrace tailWord_2565279 prefixEnd_2565279 439073713295058022605001 := by
  unfold tailWord_2565279
  simp only [CollatzResearch.WordTrace]
  refine ⟨93563411673439772618210891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62375607782293181745473927 93563411673439772618210891)
  ·
    refine ⟨140345117510159658927316337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93563411673439772618210891 140345117510159658927316337)
    ·
      refine ⟨105258838132619744195487253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140345117510159658927316337 105258838132619744195487253)
      ·
        refine ⟨4934008037466550509163465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 105258838132619744195487253 4934008037466550509163465)
        ·
          refine ⟨3700506028099912881872599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4934008037466550509163465 3700506028099912881872599)
          ·
            refine ⟨5550759042149869322808899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3700506028099912881872599 5550759042149869322808899)
            ·
              refine ⟨8326138563224803984213349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5550759042149869322808899 8326138563224803984213349)
              ·
                refine ⟨1561150980604650747040003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8326138563224803984213349 1561150980604650747040003)
                ·
                  refine ⟨2341726470906976120560005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1561150980604650747040003 2341726470906976120560005)
                  ·
                    refine ⟨439073713295058022605001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2341726470906976120560005 439073713295058022605001)
                    ·
                      rfl

theorem cell23_2565279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 4, 1, 4].length) (baseStart_2565279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565279 prefixEnd_2565279 := by exact prefixLift 2565279
  have htrace : WordTrace (prefixWord ++ tailWord_2565279) baseStart_2565279 baseEnd_2565279 := by
    simpa [prefixWord, tailWord_2565279, baseEnd_2565279] using wordTrace_append hprefix tailTrace_2565279
  have hstable : (prefixWord ++ tailWord_2565279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565279).length < 2 ^ (prefixWord ++ tailWord_2565279).sum := by decide
  have hdescent : baseEnd_2565279 < baseStart_2565279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565295 : List Nat := [1, 1, 2, 1, 2, 3, 2, 2, 4, 3, 2]
def baseStart_2565295 : Nat := 118140960795 + 2565295 * 2 ^ 59
def prefixEnd_2565295 : Nat := 4983230072969 + 3 ^ 40 * 2565295 * 2
def baseEnd_2565295 : Nat := 1317229355575646005214929

theorem tailTrace_2565295 : CollatzResearch.WordTrace tailWord_2565295 prefixEnd_2565295 1317229355575646005214929 := by
  unfold tailWord_2565295
  simp only [CollatzResearch.WordTrace]
  refine ⟨93563995241381807350793339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62375996827587871567195559 93563995241381807350793339)
  ·
    refine ⟨140345992862072711026190009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93563995241381807350793339 140345992862072711026190009)
    ·
      refine ⟨105259494646554533269642507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140345992862072711026190009 105259494646554533269642507)
      ·
        refine ⟨157889241969831799904463761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105259494646554533269642507 157889241969831799904463761)
        ·
          refine ⟨118416931477373849928347821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157889241969831799904463761 118416931477373849928347821)
          ·
            refine ⟨44406349304015193723130433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118416931477373849928347821 44406349304015193723130433)
            ·
              refine ⟨33304761978011395292347825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44406349304015193723130433 33304761978011395292347825)
              ·
                refine ⟨24978571483508546469260869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33304761978011395292347825 24978571483508546469260869)
                ·
                  refine ⟨4683482153157852462986413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24978571483508546469260869 4683482153157852462986413)
                  ·
                    refine ⟨1756305807434194673619905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4683482153157852462986413 1756305807434194673619905)
                    ·
                      refine ⟨1317229355575646005214929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1756305807434194673619905 1317229355575646005214929)
                      ·
                        rfl

theorem cell23_2565295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 3, 2].length) (baseStart_2565295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565295 prefixEnd_2565295 := by exact prefixLift 2565295
  have htrace : WordTrace (prefixWord ++ tailWord_2565295) baseStart_2565295 baseEnd_2565295 := by
    simpa [prefixWord, tailWord_2565295, baseEnd_2565295] using wordTrace_append hprefix tailTrace_2565295
  have hstable : (prefixWord ++ tailWord_2565295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565295).length < 2 ^ (prefixWord ++ tailWord_2565295).sum := by decide
  have hdescent : baseEnd_2565295 < baseStart_2565295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565312 : List Nat := [2, 1, 1, 2, 6, 1, 1, 1, 1, 5, 2]
def baseStart_2565312 : Nat := 118140960795 + 2565312 * 2 ^ 59
def prefixEnd_2565312 : Nat := 4983230072969 + 3 ^ 40 * 2565312 * 2
def baseEnd_2565312 : Nat := 1317238084746772438702351

theorem tailTrace_2565312 : CollatzResearch.WordTrace tailWord_2565312 prefixEnd_2565312 1317238084746772438702351 := by
  unfold tailWord_2565312
  simp only [CollatzResearch.WordTrace]
  refine ⟨46782307641160109627081095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62376410188213479502774793 46782307641160109627081095)
  ·
    refine ⟨70173461461740164440621643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46782307641160109627081095 70173461461740164440621643)
    ·
      refine ⟨105260192192610246660932465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70173461461740164440621643 105260192192610246660932465)
      ·
        refine ⟨78945144144457684995699349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105260192192610246660932465 78945144144457684995699349)
        ·
          refine ⟨3700553631771453984173407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 78945144144457684995699349 3700553631771453984173407)
          ·
            refine ⟨5550830447657180976260111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3700553631771453984173407 5550830447657180976260111)
            ·
              refine ⟨8326245671485771464390167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5550830447657180976260111 8326245671485771464390167)
              ·
                refine ⟨12489368507228657196585251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8326245671485771464390167 12489368507228657196585251)
                ·
                  refine ⟨18734052760842985794877877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12489368507228657196585251 18734052760842985794877877)
                  ·
                    refine ⟨1756317446329029918269801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18734052760842985794877877 1756317446329029918269801)
                    ·
                      refine ⟨1317238084746772438702351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1756317446329029918269801 1317238084746772438702351)
                      ·
                        rfl

theorem cell23_2565312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 1, 5, 2].length) (baseStart_2565312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565312 prefixEnd_2565312 := by exact prefixLift 2565312
  have htrace : WordTrace (prefixWord ++ tailWord_2565312) baseStart_2565312 baseEnd_2565312 := by
    simpa [prefixWord, tailWord_2565312, baseEnd_2565312] using wordTrace_append hprefix tailTrace_2565312
  have hstable : (prefixWord ++ tailWord_2565312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565312).length < 2 ^ (prefixWord ++ tailWord_2565312).sum := by decide
  have hdescent : baseEnd_2565312 < baseStart_2565312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565322 : List Nat := [3, 1, 2, 1, 3, 2, 4, 1, 1, 5]
def baseStart_2565322 : Nat := 118140960795 + 2565322 * 2 ^ 59
def prefixEnd_2565322 : Nat := 4983230072969 + 3 ^ 40 * 2565322 * 2
def baseEnd_2565322 : Nat := 439081073184439133192435

theorem tailTrace_2565322 : CollatzResearch.WordTrace tailWord_2565322 prefixEnd_2565322 439081073184439133192435 := by
  unfold tailWord_2565322
  simp only [CollatzResearch.WordTrace]
  refine ⟨23391245003070997740506555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62376653341522660641350813 23391245003070997740506555)
  ·
    refine ⟨35086867504606496610759833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23391245003070997740506555 35086867504606496610759833)
    ·
      refine ⟨26315150628454872458069875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35086867504606496610759833 26315150628454872458069875)
      ·
        refine ⟨39472725942682308687104813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26315150628454872458069875 39472725942682308687104813)
        ·
          refine ⟨14802272228505865757664305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39472725942682308687104813 14802272228505865757664305)
          ·
            refine ⟨11101704171379399318248229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14802272228505865757664305 11101704171379399318248229)
            ·
              refine ⟨2081569532133637372171543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11101704171379399318248229 2081569532133637372171543)
              ·
                refine ⟨3122354298200456058257315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2081569532133637372171543 3122354298200456058257315)
                ·
                  refine ⟨4683531447300684087385973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3122354298200456058257315 4683531447300684087385973)
                  ·
                    refine ⟨439081073184439133192435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4683531447300684087385973 439081073184439133192435)
                    ·
                      rfl

theorem cell23_2565322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 1, 5].length) (baseStart_2565322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565322 prefixEnd_2565322 := by exact prefixLift 2565322
  have htrace : WordTrace (prefixWord ++ tailWord_2565322) baseStart_2565322 baseEnd_2565322 := by
    simpa [prefixWord, tailWord_2565322, baseEnd_2565322] using wordTrace_append hprefix tailTrace_2565322
  have hstable : (prefixWord ++ tailWord_2565322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565322).length < 2 ^ (prefixWord ++ tailWord_2565322).sum := by decide
  have hdescent : baseEnd_2565322 < baseStart_2565322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565338 : List Nat := [3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 6]
def baseStart_2565338 : Nat := 118140960795 + 2565338 * 2 ^ 59
def prefixEnd_2565338 : Nat := 4983230072969 + 3 ^ 40 * 2565338 * 2
def baseEnd_2565338 : Nat := 1317251435243789336977231

theorem tailTrace_2565338 : CollatzResearch.WordTrace tailWord_2565338 prefixEnd_2565338 1317251435243789336977231 := by
  unfold tailWord_2565338
  simp only [CollatzResearch.WordTrace]
  refine ⟨23391390895056506423652167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62377042386817350463072445 23391390895056506423652167)
  ·
    refine ⟨35087086342584759635478251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23391390895056506423652167 35087086342584759635478251)
    ·
      refine ⟨52630629513877139453217377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35087086342584759635478251 52630629513877139453217377)
      ·
        refine ⟨39472972135407854589913033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52630629513877139453217377 39472972135407854589913033)
        ·
          refine ⟨29604729101555890942434775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39472972135407854589913033 29604729101555890942434775)
          ·
            refine ⟨44407093652333836413652163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29604729101555890942434775 44407093652333836413652163)
            ·
              refine ⟨66610640478500754620478245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44407093652333836413652163 66610640478500754620478245)
              ·
                refine ⟨12489495089718891491339671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66610640478500754620478245 12489495089718891491339671)
                ·
                  refine ⟨18734242634578337237009507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12489495089718891491339671 18734242634578337237009507)
                  ·
                    refine ⟨28101363951867505855514261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18734242634578337237009507 28101363951867505855514261)
                    ·
                      refine ⟨1317251435243789336977231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28101363951867505855514261 1317251435243789336977231)
                      ·
                        rfl

theorem cell23_2565338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_2565338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565338 prefixEnd_2565338 := by exact prefixLift 2565338
  have htrace : WordTrace (prefixWord ++ tailWord_2565338) baseStart_2565338 baseEnd_2565338 := by
    simpa [prefixWord, tailWord_2565338, baseEnd_2565338] using wordTrace_append hprefix tailTrace_2565338
  have hstable : (prefixWord ++ tailWord_2565338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565338).length < 2 ^ (prefixWord ++ tailWord_2565338).sum := by decide
  have hdescent : baseEnd_2565338 < baseStart_2565338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565345 : List Nat := [1, 2, 3, 1, 3, 3, 1, 2, 1, 1, 5]
def baseStart_2565345 : Nat := 118140960795 + 2565345 * 2 ^ 59
def prefixEnd_2565345 : Nat := 4983230072969 + 3 ^ 40 * 2565345 * 2
def baseEnd_2565345 : Nat := 1317255029608370809589699

theorem tailTrace_2565345 : CollatzResearch.WordTrace tailWord_2565345 prefixEnd_2565345 1317255029608370809589699 := by
  unfold tailWord_2565345
  simp only [CollatzResearch.WordTrace]
  refine ⟨93565818891200665890113489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62377212594133777260075659 93565818891200665890113489)
  ·
    refine ⟨70174364168400499417585117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93565818891200665890113489 70174364168400499417585117)
    ·
      refine ⟨26315386563150187281594419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70174364168400499417585117 26315386563150187281594419)
      ·
        refine ⟨39473079844725280922391629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26315386563150187281594419 39473079844725280922391629)
        ·
          refine ⟨14802404941771980345896861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39473079844725280922391629 14802404941771980345896861)
          ·
            refine ⟨5550901853164492629711323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14802404941771980345896861 5550901853164492629711323)
            ·
              refine ⟨8326352779746738944566985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5550901853164492629711323 8326352779746738944566985)
              ·
                refine ⟨6244764584810054208425239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8326352779746738944566985 6244764584810054208425239)
                ·
                  refine ⟨9367146877215081312637859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6244764584810054208425239 9367146877215081312637859)
                  ·
                    refine ⟨14050720315822621968956789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9367146877215081312637859 14050720315822621968956789)
                    ·
                      refine ⟨1317255029608370809589699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14050720315822621968956789 1317255029608370809589699)
                      ·
                        rfl

theorem cell23_2565345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_2565345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565345 prefixEnd_2565345 := by exact prefixLift 2565345
  have htrace : WordTrace (prefixWord ++ tailWord_2565345) baseStart_2565345 baseEnd_2565345 := by
    simpa [prefixWord, tailWord_2565345, baseEnd_2565345] using wordTrace_append hprefix tailTrace_2565345
  have hstable : (prefixWord ++ tailWord_2565345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565345).length < 2 ^ (prefixWord ++ tailWord_2565345).sum := by decide
  have hdescent : baseEnd_2565345 < baseStart_2565345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565355 : List Nat := [1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 4]
def baseStart_2565355 : Nat := 118140960795 + 2565355 * 2 ^ 59
def prefixEnd_2565355 : Nat := 4983230072969 + 3 ^ 40 * 2565355 * 2
def baseEnd_2565355 : Nat := 1317260164414915770464653

theorem tailTrace_2565355 : CollatzResearch.WordTrace tailWord_2565355 prefixEnd_2565355 1317260164414915770464653 := by
  unfold tailWord_2565355
  simp only [CollatzResearch.WordTrace]
  refine ⟨93566183621164437597977519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62377455747442958398651679 93566183621164437597977519)
  ·
    refine ⟨140349275431746656396966279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93566183621164437597977519 140349275431746656396966279)
    ·
      refine ⟨210523913147619984595449419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140349275431746656396966279 210523913147619984595449419)
      ·
        refine ⟨315785869721429976893174129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210523913147619984595449419 315785869721429976893174129)
        ·
          refine ⟨236839402291072482669880597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315785869721429976893174129 236839402291072482669880597)
          ·
            refine ⟨11101846982394022625150653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 236839402291072482669880597 11101846982394022625150653)
            ·
              refine ⟨4163192618397758484431495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11101846982394022625150653 4163192618397758484431495)
              ·
                refine ⟨6244788927596637726647243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4163192618397758484431495 6244788927596637726647243)
                ·
                  refine ⟨9367183391394956589970865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6244788927596637726647243 9367183391394956589970865)
                  ·
                    refine ⟨7025387543546217442478149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9367183391394956589970865 7025387543546217442478149)
                    ·
                      refine ⟨1317260164414915770464653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7025387543546217442478149 1317260164414915770464653)
                      ·
                        rfl

theorem cell23_2565355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 4].length) (baseStart_2565355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565355 prefixEnd_2565355 := by exact prefixLift 2565355
  have htrace : WordTrace (prefixWord ++ tailWord_2565355) baseStart_2565355 baseEnd_2565355 := by
    simpa [prefixWord, tailWord_2565355, baseEnd_2565355] using wordTrace_append hprefix tailTrace_2565355
  have hstable : (prefixWord ++ tailWord_2565355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565355).length < 2 ^ (prefixWord ++ tailWord_2565355).sum := by decide
  have hdescent : baseEnd_2565355 < baseStart_2565355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565436 : List Nat := [2, 2, 2, 2, 1, 4, 3, 1, 1, 3, 2]
def baseStart_2565436 : Nat := 118140960795 + 2565436 * 2 ^ 59
def prefixEnd_2565436 : Nat := 4983230072969 + 3 ^ 40 * 2565436 * 2
def baseEnd_2565436 : Nat := 1317301756347929953551781

theorem tailTrace_2565436 : CollatzResearch.WordTrace tailWord_2565436 prefixEnd_2565436 1317301756347929953551781 := by
  unfold tailWord_2565436
  simp only [CollatzResearch.WordTrace]
  refine ⟨46784568966935494215838081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62379425289247325621117441 46784568966935494215838081)
  ·
    refine ⟨35088426725201620661878561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46784568966935494215838081 35088426725201620661878561)
    ·
      refine ⟨26316320043901215496408921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35088426725201620661878561 26316320043901215496408921)
      ·
        refine ⟨19737240032925911622306691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26316320043901215496408921 19737240032925911622306691)
        ·
          refine ⟨29605860049388867433460037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19737240032925911622306691 29605860049388867433460037)
          ·
            refine ⟨5551098759260412643773757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29605860049388867433460037 5551098759260412643773757)
            ·
              refine ⟨2081662034722654741415159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5551098759260412643773757 2081662034722654741415159)
              ·
                refine ⟨3122493052083982112122739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2081662034722654741415159 3122493052083982112122739)
                ·
                  refine ⟨4683739578125973168184109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3122493052083982112122739 4683739578125973168184109)
                  ·
                    refine ⟨1756402341797239938069041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4683739578125973168184109 1756402341797239938069041)
                    ·
                      refine ⟨1317301756347929953551781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1756402341797239938069041 1317301756347929953551781)
                      ·
                        rfl

theorem cell23_2565436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_2565436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565436 prefixEnd_2565436 := by exact prefixLift 2565436
  have htrace : WordTrace (prefixWord ++ tailWord_2565436) baseStart_2565436 baseEnd_2565436 := by
    simpa [prefixWord, tailWord_2565436, baseEnd_2565436] using wordTrace_append hprefix tailTrace_2565436
  have hstable : (prefixWord ++ tailWord_2565436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565436).length < 2 ^ (prefixWord ++ tailWord_2565436).sum := by decide
  have hdescent : baseEnd_2565436 < baseStart_2565436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565449 : List Nat := [1, 2, 1, 1, 2, 3, 3, 4, 2, 2, 2]
def baseStart_2565449 : Nat := 118140960795 + 2565449 * 2 ^ 59
def prefixEnd_2565449 : Nat := 4983230072969 + 3 ^ 40 * 2565449 * 2
def baseEnd_2565449 : Nat := 1317308431596438402689221

theorem tailTrace_2565449 : CollatzResearch.WordTrace tailWord_2565449 prefixEnd_2565449 1317308431596438402689221 := by
  unfold tailWord_2565449
  simp only [CollatzResearch.WordTrace]
  refine ⟨93569612082823891651899401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62379741388549261101266267 93569612082823891651899401)
  ·
    refine ⟨70177209062117918738924551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93569612082823891651899401 70177209062117918738924551)
    ·
      refine ⟨105265813593176878108386827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70177209062117918738924551 105265813593176878108386827)
      ·
        refine ⟨157898720389765317162580241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105265813593176878108386827 157898720389765317162580241)
        ·
          refine ⟨118424040292323987871935181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157898720389765317162580241 118424040292323987871935181)
          ·
            refine ⟨44409015109621495451975693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118424040292323987871935181 44409015109621495451975693)
            ·
              refine ⟨16653380666108060794490885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44409015109621495451975693 16653380666108060794490885)
              ·
                refine ⟨3122508874895261398967041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16653380666108060794490885 3122508874895261398967041)
                ·
                  refine ⟨2341881656171446049225281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3122508874895261398967041 2341881656171446049225281)
                  ·
                    refine ⟨1756411242128584536918961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2341881656171446049225281 1756411242128584536918961)
                    ·
                      refine ⟨1317308431596438402689221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1756411242128584536918961 1317308431596438402689221)
                      ·
                        rfl

theorem cell23_2565449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 2, 2, 2].length) (baseStart_2565449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565449 prefixEnd_2565449 := by exact prefixLift 2565449
  have htrace : WordTrace (prefixWord ++ tailWord_2565449) baseStart_2565449 baseEnd_2565449 := by
    simpa [prefixWord, tailWord_2565449, baseEnd_2565449] using wordTrace_append hprefix tailTrace_2565449
  have hstable : (prefixWord ++ tailWord_2565449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565449).length < 2 ^ (prefixWord ++ tailWord_2565449).sum := by decide
  have hdescent : baseEnd_2565449 < baseStart_2565449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565465 : List Nat := [1, 2, 1, 2, 2, 2, 3, 1, 1, 5, 3]
def baseStart_2565465 : Nat := 118140960795 + 2565465 * 2 ^ 59
def prefixEnd_2565465 : Nat := 4983230072969 + 3 ^ 40 * 2565465 * 2
def baseEnd_2565465 : Nat := 1317316647286910340089147

theorem tailTrace_2565465 : CollatzResearch.WordTrace tailWord_2565465 prefixEnd_2565465 1317316647286910340089147 := by
  unfold tailWord_2565465
  simp only [CollatzResearch.WordTrace]
  refine ⟨93570195650765926384481849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62380130433843950922987899 93570195650765926384481849)
  ·
    refine ⟨70177646738074444788361387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93570195650765926384481849 70177646738074444788361387)
    ·
      refine ⟨105266470107111667182542081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70177646738074444788361387 105266470107111667182542081)
      ·
        refine ⟨78949852580333750386906561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105266470107111667182542081 78949852580333750386906561)
        ·
          refine ⟨59212389435250312790179921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78949852580333750386906561 59212389435250312790179921)
          ·
            refine ⟨44409292076437734592634941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59212389435250312790179921 44409292076437734592634941)
            ·
              refine ⟨16653484528664150472238103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44409292076437734592634941 16653484528664150472238103)
              ·
                refine ⟨24980226792996225708357155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16653484528664150472238103 24980226792996225708357155)
                ·
                  refine ⟨37470340189494338562535733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24980226792996225708357155 37470340189494338562535733)
                  ·
                    refine ⟨3512844392765094240237725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37470340189494338562535733 3512844392765094240237725)
                    ·
                      refine ⟨1317316647286910340089147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3512844392765094240237725 1317316647286910340089147)
                      ·
                        rfl

theorem cell23_2565465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 5, 3].length) (baseStart_2565465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565465 prefixEnd_2565465 := by exact prefixLift 2565465
  have htrace : WordTrace (prefixWord ++ tailWord_2565465) baseStart_2565465 baseEnd_2565465 := by
    simpa [prefixWord, tailWord_2565465, baseEnd_2565465] using wordTrace_append hprefix tailTrace_2565465
  have hstable : (prefixWord ++ tailWord_2565465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565465).length < 2 ^ (prefixWord ++ tailWord_2565465).sum := by decide
  have hdescent : baseEnd_2565465 < baseStart_2565465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565506 : List Nat := [3, 4, 2, 1, 1, 1, 2, 4, 5]
def baseStart_2565506 : Nat := 118140960795 + 2565506 * 2 ^ 59
def prefixEnd_2565506 : Nat := 4983230072969 + 3 ^ 40 * 2565506 * 2
def baseEnd_2565506 : Nat := 146370855554860519964051

theorem tailTrace_2565506 : CollatzResearch.WordTrace tailWord_2565506 prefixEnd_2565506 146370855554860519964051 := by
  unfold tailWord_2565506
  simp only [CollatzResearch.WordTrace]
  refine ⟨23392922760904347596681093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62381127362411593591149581 23392922760904347596681093)
  ·
    refine ⟨4386173017669565174377705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23392922760904347596681093 4386173017669565174377705)
    ·
      refine ⟨3289629763252173880783279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4386173017669565174377705 3289629763252173880783279)
      ·
        refine ⟨4934444644878260821174919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3289629763252173880783279 4934444644878260821174919)
        ·
          refine ⟨7401666967317391231762379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4934444644878260821174919 7401666967317391231762379)
          ·
            refine ⟨11102500450976086847643569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7401666967317391231762379 11102500450976086847643569)
            ·
              refine ⟨8326875338232065135732677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11102500450976086847643569 8326875338232065135732677)
              ·
                refine ⟨1561289125918512212949877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8326875338232065135732677 1561289125918512212949877)
                ·
                  refine ⟨146370855554860519964051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1561289125918512212949877 146370855554860519964051)
                  ·
                    rfl

theorem cell23_2565506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_2565506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565506 prefixEnd_2565506 := by exact prefixLift 2565506
  have htrace : WordTrace (prefixWord ++ tailWord_2565506) baseStart_2565506 baseEnd_2565506 := by
    simpa [prefixWord, tailWord_2565506, baseEnd_2565506] using wordTrace_append hprefix tailTrace_2565506
  have hstable : (prefixWord ++ tailWord_2565506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565506).length < 2 ^ (prefixWord ++ tailWord_2565506).sum := by decide
  have hdescent : baseEnd_2565506 < baseStart_2565506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565589 : List Nat := [1, 3, 2, 3, 1, 1, 2, 1, 5, 1, 3]
def baseStart_2565589 : Nat := 118140960795 + 2565589 * 2 ^ 59
def prefixEnd_2565589 : Nat := 4983230072969 + 3 ^ 40 * 2565589 * 2
def baseEnd_2565589 : Nat := 1317380318888067854938577

theorem tailTrace_2565589 : CollatzResearch.WordTrace tailWord_2565589 prefixEnd_2565589 1317380318888067854938577 := by
  unfold tailWord_2565589
  simp only [CollatzResearch.WordTrace]
  refine ⟨93574718302316695561995821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62383145534877797041330547 93574718302316695561995821)
  ·
    refine ⟨35090519363368760835748433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93574718302316695561995821 35090519363368760835748433)
    ·
      refine ⟨26317889522526570626811325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35090519363368760835748433 26317889522526570626811325)
      ·
        refine ⟨9869208570947463985054247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26317889522526570626811325 9869208570947463985054247)
        ·
          refine ⟨14803812856421195977581371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9869208570947463985054247 14803812856421195977581371)
          ·
            refine ⟨22205719284631793966372057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14803812856421195977581371 22205719284631793966372057)
            ·
              refine ⟨16654289463473845474779043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22205719284631793966372057 16654289463473845474779043)
              ·
                refine ⟨24981434195210768212168565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16654289463473845474779043 24981434195210768212168565)
                ·
                  refine ⟨2342009455801009519890803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24981434195210768212168565 2342009455801009519890803)
                  ·
                    refine ⟨3513014183701514279836205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2342009455801009519890803 3513014183701514279836205)
                    ·
                      refine ⟨1317380318888067854938577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3513014183701514279836205 1317380318888067854938577)
                      ·
                        rfl

theorem cell23_2565589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_2565589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565589 prefixEnd_2565589 := by exact prefixLift 2565589
  have htrace : WordTrace (prefixWord ++ tailWord_2565589) baseStart_2565589 baseEnd_2565589 := by
    simpa [prefixWord, tailWord_2565589, baseEnd_2565589] using wordTrace_append hprefix tailTrace_2565589
  have hstable : (prefixWord ++ tailWord_2565589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565589).length < 2 ^ (prefixWord ++ tailWord_2565589).sum := by decide
  have hdescent : baseEnd_2565589 < baseStart_2565589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565595 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 4]
def baseStart_2565595 : Nat := 118140960795 + 2565595 * 2 ^ 59
def prefixEnd_2565595 : Nat := 4983230072969 + 3 ^ 40 * 2565595 * 2
def baseEnd_2565595 : Nat := 1317383399771994831463549

theorem tailTrace_2565595 : CollatzResearch.WordTrace tailWord_2565595 prefixEnd_2565595 1317383399771994831463549 := by
  unfold tailWord_2565595
  simp only [CollatzResearch.WordTrace]
  refine ⟨93574937140294958586714239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62383291426863305724476159 93574937140294958586714239)
  ·
    refine ⟨140362405710442437880071359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93574937140294958586714239 140362405710442437880071359)
    ·
      refine ⟨210543608565663656820107039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140362405710442437880071359 210543608565663656820107039)
      ·
        refine ⟨315815412848495485230160559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210543608565663656820107039 315815412848495485230160559)
        ·
          refine ⟨473723119272743227845240839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315815412848495485230160559 473723119272743227845240839)
          ·
            refine ⟨710584678909114841767861259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473723119272743227845240839 710584678909114841767861259)
            ·
              refine ⟨1065877018363672262651791889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 710584678909114841767861259 1065877018363672262651791889)
              ·
                refine ⟨799407763772754196988843917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1065877018363672262651791889 799407763772754196988843917)
                ·
                  refine ⟨299777911414782823870816469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 799407763772754196988843917 299777911414782823870816469)
                  ·
                    refine ⟨7026044798783972434472261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 299777911414782823870816469 7026044798783972434472261)
                    ·
                      refine ⟨1317383399771994831463549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7026044798783972434472261 1317383399771994831463549)
                      ·
                        rfl

theorem cell23_2565595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 4].length) (baseStart_2565595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565595 prefixEnd_2565595 := by exact prefixLift 2565595
  have htrace : WordTrace (prefixWord ++ tailWord_2565595) baseStart_2565595 baseEnd_2565595 := by
    simpa [prefixWord, tailWord_2565595, baseEnd_2565595] using wordTrace_append hprefix tailTrace_2565595
  have hstable : (prefixWord ++ tailWord_2565595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565595).length < 2 ^ (prefixWord ++ tailWord_2565595).sum := by decide
  have hdescent : baseEnd_2565595 < baseStart_2565595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565635 : List Nat := [1, 1, 1, 3, 2, 1, 2, 12]
def baseStart_2565635 : Nat := 118140960795 + 2565635 * 2 ^ 59
def prefixEnd_2565635 : Nat := 4983230072969 + 3 ^ 40 * 2565635 * 2
def baseEnd_2565635 : Nat := 48792738481413876850495

theorem tailTrace_2565635 : CollatzResearch.WordTrace tailWord_2565635 prefixEnd_2565635 48792738481413876850495 := by
  unfold tailWord_2565635
  simp only [CollatzResearch.WordTrace]
  refine ⟨93576396060150045418170359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62384264040100030278780239 93576396060150045418170359)
  ·
    refine ⟨140364594090225068127255539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93576396060150045418170359 140364594090225068127255539)
    ·
      refine ⟨210546891135337602190883309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140364594090225068127255539 210546891135337602190883309)
      ·
        refine ⟨78955084175751600821581241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210546891135337602190883309 78955084175751600821581241)
        ·
          refine ⟨59216313131813700616185931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78955084175751600821581241 59216313131813700616185931)
          ·
            refine ⟨88824469697720550924278897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59216313131813700616185931 88824469697720550924278897)
            ·
              refine ⟨66618352273290413193209173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88824469697720550924278897 66618352273290413193209173)
              ·
                refine ⟨48792738481413876850495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 66618352273290413193209173 48792738481413876850495)
                ·
                  rfl

theorem cell23_2565635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 12].length) (baseStart_2565635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565635 prefixEnd_2565635 := by exact prefixLift 2565635
  have htrace : WordTrace (prefixWord ++ tailWord_2565635) baseStart_2565635 baseEnd_2565635 := by
    simpa [prefixWord, tailWord_2565635, baseEnd_2565635] using wordTrace_append hprefix tailTrace_2565635
  have hstable : (prefixWord ++ tailWord_2565635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565635).length < 2 ^ (prefixWord ++ tailWord_2565635).sum := by decide
  have hdescent : baseEnd_2565635 < baseStart_2565635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565639 : List Nat := [1, 1, 4, 3, 2, 2, 2, 1, 1, 6]
def baseStart_2565639 : Nat := 118140960795 + 2565639 * 2 ^ 59
def prefixEnd_2565639 : Nat := 4983230072969 + 3 ^ 40 * 2565639 * 2
def baseEnd_2565639 : Nat := 439135330973597553104449

theorem tailTrace_2565639 : CollatzResearch.WordTrace tailWord_2565639 prefixEnd_2565639 439135330973597553104449 := by
  unfold tailWord_2565639
  simp only [CollatzResearch.WordTrace]
  refine ⟨93576541952135554101315971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62384361301423702734210647 93576541952135554101315971)
  ·
    refine ⟨140364812928203331151973957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93576541952135554101315971 140364812928203331151973957)
    ·
      refine ⟨26318402424038124590995117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140364812928203331151973957 26318402424038124590995117)
      ·
        refine ⟨9869400909014296721623169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26318402424038124590995117 9869400909014296721623169)
        ·
          refine ⟨7402050681760722541217377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9869400909014296721623169 7402050681760722541217377)
          ·
            refine ⟨5551538011320541905913033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7402050681760722541217377 5551538011320541905913033)
            ·
              refine ⟨4163653508490406429434775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5551538011320541905913033 4163653508490406429434775)
              ·
                refine ⟨6245480262735609644152163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4163653508490406429434775 6245480262735609644152163)
                ·
                  refine ⟨9368220394103414466228245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6245480262735609644152163 9368220394103414466228245)
                  ·
                    refine ⟨439135330973597553104449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9368220394103414466228245 439135330973597553104449)
                    ·
                      rfl

theorem cell23_2565639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 6].length) (baseStart_2565639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565639 prefixEnd_2565639 := by exact prefixLift 2565639
  have htrace : WordTrace (prefixWord ++ tailWord_2565639) baseStart_2565639 baseEnd_2565639 := by
    simpa [prefixWord, tailWord_2565639, baseEnd_2565639] using wordTrace_append hprefix tailTrace_2565639
  have hstable : (prefixWord ++ tailWord_2565639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565639).length < 2 ^ (prefixWord ++ tailWord_2565639).sum := by decide
  have hdescent : baseEnd_2565639 < baseStart_2565639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565649 : List Nat := [1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 3]
def baseStart_2565649 : Nat := 118140960795 + 2565649 * 2 ^ 59
def prefixEnd_2565649 : Nat := 4983230072969 + 3 ^ 40 * 2565649 * 2
def baseEnd_2565649 : Nat := 1317411127727337620188301

theorem tailTrace_2565649 : CollatzResearch.WordTrace tailWord_2565649 prefixEnd_2565649 1317411127727337620188301 := by
  unfold tailWord_2565649
  simp only [CollatzResearch.WordTrace]
  refine ⟨93576906682099325809180001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62384604454732883872786667 93576906682099325809180001)
  ·
    refine ⟨70182680011574494356885001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93576906682099325809180001 70182680011574494356885001)
    ·
      refine ⟨52637010008680870767663751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70182680011574494356885001 52637010008680870767663751)
      ·
        refine ⟨78955515013021306151495627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52637010008680870767663751 78955515013021306151495627)
        ·
          refine ⟨118433272519531959227243441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78955515013021306151495627 118433272519531959227243441)
          ·
            refine ⟨88824954389648969420432581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118433272519531959227243441 88824954389648969420432581)
            ·
              refine ⟨16654678948059181766331109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88824954389648969420432581 16654678948059181766331109)
              ·
                refine ⟨3122752302761096581187083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16654678948059181766331109 3122752302761096581187083)
                ·
                  refine ⟨4684128454141644871780625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3122752302761096581187083 4684128454141644871780625)
                  ·
                    refine ⟨3513096340606233653835469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4684128454141644871780625 3513096340606233653835469)
                    ·
                      refine ⟨1317411127727337620188301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3513096340606233653835469 1317411127727337620188301)
                      ·
                        rfl

theorem cell23_2565649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 3].length) (baseStart_2565649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565649 prefixEnd_2565649 := by exact prefixLift 2565649
  have htrace : WordTrace (prefixWord ++ tailWord_2565649) baseStart_2565649 baseEnd_2565649 := by
    simpa [prefixWord, tailWord_2565649, baseEnd_2565649] using wordTrace_append hprefix tailTrace_2565649
  have hstable : (prefixWord ++ tailWord_2565649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565649).length < 2 ^ (prefixWord ++ tailWord_2565649).sum := by decide
  have hdescent : baseEnd_2565649 < baseStart_2565649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565663 : List Nat := [1, 1, 2, 4, 1, 1, 3, 5, 1, 2, 2]
def baseStart_2565663 : Nat := 118140960795 + 2565663 * 2 ^ 59
def prefixEnd_2565663 : Nat := 4983230072969 + 3 ^ 40 * 2565663 * 2
def baseEnd_2565663 : Nat := 1317418316456500565413237

theorem tailTrace_2565663 : CollatzResearch.WordTrace tailWord_2565663 prefixEnd_2565663 1317418316456500565413237 := by
  unfold tailWord_2565663
  simp only [CollatzResearch.WordTrace]
  refine ⟨93577417304048606200189643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62384944869365737466793095 93577417304048606200189643)
  ·
    refine ⟨140366125956072909300284465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93577417304048606200189643 140366125956072909300284465)
    ·
      refine ⟨105274594467054681975213349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140366125956072909300284465 105274594467054681975213349)
      ·
        refine ⟨19738986462572752870352503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105274594467054681975213349 19738986462572752870352503)
        ·
          refine ⟨29608479693859129305528755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19738986462572752870352503 29608479693859129305528755)
          ·
            refine ⟨44412719540788693958293133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29608479693859129305528755 44412719540788693958293133)
            ·
              refine ⟨16654769827795760234359925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44412719540788693958293133 16654769827795760234359925)
              ·
                refine ⟨1561384671355852521971243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16654769827795760234359925 1561384671355852521971243)
                ·
                  refine ⟨2342077007033778782956865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1561384671355852521971243 2342077007033778782956865)
                  ·
                    refine ⟨1756557755275334087217649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2342077007033778782956865 1756557755275334087217649)
                    ·
                      refine ⟨1317418316456500565413237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1756557755275334087217649 1317418316456500565413237)
                      ·
                        rfl

theorem cell23_2565663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 5, 1, 2, 2].length) (baseStart_2565663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565663 prefixEnd_2565663 := by exact prefixLift 2565663
  have htrace : WordTrace (prefixWord ++ tailWord_2565663) baseStart_2565663 baseEnd_2565663 := by
    simpa [prefixWord, tailWord_2565663, baseEnd_2565663] using wordTrace_append hprefix tailTrace_2565663
  have hstable : (prefixWord ++ tailWord_2565663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565663).length < 2 ^ (prefixWord ++ tailWord_2565663).sum := by decide
  have hdescent : baseEnd_2565663 < baseStart_2565663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565693 : List Nat := [1, 4, 1, 3, 4, 1, 1, 1, 1, 2, 4]
def baseStart_2565693 : Nat := 118140960795 + 2565693 * 2 ^ 59
def prefixEnd_2565693 : Nat := 4983230072969 + 3 ^ 40 * 2565693 * 2
def baseEnd_2565693 : Nat := 1317433720876135448038099

theorem tailTrace_2565693 : CollatzResearch.WordTrace tailWord_2565693 prefixEnd_2565693 1317433720876135448038099 := by
  unfold tailWord_2565693
  simp only [CollatzResearch.WordTrace]
  refine ⟨93578511493939921323781733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62385674329293280882521155 93578511493939921323781733)
  ·
    refine ⟨17545970905113735248209075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93578511493939921323781733 17545970905113735248209075)
    ·
      refine ⟨26318956357670602872313613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17545970905113735248209075 26318956357670602872313613)
      ·
        refine ⟨9869608634126476077117605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26318956357670602872313613 9869608634126476077117605)
        ·
          refine ⟨1850551618898714264459551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9869608634126476077117605 1850551618898714264459551)
          ·
            refine ⟨2775827428348071396689327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1850551618898714264459551 2775827428348071396689327)
            ·
              refine ⟨4163741142522107095033991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2775827428348071396689327 4163741142522107095033991)
              ·
                refine ⟨6245611713783160642550987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4163741142522107095033991 6245611713783160642550987)
                ·
                  refine ⟨9368417570674740963826481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6245611713783160642550987 9368417570674740963826481)
                  ·
                    refine ⟨7026313178006055722869861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9368417570674740963826481 7026313178006055722869861)
                    ·
                      refine ⟨1317433720876135448038099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7026313178006055722869861 1317433720876135448038099)
                      ·
                        rfl

theorem cell23_2565693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_2565693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565693 prefixEnd_2565693 := by exact prefixLift 2565693
  have htrace : WordTrace (prefixWord ++ tailWord_2565693) baseStart_2565693 baseEnd_2565693 := by
    simpa [prefixWord, tailWord_2565693, baseEnd_2565693] using wordTrace_append hprefix tailTrace_2565693
  have hstable : (prefixWord ++ tailWord_2565693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565693).length < 2 ^ (prefixWord ++ tailWord_2565693).sum := by decide
  have hdescent : baseEnd_2565693 < baseStart_2565693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565753 : List Nat := [1, 2, 1, 3, 3, 1, 3, 3, 2, 2, 2]
def baseStart_2565753 : Nat := 118140960795 + 2565753 * 2 ^ 59
def prefixEnd_2565753 : Nat := 4983230072969 + 3 ^ 40 * 2565753 * 2
def baseEnd_2565753 : Nat := 1317464529715405213287823

theorem tailTrace_2565753 : CollatzResearch.WordTrace tailWord_2565753 prefixEnd_2565753 1317464529715405213287823 := by
  unfold tailWord_2565753
  simp only [CollatzResearch.WordTrace]
  refine ⟨93580699873722551570965913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62387133249148367713977275 93580699873722551570965913)
  ·
    refine ⟨70185524905291913678224435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93580699873722551570965913 70185524905291913678224435)
    ·
      refine ⟨105278287357937870517336653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70185524905291913678224435 105278287357937870517336653)
      ·
        refine ⟨39479357759226701444001245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105278287357937870517336653 39479357759226701444001245)
        ·
          refine ⟨14804759159710013041500467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39479357759226701444001245 14804759159710013041500467)
          ·
            refine ⟨22207138739565019562250701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14804759159710013041500467 22207138739565019562250701)
            ·
              refine ⟨8327677027336882335844013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22207138739565019562250701 8327677027336882335844013)
              ·
                refine ⟨3122878885251330875941505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8327677027336882335844013 3122878885251330875941505)
                ·
                  refine ⟨2342159163938498156956129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3122878885251330875941505 2342159163938498156956129)
                  ·
                    refine ⟨1756619372953873617717097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2342159163938498156956129 1756619372953873617717097)
                    ·
                      refine ⟨1317464529715405213287823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1756619372953873617717097 1317464529715405213287823)
                      ·
                        rfl

theorem cell23_2565753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 2, 2, 2].length) (baseStart_2565753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565753 prefixEnd_2565753 := by exact prefixLift 2565753
  have htrace : WordTrace (prefixWord ++ tailWord_2565753) baseStart_2565753 baseEnd_2565753 := by
    simpa [prefixWord, tailWord_2565753, baseEnd_2565753] using wordTrace_append hprefix tailTrace_2565753
  have hstable : (prefixWord ++ tailWord_2565753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565753).length < 2 ^ (prefixWord ++ tailWord_2565753).sum := by decide
  have hdescent : baseEnd_2565753 < baseStart_2565753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565779 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 3, 7, 2]
def baseStart_2565779 : Nat := 118140960795 + 2565779 * 2 ^ 59
def prefixEnd_2565779 : Nat := 4983230072969 + 3 ^ 40 * 2565779 * 2
def baseEnd_2565779 : Nat := 1317477880212422111562703

theorem tailTrace_2565779 : CollatzResearch.WordTrace tailWord_2565779 prefixEnd_2565779 1317477880212422111562703 := by
  unfold tailWord_2565779
  simp only [CollatzResearch.WordTrace]
  refine ⟨93581648171628358011412391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62387765447752238674274927 93581648171628358011412391)
  ·
    refine ⟨140372472257442537017118587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93581648171628358011412391 140372472257442537017118587)
    ·
      refine ⟨210558708386163805525677881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140372472257442537017118587 210558708386163805525677881)
      ·
        refine ⟨157919031289622854144258411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210558708386163805525677881 157919031289622854144258411)
        ·
          refine ⟨236878546934434281216387617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157919031289622854144258411 236878546934434281216387617)
          ·
            refine ⟨177658910200825710912290713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236878546934434281216387617 177658910200825710912290713)
            ·
              refine ⟨133244182650619283184218035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177658910200825710912290713 133244182650619283184218035)
              ·
                refine ⟨199866273975928924776327053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133244182650619283184218035 199866273975928924776327053)
                ·
                  refine ⟨74949852740973346791122645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 199866273975928924776327053 74949852740973346791122645)
                  ·
                    refine ⟨1756637173616562815416937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 74949852740973346791122645 1756637173616562815416937)
                    ·
                      refine ⟨1317477880212422111562703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1756637173616562815416937 1317477880212422111562703)
                      ·
                        rfl

theorem cell23_2565779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 7, 2].length) (baseStart_2565779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565779 prefixEnd_2565779 := by exact prefixLift 2565779
  have htrace : WordTrace (prefixWord ++ tailWord_2565779) baseStart_2565779 baseEnd_2565779 := by
    simpa [prefixWord, tailWord_2565779, baseEnd_2565779] using wordTrace_append hprefix tailTrace_2565779
  have hstable : (prefixWord ++ tailWord_2565779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565779).length < 2 ^ (prefixWord ++ tailWord_2565779).sum := by decide
  have hdescent : baseEnd_2565779 < baseStart_2565779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565793 : List Nat := [1, 2, 3, 3, 2, 1, 4, 2, 5]
def baseStart_2565793 : Nat := 118140960795 + 2565793 * 2 ^ 59
def prefixEnd_2565793 : Nat := 4983230072969 + 3 ^ 40 * 2565793 * 2
def baseEnd_2565793 : Nat := 146387229882398339643071

theorem tailTrace_2565793 : CollatzResearch.WordTrace tailWord_2565793 prefixEnd_2565793 146387229882398339643071 := by
  unfold tailWord_2565793
  simp only [CollatzResearch.WordTrace]
  refine ⟨93582158793577638402422033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62388105862385092268281355 93582158793577638402422033)
  ·
    refine ⟨70186619095183228801816525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93582158793577638402422033 70186619095183228801816525)
    ·
      refine ⟨26319982160693710800681197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70186619095183228801816525 26319982160693710800681197)
      ·
        refine ⟨9869993310260141550255449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26319982160693710800681197 9869993310260141550255449)
        ·
          refine ⟨7402494982695106162691587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9869993310260141550255449 7402494982695106162691587)
          ·
            refine ⟨11103742474042659244037381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7402494982695106162691587 11103742474042659244037381)
            ·
              refine ⟨2081951713882998608257009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11103742474042659244037381 2081951713882998608257009)
              ·
                refine ⟨1561463785412248956192757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2081951713882998608257009 1561463785412248956192757)
                ·
                  refine ⟨146387229882398339643071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1561463785412248956192757 146387229882398339643071)
                  ·
                    rfl

theorem cell23_2565793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 2, 5].length) (baseStart_2565793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565793 prefixEnd_2565793 := by exact prefixLift 2565793
  have htrace : WordTrace (prefixWord ++ tailWord_2565793) baseStart_2565793 baseEnd_2565793 := by
    simpa [prefixWord, tailWord_2565793, baseEnd_2565793] using wordTrace_append hprefix tailTrace_2565793
  have hstable : (prefixWord ++ tailWord_2565793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565793).length < 2 ^ (prefixWord ++ tailWord_2565793).sum := by decide
  have hdescent : baseEnd_2565793 < baseStart_2565793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565796 : List Nat := [2, 3, 1, 2, 2, 2, 1, 1, 2, 5, 2]
def baseStart_2565796 : Nat := 118140960795 + 2565796 * 2 ^ 59
def prefixEnd_2565796 : Nat := 4983230072969 + 3 ^ 40 * 2565796 * 2
def baseEnd_2565796 : Nat := 1317486609383548545050125

theorem tailTrace_2565796 : CollatzResearch.WordTrace tailWord_2565796 prefixEnd_2565796 1317486609383548545050125 := by
  unfold tailWord_2565796
  simp only [CollatzResearch.WordTrace]
  refine ⟨46791134106283384957390621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62388178808377846609854161 46791134106283384957390621)
  ·
    refine ⟨17546675289856269359021483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46791134106283384957390621 17546675289856269359021483)
    ·
      refine ⟨26320012934784404038532225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17546675289856269359021483 26320012934784404038532225)
      ·
        refine ⟨19740009701088303028899169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26320012934784404038532225 19740009701088303028899169)
        ·
          refine ⟨14805007275816227271674377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19740009701088303028899169 14805007275816227271674377)
          ·
            refine ⟨11103755456862170453755783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14805007275816227271674377 11103755456862170453755783)
            ·
              refine ⟨16655633185293255680633675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11103755456862170453755783 16655633185293255680633675)
              ·
                refine ⟨24983449777939883520950513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16655633185293255680633675 24983449777939883520950513)
                ·
                  refine ⟨18737587333454912640712885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24983449777939883520950513 18737587333454912640712885)
                  ·
                    refine ⟨1756648812511398060066833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18737587333454912640712885 1756648812511398060066833)
                    ·
                      refine ⟨1317486609383548545050125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1756648812511398060066833 1317486609383548545050125)
                      ·
                        rfl

theorem cell23_2565796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_2565796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565796 prefixEnd_2565796 := by exact prefixLift 2565796
  have htrace : WordTrace (prefixWord ++ tailWord_2565796) baseStart_2565796 baseEnd_2565796 := by
    simpa [prefixWord, tailWord_2565796, baseEnd_2565796] using wordTrace_append hprefix tailTrace_2565796
  have hstable : (prefixWord ++ tailWord_2565796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565796).length < 2 ^ (prefixWord ++ tailWord_2565796).sum := by decide
  have hdescent : baseEnd_2565796 < baseStart_2565796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565800 : List Nat := [2, 1, 7, 1, 1, 1, 1, 1, 2, 2, 4]
def baseStart_2565800 : Nat := 118140960795 + 2565800 * 2 ^ 59
def prefixEnd_2565800 : Nat := 4983230072969 + 3 ^ 40 * 2565800 * 2
def baseEnd_2565800 : Nat := 1317488663306166529400107

theorem tailTrace_2565800 : CollatzResearch.WordTrace tailWord_2565800 prefixEnd_2565800 1317488663306166529400107 := by
  unfold tailWord_2565800
  simp only [CollatzResearch.WordTrace]
  refine ⟨46791207052276139298963427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62388276069701519065284569 46791207052276139298963427)
  ·
    refine ⟨70186810578414208948445141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46791207052276139298963427 70186810578414208948445141)
    ·
      refine ⟨1645003372931583022229183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 70186810578414208948445141 1645003372931583022229183)
      ·
        refine ⟨2467505059397374533343775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1645003372931583022229183 2467505059397374533343775)
        ·
          refine ⟨3701257589096061800015663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2467505059397374533343775 3701257589096061800015663)
          ·
            refine ⟨5551886383644092700023495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3701257589096061800015663 5551886383644092700023495)
            ·
              refine ⟨8327829575466139050035243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5551886383644092700023495 8327829575466139050035243)
              ·
                refine ⟨12491744363199208575052865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8327829575466139050035243 12491744363199208575052865)
                ·
                  refine ⟨9368808272399406431289649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12491744363199208575052865 9368808272399406431289649)
                  ·
                    refine ⟨7026606204299554823467237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9368808272399406431289649 7026606204299554823467237)
                    ·
                      refine ⟨1317488663306166529400107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7026606204299554823467237 1317488663306166529400107)
                      ·
                        rfl

theorem cell23_2565800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_2565800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565800 prefixEnd_2565800 := by exact prefixLift 2565800
  have htrace : WordTrace (prefixWord ++ tailWord_2565800) baseStart_2565800 baseEnd_2565800 := by
    simpa [prefixWord, tailWord_2565800, baseEnd_2565800] using wordTrace_append hprefix tailTrace_2565800
  have hstable : (prefixWord ++ tailWord_2565800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565800).length < 2 ^ (prefixWord ++ tailWord_2565800).sum := by decide
  have hdescent : baseEnd_2565800 < baseStart_2565800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565829 : List Nat := [1, 3, 1, 1, 1, 1, 2, 5, 1, 4, 3]
def baseStart_2565829 : Nat := 118140960795 + 2565829 * 2 ^ 59
def prefixEnd_2565829 : Nat := 4983230072969 + 3 ^ 40 * 2565829 * 2
def baseEnd_2565829 : Nat := 1317503554245146915937473

theorem tailTrace_2565829 : CollatzResearch.WordTrace tailWord_2565829 prefixEnd_2565829 1317503554245146915937473 := by
  unfold tailWord_2565829
  simp only [CollatzResearch.WordTrace]
  refine ⟨93583471821447216550732541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62388981214298144367155027 93583471821447216550732541)
  ·
    refine ⟨35093801933042706206524703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93583471821447216550732541 35093801933042706206524703)
    ·
      refine ⟨52640702899564059309787055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35093801933042706206524703 52640702899564059309787055)
      ·
        refine ⟨78961054349346088964680583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52640702899564059309787055 78961054349346088964680583)
        ·
          refine ⟨118441581524019133447020875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78961054349346088964680583 118441581524019133447020875)
          ·
            refine ⟨177662372286028700170531313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118441581524019133447020875 177662372286028700170531313)
            ·
              refine ⟨133246779214521525127898485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177662372286028700170531313 133246779214521525127898485)
              ·
                refine ⟨12491885551361392980740483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 133246779214521525127898485 12491885551361392980740483)
                ·
                  refine ⟨18737828327042089471110725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12491885551361392980740483 18737828327042089471110725)
                  ·
                    refine ⟨3513342811320391775833261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18737828327042089471110725 3513342811320391775833261)
                    ·
                      refine ⟨1317503554245146915937473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3513342811320391775833261 1317503554245146915937473)
                      ·
                        rfl

theorem cell23_2565829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 4, 3].length) (baseStart_2565829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565829 prefixEnd_2565829 := by exact prefixLift 2565829
  have htrace : WordTrace (prefixWord ++ tailWord_2565829) baseStart_2565829 baseEnd_2565829 := by
    simpa [prefixWord, tailWord_2565829, baseEnd_2565829] using wordTrace_append hprefix tailTrace_2565829
  have hstable : (prefixWord ++ tailWord_2565829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565829).length < 2 ^ (prefixWord ++ tailWord_2565829).sum := by decide
  have hdescent : baseEnd_2565829 < baseStart_2565829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565849 : List Nat := [1, 2, 1, 2, 3, 4, 1, 1, 8]
def baseStart_2565849 : Nat := 118140960795 + 2565849 * 2 ^ 59
def prefixEnd_2565849 : Nat := 4983230072969 + 3 ^ 40 * 2565849 * 2
def baseEnd_2565849 : Nat := 146390424873137426409709

theorem tailTrace_2565849 : CollatzResearch.WordTrace tailWord_2565849 prefixEnd_2565849 146390424873137426409709 := by
  unfold tailWord_2565849
  simp only [CollatzResearch.WordTrace]
  refine ⟨93584201281374759966460601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62389467520916506644307067 93584201281374759966460601)
  ·
    refine ⟨70188150961031069974845451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93584201281374759966460601 70188150961031069974845451)
    ·
      refine ⟨105282226441546604962268177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70188150961031069974845451 105282226441546604962268177)
      ·
        refine ⟨78961669831159953721701133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105282226441546604962268177 78961669831159953721701133)
        ·
          refine ⟨29610626186684982645637925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78961669831159953721701133 29610626186684982645637925)
          ·
            refine ⟨5551992410003434246057111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29610626186684982645637925 5551992410003434246057111)
            ·
              refine ⟨8327988615005151369085667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5551992410003434246057111 8327988615005151369085667)
              ·
                refine ⟨12491982922507727053628501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8327988615005151369085667 12491982922507727053628501)
                ·
                  refine ⟨146390424873137426409709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12491982922507727053628501 146390424873137426409709)
                  ·
                    rfl

theorem cell23_2565849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 8].length) (baseStart_2565849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565849 prefixEnd_2565849 := by exact prefixLift 2565849
  have htrace : WordTrace (prefixWord ++ tailWord_2565849) baseStart_2565849 baseEnd_2565849 := by
    simpa [prefixWord, tailWord_2565849, baseEnd_2565849] using wordTrace_append hprefix tailTrace_2565849
  have hstable : (prefixWord ++ tailWord_2565849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565849).length < 2 ^ (prefixWord ++ tailWord_2565849).sum := by decide
  have hdescent : baseEnd_2565849 < baseStart_2565849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565879 : List Nat := [1, 1, 3, 1, 1, 1, 4, 3, 3, 5]
def baseStart_2565879 : Nat := 118140960795 + 2565879 * 2 ^ 59
def prefixEnd_2565879 : Nat := 4983230072969 + 3 ^ 40 * 2565879 * 2
def baseEnd_2565879 : Nat := 439176409425957240104081

theorem tailTrace_2565879 : CollatzResearch.WordTrace tailWord_2565879 prefixEnd_2565879 439176409425957240104081 := by
  unfold tailWord_2565879
  simp only [CollatzResearch.WordTrace]
  refine ⟨93585295471266075090052691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62390196980844050060035127 93585295471266075090052691)
  ·
    refine ⟨140377943206899112635079037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93585295471266075090052691 140377943206899112635079037)
    ·
      refine ⟨52641728702587167238154639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140377943206899112635079037 52641728702587167238154639)
      ·
        refine ⟨78962593053880750857231959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52641728702587167238154639 78962593053880750857231959)
        ·
          refine ⟨118443889580821126285847939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78962593053880750857231959 118443889580821126285847939)
          ·
            refine ⟨177665834371231689428771909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118443889580821126285847939 177665834371231689428771909)
            ·
              refine ⟨33312343944605941767894733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 177665834371231689428771909 33312343944605941767894733)
              ·
                refine ⟨12492128979227228162960525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33312343944605941767894733 12492128979227228162960525)
                ·
                  refine ⟨4684548367210210561110197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12492128979227228162960525 4684548367210210561110197)
                  ·
                    refine ⟨439176409425957240104081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4684548367210210561110197 439176409425957240104081)
                    ·
                      rfl

theorem cell23_2565879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 5].length) (baseStart_2565879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565879 prefixEnd_2565879 := by exact prefixLift 2565879
  have htrace : WordTrace (prefixWord ++ tailWord_2565879) baseStart_2565879 baseEnd_2565879 := by
    simpa [prefixWord, tailWord_2565879, baseEnd_2565879] using wordTrace_append hprefix tailTrace_2565879
  have hstable : (prefixWord ++ tailWord_2565879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565879).length < 2 ^ (prefixWord ++ tailWord_2565879).sum := by decide
  have hdescent : baseEnd_2565879 < baseStart_2565879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565896 : List Nat := [2, 1, 3, 2, 2, 1, 1, 5, 1, 5]
def baseStart_2565896 : Nat := 118140960795 + 2565896 * 2 ^ 59
def prefixEnd_2565896 : Nat := 4983230072969 + 3 ^ 40 * 2565896 * 2
def baseEnd_2565896 : Nat := 439179319149666051266555

theorem tailTrace_2565896 : CollatzResearch.WordTrace tailWord_2565896 prefixEnd_2565896 439179319149666051266555 := by
  unfold tailWord_2565896
  simp only [CollatzResearch.WordTrace]
  refine ⟨46792957756102243496710771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62390610341469657995614361 46792957756102243496710771)
  ·
    refine ⟨70189436634153365245066157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46792957756102243496710771 70189436634153365245066157)
    ·
      refine ⟨26321038737807511966899809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70189436634153365245066157 26321038737807511966899809)
      ·
        refine ⟨19740779053355633975174857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26321038737807511966899809 19740779053355633975174857)
        ·
          refine ⟨14805584290016725481381143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19740779053355633975174857 14805584290016725481381143)
          ·
            refine ⟨22208376435025088222071715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14805584290016725481381143 22208376435025088222071715)
            ·
              refine ⟨33312564652537632333107573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22208376435025088222071715 33312564652537632333107573)
              ·
                refine ⟨3123052936175403031228835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33312564652537632333107573 3123052936175403031228835)
                ·
                  refine ⟨4684579404263104546843253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3123052936175403031228835 4684579404263104546843253)
                  ·
                    refine ⟨439179319149666051266555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4684579404263104546843253 439179319149666051266555)
                    ·
                      rfl

theorem cell23_2565896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_2565896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565896 prefixEnd_2565896 := by exact prefixLift 2565896
  have htrace : WordTrace (prefixWord ++ tailWord_2565896) baseStart_2565896 baseEnd_2565896 := by
    simpa [prefixWord, tailWord_2565896, baseEnd_2565896] using wordTrace_append hprefix tailTrace_2565896
  have hstable : (prefixWord ++ tailWord_2565896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565896).length < 2 ^ (prefixWord ++ tailWord_2565896).sum := by decide
  have hdescent : baseEnd_2565896 < baseStart_2565896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565916 : List Nat := [2, 2, 3, 1, 1, 2, 2, 2, 3, 1, 4]
def baseStart_2565916 : Nat := 118140960795 + 2565916 * 2 ^ 59
def prefixEnd_2565916 : Nat := 4983230072969 + 3 ^ 40 * 2565916 * 2
def baseEnd_2565916 : Nat := 1317548227062088075549573

theorem tailTrace_2565916 : CollatzResearch.WordTrace tailWord_2565916 prefixEnd_2565916 1317548227062088075549573 := by
  unfold tailWord_2565916
  simp only [CollatzResearch.WordTrace]
  refine ⟨46793322486066015204574801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62391096648088020272766401 46793322486066015204574801)
  ·
    refine ⟨35094991864549511403431101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46793322486066015204574801 35094991864549511403431101)
    ·
      refine ⟨13160621949206066776286663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35094991864549511403431101 13160621949206066776286663)
      ·
        refine ⟨19740932923809100164429995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13160621949206066776286663 19740932923809100164429995)
        ·
          refine ⟨29611399385713650246644993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19740932923809100164429995 29611399385713650246644993)
          ·
            refine ⟨22208549539285237684983745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29611399385713650246644993 22208549539285237684983745)
            ·
              refine ⟨16656412154463928263737809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22208549539285237684983745 16656412154463928263737809)
              ·
                refine ⟨12492309115847946197803357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16656412154463928263737809 12492309115847946197803357)
                ·
                  refine ⟨4684615918442979824176259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12492309115847946197803357 4684615918442979824176259)
                  ·
                    refine ⟨7026923877664469736264389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4684615918442979824176259 7026923877664469736264389)
                    ·
                      refine ⟨1317548227062088075549573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7026923877664469736264389 1317548227062088075549573)
                      ·
                        rfl

theorem cell23_2565916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_2565916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565916 prefixEnd_2565916 := by exact prefixLift 2565916
  have htrace : WordTrace (prefixWord ++ tailWord_2565916) baseStart_2565916 baseEnd_2565916 := by
    simpa [prefixWord, tailWord_2565916, baseEnd_2565916] using wordTrace_append hprefix tailTrace_2565916
  have hstable : (prefixWord ++ tailWord_2565916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565916).length < 2 ^ (prefixWord ++ tailWord_2565916).sum := by decide
  have hdescent : baseEnd_2565916 < baseStart_2565916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565946 : List Nat := [3, 1, 1, 1, 5, 1, 1, 1, 3, 2, 4]
def baseStart_2565946 : Nat := 118140960795 + 2565946 * 2 ^ 59
def prefixEnd_2565946 : Nat := 4983230072969 + 3 ^ 40 * 2565946 * 2
def baseEnd_2565946 : Nat := 1317563631481722958174435

theorem tailTrace_2565946 : CollatzResearch.WordTrace tailWord_2565946 prefixEnd_2565946 1317563631481722958174435 := by
  unfold tailWord_2565946
  simp only [CollatzResearch.WordTrace]
  refine ⟨23396934790505836383185423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62391826108015563688494461 23396934790505836383185423)
  ·
    refine ⟨35095402185758754574778135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23396934790505836383185423 35095402185758754574778135)
    ·
      refine ⟨52643103278638131862167203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35095402185758754574778135 52643103278638131862167203)
      ·
        refine ⟨78964654917957197793250805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52643103278638131862167203 78964654917957197793250805)
        ·
          refine ⟨7402936398558487293117263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78964654917957197793250805 7402936398558487293117263)
          ·
            refine ⟨11104404597837730939675895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7402936398558487293117263 11104404597837730939675895)
            ·
              refine ⟨16656606896756596409513843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11104404597837730939675895 16656606896756596409513843)
              ·
                refine ⟨24984910345134894614270765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16656606896756596409513843 24984910345134894614270765)
                ·
                  refine ⟨9369341379425585480351537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24984910345134894614270765 9369341379425585480351537)
                  ·
                    refine ⟨7027006034569189110263653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9369341379425585480351537 7027006034569189110263653)
                    ·
                      refine ⟨1317563631481722958174435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7027006034569189110263653 1317563631481722958174435)
                      ·
                        rfl

theorem cell23_2565946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 3, 2, 4].length) (baseStart_2565946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565946 prefixEnd_2565946 := by exact prefixLift 2565946
  have htrace : WordTrace (prefixWord ++ tailWord_2565946) baseStart_2565946 baseEnd_2565946 := by
    simpa [prefixWord, tailWord_2565946, baseEnd_2565946] using wordTrace_append hprefix tailTrace_2565946
  have hstable : (prefixWord ++ tailWord_2565946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565946).length < 2 ^ (prefixWord ++ tailWord_2565946).sum := by decide
  have hdescent : baseEnd_2565946 < baseStart_2565946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565980 : List Nat := [2, 2, 4, 2, 2, 1, 2, 1, 1, 2, 4]
def baseStart_2565980 : Nat := 118140960795 + 2565980 * 2 ^ 59
def prefixEnd_2565980 : Nat := 4983230072969 + 3 ^ 40 * 2565980 * 2
def baseEnd_2565980 : Nat := 1317581089823975825149279

theorem tailTrace_2565980 : CollatzResearch.WordTrace tailWord_2565980 prefixEnd_2565980 1317581089823975825149279 := by
  unfold tailWord_2565980
  simp only [CollatzResearch.WordTrace]
  refine ⟨46794489621950084669739697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62392652829266779559652929 46794489621950084669739697)
  ·
    refine ⟨35095867216462563502304773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46794489621950084669739697 35095867216462563502304773)
    ·
      refine ⟨6580475103086730656682145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35095867216462563502304773 6580475103086730656682145)
      ·
        refine ⟨4935356327315047992511609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6580475103086730656682145 4935356327315047992511609)
        ·
          refine ⟨3701517245486285994383707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4935356327315047992511609 3701517245486285994383707)
          ·
            refine ⟨5552275868229428991575561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3701517245486285994383707 5552275868229428991575561)
            ·
              refine ⟨4164206901172071743681671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5552275868229428991575561 4164206901172071743681671)
              ·
                refine ⟨6246310351758107615522507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4164206901172071743681671 6246310351758107615522507)
                ·
                  refine ⟨9369465527637161423283761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6246310351758107615522507 9369465527637161423283761)
                  ·
                    refine ⟨7027099145727871067462821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9369465527637161423283761 7027099145727871067462821)
                    ·
                      refine ⟨1317581089823975825149279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7027099145727871067462821 1317581089823975825149279)
                      ·
                        rfl

theorem cell23_2565980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_2565980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565980 prefixEnd_2565980 := by exact prefixLift 2565980
  have htrace : WordTrace (prefixWord ++ tailWord_2565980) baseStart_2565980 baseEnd_2565980 := by
    simpa [prefixWord, tailWord_2565980, baseEnd_2565980] using wordTrace_append hprefix tailTrace_2565980
  have hstable : (prefixWord ++ tailWord_2565980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565980).length < 2 ^ (prefixWord ++ tailWord_2565980).sum := by decide
  have hdescent : baseEnd_2565980 < baseStart_2565980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565983 : List Nat := [1, 1, 2, 3, 1, 5, 2, 1, 1, 3, 3]
def baseStart_2565983 : Nat := 118140960795 + 2565983 * 2 ^ 59
def prefixEnd_2565983 : Nat := 4983230072969 + 3 ^ 40 * 2565983 * 2
def baseEnd_2565983 : Nat := 1317582630265939313411765

theorem tailTrace_2565983 : CollatzResearch.WordTrace tailWord_2565983 prefixEnd_2565983 1317582630265939313411765 := by
  unfold tailWord_2565983
  simp only [CollatzResearch.WordTrace]
  refine ⟨93589088662889300851838603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62392725775259533901225735 93589088662889300851838603)
  ·
    refine ⟨140383632994333951277757905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93589088662889300851838603 140383632994333951277757905)
    ·
      refine ⟨105287724745750463458318429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140383632994333951277757905 105287724745750463458318429)
      ·
        refine ⟨39482896779656423796869411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105287724745750463458318429 39482896779656423796869411)
        ·
          refine ⟨59224345169484635695304117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39482896779656423796869411 59224345169484635695304117)
          ·
            refine ⟨5552282359639184596434761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59224345169484635695304117 5552282359639184596434761)
            ·
              refine ⟨4164211769729388447326071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5552282359639184596434761 4164211769729388447326071)
              ·
                refine ⟨6246317654594082670989107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4164211769729388447326071 6246317654594082670989107)
                ·
                  refine ⟨9369476481891124006483661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6246317654594082670989107 9369476481891124006483661)
                  ·
                    refine ⟨3513553680709171502431373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9369476481891124006483661 3513553680709171502431373)
                    ·
                      refine ⟨1317582630265939313411765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3513553680709171502431373 1317582630265939313411765)
                      ·
                        rfl

theorem cell23_2565983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 3, 3].length) (baseStart_2565983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2565983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2565983 prefixEnd_2565983 := by exact prefixLift 2565983
  have htrace : WordTrace (prefixWord ++ tailWord_2565983) baseStart_2565983 baseEnd_2565983 := by
    simpa [prefixWord, tailWord_2565983, baseEnd_2565983] using wordTrace_append hprefix tailTrace_2565983
  have hstable : (prefixWord ++ tailWord_2565983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565983).length < 2 ^ (prefixWord ++ tailWord_2565983).sum := by decide
  have hdescent : baseEnd_2565983 < baseStart_2565983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566017 : List Nat := [1, 2, 4, 4, 1, 1, 1, 1, 4, 1, 3]
def baseStart_2566017 : Nat := 118140960795 + 2566017 * 2 ^ 59
def prefixEnd_2566017 : Nat := 4983230072969 + 3 ^ 40 * 2566017 * 2
def baseEnd_2566017 : Nat := 1317600088608192180386609

theorem tailTrace_2566017 : CollatzResearch.WordTrace tailWord_2566017 prefixEnd_2566017 1317600088608192180386609 := by
  unfold tailWord_2566017
  simp only [CollatzResearch.WordTrace]
  refine ⟨93590328744766124658576305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62393552496510749772384203 93590328744766124658576305)
  ·
    refine ⟨70192746558574593493932229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93590328744766124658576305 70192746558574593493932229)
    ·
      refine ⟨13161139979732736280112293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70192746558574593493932229 13161139979732736280112293)
      ·
        refine ⟨2467713746199888052521055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13161139979732736280112293 2467713746199888052521055)
        ·
          refine ⟨3701570619299832078781583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2467713746199888052521055 3701570619299832078781583)
          ·
            refine ⟨5552355928949748118172375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3701570619299832078781583 5552355928949748118172375)
            ·
              refine ⟨8328533893424622177258563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5552355928949748118172375 8328533893424622177258563)
              ·
                refine ⟨12492800840136933265887845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8328533893424622177258563 12492800840136933265887845)
                ·
                  refine ⟨2342400157525674987353971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12492800840136933265887845 2342400157525674987353971)
                  ·
                    refine ⟨3513600236288512481030957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2342400157525674987353971 3513600236288512481030957)
                    ·
                      refine ⟨1317600088608192180386609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3513600236288512481030957 1317600088608192180386609)
                      ·
                        rfl

theorem cell23_2566017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_2566017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566017 prefixEnd_2566017 := by exact prefixLift 2566017
  have htrace : WordTrace (prefixWord ++ tailWord_2566017) baseStart_2566017 baseEnd_2566017 := by
    simpa [prefixWord, tailWord_2566017, baseEnd_2566017] using wordTrace_append hprefix tailTrace_2566017
  have hstable : (prefixWord ++ tailWord_2566017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566017).length < 2 ^ (prefixWord ++ tailWord_2566017).sum := by decide
  have hdescent : baseEnd_2566017 < baseStart_2566017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566034 : List Nat := [3, 2, 3, 2, 1, 2, 3, 1, 2, 1, 3]
def baseStart_2566034 : Nat := 118140960795 + 2566034 * 2 ^ 59
def prefixEnd_2566034 : Nat := 4983230072969 + 3 ^ 40 * 2566034 * 2
def baseEnd_2566034 : Nat := 1317608817779318613874031

theorem tailTrace_2566034 : CollatzResearch.WordTrace tailWord_2566034 prefixEnd_2566034 1317608817779318613874031 := by
  unfold tailWord_2566034
  simp only [CollatzResearch.WordTrace]
  refine ⟨23397737196426134140486289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62393965857136357707963437 23397737196426134140486289)
  ·
    refine ⟨17548302897319600605364717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23397737196426134140486289 17548302897319600605364717)
    ·
      refine ⟨6580613586494850227011769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17548302897319600605364717 6580613586494850227011769)
      ·
        refine ⟨4935460189871137670258827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6580613586494850227011769 4935460189871137670258827)
        ·
          refine ⟨7403190284806706505388241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4935460189871137670258827 7403190284806706505388241)
          ·
            refine ⟨5552392713605029879041181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7403190284806706505388241 5552392713605029879041181)
            ·
              refine ⟨2082147267601886204640443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5552392713605029879041181 2082147267601886204640443)
              ·
                refine ⟨3123220901402829306960665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2082147267601886204640443 3123220901402829306960665)
                ·
                  refine ⟨2342415676052121980220499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3123220901402829306960665 2342415676052121980220499)
                  ·
                    refine ⟨3513623514078182970330749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2342415676052121980220499 3513623514078182970330749)
                    ·
                      refine ⟨1317608817779318613874031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3513623514078182970330749 1317608817779318613874031)
                      ·
                        rfl

theorem cell23_2566034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_2566034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566034 prefixEnd_2566034 := by exact prefixLift 2566034
  have htrace : WordTrace (prefixWord ++ tailWord_2566034) baseStart_2566034 baseEnd_2566034 := by
    simpa [prefixWord, tailWord_2566034, baseEnd_2566034] using wordTrace_append hprefix tailTrace_2566034
  have hstable : (prefixWord ++ tailWord_2566034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566034).length < 2 ^ (prefixWord ++ tailWord_2566034).sum := by decide
  have hdescent : baseEnd_2566034 < baseStart_2566034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566080 : List Nat := [2, 1, 1, 2, 3, 2, 5, 2, 5]
def baseStart_2566080 : Nat := 118140960795 + 2566080 * 2 ^ 59
def prefixEnd_2566080 : Nat := 4983230072969 + 3 ^ 40 * 2566080 * 2
def baseEnd_2566080 : Nat := 146403604209936159322091

theorem tailTrace_2566080 : CollatzResearch.WordTrace tailWord_2566080 prefixEnd_2566080 146403604209936159322091 := by
  unfold tailWord_2566080
  simp only [CollatzResearch.WordTrace]
  refine ⟨46796313271768943209059847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62395084362358590945413129 46796313271768943209059847)
  ·
    refine ⟨70194469907653414813589771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46796313271768943209059847 70194469907653414813589771)
    ·
      refine ⟨105291704861480122220384657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70194469907653414813589771 105291704861480122220384657)
      ·
        refine ⟨78968778646110091665288493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105291704861480122220384657 78968778646110091665288493)
        ·
          refine ⟨29613291992291284374483185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78968778646110091665288493 29613291992291284374483185)
          ·
            refine ⟨22209968994218463280862389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29613291992291284374483185 22209968994218463280862389)
            ·
              refine ⟨2082184593207980932580849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22209968994218463280862389 2082184593207980932580849)
              ·
                refine ⟨1561638444905985699435637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2082184593207980932580849 1561638444905985699435637)
                ·
                  refine ⟨146403604209936159322091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1561638444905985699435637 146403604209936159322091)
                  ·
                    rfl

theorem cell23_2566080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 2, 5].length) (baseStart_2566080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566080 prefixEnd_2566080 := by exact prefixLift 2566080
  have htrace : WordTrace (prefixWord ++ tailWord_2566080) baseStart_2566080 baseEnd_2566080 := by
    simpa [prefixWord, tailWord_2566080, baseEnd_2566080] using wordTrace_append hprefix tailTrace_2566080
  have hstable : (prefixWord ++ tailWord_2566080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566080).length < 2 ^ (prefixWord ++ tailWord_2566080).sum := by decide
  have hdescent : baseEnd_2566080 < baseStart_2566080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566096 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 4]
def baseStart_2566096 : Nat := 118140960795 + 2566096 * 2 ^ 59
def prefixEnd_2566096 : Nat := 4983230072969 + 3 ^ 40 * 2566096 * 2
def baseEnd_2566096 : Nat := 1317640653579897371298745

theorem tailTrace_2566096 : CollatzResearch.WordTrace tailWord_2566096 prefixEnd_2566096 1317640653579897371298745 := by
  unfold tailWord_2566096
  simp only [CollatzResearch.WordTrace]
  refine ⟨46796605055739960575351071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62395473407653280767134761 46796605055739960575351071)
  ·
    refine ⟨70194907583609940863026607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46796605055739960575351071 70194907583609940863026607)
    ·
      refine ⟨105292361375414911294539911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70194907583609940863026607 105292361375414911294539911)
      ·
        refine ⟨157938542063122366941809867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105292361375414911294539911 157938542063122366941809867)
        ·
          refine ⟨236907813094683550412714801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157938542063122366941809867 236907813094683550412714801)
          ·
            refine ⟨177680859821012662809536101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236907813094683550412714801 177680859821012662809536101)
            ·
              refine ⟨33315161216439874276788019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 177680859821012662809536101 33315161216439874276788019)
              ·
                refine ⟨49972741824659811415182029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33315161216439874276788019 49972741824659811415182029)
                ·
                  refine ⟨18739778184247429280693261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49972741824659811415182029 18739778184247429280693261)
                  ·
                    refine ⟨7027416819092785980259973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18739778184247429280693261 7027416819092785980259973)
                    ·
                      refine ⟨1317640653579897371298745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7027416819092785980259973 1317640653579897371298745)
                      ·
                        rfl

theorem cell23_2566096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 4].length) (baseStart_2566096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566096 prefixEnd_2566096 := by exact prefixLift 2566096
  have htrace : WordTrace (prefixWord ++ tailWord_2566096) baseStart_2566096 baseEnd_2566096 := by
    simpa [prefixWord, tailWord_2566096, baseEnd_2566096] using wordTrace_append hprefix tailTrace_2566096
  have hstable : (prefixWord ++ tailWord_2566096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566096).length < 2 ^ (prefixWord ++ tailWord_2566096).sum := by decide
  have hdescent : baseEnd_2566096 < baseStart_2566096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566113 : List Nat := [1, 2, 3, 1, 2, 1, 3, 3, 2, 1, 4]
def baseStart_2566113 : Nat := 118140960795 + 2566113 * 2 ^ 59
def prefixEnd_2566113 : Nat := 4983230072969 + 3 ^ 40 * 2566113 * 2
def baseEnd_2566113 : Nat := 1317649382751023804786167

theorem tailTrace_2566113 : CollatzResearch.WordTrace tailWord_2566113 prefixEnd_2566113 1317649382751023804786167 := by
  unfold tailWord_2566113
  simp only [CollatzResearch.WordTrace]
  refine ⟨93593830152418333054070993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62395886768278888702713995 93593830152418333054070993)
  ·
    refine ⟨70195372614313749790553245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93593830152418333054070993 70195372614313749790553245)
    ·
      refine ⟨26323264730367656171457467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70195372614313749790553245 26323264730367656171457467)
      ·
        refine ⟨39484897095551484257186201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26323264730367656171457467 39484897095551484257186201)
        ·
          refine ⟨29613672821663613192889651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39484897095551484257186201 29613672821663613192889651)
          ·
            refine ⟨44420509232495419789334477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29613672821663613192889651 44420509232495419789334477)
            ·
              refine ⟨16657690962185782421000429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44420509232495419789334477 16657690962185782421000429)
              ·
                refine ⟨6246634110819668407875161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16657690962185782421000429 6246634110819668407875161)
                ·
                  refine ⟨4684975583114751305906371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6246634110819668407875161 4684975583114751305906371)
                  ·
                    refine ⟨7027463374672126958859557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4684975583114751305906371 7027463374672126958859557)
                    ·
                      refine ⟨1317649382751023804786167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7027463374672126958859557 1317649382751023804786167)
                      ·
                        rfl

theorem cell23_2566113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_2566113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566113 prefixEnd_2566113 := by exact prefixLift 2566113
  have htrace : WordTrace (prefixWord ++ tailWord_2566113) baseStart_2566113 baseEnd_2566113 := by
    simpa [prefixWord, tailWord_2566113, baseEnd_2566113] using wordTrace_append hprefix tailTrace_2566113
  have hstable : (prefixWord ++ tailWord_2566113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566113).length < 2 ^ (prefixWord ++ tailWord_2566113).sum := by decide
  have hdescent : baseEnd_2566113 < baseStart_2566113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566136 : List Nat := [2, 1, 2, 1, 1, 3, 2, 3, 8]
def baseStart_2566136 : Nat := 118140960795 + 2566136 * 2 ^ 59
def prefixEnd_2566136 : Nat := 4983230072969 + 3 ^ 40 * 2566136 * 2
def baseEnd_2566136 : Nat := 146406799200675246088729

theorem tailTrace_2566136 : CollatzResearch.WordTrace tailWord_2566136 prefixEnd_2566136 146406799200675246088729 := by
  unfold tailWord_2566136
  simp only [CollatzResearch.WordTrace]
  refine ⟨46797334515667503991079131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62396446020890005321438841 46797334515667503991079131)
  ·
    refine ⟨70196001773501255986618697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46797334515667503991079131 70196001773501255986618697)
    ·
      refine ⟨52647001330125941989964023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70196001773501255986618697 52647001330125941989964023)
      ·
        refine ⟨78970501995188912984946035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52647001330125941989964023 78970501995188912984946035)
        ·
          refine ⟨118455752992783369477419053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78970501995188912984946035 118455752992783369477419053)
          ·
            refine ⟨44420907372293763554032145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118455752992783369477419053 44420907372293763554032145)
            ·
              refine ⟨33315680529220322665524109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44420907372293763554032145 33315680529220322665524109)
              ·
                refine ⟨12493380198457620999571541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33315680529220322665524109 12493380198457620999571541)
                ·
                  refine ⟨146406799200675246088729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12493380198457620999571541 146406799200675246088729)
                  ·
                    rfl

theorem cell23_2566136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 8].length) (baseStart_2566136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566136 prefixEnd_2566136 := by exact prefixLift 2566136
  have htrace : WordTrace (prefixWord ++ tailWord_2566136) baseStart_2566136 baseEnd_2566136 := by
    simpa [prefixWord, tailWord_2566136, baseEnd_2566136] using wordTrace_append hprefix tailTrace_2566136
  have hstable : (prefixWord ++ tailWord_2566136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566136).length < 2 ^ (prefixWord ++ tailWord_2566136).sum := by decide
  have hdescent : baseEnd_2566136 < baseStart_2566136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566214 : List Nat := [6, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3]
def baseStart_2566214 : Nat := 118140960795 + 2566214 * 2 ^ 59
def prefixEnd_2566214 : Nat := 4983230072969 + 3 ^ 40 * 2566214 * 2
def baseEnd_2566214 : Nat := 1317701244297127909623203

theorem tailTrace_2566214 : CollatzResearch.WordTrace tailWord_2566214 prefixEnd_2566214 1317701244297127909623203 := by
  unfold tailWord_2566214
  simp only [CollatzResearch.WordTrace]
  refine ⟨2924922310157888353234303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 62398342616701618202331797 2924922310157888353234303)
  ·
    refine ⟨4387383465236832529851455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2924922310157888353234303 4387383465236832529851455)
    ·
      refine ⟨6581075197855248794777183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4387383465236832529851455 6581075197855248794777183)
      ·
        refine ⟨9871612796782873192165775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6581075197855248794777183 9871612796782873192165775)
        ·
          refine ⟨14807419195174309788248663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9871612796782873192165775 14807419195174309788248663)
          ·
            refine ⟨22211128792761464682372995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14807419195174309788248663 22211128792761464682372995)
            ·
              refine ⟨33316693189142197023559493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22211128792761464682372995 33316693189142197023559493)
              ·
                refine ⟨6246879972964161941917405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33316693189142197023559493 6246879972964161941917405)
                ·
                  refine ⟨2342579989861560728219027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6246879972964161941917405 2342579989861560728219027)
                  ·
                    refine ⟨3513869984792341092328541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2342579989861560728219027 3513869984792341092328541)
                    ·
                      refine ⟨1317701244297127909623203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3513869984792341092328541 1317701244297127909623203)
                      ·
                        rfl

theorem cell23_2566214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_2566214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566214 prefixEnd_2566214 := by exact prefixLift 2566214
  have htrace : WordTrace (prefixWord ++ tailWord_2566214) baseStart_2566214 baseEnd_2566214 := by
    simpa [prefixWord, tailWord_2566214, baseEnd_2566214] using wordTrace_append hprefix tailTrace_2566214
  have hstable : (prefixWord ++ tailWord_2566214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566214).length < 2 ^ (prefixWord ++ tailWord_2566214).sum := by decide
  have hdescent : baseEnd_2566214 < baseStart_2566214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566220 : List Nat := [2, 2, 1, 3, 1, 1, 3, 4, 1, 1, 4]
def baseStart_2566220 : Nat := 118140960795 + 2566220 * 2 ^ 59
def prefixEnd_2566220 : Nat := 4983230072969 + 3 ^ 40 * 2566220 * 2
def baseEnd_2566220 : Nat := 1317704325181054886148175

theorem tailTrace_2566220 : CollatzResearch.WordTrace tailWord_2566220 prefixEnd_2566220 1317704325181054886148175 := by
  unfold tailWord_2566220
  simp only [CollatzResearch.WordTrace]
  refine ⟨46798866381515345164108057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62398488508687126885477409 46798866381515345164108057)
  ·
    refine ⟨35099149786136508873081043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46798866381515345164108057 35099149786136508873081043)
    ·
      refine ⟨52648724679204763309621565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35099149786136508873081043 52648724679204763309621565)
      ·
        refine ⟨19743271754701786241108087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52648724679204763309621565 19743271754701786241108087)
        ·
          refine ⟨29614907632052679361662131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19743271754701786241108087 29614907632052679361662131)
          ·
            refine ⟨44422361448079019042493197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29614907632052679361662131 44422361448079019042493197)
            ·
              refine ⟨16658385543029632140934949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44422361448079019042493197 16658385543029632140934949)
              ·
                refine ⟨3123447289318056026425303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16658385543029632140934949 3123447289318056026425303)
                ·
                  refine ⟨4685170933977084039637955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3123447289318056026425303 4685170933977084039637955)
                  ·
                    refine ⟨7027756400965626059456933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4685170933977084039637955 7027756400965626059456933)
                    ·
                      refine ⟨1317704325181054886148175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7027756400965626059456933 1317704325181054886148175)
                      ·
                        rfl

theorem cell23_2566220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_2566220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566220 prefixEnd_2566220 := by exact prefixLift 2566220
  have htrace : WordTrace (prefixWord ++ tailWord_2566220) baseStart_2566220 baseEnd_2566220 := by
    simpa [prefixWord, tailWord_2566220, baseEnd_2566220] using wordTrace_append hprefix tailTrace_2566220
  have hstable : (prefixWord ++ tailWord_2566220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566220).length < 2 ^ (prefixWord ++ tailWord_2566220).sum := by decide
  have hdescent : baseEnd_2566220 < baseStart_2566220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566233 : List Nat := [1, 2, 1, 2, 2, 1, 4, 1, 3, 2, 4]
def baseStart_2566233 : Nat := 118140960795 + 2566233 * 2 ^ 59
def prefixEnd_2566233 : Nat := 4983230072969 + 3 ^ 40 * 2566233 * 2
def baseEnd_2566233 : Nat := 1317711000429563335285615

theorem tailTrace_2566233 : CollatzResearch.WordTrace tailWord_2566233 prefixEnd_2566233 1317711000429563335285615 := by
  unfold tailWord_2566233
  simp only [CollatzResearch.WordTrace]
  refine ⟨93598206911983593548439353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62398804607989062365626235 93598206911983593548439353)
  ·
    refine ⟨70198655183987695161329515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93598206911983593548439353 70198655183987695161329515)
    ·
      refine ⟨105297982775981542741994273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70198655183987695161329515 105297982775981542741994273)
      ·
        refine ⟨78973487081986157056495705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105297982775981542741994273 78973487081986157056495705)
        ·
          refine ⟨59230115311489617792371779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78973487081986157056495705 59230115311489617792371779)
          ·
            refine ⟨88845172967234426688557669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59230115311489617792371779 88845172967234426688557669)
            ·
              refine ⟨16658469931356455004104563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88845172967234426688557669 16658469931356455004104563)
              ·
                refine ⟨24987704897034682506156845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16658469931356455004104563 24987704897034682506156845)
                ·
                  refine ⟨9370389336388005939808817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24987704897034682506156845 9370389336388005939808817)
                  ·
                    refine ⟨7027792002291004454856613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9370389336388005939808817 7027792002291004454856613)
                    ·
                      refine ⟨1317711000429563335285615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7027792002291004454856613 1317711000429563335285615)
                      ·
                        rfl

theorem cell23_2566233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 2, 4].length) (baseStart_2566233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566233 prefixEnd_2566233 := by exact prefixLift 2566233
  have htrace : WordTrace (prefixWord ++ tailWord_2566233) baseStart_2566233 baseEnd_2566233 := by
    simpa [prefixWord, tailWord_2566233, baseEnd_2566233] using wordTrace_append hprefix tailTrace_2566233
  have hstable : (prefixWord ++ tailWord_2566233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566233).length < 2 ^ (prefixWord ++ tailWord_2566233).sum := by decide
  have hdescent : baseEnd_2566233 < baseStart_2566233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566240 : List Nat := [2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 5]
def baseStart_2566240 : Nat := 118140960795 + 2566240 * 2 ^ 59
def prefixEnd_2566240 : Nat := 4983230072969 + 3 ^ 40 * 2566240 * 2
def baseEnd_2566240 : Nat := 1317714594794144807898083

theorem tailTrace_2566240 : CollatzResearch.WordTrace tailWord_2566240 prefixEnd_2566240 1317714594794144807898083 := by
  unfold tailWord_2566240
  simp only [CollatzResearch.WordTrace]
  refine ⟨46799231111479116871972087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62398974815305489162629449 46799231111479116871972087)
  ·
    refine ⟨70198846667218675307958131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46799231111479116871972087 70198846667218675307958131)
    ·
      refine ⟨105298270000828012961937197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70198846667218675307958131 105298270000828012961937197)
      ·
        refine ⟨39486851250310504860726449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105298270000828012961937197 39486851250310504860726449)
        ·
          refine ⟨29615138437732878645544837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39486851250310504860726449 29615138437732878645544837)
          ·
            refine ⟨5552838457074914746039657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29615138437732878645544837 5552838457074914746039657)
            ·
              refine ⟨4164628842806186059529743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5552838457074914746039657 4164628842806186059529743)
              ·
                refine ⟨6246943264209279089294615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4164628842806186059529743 6246943264209279089294615)
                ·
                  refine ⟨9370414896313918633941923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6246943264209279089294615 9370414896313918633941923)
                  ·
                    refine ⟨14055622344470877950912885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9370414896313918633941923 14055622344470877950912885)
                    ·
                      refine ⟨1317714594794144807898083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14055622344470877950912885 1317714594794144807898083)
                      ·
                        rfl

theorem cell23_2566240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 5].length) (baseStart_2566240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566240 prefixEnd_2566240 := by exact prefixLift 2566240
  have htrace : WordTrace (prefixWord ++ tailWord_2566240) baseStart_2566240 baseEnd_2566240 := by
    simpa [prefixWord, tailWord_2566240, baseEnd_2566240] using wordTrace_append hprefix tailTrace_2566240
  have hstable : (prefixWord ++ tailWord_2566240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566240).length < 2 ^ (prefixWord ++ tailWord_2566240).sum := by decide
  have hdescent : baseEnd_2566240 < baseStart_2566240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566294 : List Nat := [5, 3, 2, 1, 12]
def baseStart_2566294 : Nat := 118140960795 + 2566294 * 2 ^ 59
def prefixEnd_2566294 : Nat := 4983230072969 + 3 ^ 40 * 2566294 * 2
def baseEnd_2566294 : Nat := 1807602637516443891115

theorem tailTrace_2566294 : CollatzResearch.WordTrace tailWord_2566294 prefixEnd_2566294 1807602637516443891115 := by
  unfold tailWord_2566294
  simp only [CollatzResearch.WordTrace]
  refine ⟨5850026985297662560400621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62400287843175067310939957 5850026985297662560400621)
  ·
    refine ⟨2193760119486623460150233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5850026985297662560400621 2193760119486623460150233)
    ·
      refine ⟨1645320089614967595112675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2193760119486623460150233 1645320089614967595112675)
      ·
        refine ⟨2467980134422451392669013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1645320089614967595112675 2467980134422451392669013)
        ·
          refine ⟨1807602637516443891115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 2467980134422451392669013 1807602637516443891115)
          ·
            rfl

theorem cell23_2566294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 12].length) (baseStart_2566294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566294 prefixEnd_2566294 := by exact prefixLift 2566294
  have htrace : WordTrace (prefixWord ++ tailWord_2566294) baseStart_2566294 baseEnd_2566294 := by
    simpa [prefixWord, tailWord_2566294, baseEnd_2566294] using wordTrace_append hprefix tailTrace_2566294
  have hstable : (prefixWord ++ tailWord_2566294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566294).length < 2 ^ (prefixWord ++ tailWord_2566294).sum := by decide
  have hdescent : baseEnd_2566294 < baseStart_2566294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566297 : List Nat := [1, 2, 1, 2, 1, 2, 1, 7, 1, 3, 2]
def baseStart_2566297 : Nat := 118140960795 + 2566297 * 2 ^ 59
def prefixEnd_2566297 : Nat := 4983230072969 + 3 ^ 40 * 2566297 * 2
def baseEnd_2566297 : Nat := 1317743863191451084885321

theorem tailTrace_2566297 : CollatzResearch.WordTrace tailWord_2566297 prefixEnd_2566297 1317743863191451084885321 := by
  unfold tailWord_2566297
  simp only [CollatzResearch.WordTrace]
  refine ⟨93600541183751732478769145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62400360789167821652512763 93600541183751732478769145)
  ·
    refine ⟨70200405887813799359076859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93600541183751732478769145 70200405887813799359076859)
    ·
      refine ⟨105300608831720699038615289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70200405887813799359076859 105300608831720699038615289)
      ·
        refine ⟨78975456623790524278961467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105300608831720699038615289 78975456623790524278961467)
        ·
          refine ⟨118463184935685786418442201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78975456623790524278961467 118463184935685786418442201)
          ·
            refine ⟨88847388701764339813831651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118463184935685786418442201 88847388701764339813831651)
            ·
              refine ⟨133271083052646509720747477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88847388701764339813831651 133271083052646509720747477)
              ·
                refine ⟨3123541009046402571580019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 133271083052646509720747477 3123541009046402571580019)
                ·
                  refine ⟨4685311513569603857370029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3123541009046402571580019 4685311513569603857370029)
                  ·
                    refine ⟨1756991817588601446513761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4685311513569603857370029 1756991817588601446513761)
                    ·
                      refine ⟨1317743863191451084885321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1756991817588601446513761 1317743863191451084885321)
                      ·
                        rfl

theorem cell23_2566297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 3, 2].length) (baseStart_2566297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566297 prefixEnd_2566297 := by exact prefixLift 2566297
  have htrace : WordTrace (prefixWord ++ tailWord_2566297) baseStart_2566297 baseEnd_2566297 := by
    simpa [prefixWord, tailWord_2566297, baseEnd_2566297] using wordTrace_append hprefix tailTrace_2566297
  have hstable : (prefixWord ++ tailWord_2566297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566297).length < 2 ^ (prefixWord ++ tailWord_2566297).sum := by decide
  have hdescent : baseEnd_2566297 < baseStart_2566297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566304 : List Nat := [2, 1, 1, 4, 2, 3, 2, 2, 2, 1, 3]
def baseStart_2566304 : Nat := 118140960795 + 2566304 * 2 ^ 59
def prefixEnd_2566304 : Nat := 4983230072969 + 3 ^ 40 * 2566304 * 2
def baseEnd_2566304 : Nat := 1317747457556032557497789

theorem tailTrace_2566304 : CollatzResearch.WordTrace tailWord_2566304 prefixEnd_2566304 1317747457556032557497789 := by
  unfold tailWord_2566304
  simp only [CollatzResearch.WordTrace]
  refine ⟨46800398247363186337136983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62400530996484248449515977 46800398247363186337136983)
  ·
    refine ⟨70200597371044779505705475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46800398247363186337136983 70200597371044779505705475)
    ·
      refine ⟨105300896056567169258558213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70200597371044779505705475 105300896056567169258558213)
      ·
        refine ⟨19743918010606344235979665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105300896056567169258558213 19743918010606344235979665)
        ·
          refine ⟨14807938507954758176984749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19743918010606344235979665 14807938507954758176984749)
          ·
            refine ⟨5552976940483034316369281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14807938507954758176984749 5552976940483034316369281)
            ·
              refine ⟨4164732705362275737276961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5552976940483034316369281 4164732705362275737276961)
              ·
                refine ⟨3123549529021706802957721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4164732705362275737276961 3123549529021706802957721)
                ·
                  refine ⟨2342662146766280102218291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3123549529021706802957721 2342662146766280102218291)
                  ·
                    refine ⟨3513993220149420153327437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2342662146766280102218291 3513993220149420153327437)
                    ·
                      refine ⟨1317747457556032557497789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3513993220149420153327437 1317747457556032557497789)
                      ·
                        rfl

theorem cell23_2566304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_2566304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566304 prefixEnd_2566304 := by exact prefixLift 2566304
  have htrace : WordTrace (prefixWord ++ tailWord_2566304) baseStart_2566304 baseEnd_2566304 := by
    simpa [prefixWord, tailWord_2566304, baseEnd_2566304] using wordTrace_append hprefix tailTrace_2566304
  have hstable : (prefixWord ++ tailWord_2566304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566304).length < 2 ^ (prefixWord ++ tailWord_2566304).sum := by decide
  have hdescent : baseEnd_2566304 < baseStart_2566304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566327 : List Nat := [1, 1, 3, 1, 4, 2, 1, 3, 1, 4, 2]
def baseStart_2566327 : Nat := 118140960795 + 2566327 * 2 ^ 59
def prefixEnd_2566327 : Nat := 4983230072969 + 3 ^ 40 * 2566327 * 2
def baseEnd_2566327 : Nat := 1317759267611085967510183

theorem tailTrace_2566327 : CollatzResearch.WordTrace tailWord_2566327 prefixEnd_2566327 1317759267611085967510183 := by
  unfold tailWord_2566327
  simp only [CollatzResearch.WordTrace]
  refine ⟨93601635373643047602361235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62401090249095365068240823 93601635373643047602361235)
  ·
    refine ⟨140402453060464571403541853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93601635373643047602361235 140402453060464571403541853)
    ·
      refine ⟨52650919897674214276328195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140402453060464571403541853 52650919897674214276328195)
      ·
        refine ⟨78976379846511321414492293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52650919897674214276328195 78976379846511321414492293)
        ·
          refine ⟨14808071221220872765217305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78976379846511321414492293 14808071221220872765217305)
          ·
            refine ⟨11106053415915654573912979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14808071221220872765217305 11106053415915654573912979)
            ·
              refine ⟨16659080123873481860869469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11106053415915654573912979 16659080123873481860869469)
              ·
                refine ⟨6247155046452555697826051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16659080123873481860869469 6247155046452555697826051)
                ·
                  refine ⟨9370732569678833546739077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6247155046452555697826051 9370732569678833546739077)
                  ·
                    refine ⟨1757012356814781290013577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9370732569678833546739077 1757012356814781290013577)
                    ·
                      refine ⟨1317759267611085967510183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1757012356814781290013577 1317759267611085967510183)
                      ·
                        rfl

theorem cell23_2566327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 4, 2].length) (baseStart_2566327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566327 prefixEnd_2566327 := by exact prefixLift 2566327
  have htrace : WordTrace (prefixWord ++ tailWord_2566327) baseStart_2566327 baseEnd_2566327 := by
    simpa [prefixWord, tailWord_2566327, baseEnd_2566327] using wordTrace_append hprefix tailTrace_2566327
  have hstable : (prefixWord ++ tailWord_2566327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566327).length < 2 ^ (prefixWord ++ tailWord_2566327).sum := by decide
  have hdescent : baseEnd_2566327 < baseStart_2566327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
