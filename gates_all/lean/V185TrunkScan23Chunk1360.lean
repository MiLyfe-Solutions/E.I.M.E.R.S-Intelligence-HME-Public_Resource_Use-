import V185TrunkScan23Chunk1359

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8054093 : List Nat := [1, 6, 1, 3, 1, 1, 2, 2, 1, 1, 4]
def baseStart_8054093 : Nat := 118140960795 + 8054093 * 2 ^ 59
def prefixEnd_8054093 : Nat := 4983230072969 + 3 ^ 40 * 8054093 * 2
def baseEnd_8054093 : Nat := 4135620945012462057797407

theorem tailTrace_8054093 : CollatzResearch.WordTrace tailWord_8054093 prefixEnd_8054093 4135620945012462057797407 := by
  unfold tailWord_8054093
  simp only [CollatzResearch.WordTrace]
  refine ⟨293756904810404065418006933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195837936540269376945337955 293756904810404065418006933)
  ·
    refine ⟨13769854912987690566469075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 293756904810404065418006933 13769854912987690566469075)
    ·
      refine ⟨20654782369481535849703613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13769854912987690566469075 20654782369481535849703613)
      ·
        refine ⟨7745543388555575943638855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20654782369481535849703613 7745543388555575943638855)
        ·
          refine ⟨11618315082833363915458283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7745543388555575943638855 11618315082833363915458283)
          ·
            refine ⟨17427472624250045873187425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11618315082833363915458283 17427472624250045873187425)
            ·
              refine ⟨13070604468187534404890569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17427472624250045873187425 13070604468187534404890569)
              ·
                refine ⟨9802953351140650803667927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13070604468187534404890569 9802953351140650803667927)
                ·
                  refine ⟨14704430026710976205501891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9802953351140650803667927 14704430026710976205501891)
                  ·
                    refine ⟨22056645040066464308252837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14704430026710976205501891 22056645040066464308252837)
                    ·
                      refine ⟨4135620945012462057797407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22056645040066464308252837 4135620945012462057797407)
                      ·
                        rfl

theorem cell23_8054093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_8054093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054093 prefixEnd_8054093 := by exact prefixLift 8054093
  have htrace : WordTrace (prefixWord ++ tailWord_8054093) baseStart_8054093 baseEnd_8054093 := by
    simpa [prefixWord, tailWord_8054093, baseEnd_8054093] using wordTrace_append hprefix tailTrace_8054093
  have hstable : (prefixWord ++ tailWord_8054093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054093).length < 2 ^ (prefixWord ++ tailWord_8054093).sum := by decide
  have hdescent : baseEnd_8054093 < baseStart_8054093 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054105 : List Nat := [1, 2, 1, 2, 2, 2, 3, 1, 2, 2, 5]
def baseStart_8054105 : Nat := 118140960795 + 8054105 * 2 ^ 59
def prefixEnd_8054105 : Nat := 4983230072969 + 3 ^ 40 * 8054105 * 2
def baseEnd_8054105 : Nat := 4135627106780316010847351

theorem tailTrace_8054105 : CollatzResearch.WordTrace tailWord_8054105 prefixEnd_8054105 4135627106780316010847351 := by
  unfold tailWord_8054105
  simp only [CollatzResearch.WordTrace]
  refine ⟨293757342486360591467443769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195838228324240394311629179 293757342486360591467443769)
  ·
    refine ⟨220318006864770443600582827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293757342486360591467443769 220318006864770443600582827)
    ·
      refine ⟨330477010297155665400874241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220318006864770443600582827 330477010297155665400874241)
      ·
        refine ⟨247857757722866749050655681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330477010297155665400874241 247857757722866749050655681)
        ·
          refine ⟨185893318292150061787991761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247857757722866749050655681 185893318292150061787991761)
          ·
            refine ⟨139419988719112546340993821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185893318292150061787991761 139419988719112546340993821)
            ·
              refine ⟨52282495769667204877872683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139419988719112546340993821 52282495769667204877872683)
              ·
                refine ⟨78423743654500807316809025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52282495769667204877872683 78423743654500807316809025)
                ·
                  refine ⟨58817807740875605487606769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78423743654500807316809025 58817807740875605487606769)
                  ·
                    refine ⟨44113355805656704115705077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58817807740875605487606769 44113355805656704115705077)
                    ·
                      refine ⟨4135627106780316010847351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44113355805656704115705077 4135627106780316010847351)
                      ·
                        rfl

theorem cell23_8054105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_8054105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054105 prefixEnd_8054105 := by exact prefixLift 8054105
  have htrace : WordTrace (prefixWord ++ tailWord_8054105) baseStart_8054105 baseEnd_8054105 := by
    simpa [prefixWord, tailWord_8054105, baseEnd_8054105] using wordTrace_append hprefix tailTrace_8054105
  have hstable : (prefixWord ++ tailWord_8054105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054105).length < 2 ^ (prefixWord ++ tailWord_8054105).sum := by decide
  have hdescent : baseEnd_8054105 < baseStart_8054105 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054135 : List Nat := [1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 5]
def baseStart_8054135 : Nat := 118140960795 + 8054135 * 2 ^ 59
def prefixEnd_8054135 : Nat := 4983230072969 + 3 ^ 40 * 8054135 * 2
def baseEnd_8054135 : Nat := 4135642511199950893472213

theorem tailTrace_8054135 : CollatzResearch.WordTrace tailWord_8054135 prefixEnd_8054135 4135642511199950893472213 := by
  unfold tailWord_8054135
  simp only [CollatzResearch.WordTrace]
  refine ⟨293758436676251906591035859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195838957784167937727357239 293758436676251906591035859)
  ·
    refine ⟨440637655014377859886553789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293758436676251906591035859 440637655014377859886553789)
    ·
      refine ⟨165239120630391697457457671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 440637655014377859886553789 165239120630391697457457671)
      ·
        refine ⟨247858680945587546186186507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165239120630391697457457671 247858680945587546186186507)
        ·
          refine ⟨371788021418381319279279761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247858680945587546186186507 371788021418381319279279761)
          ·
            refine ⟨278841016063785989459459821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371788021418381319279279761 278841016063785989459459821)
            ·
              refine ⟨104565381023919746047297433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 278841016063785989459459821 104565381023919746047297433)
              ·
                refine ⟨78424035767939809535473075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104565381023919746047297433 78424035767939809535473075)
                ·
                  refine ⟨117636053651909714303209613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78424035767939809535473075 117636053651909714303209613)
                  ·
                    refine ⟨44113520119466142863703605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117636053651909714303209613 44113520119466142863703605)
                    ·
                      refine ⟨4135642511199950893472213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44113520119466142863703605 4135642511199950893472213)
                      ·
                        rfl

theorem cell23_8054135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_8054135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054135 prefixEnd_8054135 := by exact prefixLift 8054135
  have htrace : WordTrace (prefixWord ++ tailWord_8054135) baseStart_8054135 baseEnd_8054135 := by
    simpa [prefixWord, tailWord_8054135, baseEnd_8054135] using wordTrace_append hprefix tailTrace_8054135
  have hstable : (prefixWord ++ tailWord_8054135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054135).length < 2 ^ (prefixWord ++ tailWord_8054135).sum := by decide
  have hdescent : baseEnd_8054135 < baseStart_8054135 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054152 : List Nat := [2, 1, 3, 3, 1, 2, 1, 2, 2, 1, 5]
def baseStart_8054152 : Nat := 118140960795 + 8054152 * 2 ^ 59
def prefixEnd_8054152 : Nat := 4983230072969 + 3 ^ 40 * 8054152 * 2
def baseEnd_8054152 : Nat := 4135651240371077326959635

theorem tailTrace_8054152 : CollatzResearch.WordTrace tailWord_8054152 prefixEnd_8054152 4135651240371077326959635 := by
  unfold tailWord_8054152
  simp only [CollatzResearch.WordTrace]
  refine ⟨146879528358595159247202355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195839371144793545662936473 146879528358595159247202355)
  ·
    refine ⟨220319292537892738870803533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146879528358595159247202355 220319292537892738870803533)
    ·
      refine ⟨82619734701709777076551325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220319292537892738870803533 82619734701709777076551325)
      ·
        refine ⟨30982400513141166403706747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82619734701709777076551325 30982400513141166403706747)
        ·
          refine ⟨46473600769711749605560121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30982400513141166403706747 46473600769711749605560121)
          ·
            refine ⟨34855200577283812204170091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46473600769711749605560121 34855200577283812204170091)
            ·
              refine ⟨52282800865925718306255137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34855200577283812204170091 52282800865925718306255137)
              ·
                refine ⟨39212100649444288729691353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52282800865925718306255137 39212100649444288729691353)
                ·
                  refine ⟨29409075487083216547268515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39212100649444288729691353 29409075487083216547268515)
                  ·
                    refine ⟨44113613230624824820902773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29409075487083216547268515 44113613230624824820902773)
                    ·
                      refine ⟨4135651240371077326959635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44113613230624824820902773 4135651240371077326959635)
                      ·
                        rfl

theorem cell23_8054152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_8054152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054152 prefixEnd_8054152 := by exact prefixLift 8054152
  have htrace : WordTrace (prefixWord ++ tailWord_8054152) baseStart_8054152 baseEnd_8054152 := by
    simpa [prefixWord, tailWord_8054152, baseEnd_8054152] using wordTrace_append hprefix tailTrace_8054152
  have hstable : (prefixWord ++ tailWord_8054152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054152).length < 2 ^ (prefixWord ++ tailWord_8054152).sum := by decide
  have hdescent : baseEnd_8054152 < baseStart_8054152 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054153 : List Nat := [1, 2, 1, 1, 7, 2, 1, 2, 1, 3, 2]
def baseStart_8054153 : Nat := 118140960795 + 8054153 * 2 ^ 59
def prefixEnd_8054153 : Nat := 4983230072969 + 3 ^ 40 * 8054153 * 2
def baseEnd_8054153 : Nat := 4135651753851731823047131

theorem tailTrace_8054153 : CollatzResearch.WordTrace tailWord_8054153 prefixEnd_8054153 4135651753851731823047131 := by
  unfold tailWord_8054153
  simp only [CollatzResearch.WordTrace]
  refine ⟨293759093190186695665191113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195839395460124463776794075 293759093190186695665191113)
  ·
    refine ⟨220319319892640021748893335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293759093190186695665191113 220319319892640021748893335)
    ·
      refine ⟨330478979838960032623340003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220319319892640021748893335 330478979838960032623340003)
      ·
        refine ⟨495718469758440048935010005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330478979838960032623340003 495718469758440048935010005)
        ·
          refine ⟨11618401634963438646914297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 495718469758440048935010005 11618401634963438646914297)
          ·
            refine ⟨8713801226222578985185723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11618401634963438646914297 8713801226222578985185723)
            ·
              refine ⟨13070701839333868477778585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8713801226222578985185723 13070701839333868477778585)
              ·
                refine ⟨9803026379500401358333939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13070701839333868477778585 9803026379500401358333939)
                ·
                  refine ⟨14704539569250602037500909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9803026379500401358333939 14704539569250602037500909)
                  ·
                    refine ⟨5514202338468975764062841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14704539569250602037500909 5514202338468975764062841)
                    ·
                      refine ⟨4135651753851731823047131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5514202338468975764062841 4135651753851731823047131)
                      ·
                        rfl

theorem cell23_8054153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 3, 2].length) (baseStart_8054153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054153 prefixEnd_8054153 := by exact prefixLift 8054153
  have htrace : WordTrace (prefixWord ++ tailWord_8054153) baseStart_8054153 baseEnd_8054153 := by
    simpa [prefixWord, tailWord_8054153, baseEnd_8054153] using wordTrace_append hprefix tailTrace_8054153
  have hstable : (prefixWord ++ tailWord_8054153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054153).length < 2 ^ (prefixWord ++ tailWord_8054153).sum := by decide
  have hdescent : baseEnd_8054153 < baseStart_8054153 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054155 : List Nat := [1, 1, 1, 1, 4, 3, 2, 1, 9]
def baseStart_8054155 : Nat := 118140960795 + 8054155 * 2 ^ 59
def prefixEnd_8054155 : Nat := 4983230072969 + 3 ^ 40 * 8054155 * 2
def baseEnd_8054155 : Nat := 459516975645893423913569

theorem tailTrace_8054155 : CollatzResearch.WordTrace tailWord_8054155 prefixEnd_8054155 459516975645893423913569 := by
  unfold tailWord_8054155
  simp only [CollatzResearch.WordTrace]
  refine ⟨293759166136179450006763919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195839444090786300004509279 293759166136179450006763919)
  ·
    refine ⟨440638749204269175010145879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293759166136179450006763919 440638749204269175010145879)
    ·
      refine ⟨660958123806403762515218819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440638749204269175010145879 660958123806403762515218819)
      ·
        refine ⟨991437185709605643772828229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660958123806403762515218819 991437185709605643772828229)
        ·
          refine ⟨185894472320551058207405293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 991437185709605643772828229 185894472320551058207405293)
          ·
            refine ⟨69710427120206646827776985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185894472320551058207405293 69710427120206646827776985)
            ·
              refine ⟨52282820340154985120832739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69710427120206646827776985 52282820340154985120832739)
              ·
                refine ⟨78424230510232477681249109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52282820340154985120832739 78424230510232477681249109)
                ·
                  refine ⟨459516975645893423913569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 78424230510232477681249109 459516975645893423913569)
                  ·
                    rfl

theorem cell23_8054155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 9].length) (baseStart_8054155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054155 prefixEnd_8054155 := by exact prefixLift 8054155
  have htrace : WordTrace (prefixWord ++ tailWord_8054155) baseStart_8054155 baseEnd_8054155 := by
    simpa [prefixWord, tailWord_8054155, baseEnd_8054155] using wordTrace_append hprefix tailTrace_8054155
  have hstable : (prefixWord ++ tailWord_8054155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054155).length < 2 ^ (prefixWord ++ tailWord_8054155).sum := by decide
  have hdescent : baseEnd_8054155 < baseStart_8054155 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054183 : List Nat := [1, 1, 6, 1, 1, 1, 4, 2, 2, 2, 2]
def baseStart_8054183 : Nat := 118140960795 + 8054183 * 2 ^ 59
def prefixEnd_8054183 : Nat := 4983230072969 + 3 ^ 40 * 8054183 * 2
def baseEnd_8054183 : Nat := 4135667158271366705671993

theorem tailTrace_8054183 : CollatzResearch.WordTrace tailWord_8054183 prefixEnd_8054183 4135667158271366705671993 := by
  unfold tailWord_8054183
  simp only [CollatzResearch.WordTrace]
  refine ⟨293760187380078010788783203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195840124920052007192522135 293760187380078010788783203)
  ·
    refine ⟨440640281070117016183174805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293760187380078010788783203 440640281070117016183174805)
    ·
      refine ⟨20655013175161735133586319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 440640281070117016183174805 20655013175161735133586319)
      ·
        refine ⟨30982519762742602700379479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20655013175161735133586319 30982519762742602700379479)
        ·
          refine ⟨46473779644113904050569219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30982519762742602700379479 46473779644113904050569219)
          ·
            refine ⟨69710669466170856075853829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46473779644113904050569219 69710669466170856075853829)
            ·
              refine ⟨13070750524907035514222593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69710669466170856075853829 13070750524907035514222593)
              ·
                refine ⟨9803062893680276635666945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13070750524907035514222593 9803062893680276635666945)
                ·
                  refine ⟨7352297170260207476750209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9803062893680276635666945 7352297170260207476750209)
                  ·
                    refine ⟨5514222877695155607562657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7352297170260207476750209 5514222877695155607562657)
                    ·
                      refine ⟨4135667158271366705671993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5514222877695155607562657 4135667158271366705671993)
                      ·
                        rfl

theorem cell23_8054183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_8054183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054183 prefixEnd_8054183 := by exact prefixLift 8054183
  have htrace : WordTrace (prefixWord ++ tailWord_8054183) baseStart_8054183 baseEnd_8054183 := by
    simpa [prefixWord, tailWord_8054183, baseEnd_8054183] using wordTrace_append hprefix tailTrace_8054183
  have hstable : (prefixWord ++ tailWord_8054183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054183).length < 2 ^ (prefixWord ++ tailWord_8054183).sum := by decide
  have hdescent : baseEnd_8054183 < baseStart_8054183 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054185 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 5, 7]
def baseStart_8054185 : Nat := 118140960795 + 8054185 * 2 ^ 59
def prefixEnd_8054185 : Nat := 4983230072969 + 3 ^ 40 * 8054185 * 2
def baseEnd_8054185 : Nat := 1378556061744225232615661

theorem tailTrace_8054185 : CollatzResearch.WordTrace tailWord_8054185 prefixEnd_8054185 1378556061744225232615661 := by
  unfold tailWord_8054185
  simp only [CollatzResearch.WordTrace]
  refine ⟨293760260326070765130356009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195840173550713843420237339 293760260326070765130356009)
  ·
    refine ⟨220320195244553073847767007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293760260326070765130356009 220320195244553073847767007)
    ·
      refine ⟨330480292866829610771650511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220320195244553073847767007 330480292866829610771650511)
      ·
        refine ⟨495720439300244416157475767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330480292866829610771650511 495720439300244416157475767)
        ·
          refine ⟨743580658950366624236213651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495720439300244416157475767 743580658950366624236213651)
          ·
            refine ⟨1115370988425549936354320477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 743580658950366624236213651 1115370988425549936354320477)
            ·
              refine ⟨418264120659581226132870179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1115370988425549936354320477 418264120659581226132870179)
              ·
                refine ⟨627396180989371839199305269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418264120659581226132870179 627396180989371839199305269)
                ·
                  refine ⟨58818391967753609924934869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 627396180989371839199305269 58818391967753609924934869)
                  ·
                    refine ⟨1378556061744225232615661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58818391967753609924934869 1378556061744225232615661)
                    ·
                      rfl

theorem cell23_8054185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 7].length) (baseStart_8054185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054185 prefixEnd_8054185 := by exact prefixLift 8054185
  have htrace : WordTrace (prefixWord ++ tailWord_8054185) baseStart_8054185 baseEnd_8054185 := by
    simpa [prefixWord, tailWord_8054185, baseEnd_8054185] using wordTrace_append hprefix tailTrace_8054185
  have hstable : (prefixWord ++ tailWord_8054185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054185).length < 2 ^ (prefixWord ++ tailWord_8054185).sum := by decide
  have hdescent : baseEnd_8054185 < baseStart_8054185 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054239 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 4, 4, 2]
def baseStart_8054239 : Nat := 118140960795 + 8054239 * 2 ^ 59
def prefixEnd_8054239 : Nat := 4983230072969 + 3 ^ 40 * 8054239 * 2
def baseEnd_8054239 : Nat := 4135695913188018486571735

theorem tailTrace_8054239 : CollatzResearch.WordTrace tailWord_8054239 prefixEnd_8054239 4135695913188018486571735 := by
  unfold tailWord_8054239
  simp only [CollatzResearch.WordTrace]
  refine ⟨293762229867875132352821771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195841486578583421568547847 293762229867875132352821771)
  ·
    refine ⟨440643344801812698529232657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293762229867875132352821771 440643344801812698529232657)
    ·
      refine ⟨330482508601359523896924493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440643344801812698529232657 330482508601359523896924493)
      ·
        refine ⟨123930940725509821461346685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330482508601359523896924493 123930940725509821461346685)
        ·
          refine ⟨46474102772066183048005007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123930940725509821461346685 46474102772066183048005007)
          ·
            refine ⟨69711154158099274572007511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46474102772066183048005007 69711154158099274572007511)
            ·
              refine ⟨104566731237148911858011267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69711154158099274572007511 104566731237148911858011267)
              ·
                refine ⟨156850096855723367787016901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104566731237148911858011267 156850096855723367787016901)
                ·
                  refine ⟨29409393160448131460065669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156850096855723367787016901 29409393160448131460065669)
                  ·
                    refine ⟨5514261217584024648762313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29409393160448131460065669 5514261217584024648762313)
                    ·
                      refine ⟨4135695913188018486571735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5514261217584024648762313 4135695913188018486571735)
                      ·
                        rfl

theorem cell23_8054239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 4, 2].length) (baseStart_8054239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054239 prefixEnd_8054239 := by exact prefixLift 8054239
  have htrace : WordTrace (prefixWord ++ tailWord_8054239) baseStart_8054239 baseEnd_8054239 := by
    simpa [prefixWord, tailWord_8054239, baseEnd_8054239] using wordTrace_append hprefix tailTrace_8054239
  have hstable : (prefixWord ++ tailWord_8054239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054239).length < 2 ^ (prefixWord ++ tailWord_8054239).sum := by decide
  have hdescent : baseEnd_8054239 < baseStart_8054239 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054343 : List Nat := [1, 1, 4, 1, 5, 1, 3, 1, 1, 5]
def baseStart_8054343 : Nat := 118140960795 + 8054343 * 2 ^ 59
def prefixEnd_8054343 : Nat := 4983230072969 + 3 ^ 40 * 8054343 * 2
def baseEnd_8054343 : Nat := 1378583105058695359890419

theorem tailTrace_8054343 : CollatzResearch.WordTrace tailWord_8054343 prefixEnd_8054343 1378583105058695359890419 := by
  unfold tailWord_8054343
  simp only [CollatzResearch.WordTrace]
  refine ⟨293766023059498358114607683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195844015372998905409738455 293766023059498358114607683)
  ·
    refine ⟨440649034589247537171911525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293766023059498358114607683 440649034589247537171911525)
    ·
      refine ⟨82621693985483913219733411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 440649034589247537171911525 82621693985483913219733411)
      ·
        refine ⟨123932540978225869829600117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82621693985483913219733411 123932540978225869829600117)
        ·
          refine ⟨11618675716708675296525011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123932540978225869829600117 11618675716708675296525011)
          ·
            refine ⟨17428013575063012944787517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11618675716708675296525011 17428013575063012944787517)
            ·
              refine ⟨6535505090648629854295319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17428013575063012944787517 6535505090648629854295319)
              ·
                refine ⟨9803257635972944781442979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6535505090648629854295319 9803257635972944781442979)
                ·
                  refine ⟨14704886453959417172164469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9803257635972944781442979 14704886453959417172164469)
                  ·
                    refine ⟨1378583105058695359890419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14704886453959417172164469 1378583105058695359890419)
                    ·
                      rfl

theorem cell23_8054343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 1, 5].length) (baseStart_8054343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054343 prefixEnd_8054343 := by exact prefixLift 8054343
  have htrace : WordTrace (prefixWord ++ tailWord_8054343) baseStart_8054343 baseEnd_8054343 := by
    simpa [prefixWord, tailWord_8054343, baseEnd_8054343] using wordTrace_append hprefix tailTrace_8054343
  have hstable : (prefixWord ++ tailWord_8054343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054343).length < 2 ^ (prefixWord ++ tailWord_8054343).sum := by decide
  have hdescent : baseEnd_8054343 < baseStart_8054343 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054376 : List Nat := [2, 1, 4, 3, 1, 1, 1, 3, 1, 2, 4]
def baseStart_8054376 : Nat := 118140960795 + 8054376 * 2 ^ 59
def prefixEnd_8054376 : Nat := 4983230072969 + 3 ^ 40 * 8054376 * 2
def baseEnd_8054376 : Nat := 4135766260037684450558605

theorem tailTrace_8054376 : CollatzResearch.WordTrace tailWord_8054376 prefixEnd_8054376 4135766260037684450558605 := by
  unfold tailWord_8054376
  simp only [CollatzResearch.WordTrace]
  refine ⟨146883613334189402375279491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195844817778919203167039321 146883613334189402375279491)
  ·
    refine ⟨220325420001284103562919237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146883613334189402375279491 220325420001284103562919237)
    ·
      refine ⟨41311016250240769418047357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220325420001284103562919237 41311016250240769418047357)
      ·
        refine ⟨15491631093840288531767759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41311016250240769418047357 15491631093840288531767759)
        ·
          refine ⟨23237446640760432797651639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15491631093840288531767759 23237446640760432797651639)
          ·
            refine ⟨34856169961140649196477459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23237446640760432797651639 34856169961140649196477459)
            ·
              refine ⟨52284254941710973794716189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34856169961140649196477459 52284254941710973794716189)
              ·
                refine ⟨19606595603141615173018571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52284254941710973794716189 19606595603141615173018571)
                ·
                  refine ⟨29409893404712422759527857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19606595603141615173018571 29409893404712422759527857)
                  ·
                    refine ⟨22057420053534317069645893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29409893404712422759527857 22057420053534317069645893)
                    ·
                      refine ⟨4135766260037684450558605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22057420053534317069645893 4135766260037684450558605)
                      ·
                        rfl

theorem cell23_8054376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_8054376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054376 prefixEnd_8054376 := by exact prefixLift 8054376
  have htrace : WordTrace (prefixWord ++ tailWord_8054376) baseStart_8054376 baseEnd_8054376 := by
    simpa [prefixWord, tailWord_8054376, baseEnd_8054376] using wordTrace_append hprefix tailTrace_8054376
  have hstable : (prefixWord ++ tailWord_8054376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054376).length < 2 ^ (prefixWord ++ tailWord_8054376).sum := by decide
  have hdescent : baseEnd_8054376 < baseStart_8054376 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054386 : List Nat := [3, 2, 1, 2, 3, 2, 3, 7]
def baseStart_8054386 : Nat := 118140960795 + 8054386 * 2 ^ 59
def prefixEnd_8054386 : Nat := 4983230072969 + 3 ^ 40 * 8054386 * 2
def baseEnd_8054386 : Nat := 153176718327564052275317

theorem tailTrace_8054386 : CollatzResearch.WordTrace tailWord_8054386 prefixEnd_8054386 153176718327564052275317 := by
  unfold tailWord_8054386
  simp only [CollatzResearch.WordTrace]
  refine ⟨73441897849585644114605753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195845060932228384305615341 73441897849585644114605753)
  ·
    refine ⟨55081423387189233085954315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73441897849585644114605753 55081423387189233085954315)
    ·
      refine ⟨82622135080783849628931473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55081423387189233085954315 82622135080783849628931473)
      ·
        refine ⟨61966601310587887221698605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82622135080783849628931473 61966601310587887221698605)
        ·
          refine ⟨23237475491470457708136977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61966601310587887221698605 23237475491470457708136977)
          ·
            refine ⟨17428106618602843281102733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23237475491470457708136977 17428106618602843281102733)
            ·
              refine ⟨6535539981976066230413525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17428106618602843281102733 6535539981976066230413525)
              ·
                refine ⟨153176718327564052275317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6535539981976066230413525 153176718327564052275317)
                ·
                  rfl

theorem cell23_8054386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 7].length) (baseStart_8054386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054386 prefixEnd_8054386 := by exact prefixLift 8054386
  have htrace : WordTrace (prefixWord ++ tailWord_8054386) baseStart_8054386 baseEnd_8054386 := by
    simpa [prefixWord, tailWord_8054386, baseEnd_8054386] using wordTrace_append hprefix tailTrace_8054386
  have hstable : (prefixWord ++ tailWord_8054386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054386).length < 2 ^ (prefixWord ++ tailWord_8054386).sum := by decide
  have hdescent : baseEnd_8054386 < baseStart_8054386 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054396 : List Nat := [2, 2, 2, 1, 1, 2, 1, 4, 4, 1, 3]
def baseStart_8054396 : Nat := 118140960795 + 8054396 * 2 ^ 59
def prefixEnd_8054396 : Nat := 4983230072969 + 3 ^ 40 * 8054396 * 2
def baseEnd_8054396 : Nat := 4135776529650774372308513

theorem tailTrace_8054396 : CollatzResearch.WordTrace tailWord_8054396 prefixEnd_8054396 4135776529650774372308513 := by
  unfold tailWord_8054396
  simp only [CollatzResearch.WordTrace]
  refine ⟨146883978064153174083143521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195845304085537565444191361 146883978064153174083143521)
  ·
    refine ⟨110162983548114880562357641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146883978064153174083143521 110162983548114880562357641)
    ·
      refine ⟨82622237661086160421768231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110162983548114880562357641 82622237661086160421768231)
      ·
        refine ⟨123933356491629240632652347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82622237661086160421768231 123933356491629240632652347)
        ·
          refine ⟨185900034737443860948978521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123933356491629240632652347 185900034737443860948978521)
          ·
            refine ⟨139425026053082895711733891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185900034737443860948978521 139425026053082895711733891)
            ·
              refine ⟨209137539079624343567600837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139425026053082895711733891 209137539079624343567600837)
              ·
                refine ⟨39213288577429564418925157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 209137539079624343567600837 39213288577429564418925157)
                ·
                  refine ⟨7352491608268043328548467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39213288577429564418925157 7352491608268043328548467)
                  ·
                    refine ⟨11028737412402064992822701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7352491608268043328548467 11028737412402064992822701)
                    ·
                      refine ⟨4135776529650774372308513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11028737412402064992822701 4135776529650774372308513)
                      ·
                        rfl

theorem cell23_8054396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 4, 1, 3].length) (baseStart_8054396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054396 prefixEnd_8054396 := by exact prefixLift 8054396
  have htrace : WordTrace (prefixWord ++ tailWord_8054396) baseStart_8054396 baseEnd_8054396 := by
    simpa [prefixWord, tailWord_8054396, baseEnd_8054396] using wordTrace_append hprefix tailTrace_8054396
  have hstable : (prefixWord ++ tailWord_8054396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054396).length < 2 ^ (prefixWord ++ tailWord_8054396).sum := by decide
  have hdescent : baseEnd_8054396 < baseStart_8054396 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054397 : List Nat := [1, 4, 1, 1, 4, 2, 2, 3, 1, 2, 2]
def baseStart_8054397 : Nat := 118140960795 + 8054397 * 2 ^ 59
def prefixEnd_8054397 : Nat := 4983230072969 + 3 ^ 40 * 8054397 * 2
def baseEnd_8054397 : Nat := 4135777043131428868396009

theorem tailTrace_8054397 : CollatzResearch.WordTrace tailWord_8054397 prefixEnd_8054397 4135777043131428868396009 := by
  unfold tailWord_8054397
  simp only [CollatzResearch.WordTrace]
  refine ⟨293767992601302725337073445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195845328400868483558048963 293767992601302725337073445)
  ·
    refine ⟨55081498612744261000701271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293767992601302725337073445 55081498612744261000701271)
    ·
      refine ⟨82622247919116391501051907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55081498612744261000701271 82622247919116391501051907)
      ·
        refine ⟨123933371878674587251577861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82622247919116391501051907 123933371878674587251577861)
        ·
          refine ⟨23237507227251485109670849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123933371878674587251577861 23237507227251485109670849)
          ·
            refine ⟨17428130420438613832253137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23237507227251485109670849 17428130420438613832253137)
            ·
              refine ⟨13071097815328960374189853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17428130420438613832253137 13071097815328960374189853)
              ·
                refine ⟨4901661680748360140321195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13071097815328960374189853 4901661680748360140321195)
                ·
                  refine ⟨7352492521122540210481793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4901661680748360140321195 7352492521122540210481793)
                  ·
                    refine ⟨5514369390841905157861345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7352492521122540210481793 5514369390841905157861345)
                    ·
                      refine ⟨4135777043131428868396009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5514369390841905157861345 4135777043131428868396009)
                      ·
                        rfl

theorem cell23_8054397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 3, 1, 2, 2].length) (baseStart_8054397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054397 prefixEnd_8054397 := by exact prefixLift 8054397
  have htrace : WordTrace (prefixWord ++ tailWord_8054397) baseStart_8054397 baseEnd_8054397 := by
    simpa [prefixWord, tailWord_8054397, baseEnd_8054397] using wordTrace_append hprefix tailTrace_8054397
  have hstable : (prefixWord ++ tailWord_8054397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054397).length < 2 ^ (prefixWord ++ tailWord_8054397).sum := by decide
  have hdescent : baseEnd_8054397 < baseStart_8054397 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054430 : List Nat := [4, 3, 1, 1, 1, 4, 1, 1, 1, 3, 3]
def baseStart_8054430 : Nat := 118140960795 + 8054430 * 2 ^ 59
def prefixEnd_8054430 : Nat := 4983230072969 + 3 ^ 40 * 8054430 * 2
def baseEnd_8054430 : Nat := 4135793987993027239283357

theorem tailTrace_8054430 : CollatzResearch.WordTrace tailWord_8054430 prefixEnd_8054430 4135793987993027239283357 := by
  unfold tailWord_8054430
  simp only [CollatzResearch.WordTrace]
  refine ⟨36721149526272896496628093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195846130806788781315349829 36721149526272896496628093)
  ·
    refine ⟨13770431072352336186235535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36721149526272896496628093 13770431072352336186235535)
    ·
      refine ⟨20655646608528504279353303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13770431072352336186235535 20655646608528504279353303)
      ·
        refine ⟨30983469912792756419029955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20655646608528504279353303 30983469912792756419029955)
        ·
          refine ⟨46475204869189134628544933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30983469912792756419029955 46475204869189134628544933)
          ·
            refine ⟨8714100912972962742852175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46475204869189134628544933 8714100912972962742852175)
            ·
              refine ⟨13071151369459444114278263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8714100912972962742852175 13071151369459444114278263)
              ·
                refine ⟨19606727054189166171417395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13071151369459444114278263 19606727054189166171417395)
                ·
                  refine ⟨29410090581283749257126093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19606727054189166171417395 29410090581283749257126093)
                  ·
                    refine ⟨11028783967981405971422285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29410090581283749257126093 11028783967981405971422285)
                    ·
                      refine ⟨4135793987993027239283357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11028783967981405971422285 4135793987993027239283357)
                      ·
                        rfl

theorem cell23_8054430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_8054430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054430 prefixEnd_8054430 := by exact prefixLift 8054430
  have htrace : WordTrace (prefixWord ++ tailWord_8054430) baseStart_8054430 baseEnd_8054430 := by
    simpa [prefixWord, tailWord_8054430, baseEnd_8054430] using wordTrace_append hprefix tailTrace_8054430
  have hstable : (prefixWord ++ tailWord_8054430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054430).length < 2 ^ (prefixWord ++ tailWord_8054430).sum := by decide
  have hdescent : baseEnd_8054430 < baseStart_8054430 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054506 : List Nat := [3, 1, 3, 1, 1, 1, 3, 3, 2, 5]
def baseStart_8054506 : Nat := 118140960795 + 8054506 * 2 ^ 59
def prefixEnd_8054506 : Nat := 4983230072969 + 3 ^ 40 * 8054506 * 2
def baseEnd_8054506 : Nat := 1378611004174256313977669

theorem tailTrace_8054506 : CollatzResearch.WordTrace tailWord_8054506 prefixEnd_8054506 1378611004174256313977669 := by
  unfold tailWord_8054506
  simp only [CollatzResearch.WordTrace]
  refine ⟨73442992039476959238197843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195847978771938557968527581 73442992039476959238197843)
  ·
    refine ⟨110164488059215438857296765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73442992039476959238197843 110164488059215438857296765)
    ·
      refine ⟨41311683022205789571486287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110164488059215438857296765 41311683022205789571486287)
      ·
        refine ⟨61967524533308684357229431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41311683022205789571486287 61967524533308684357229431)
        ·
          refine ⟨92951286799963026535844147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61967524533308684357229431 92951286799963026535844147)
          ·
            refine ⟨139426930199944539803766221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92951286799963026535844147 139426930199944539803766221)
            ·
              refine ⟨52285098824979202426412333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139426930199944539803766221 52285098824979202426412333)
              ·
                refine ⟨19606912059367200909904625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52285098824979202426412333 19606912059367200909904625)
                ·
                  refine ⟨14705184044525400682428469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19606912059367200909904625 14705184044525400682428469)
                  ·
                    refine ⟨1378611004174256313977669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14705184044525400682428469 1378611004174256313977669)
                    ·
                      rfl

theorem cell23_8054506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_8054506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054506 prefixEnd_8054506 := by exact prefixLift 8054506
  have htrace : WordTrace (prefixWord ++ tailWord_8054506) baseStart_8054506 baseEnd_8054506 := by
    simpa [prefixWord, tailWord_8054506, baseEnd_8054506] using wordTrace_append hprefix tailTrace_8054506
  have hstable : (prefixWord ++ tailWord_8054506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054506).length < 2 ^ (prefixWord ++ tailWord_8054506).sum := by decide
  have hdescent : baseEnd_8054506 < baseStart_8054506 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054563 : List Nat := [1, 1, 1, 4, 2, 1, 5, 1, 2, 2, 3]
def baseStart_8054563 : Nat := 118140960795 + 8054563 * 2 ^ 59
def prefixEnd_8054563 : Nat := 4983230072969 + 3 ^ 40 * 8054563 * 2
def baseEnd_8054563 : Nat := 4135862280920075218920245

theorem tailTrace_8054563 : CollatzResearch.WordTrace tailWord_8054563 prefixEnd_8054563 4135862280920075218920245 := by
  unfold tailWord_8054563
  simp only [CollatzResearch.WordTrace]
  refine ⟨293774047118701335687616343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195849364745800890458410895 293774047118701335687616343)
  ·
    refine ⟨440661070678052003531424515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293774047118701335687616343 440661070678052003531424515)
    ·
      refine ⟨660991606017078005297136773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440661070678052003531424515 660991606017078005297136773)
      ·
        refine ⟨123935926128202125993213145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 660991606017078005297136773 123935926128202125993213145)
        ·
          refine ⟨92951944596151594494909859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123935926128202125993213145 92951944596151594494909859)
          ·
            refine ⟨139427916894227391742364789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92951944596151594494909859 139427916894227391742364789)
            ·
              refine ⟨13071367208833817975846699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 139427916894227391742364789 13071367208833817975846699)
              ·
                refine ⟨19607050813250726963770049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13071367208833817975846699 19607050813250726963770049)
                ·
                  refine ⟨14705288109938045222827537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19607050813250726963770049 14705288109938045222827537)
                  ·
                    refine ⟨11028966082453533917120653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14705288109938045222827537 11028966082453533917120653)
                    ·
                      refine ⟨4135862280920075218920245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11028966082453533917120653 4135862280920075218920245)
                      ·
                        rfl

theorem cell23_8054563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 2, 3].length) (baseStart_8054563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054563 prefixEnd_8054563 := by exact prefixLift 8054563
  have htrace : WordTrace (prefixWord ++ tailWord_8054563) baseStart_8054563 baseEnd_8054563 := by
    simpa [prefixWord, tailWord_8054563, baseEnd_8054563] using wordTrace_append hprefix tailTrace_8054563
  have hstable : (prefixWord ++ tailWord_8054563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054563).length < 2 ^ (prefixWord ++ tailWord_8054563).sum := by decide
  have hdescent : baseEnd_8054563 < baseStart_8054563 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054569 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 3, 1, 8]
def baseStart_8054569 : Nat := 118140960795 + 8054569 * 2 ^ 59
def prefixEnd_8054569 : Nat := 4983230072969 + 3 ^ 40 * 8054569 * 2
def baseEnd_8054569 : Nat := 4135865361804002195445217

theorem tailTrace_8054569 : CollatzResearch.WordTrace tailWord_8054569 prefixEnd_8054569 4135865361804002195445217 := by
  unfold tailWord_8054569
  simp only [CollatzResearch.WordTrace]
  refine ⟨293774265956679598712334761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195849510637786399141556507 293774265956679598712334761)
  ·
    refine ⟨220330699467509699034251071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293774265956679598712334761 220330699467509699034251071)
    ·
      refine ⟨330496049201264548551376607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220330699467509699034251071 330496049201264548551376607)
      ·
        refine ⟨495744073801896822827064911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330496049201264548551376607 495744073801896822827064911)
        ·
          refine ⟨743616110702845234240597367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495744073801896822827064911 743616110702845234240597367)
          ·
            refine ⟨1115424166054267851360896051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 743616110702845234240597367 1115424166054267851360896051)
            ·
              refine ⟨1673136249081401777041344077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1115424166054267851360896051 1673136249081401777041344077)
              ·
                refine ⟨627426093405525666390504029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1673136249081401777041344077 627426093405525666390504029)
                ·
                  refine ⟨235284785027072124896439011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 627426093405525666390504029 235284785027072124896439011)
                  ·
                    refine ⟨352927177540608187344658517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 235284785027072124896439011 352927177540608187344658517)
                    ·
                      refine ⟨4135865361804002195445217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 352927177540608187344658517 4135865361804002195445217)
                      ·
                        rfl

theorem cell23_8054569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 1, 8].length) (baseStart_8054569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054569 prefixEnd_8054569 := by exact prefixLift 8054569
  have htrace : WordTrace (prefixWord ++ tailWord_8054569) baseStart_8054569 baseEnd_8054569 := by
    simpa [prefixWord, tailWord_8054569, baseEnd_8054569] using wordTrace_append hprefix tailTrace_8054569
  have hstable : (prefixWord ++ tailWord_8054569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054569).length < 2 ^ (prefixWord ++ tailWord_8054569).sum := by decide
  have hdescent : baseEnd_8054569 < baseStart_8054569 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054586 : List Nat := [3, 1, 1, 1, 5, 1, 1, 1, 1, 2, 6]
def baseStart_8054586 : Nat := 118140960795 + 8054586 * 2 ^ 59
def prefixEnd_8054586 : Nat := 4983230072969 + 3 ^ 40 * 8054586 * 2
def baseEnd_8054586 : Nat := 4135874090975128628932639

theorem tailTrace_8054586 : CollatzResearch.WordTrace tailWord_8054586 prefixEnd_8054586 4135874090975128628932639 := by
  unfold tailWord_8054586
  simp only [CollatzResearch.WordTrace]
  refine ⟨73443721499404502653925903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195849923998412007077135741 73443721499404502653925903)
  ·
    refine ⟨110165582249106753980888855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73443721499404502653925903 110165582249106753980888855)
    ·
      refine ⟨165248373373660130971333283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110165582249106753980888855 165248373373660130971333283)
      ·
        refine ⟨247872560060490196456999925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165248373373660130971333283 247872560060490196456999925)
        ·
          refine ⟨23238052505670955917843743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 247872560060490196456999925 23238052505670955917843743)
          ·
            refine ⟨34857078758506433876765615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23238052505670955917843743 34857078758506433876765615)
            ·
              refine ⟨52285618137759650815148423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34857078758506433876765615 52285618137759650815148423)
              ·
                refine ⟨78428427206639476222722635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52285618137759650815148423 78428427206639476222722635)
                ·
                  refine ⟨117642640809959214334083953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78428427206639476222722635 117642640809959214334083953)
                  ·
                    refine ⟨88231980607469410750562965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117642640809959214334083953 88231980607469410750562965)
                    ·
                      refine ⟨4135874090975128628932639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88231980607469410750562965 4135874090975128628932639)
                      ·
                        rfl

theorem cell23_8054586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 2, 6].length) (baseStart_8054586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054586 prefixEnd_8054586 := by exact prefixLift 8054586
  have htrace : WordTrace (prefixWord ++ tailWord_8054586) baseStart_8054586 baseEnd_8054586 := by
    simpa [prefixWord, tailWord_8054586, baseEnd_8054586] using wordTrace_append hprefix tailTrace_8054586
  have hstable : (prefixWord ++ tailWord_8054586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054586).length < 2 ^ (prefixWord ++ tailWord_8054586).sum := by decide
  have hdescent : baseEnd_8054586 < baseStart_8054586 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054610 : List Nat := [3, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3]
def baseStart_8054610 : Nat := 118140960795 + 8054610 * 2 ^ 59
def prefixEnd_8054610 : Nat := 4983230072969 + 3 ^ 40 * 8054610 * 2
def baseEnd_8054610 : Nat := 4135886414510836535032529

theorem tailTrace_8054610 : CollatzResearch.WordTrace tailWord_8054610 prefixEnd_8054610 4135886414510836535032529 := by
  unfold tailWord_8054610
  simp only [CollatzResearch.WordTrace]
  refine ⟨73443940337382765678644321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195850507566354041809718189 73443940337382765678644321)
  ·
    refine ⟨55082955253037074258983241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73443940337382765678644321 55082955253037074258983241)
    ·
      refine ⟨41312216439777805694237431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55082955253037074258983241 41312216439777805694237431)
      ·
        refine ⟨61968324659666708541356147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41312216439777805694237431 61968324659666708541356147)
        ·
          refine ⟨92952486989500062812034221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61968324659666708541356147 92952486989500062812034221)
          ·
            refine ⟨34857182621062523554512833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92952486989500062812034221 34857182621062523554512833)
            ·
              refine ⟨26142886965796892665884625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34857182621062523554512833 26142886965796892665884625)
              ·
                refine ⟨19607165224347669499413469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26142886965796892665884625 19607165224347669499413469)
                ·
                  refine ⟨7352686959130376062280051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19607165224347669499413469 7352686959130376062280051)
                  ·
                    refine ⟨11029030438695564093420077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7352686959130376062280051 11029030438695564093420077)
                    ·
                      refine ⟨4135886414510836535032529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11029030438695564093420077 4135886414510836535032529)
                      ·
                        rfl

theorem cell23_8054610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_8054610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054610 prefixEnd_8054610 := by exact prefixLift 8054610
  have htrace : WordTrace (prefixWord ++ tailWord_8054610) baseStart_8054610 baseEnd_8054610 := by
    simpa [prefixWord, tailWord_8054610, baseEnd_8054610] using wordTrace_append hprefix tailTrace_8054610
  have hstable : (prefixWord ++ tailWord_8054610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054610).length < 2 ^ (prefixWord ++ tailWord_8054610).sum := by decide
  have hdescent : baseEnd_8054610 < baseStart_8054610 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054613 : List Nat := [1, 3, 2, 2, 2, 2, 1, 4, 1, 5]
def baseStart_8054613 : Nat := 118140960795 + 8054613 * 2 ^ 59
def prefixEnd_8054613 : Nat := 4983230072969 + 3 ^ 40 * 8054613 * 2
def baseEnd_8054613 : Nat := 1378629318317600007765005

theorem tailTrace_8054613 : CollatzResearch.WordTrace tailWord_8054613 prefixEnd_8054613 1378629318317600007765005 := by
  unfold tailWord_8054613
  simp only [CollatzResearch.WordTrace]
  refine ⟨293775870768520194226936493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195850580512346796151290995 293775870768520194226936493)
  ·
    refine ⟨110165951538195072835101185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293775870768520194226936493 110165951538195072835101185)
    ·
      refine ⟨82624463653646304626325889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110165951538195072835101185 82624463653646304626325889)
      ·
        refine ⟨61968347740234728469744417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82624463653646304626325889 61968347740234728469744417)
        ·
          refine ⟨46476260805176046352308313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61968347740234728469744417 46476260805176046352308313)
          ·
            refine ⟨34857195603882034764231235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46476260805176046352308313 34857195603882034764231235)
            ·
              refine ⟨52285793405823052146346853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34857195603882034764231235 52285793405823052146346853)
              ·
                refine ⟨9803586263591822277440035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52285793405823052146346853 9803586263591822277440035)
                ·
                  refine ⟨14705379395387733416160053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9803586263591822277440035 14705379395387733416160053)
                  ·
                    refine ⟨1378629318317600007765005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14705379395387733416160053 1378629318317600007765005)
                    ·
                      rfl

theorem cell23_8054613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 5].length) (baseStart_8054613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054613 prefixEnd_8054613 := by exact prefixLift 8054613
  have htrace : WordTrace (prefixWord ++ tailWord_8054613) baseStart_8054613 baseEnd_8054613 := by
    simpa [prefixWord, tailWord_8054613, baseEnd_8054613] using wordTrace_append hprefix tailTrace_8054613
  have hstable : (prefixWord ++ tailWord_8054613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054613).length < 2 ^ (prefixWord ++ tailWord_8054613).sum := by decide
  have hdescent : baseEnd_8054613 < baseStart_8054613 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054643 : List Nat := [1, 1, 1, 2, 2, 1, 3, 6, 2, 4]
def baseStart_8054643 : Nat := 118140960795 + 8054643 * 2 ^ 59
def prefixEnd_8054643 : Nat := 4983230072969 + 3 ^ 40 * 8054643 * 2
def baseEnd_8054643 : Nat := 1378634453124144968639959

theorem tailTrace_8054643 : CollatzResearch.WordTrace tailWord_8054643 prefixEnd_8054643 1378634453124144968639959 := by
  unfold tailWord_8054643
  simp only [CollatzResearch.WordTrace]
  refine ⟨293776964958411509350528583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195851309972274339567019055 293776964958411509350528583)
  ·
    refine ⟨440665447437617264025792875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293776964958411509350528583 440665447437617264025792875)
    ·
      refine ⟨660998171156425896038689313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440665447437617264025792875 660998171156425896038689313)
      ·
        refine ⟨495748628367319422029016985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 660998171156425896038689313 495748628367319422029016985)
        ·
          refine ⟨371811471275489566521762739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 495748628367319422029016985 371811471275489566521762739)
          ·
            refine ⟨557717206913234349782644109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371811471275489566521762739 557717206913234349782644109)
            ·
              refine ⟨209143952592462881168491541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 557717206913234349782644109 209143952592462881168491541)
              ·
                refine ⟨9803622777771697554773041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 209143952592462881168491541 9803622777771697554773041)
                ·
                  refine ⟨7352717083328773166079781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9803622777771697554773041 7352717083328773166079781)
                  ·
                    refine ⟨1378634453124144968639959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7352717083328773166079781 1378634453124144968639959)
                    ·
                      rfl

theorem cell23_8054643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 2, 4].length) (baseStart_8054643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054643 prefixEnd_8054643 := by exact prefixLift 8054643
  have htrace : WordTrace (prefixWord ++ tailWord_8054643) baseStart_8054643 baseEnd_8054643 := by
    simpa [prefixWord, tailWord_8054643, baseEnd_8054643] using wordTrace_append hprefix tailTrace_8054643
  have hstable : (prefixWord ++ tailWord_8054643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054643).length < 2 ^ (prefixWord ++ tailWord_8054643).sum := by decide
  have hdescent : baseEnd_8054643 < baseStart_8054643 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054653 : List Nat := [1, 4, 1, 1, 2, 1, 1, 4, 3, 2, 3]
def baseStart_8054653 : Nat := 118140960795 + 8054653 * 2 ^ 59
def prefixEnd_8054653 : Nat := 4983230072969 + 3 ^ 40 * 8054653 * 2
def baseEnd_8054653 : Nat := 4135908494178979866794831

theorem tailTrace_8054653 : CollatzResearch.WordTrace tailWord_8054653 prefixEnd_8054653 4135908494178979866794831 := by
  unfold tailWord_8054653
  simp only [CollatzResearch.WordTrace]
  refine ⟨293777329688375281058392613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195851553125583520705595075 293777329688375281058392613)
  ·
    refine ⟨55083249316570365198448615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293777329688375281058392613 55083249316570365198448615)
    ·
      refine ⟨82624873974855547797672923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55083249316570365198448615 82624873974855547797672923)
      ·
        refine ⟨123937310962283321696509385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82624873974855547797672923 123937310962283321696509385)
        ·
          refine ⟨92952983221712491272382039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123937310962283321696509385 92952983221712491272382039)
          ·
            refine ⟨139429474832568736908573059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92952983221712491272382039 139429474832568736908573059)
            ·
              refine ⟨209144212248853105362859589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139429474832568736908573059 209144212248853105362859589)
              ·
                refine ⟨39214539796659957255536173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 209144212248853105362859589 39214539796659957255536173)
                ·
                  refine ⟨14705452423747483970826065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39214539796659957255536173 14705452423747483970826065)
                  ·
                    refine ⟨11029089317810612978119549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14705452423747483970826065 11029089317810612978119549)
                    ·
                      refine ⟨4135908494178979866794831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11029089317810612978119549 4135908494178979866794831)
                      ·
                        rfl

theorem cell23_8054653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_8054653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054653 prefixEnd_8054653 := by exact prefixLift 8054653
  have htrace : WordTrace (prefixWord ++ tailWord_8054653) baseStart_8054653 baseEnd_8054653 := by
    simpa [prefixWord, tailWord_8054653, baseEnd_8054653] using wordTrace_append hprefix tailTrace_8054653
  have hstable : (prefixWord ++ tailWord_8054653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054653).length < 2 ^ (prefixWord ++ tailWord_8054653).sum := by decide
  have hdescent : baseEnd_8054653 < baseStart_8054653 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054656 : List Nat := [2, 1, 1, 2, 1, 2, 6, 8]
def baseStart_8054656 : Nat := 118140960795 + 8054656 * 2 ^ 59
def prefixEnd_8054656 : Nat := 4983230072969 + 3 ^ 40 * 8054656 * 2
def baseEnd_8054656 : Nat := 153181853134109013150271

theorem tailTrace_8054656 : CollatzResearch.WordTrace tailWord_8054656 prefixEnd_8054656 153181853134109013150271 := by
  unfold tailWord_8054656
  simp only [CollatzResearch.WordTrace]
  refine ⟨146888719553682206285375911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195851626071576275047167881 146888719553682206285375911)
  ·
    refine ⟨220333079330523309428063867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146888719553682206285375911 220333079330523309428063867)
    ·
      refine ⟨330499618995784964142095801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220333079330523309428063867 330499618995784964142095801)
      ·
        refine ⟨247874714246838723106571851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330499618995784964142095801 247874714246838723106571851)
        ·
          refine ⟨371812071370258084659857777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247874714246838723106571851 371812071370258084659857777)
          ·
            refine ⟨278859053527693563494893333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371812071370258084659857777 278859053527693563494893333)
            ·
              refine ⟨13071518134110635788823125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 278859053527693563494893333 13071518134110635788823125)
              ·
                refine ⟨153181853134109013150271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13071518134110635788823125 153181853134109013150271)
                ·
                  rfl

theorem cell23_8054656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 8].length) (baseStart_8054656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054656 prefixEnd_8054656 := by exact prefixLift 8054656
  have htrace : WordTrace (prefixWord ++ tailWord_8054656) baseStart_8054656 baseEnd_8054656 := by
    simpa [prefixWord, tailWord_8054656, baseEnd_8054656] using wordTrace_append hprefix tailTrace_8054656
  have hstable : (prefixWord ++ tailWord_8054656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054656).length < 2 ^ (prefixWord ++ tailWord_8054656).sum := by decide
  have hdescent : baseEnd_8054656 < baseStart_8054656 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054687 : List Nat := [1, 1, 2, 5, 4, 1, 1, 1, 1, 1, 5]
def baseStart_8054687 : Nat := 118140960795 + 8054687 * 2 ^ 59
def prefixEnd_8054687 : Nat := 4983230072969 + 3 ^ 40 * 8054687 * 2
def baseEnd_8054687 : Nat := 4135925952521232733769675

theorem tailTrace_8054687 : CollatzResearch.WordTrace tailWord_8054687 prefixEnd_8054687 4135925952521232733769675 := by
  unfold tailWord_8054687
  simp only [CollatzResearch.WordTrace]
  refine ⟨293778569770252104865130315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195852379846834736576753543 293778569770252104865130315)
  ·
    refine ⟨440667854655378157297695473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293778569770252104865130315 440667854655378157297695473)
    ·
      refine ⟨330500890991533617973271605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440667854655378157297695473 330500890991533617973271605)
      ·
        refine ⟨30984458530456276684994213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 330500890991533617973271605 30984458530456276684994213)
        ·
          refine ⟨5809585974460551878436415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30984458530456276684994213 5809585974460551878436415)
          ·
            refine ⟨8714378961690827817654623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5809585974460551878436415 8714378961690827817654623)
            ·
              refine ⟨13071568442536241726481935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8714378961690827817654623 13071568442536241726481935)
              ·
                refine ⟨19607352663804362589722903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13071568442536241726481935 19607352663804362589722903)
                ·
                  refine ⟨29411028995706543884584355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19607352663804362589722903 29411028995706543884584355)
                  ·
                    refine ⟨44116543493559815826876533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29411028995706543884584355 44116543493559815826876533)
                    ·
                      refine ⟨4135925952521232733769675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44116543493559815826876533 4135925952521232733769675)
                      ·
                        rfl

theorem cell23_8054687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_8054687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054687 prefixEnd_8054687 := by exact prefixLift 8054687
  have htrace : WordTrace (prefixWord ++ tailWord_8054687) baseStart_8054687 baseEnd_8054687 := by
    simpa [prefixWord, tailWord_8054687, baseEnd_8054687] using wordTrace_append hprefix tailTrace_8054687
  have hstable : (prefixWord ++ tailWord_8054687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054687).length < 2 ^ (prefixWord ++ tailWord_8054687).sum := by decide
  have hdescent : baseEnd_8054687 < baseStart_8054687 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054717 : List Nat := [1, 4, 1, 2, 3, 1, 2, 3, 2, 1, 3]
def baseStart_8054717 : Nat := 118140960795 + 8054717 * 2 ^ 59
def prefixEnd_8054717 : Nat := 4983230072969 + 3 ^ 40 * 8054717 * 2
def baseEnd_8054717 : Nat := 4135941356940867616394537

theorem tailTrace_8054717 : CollatzResearch.WordTrace tailWord_8054717 prefixEnd_8054717 4135941356940867616394537 := by
  unfold tailWord_8054717
  simp only [CollatzResearch.WordTrace]
  refine ⟨293779663960143419988722405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195853109306762279992481603 293779663960143419988722405)
  ·
    refine ⟨55083686992526891247885451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293779663960143419988722405 55083686992526891247885451)
    ·
      refine ⟨82625530488790336871828177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55083686992526891247885451 82625530488790336871828177)
      ·
        refine ⟨61969147866592752653871133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82625530488790336871828177 61969147866592752653871133)
        ·
          refine ⟨23238430449972282245201675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61969147866592752653871133 23238430449972282245201675)
          ·
            refine ⟨34857645674958423367802513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23238430449972282245201675 34857645674958423367802513)
            ·
              refine ⟨26143234256218817525851885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34857645674958423367802513 26143234256218817525851885)
              ·
                refine ⟨9803712846082056572194457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26143234256218817525851885 9803712846082056572194457)
                ·
                  refine ⟨7352784634561542429145843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9803712846082056572194457 7352784634561542429145843)
                  ·
                    refine ⟨11029176951842313643718765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7352784634561542429145843 11029176951842313643718765)
                    ·
                      refine ⟨4135941356940867616394537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11029176951842313643718765 4135941356940867616394537)
                      ·
                        rfl

theorem cell23_8054717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_8054717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054717 prefixEnd_8054717 := by exact prefixLift 8054717
  have htrace : WordTrace (prefixWord ++ tailWord_8054717) baseStart_8054717 baseEnd_8054717 := by
    simpa [prefixWord, tailWord_8054717, baseEnd_8054717] using wordTrace_append hprefix tailTrace_8054717
  have hstable : (prefixWord ++ tailWord_8054717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054717).length < 2 ^ (prefixWord ++ tailWord_8054717).sum := by decide
  have hdescent : baseEnd_8054717 < baseStart_8054717 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054753 : List Nat := [1, 2, 3, 1, 2, 1, 3, 2, 2, 2, 4]
def baseStart_8054753 : Nat := 118140960795 + 8054753 * 2 ^ 59
def prefixEnd_8054753 : Nat := 4983230072969 + 3 ^ 40 * 8054753 * 2
def baseEnd_8054753 : Nat := 4135959842244429475544371

theorem tailTrace_8054753 : CollatzResearch.WordTrace tailWord_8054753 prefixEnd_8054753 4135959842244429475544371 := by
  unfold tailWord_8054753
  simp only [CollatzResearch.WordTrace]
  refine ⟨293780976988012998137032913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195853984658675332091355275 293780976988012998137032913)
  ·
    refine ⟨220335732741009748602774685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293780976988012998137032913 220335732741009748602774685)
    ·
      refine ⟨82625899777878655726040507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220335732741009748602774685 82625899777878655726040507)
      ·
        refine ⟨123938849666817983589060761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82625899777878655726040507 123938849666817983589060761)
        ·
          refine ⟨92954137250113487691795571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123938849666817983589060761 92954137250113487691795571)
          ·
            refine ⟨139431205875170231537693357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92954137250113487691795571 139431205875170231537693357)
            ·
              refine ⟨52286702203188836826635009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139431205875170231537693357 52286702203188836826635009)
              ·
                refine ⟨39215026652391627619976257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52286702203188836826635009 39215026652391627619976257)
                ·
                  refine ⟨29411269989293720714982193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39215026652391627619976257 29411269989293720714982193)
                  ·
                    refine ⟨22058452491970290536236645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29411269989293720714982193 22058452491970290536236645)
                    ·
                      refine ⟨4135959842244429475544371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22058452491970290536236645 4135959842244429475544371)
                      ·
                        rfl

theorem cell23_8054753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_8054753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054753 prefixEnd_8054753 := by exact prefixLift 8054753
  have htrace : WordTrace (prefixWord ++ tailWord_8054753) baseStart_8054753 baseEnd_8054753 := by
    simpa [prefixWord, tailWord_8054753, baseEnd_8054753] using wordTrace_append hprefix tailTrace_8054753
  have hstable : (prefixWord ++ tailWord_8054753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054753).length < 2 ^ (prefixWord ++ tailWord_8054753).sum := by decide
  have hdescent : baseEnd_8054753 < baseStart_8054753 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054810 : List Nat := [3, 1, 1, 3, 1, 4, 1, 2, 2, 5]
def baseStart_8054810 : Nat := 118140960795 + 8054810 * 2 ^ 59
def prefixEnd_8054810 : Nat := 4983230072969 + 3 ^ 40 * 8054810 * 2
def baseEnd_8054810 : Nat := 1378663036880578584177203

theorem tailTrace_8054810 : CollatzResearch.WordTrace tailWord_8054810 prefixEnd_8054810 1378663036880578584177203 := by
  unfold tailWord_8054810
  simp only [CollatzResearch.WordTrace]
  refine ⟨73445763987201624217964471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195855370632537664581238589 73445763987201624217964471)
  ·
    refine ⟨110168645980802436326946707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73445763987201624217964471 110168645980802436326946707)
    ·
      refine ⟨165252968971203654490420061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110168645980802436326946707 165252968971203654490420061)
      ·
        refine ⟨61969863364201370433907523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165252968971203654490420061 61969863364201370433907523)
        ·
          refine ⟨92954795046302055650861285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61969863364201370433907523 92954795046302055650861285)
          ·
            refine ⟨17429024071181635434536491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92954795046302055650861285 17429024071181635434536491)
            ·
              refine ⟨26143536106772453151804737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17429024071181635434536491 26143536106772453151804737)
              ·
                refine ⟨19607652080079339863853553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26143536106772453151804737 19607652080079339863853553)
                ·
                  refine ⟨14705739060059504897890165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19607652080079339863853553 14705739060059504897890165)
                  ·
                    refine ⟨1378663036880578584177203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14705739060059504897890165 1378663036880578584177203)
                    ·
                      rfl

theorem cell23_8054810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 2, 5].length) (baseStart_8054810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054810 prefixEnd_8054810 := by exact prefixLift 8054810
  have htrace : WordTrace (prefixWord ++ tailWord_8054810) baseStart_8054810 baseEnd_8054810 := by
    simpa [prefixWord, tailWord_8054810, baseEnd_8054810] using wordTrace_append hprefix tailTrace_8054810
  have hstable : (prefixWord ++ tailWord_8054810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054810).length < 2 ^ (prefixWord ++ tailWord_8054810).sum := by decide
  have hdescent : baseEnd_8054810 < baseStart_8054810 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054857 : List Nat := [1, 2, 1, 1, 2, 2, 4, 5, 1, 4]
def baseStart_8054857 : Nat := 118140960795 + 8054857 * 2 ^ 59
def prefixEnd_8054857 : Nat := 4983230072969 + 3 ^ 40 * 8054857 * 2
def baseEnd_8054857 : Nat := 1378671081410832356214631

theorem tailTrace_8054857 : CollatzResearch.WordTrace tailWord_8054857 prefixEnd_8054857 1378671081410832356214631 := by
  unfold tailWord_8054857
  simp only [CollatzResearch.WordTrace]
  refine ⟨293784770179636223898818825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195856513453090815932545883 293784770179636223898818825)
  ·
    refine ⟨220338577634727167924114119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293784770179636223898818825 220338577634727167924114119)
    ·
      refine ⟨330507866452090751886171179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220338577634727167924114119 330507866452090751886171179)
      ·
        refine ⟨495761799678136127829256769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330507866452090751886171179 495761799678136127829256769)
        ·
          refine ⟨371821349758602095871942577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 495761799678136127829256769 371821349758602095871942577)
          ·
            refine ⟨278866012318951571903956933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371821349758602095871942577 278866012318951571903956933)
            ·
              refine ⟨52287377309803419731991925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 278866012318951571903956933 52287377309803419731991925)
              ·
                refine ⟨4901941622794070599874243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52287377309803419731991925 4901941622794070599874243)
                ·
                  refine ⟨7352912434191105899811365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4901941622794070599874243 7352912434191105899811365)
                  ·
                    refine ⟨1378671081410832356214631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7352912434191105899811365 1378671081410832356214631)
                    ·
                      rfl

theorem cell23_8054857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 5, 1, 4].length) (baseStart_8054857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054857 prefixEnd_8054857 := by exact prefixLift 8054857
  have htrace : WordTrace (prefixWord ++ tailWord_8054857) baseStart_8054857 baseEnd_8054857 := by
    simpa [prefixWord, tailWord_8054857, baseEnd_8054857] using wordTrace_append hprefix tailTrace_8054857
  have hstable : (prefixWord ++ tailWord_8054857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054857).length < 2 ^ (prefixWord ++ tailWord_8054857).sum := by decide
  have hdescent : baseEnd_8054857 < baseStart_8054857 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054873 : List Nat := [1, 2, 1, 2, 2, 1, 4, 1, 1, 2, 6]
def baseStart_8054873 : Nat := 118140960795 + 8054873 * 2 ^ 59
def prefixEnd_8054873 : Nat := 4983230072969 + 3 ^ 40 * 8054873 * 2
def baseEnd_8054873 : Nat := 4136021459922969006043819

theorem tailTrace_8054873 : CollatzResearch.WordTrace tailWord_8054873 prefixEnd_8054873 4136021459922969006043819 := by
  unfold tailWord_8054873
  simp only [CollatzResearch.WordTrace]
  refine ⟨293785353747578258631401273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195856902498385505754267515 293785353747578258631401273)
  ·
    refine ⟨220339015310683693973550955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293785353747578258631401273 220339015310683693973550955)
    ·
      refine ⟨330508522966025540960326433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220339015310683693973550955 330508522966025540960326433)
      ·
        refine ⟨247881392224519155720244825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330508522966025540960326433 247881392224519155720244825)
        ·
          refine ⟨185911044168389366790183619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247881392224519155720244825 185911044168389366790183619)
          ·
            refine ⟨278866566252584050185275429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185911044168389366790183619 278866566252584050185275429)
            ·
              refine ⟨52287481172359509409739143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 278866566252584050185275429 52287481172359509409739143)
              ·
                refine ⟨78431221758539264114608715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52287481172359509409739143 78431221758539264114608715)
                ·
                  refine ⟨117646832637808896171913073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78431221758539264114608715 117646832637808896171913073)
                  ·
                    refine ⟨88235124478356672128934805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117646832637808896171913073 88235124478356672128934805)
                    ·
                      refine ⟨4136021459922969006043819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88235124478356672128934805 4136021459922969006043819)
                      ·
                        rfl

theorem cell23_8054873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_8054873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054873 prefixEnd_8054873 := by exact prefixLift 8054873
  have htrace : WordTrace (prefixWord ++ tailWord_8054873) baseStart_8054873 baseEnd_8054873 := by
    simpa [prefixWord, tailWord_8054873, baseEnd_8054873] using wordTrace_append hprefix tailTrace_8054873
  have hstable : (prefixWord ++ tailWord_8054873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054873).length < 2 ^ (prefixWord ++ tailWord_8054873).sum := by decide
  have hdescent : baseEnd_8054873 < baseStart_8054873 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054897 : List Nat := [1, 2, 2, 2, 1, 1, 5, 2, 3, 1, 3]
def baseStart_8054897 : Nat := 118140960795 + 8054897 * 2 ^ 59
def prefixEnd_8054897 : Nat := 4983230072969 + 3 ^ 40 * 8054897 * 2
def baseEnd_8054897 : Nat := 4136033783458676912143709

theorem tailTrace_8054897 : CollatzResearch.WordTrace tailWord_8054897 prefixEnd_8054897 4136033783458676912143709 := by
  unfold tailWord_8054897
  simp only [CollatzResearch.WordTrace]
  refine ⟨293786229099491310730274945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195857486066327540486849963 293786229099491310730274945)
  ·
    refine ⟨220339671824618483047706209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293786229099491310730274945 220339671824618483047706209)
    ·
      refine ⟨165254753868463862285779657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220339671824618483047706209 165254753868463862285779657)
      ·
        refine ⟨123941065401347896714334743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165254753868463862285779657 123941065401347896714334743)
        ·
          refine ⟨185911598102021845071502115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123941065401347896714334743 185911598102021845071502115)
          ·
            refine ⟨278867397153032767607253173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185911598102021845071502115 278867397153032767607253173)
            ·
              refine ⟨26143818483096821963179985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 278867397153032767607253173 26143818483096821963179985)
              ·
                refine ⟨19607863862322616472384989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26143818483096821963179985 19607863862322616472384989)
                ·
                  refine ⟨7352948948370981177144371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19607863862322616472384989 7352948948370981177144371)
                  ·
                    refine ⟨11029423422556471765716557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7352948948370981177144371 11029423422556471765716557)
                    ·
                      refine ⟨4136033783458676912143709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11029423422556471765716557 4136033783458676912143709)
                      ·
                        rfl

theorem cell23_8054897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 3, 1, 3].length) (baseStart_8054897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054897 prefixEnd_8054897 := by exact prefixLift 8054897
  have htrace : WordTrace (prefixWord ++ tailWord_8054897) baseStart_8054897 baseEnd_8054897 := by
    simpa [prefixWord, tailWord_8054897, baseEnd_8054897] using wordTrace_append hprefix tailTrace_8054897
  have hstable : (prefixWord ++ tailWord_8054897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054897).length < 2 ^ (prefixWord ++ tailWord_8054897).sum := by decide
  have hdescent : baseEnd_8054897 < baseStart_8054897 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054917 : List Nat := [1, 3, 1, 1, 5, 2, 1, 3, 1, 5]
def baseStart_8054917 : Nat := 118140960795 + 8054917 * 2 ^ 59
def prefixEnd_8054917 : Nat := 4983230072969 + 3 ^ 40 * 8054917 * 2
def baseEnd_8054917 : Nat := 1378681351023922277964539

theorem tailTrace_8054917 : CollatzResearch.WordTrace tailWord_8054917 prefixEnd_8054917 1378681351023922277964539 := by
  unfold tailWord_8054917
  simp only [CollatzResearch.WordTrace]
  refine ⟨293786958559418854146003005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195857972372945902764002003 293786958559418854146003005)
  ·
    refine ⟨110170109459782070304751127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293786958559418854146003005 110170109459782070304751127)
    ·
      refine ⟨165255164189673105457126691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110170109459782070304751127 165255164189673105457126691)
      ·
        refine ⟨247882746284509658185690037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165255164189673105457126691 247882746284509658185690037)
        ·
          refine ⟨23239007464172780454908441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 247882746284509658185690037 23239007464172780454908441)
          ·
            refine ⟨17429255598129585341181331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23239007464172780454908441 17429255598129585341181331)
            ·
              refine ⟨26143883397194378011771997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17429255598129585341181331 26143883397194378011771997)
              ·
                refine ⟨9803956273947891754414499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26143883397194378011771997 9803956273947891754414499)
                ·
                  refine ⟨14705934410921837631621749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9803956273947891754414499 14705934410921837631621749)
                  ·
                    refine ⟨1378681351023922277964539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14705934410921837631621749 1378681351023922277964539)
                    ·
                      rfl

theorem cell23_8054917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 5].length) (baseStart_8054917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054917 prefixEnd_8054917 := by exact prefixLift 8054917
  have htrace : WordTrace (prefixWord ++ tailWord_8054917) baseStart_8054917 baseEnd_8054917 := by
    simpa [prefixWord, tailWord_8054917, baseEnd_8054917] using wordTrace_append hprefix tailTrace_8054917
  have hstable : (prefixWord ++ tailWord_8054917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054917).length < 2 ^ (prefixWord ++ tailWord_8054917).sum := by decide
  have hdescent : baseEnd_8054917 < baseStart_8054917 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054965 : List Nat := [1, 3, 3, 4, 1, 2, 1, 3, 1, 1, 3]
def baseStart_8054965 : Nat := 118140960795 + 8054965 * 2 ^ 59
def prefixEnd_8054965 : Nat := 4983230072969 + 3 ^ 40 * 8054965 * 2
def baseEnd_8054965 : Nat := 4136068700143182646093397

theorem tailTrace_8054965 : CollatzResearch.WordTrace tailWord_8054965 prefixEnd_8054965 4136068700143182646093397 := by
  unfold tailWord_8054965
  simp only [CollatzResearch.WordTrace]
  refine ⟨293788709263244958343750349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195859139508829972229166899 293788709263244958343750349)
  ·
    refine ⟨110170765973716859378906381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293788709263244958343750349 110170765973716859378906381)
    ·
      refine ⟨41314037240143822267089893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110170765973716859378906381 41314037240143822267089893)
      ·
        refine ⟨7746381982526966675079355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41314037240143822267089893 7746381982526966675079355)
        ·
          refine ⟨11619572973790450012619033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7746381982526966675079355 11619572973790450012619033)
          ·
            refine ⟨8714679730342837509464275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11619572973790450012619033 8714679730342837509464275)
            ·
              refine ⟨13072019595514256264196413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8714679730342837509464275 13072019595514256264196413)
              ·
                refine ⟨4902007348317846099073655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13072019595514256264196413 4902007348317846099073655)
                ·
                  refine ⟨7353011022476769148610483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4902007348317846099073655 7353011022476769148610483)
                  ·
                    refine ⟨11029516533715153722915725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7353011022476769148610483 11029516533715153722915725)
                    ·
                      refine ⟨4136068700143182646093397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11029516533715153722915725 4136068700143182646093397)
                      ·
                        rfl

theorem cell23_8054965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_8054965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054965 prefixEnd_8054965 := by exact prefixLift 8054965
  have htrace : WordTrace (prefixWord ++ tailWord_8054965) baseStart_8054965 baseEnd_8054965 := by
    simpa [prefixWord, tailWord_8054965, baseEnd_8054965] using wordTrace_append hprefix tailTrace_8054965
  have hstable : (prefixWord ++ tailWord_8054965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054965).length < 2 ^ (prefixWord ++ tailWord_8054965).sum := by decide
  have hdescent : baseEnd_8054965 < baseStart_8054965 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054974 : List Nat := [4, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5]
def baseStart_8054974 : Nat := 118140960795 + 8054974 * 2 ^ 59
def prefixEnd_8054974 : Nat := 4983230072969 + 3 ^ 40 * 8054974 * 2
def baseEnd_8054974 : Nat := 4136073321469073110880855

theorem tailTrace_8054974 : CollatzResearch.WordTrace tailWord_8054974 prefixEnd_8054974 4136073321469073110880855 := by
  unfold tailWord_8054974
  simp only [CollatzResearch.WordTrace]
  refine ⟨36723629690026544110103497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195859358346808235253885317 36723629690026544110103497)
  ·
    refine ⟨27542722267519908082577623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36723629690026544110103497 27542722267519908082577623)
    ·
      refine ⟨41314083401279862123866435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27542722267519908082577623 41314083401279862123866435)
      ·
        refine ⟨61971125101919793185799653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41314083401279862123866435 61971125101919793185799653)
        ·
          refine ⟨11619585956609961222337435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61971125101919793185799653 11619585956609961222337435)
          ·
            refine ⟨17429378934914941833506153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11619585956609961222337435 17429378934914941833506153)
            ·
              refine ⟨13072034201186206375129615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17429378934914941833506153 13072034201186206375129615)
              ·
                refine ⟨19608051301779309562694423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13072034201186206375129615 19608051301779309562694423)
                ·
                  refine ⟨29412076952668964344041635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19608051301779309562694423 29412076952668964344041635)
                  ·
                    refine ⟨44118115429003446516062453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29412076952668964344041635 44118115429003446516062453)
                    ·
                      refine ⟨4136073321469073110880855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44118115429003446516062453 4136073321469073110880855)
                      ·
                        rfl

theorem cell23_8054974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_8054974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054974 prefixEnd_8054974 := by exact prefixLift 8054974
  have htrace : WordTrace (prefixWord ++ tailWord_8054974) baseStart_8054974 baseEnd_8054974 := by
    simpa [prefixWord, tailWord_8054974, baseEnd_8054974] using wordTrace_append hprefix tailTrace_8054974
  have hstable : (prefixWord ++ tailWord_8054974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054974).length < 2 ^ (prefixWord ++ tailWord_8054974).sum := by decide
  have hdescent : baseEnd_8054974 < baseStart_8054974 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054987 : List Nat := [1, 1, 1, 1, 3, 2, 3, 3, 4, 1, 3]
def baseStart_8054987 : Nat := 118140960795 + 8054987 * 2 ^ 59
def prefixEnd_8054987 : Nat := 4983230072969 + 3 ^ 40 * 8054987 * 2
def baseEnd_8054987 : Nat := 4136079996717581560018295

theorem tailTrace_8054987 : CollatzResearch.WordTrace tailWord_8054987 prefixEnd_8054987 4136079996717581560018295 := by
  unfold tailWord_8054987
  simp only [CollatzResearch.WordTrace]
  refine ⟨293789511669165256101051215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195859674446110170734034143 293789511669165256101051215)
  ·
    refine ⟨440684267503747884151576823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293789511669165256101051215 440684267503747884151576823)
    ·
      refine ⟨661026401255621826227365235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440684267503747884151576823 661026401255621826227365235)
      ·
        refine ⟨991539601883432739341047853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661026401255621826227365235 991539601883432739341047853)
        ·
          refine ⟨371827350706287277252892945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 991539601883432739341047853 371827350706287277252892945)
          ·
            refine ⟨278870513029715457939669709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371827350706287277252892945 278870513029715457939669709)
            ·
              refine ⟨104576442386143296727376141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 278870513029715457939669709 104576442386143296727376141)
              ·
                refine ⟨39216165894803736272766053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104576442386143296727376141 39216165894803736272766053)
                ·
                  refine ⟨7353031105275700551143635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39216165894803736272766053 7353031105275700551143635)
                  ·
                    refine ⟨11029546657913550826715453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7353031105275700551143635 11029546657913550826715453)
                    ·
                      refine ⟨4136079996717581560018295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11029546657913550826715453 4136079996717581560018295)
                      ·
                        rfl

theorem cell23_8054987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 4, 1, 3].length) (baseStart_8054987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054987 prefixEnd_8054987 := by exact prefixLift 8054987
  have htrace : WordTrace (prefixWord ++ tailWord_8054987) baseStart_8054987 baseEnd_8054987 := by
    simpa [prefixWord, tailWord_8054987, baseEnd_8054987] using wordTrace_append hprefix tailTrace_8054987
  have hstable : (prefixWord ++ tailWord_8054987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054987).length < 2 ^ (prefixWord ++ tailWord_8054987).sum := by decide
  have hdescent : baseEnd_8054987 < baseStart_8054987 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054998 : List Nat := [5, 2, 1, 2, 1, 1, 4, 1, 2, 4]
def baseStart_8054998 : Nat := 118140960795 + 8054998 * 2 ^ 59
def prefixEnd_8054998 : Nat := 4983230072969 + 3 ^ 40 * 8054998 * 2
def baseEnd_8054998 : Nat := 1378695215001593672326915

theorem tailTrace_8054998 : CollatzResearch.WordTrace tailWord_8054998 prefixEnd_8054998 1378695215001593672326915 := by
  unfold tailWord_8054998
  simp only [CollatzResearch.WordTrace]
  refine ⟨18361869554507837811231353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195859941914750269986467765 18361869554507837811231353)
  ·
    refine ⟨13771402165880878358423515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18361869554507837811231353 13771402165880878358423515)
    ·
      refine ⟨20657103248821317537635273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13771402165880878358423515 20657103248821317537635273)
      ·
        refine ⟨15492827436615988153226455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20657103248821317537635273 15492827436615988153226455)
        ·
          refine ⟨23239241154923982229839683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15492827436615988153226455 23239241154923982229839683)
          ·
            refine ⟨34858861732385973344759525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23239241154923982229839683 34858861732385973344759525)
            ·
              refine ⟨6536036574822370002142411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34858861732385973344759525 6536036574822370002142411)
              ·
                refine ⟨9804054862233555003213617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6536036574822370002142411 9804054862233555003213617)
                ·
                  refine ⟨7353041146675166252410213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9804054862233555003213617 7353041146675166252410213)
                  ·
                    refine ⟨1378695215001593672326915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7353041146675166252410213 1378695215001593672326915)
                    ·
                      rfl

theorem cell23_8054998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_8054998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054998 prefixEnd_8054998 := by exact prefixLift 8054998
  have htrace : WordTrace (prefixWord ++ tailWord_8054998) baseStart_8054998 baseEnd_8054998 := by
    simpa [prefixWord, tailWord_8054998, baseEnd_8054998] using wordTrace_append hprefix tailTrace_8054998
  have hstable : (prefixWord ++ tailWord_8054998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054998).length < 2 ^ (prefixWord ++ tailWord_8054998).sum := by decide
  have hdescent : baseEnd_8054998 < baseStart_8054998 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055057 : List Nat := [1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 4]
def baseStart_8055057 : Nat := 118140960795 + 8055057 * 2 ^ 59
def prefixEnd_8055057 : Nat := 4983230072969 + 3 ^ 40 * 8055057 * 2
def baseEnd_8055057 : Nat := 4136115940363396286142973

theorem tailTrace_8055057 : CollatzResearch.WordTrace tailWord_8055057 prefixEnd_8055057 4136115940363396286142973 := by
  unfold tailWord_8055057
  simp only [CollatzResearch.WordTrace]
  refine ⟨293792064778911658056099425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195861376519274438704066283 293792064778911658056099425)
  ·
    refine ⟨220344048584183743542074569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293792064778911658056099425 220344048584183743542074569)
    ·
      refine ⟨165258036438137807656555927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220344048584183743542074569 165258036438137807656555927)
      ·
        refine ⟨247887054657206711484833891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165258036438137807656555927 247887054657206711484833891)
        ·
          refine ⟨371830581985810067227250837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247887054657206711484833891 371830581985810067227250837)
          ·
            refine ⟨17429558530584846901277383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 371830581985810067227250837 17429558530584846901277383)
            ·
              refine ⟨26144337795877270351916075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17429558530584846901277383 26144337795877270351916075)
              ·
                refine ⟨39216506693815905527874113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26144337795877270351916075 39216506693815905527874113)
                ·
                  refine ⟨29412380020361929145905585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39216506693815905527874113 29412380020361929145905585)
                  ·
                    refine ⟨22059285015271446859429189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29412380020361929145905585 22059285015271446859429189)
                    ·
                      refine ⟨4136115940363396286142973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22059285015271446859429189 4136115940363396286142973)
                      ·
                        rfl

theorem cell23_8055057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 4].length) (baseStart_8055057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055057 prefixEnd_8055057 := by exact prefixLift 8055057
  have htrace : WordTrace (prefixWord ++ tailWord_8055057) baseStart_8055057 baseEnd_8055057 := by
    simpa [prefixWord, tailWord_8055057, baseEnd_8055057] using wordTrace_append hprefix tailTrace_8055057
  have hstable : (prefixWord ++ tailWord_8055057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055057).length < 2 ^ (prefixWord ++ tailWord_8055057).sum := by decide
  have hdescent : baseEnd_8055057 < baseStart_8055057 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055061 : List Nat := [1, 3, 2, 1, 2, 1, 4, 3, 2, 2, 2]
def baseStart_8055061 : Nat := 118140960795 + 8055061 * 2 ^ 59
def prefixEnd_8055061 : Nat := 4983230072969 + 3 ^ 40 * 8055061 * 2
def baseEnd_8055061 : Nat := 4136117994286014270492955

theorem tailTrace_8055061 : CollatzResearch.WordTrace tailWord_8055061 prefixEnd_8055061 4136117994286014270492955 := by
  unfold tailWord_8055061
  simp only [CollatzResearch.WordTrace]
  refine ⟨293792210670897166739245037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195861473780598111159496691 293792210670897166739245037)
  ·
    refine ⟨110172079001586437527216889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293792210670897166739245037 110172079001586437527216889)
    ·
      refine ⟨82629059251189828145412667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110172079001586437527216889 82629059251189828145412667)
      ·
        refine ⟨123943588876784742218119001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82629059251189828145412667 123943588876784742218119001)
        ·
          refine ⟨92957691657588556663589251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123943588876784742218119001 92957691657588556663589251)
          ·
            refine ⟨139436537486382834995383877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92957691657588556663589251 139436537486382834995383877)
            ·
              refine ⟨26144350778696781561634477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139436537486382834995383877 26144350778696781561634477)
              ·
                refine ⟨9804131542011293085612929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26144350778696781561634477 9804131542011293085612929)
                ·
                  refine ⟨7353098656508469814209697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9804131542011293085612929 7353098656508469814209697)
                  ·
                    refine ⟨5514823992381352360657273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7353098656508469814209697 5514823992381352360657273)
                    ·
                      refine ⟨4136117994286014270492955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5514823992381352360657273 4136117994286014270492955)
                      ·
                        rfl

theorem cell23_8055061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 2, 2, 2].length) (baseStart_8055061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055061 prefixEnd_8055061 := by exact prefixLift 8055061
  have htrace : WordTrace (prefixWord ++ tailWord_8055061) baseStart_8055061 baseEnd_8055061 := by
    simpa [prefixWord, tailWord_8055061, baseEnd_8055061] using wordTrace_append hprefix tailTrace_8055061
  have hstable : (prefixWord ++ tailWord_8055061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055061).length < 2 ^ (prefixWord ++ tailWord_8055061).sum := by decide
  have hdescent : baseEnd_8055061 < baseStart_8055061 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055082 : List Nat := [3, 1, 4, 2, 3, 1, 2, 1, 1, 3, 2]
def baseStart_8055082 : Nat := 118140960795 + 8055082 * 2 ^ 59
def prefixEnd_8055082 : Nat := 4983230072969 + 3 ^ 40 * 8055082 * 2
def baseEnd_8055082 : Nat := 4136128777379758688330359

theorem tailTrace_8055082 : CollatzResearch.WordTrace tailWord_8055082 prefixEnd_8055082 4136128777379758688330359 := by
  unfold tailWord_8055082
  simp only [CollatzResearch.WordTrace]
  refine ⟨73448244150955271831439875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195861984402547391550506333 73448244150955271831439875)
  ·
    refine ⟨110172366226432907747159813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73448244150955271831439875 110172366226432907747159813)
    ·
      refine ⟨20657318667456170202592465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110172366226432907747159813 20657318667456170202592465)
      ·
        refine ⟨15492989000592127651944349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20657318667456170202592465 15492989000592127651944349)
        ·
          refine ⟨5809870875222047869479131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15492989000592127651944349 5809870875222047869479131)
          ·
            refine ⟨8714806312833071804218697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5809870875222047869479131 8714806312833071804218697)
            ·
              refine ⟨6536104734624803853164023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8714806312833071804218697 6536104734624803853164023)
              ·
                refine ⟨9804157101937205779746035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6536104734624803853164023 9804157101937205779746035)
                ·
                  refine ⟨14706235652905808669619053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9804157101937205779746035 14706235652905808669619053)
                  ·
                    refine ⟨5514838369839678251107145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14706235652905808669619053 5514838369839678251107145)
                    ·
                      refine ⟨4136128777379758688330359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5514838369839678251107145 4136128777379758688330359)
                      ·
                        rfl

theorem cell23_8055082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_8055082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055082 prefixEnd_8055082 := by exact prefixLift 8055082
  have htrace : WordTrace (prefixWord ++ tailWord_8055082) baseStart_8055082 baseEnd_8055082 := by
    simpa [prefixWord, tailWord_8055082, baseEnd_8055082] using wordTrace_append hprefix tailTrace_8055082
  have hstable : (prefixWord ++ tailWord_8055082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055082).length < 2 ^ (prefixWord ++ tailWord_8055082).sum := by decide
  have hdescent : baseEnd_8055082 < baseStart_8055082 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055154 : List Nat := [3, 2, 1, 2, 1, 3, 1, 1, 4, 2, 3]
def baseStart_8055154 : Nat := 118140960795 + 8055154 * 2 ^ 59
def prefixEnd_8055154 : Nat := 4983230072969 + 3 ^ 40 * 8055154 * 2
def baseEnd_8055154 : Nat := 4136165747986882406630027

theorem tailTrace_8055154 : CollatzResearch.WordTrace tailWord_8055154 prefixEnd_8055154 4136165747986882406630027 := by
  unfold tailWord_8055154
  simp only [CollatzResearch.WordTrace]
  refine ⟨73448900664890060905595129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195863735106373495748253677 73448900664890060905595129)
  ·
    refine ⟨55086675498667545679196347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73448900664890060905595129 55086675498667545679196347)
    ·
      refine ⟨82630013248001318518794521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55086675498667545679196347 82630013248001318518794521)
      ·
        refine ⟨61972509936000988889095891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82630013248001318518794521 61972509936000988889095891)
        ·
          refine ⟨92958764904001483333643837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61972509936000988889095891 92958764904001483333643837)
          ·
            refine ⟨34859536839000556250116439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92958764904001483333643837 34859536839000556250116439)
            ·
              refine ⟨52289305258500834375174659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34859536839000556250116439 52289305258500834375174659)
              ·
                refine ⟨78433957887751251562761989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52289305258500834375174659 78433957887751251562761989)
                ·
                  refine ⟨14706367103953359668017873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78433957887751251562761989 14706367103953359668017873)
                  ·
                    refine ⟨11029775327965019751013405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14706367103953359668017873 11029775327965019751013405)
                    ·
                      refine ⟨4136165747986882406630027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11029775327965019751013405 4136165747986882406630027)
                      ·
                        rfl

theorem cell23_8055154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_8055154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055154 prefixEnd_8055154 := by exact prefixLift 8055154
  have htrace : WordTrace (prefixWord ++ tailWord_8055154) baseStart_8055154 baseEnd_8055154 := by
    simpa [prefixWord, tailWord_8055154, baseEnd_8055154] using wordTrace_append hprefix tailTrace_8055154
  have hstable : (prefixWord ++ tailWord_8055154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055154).length < 2 ^ (prefixWord ++ tailWord_8055154).sum := by decide
  have hdescent : baseEnd_8055154 < baseStart_8055154 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055188 : List Nat := [2, 4, 2, 1, 3, 1, 2, 1, 2, 2, 3]
def baseStart_8055188 : Nat := 118140960795 + 8055188 * 2 ^ 59
def prefixEnd_8055188 : Nat := 4983230072969 + 3 ^ 40 * 8055188 * 2
def baseEnd_8055188 : Nat := 4136183206329135273604871

theorem tailTrace_8055188 : CollatzResearch.WordTrace tailWord_8055188 prefixEnd_8055188 4136183206329135273604871 := by
  unfold tailWord_8055188
  simp only [CollatzResearch.WordTrace]
  refine ⟨146898421370718533714559109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195864561827624711619412145 146898421370718533714559109)
  ·
    refine ⟨27543454007009725071479833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146898421370718533714559109 27543454007009725071479833)
    ·
      refine ⟨20657590505257293803609875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27543454007009725071479833 20657590505257293803609875)
      ·
        refine ⟨30986385757885940705414813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20657590505257293803609875 30986385757885940705414813)
        ·
          refine ⟨11619894659207227764530555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30986385757885940705414813 11619894659207227764530555)
          ·
            refine ⟨17429841988810841646795833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11619894659207227764530555 17429841988810841646795833)
            ·
              refine ⟨13072381491608131235096875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17429841988810841646795833 13072381491608131235096875)
              ·
                refine ⟨19608572237412196852645313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13072381491608131235096875 19608572237412196852645313)
                ·
                  refine ⟨14706429178059147639483985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19608572237412196852645313 14706429178059147639483985)
                  ·
                    refine ⟨11029821883544360729612989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14706429178059147639483985 11029821883544360729612989)
                    ·
                      refine ⟨4136183206329135273604871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11029821883544360729612989 4136183206329135273604871)
                      ·
                        rfl

theorem cell23_8055188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_8055188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055188 prefixEnd_8055188 := by exact prefixLift 8055188
  have htrace : WordTrace (prefixWord ++ tailWord_8055188) baseStart_8055188 baseEnd_8055188 := by
    simpa [prefixWord, tailWord_8055188, baseEnd_8055188] using wordTrace_append hprefix tailTrace_8055188
  have hstable : (prefixWord ++ tailWord_8055188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055188).length < 2 ^ (prefixWord ++ tailWord_8055188).sum := by decide
  have hdescent : baseEnd_8055188 < baseStart_8055188 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055204 : List Nat := [2, 3, 1, 2, 1, 1, 2, 5, 1, 5]
def baseStart_8055204 : Nat := 118140960795 + 8055204 * 2 ^ 59
def prefixEnd_8055204 : Nat := 4983230072969 + 3 ^ 40 * 8055204 * 2
def baseEnd_8055204 : Nat := 1378730474006535737001599

theorem tailTrace_8055204 : CollatzResearch.WordTrace tailWord_8055204 prefixEnd_8055204 1378730474006535737001599 := by
  unfold tailWord_8055204
  simp only [CollatzResearch.WordTrace]
  refine ⟨146898713154689551080850333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195864950872919401441133777 146898713154689551080850333)
  ·
    refine ⟨55087017433008581655318875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146898713154689551080850333 55087017433008581655318875)
    ·
      refine ⟨82630526149512872482978313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55087017433008581655318875 82630526149512872482978313)
      ·
        refine ⟨61972894612134654362233735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82630526149512872482978313 61972894612134654362233735)
        ·
          refine ⟨92959341918201981543350603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61972894612134654362233735 92959341918201981543350603)
          ·
            refine ⟨139439012877302972315025905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92959341918201981543350603 139439012877302972315025905)
            ·
              refine ⟨104579259657977229236269429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139439012877302972315025905 104579259657977229236269429)
              ·
                refine ⟨9804305592935365240900259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104579259657977229236269429 9804305592935365240900259)
                ·
                  refine ⟨14706458389403047861350389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9804305592935365240900259 14706458389403047861350389)
                  ·
                    refine ⟨1378730474006535737001599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14706458389403047861350389 1378730474006535737001599)
                    ·
                      rfl

theorem cell23_8055204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 1, 5].length) (baseStart_8055204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055204 prefixEnd_8055204 := by exact prefixLift 8055204
  have htrace : WordTrace (prefixWord ++ tailWord_8055204) baseStart_8055204 baseEnd_8055204 := by
    simpa [prefixWord, tailWord_8055204, baseEnd_8055204] using wordTrace_append hprefix tailTrace_8055204
  have hstable : (prefixWord ++ tailWord_8055204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055204).length < 2 ^ (prefixWord ++ tailWord_8055204).sum := by decide
  have hdescent : baseEnd_8055204 < baseStart_8055204 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055218 : List Nat := [3, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3]
def baseStart_8055218 : Nat := 118140960795 + 8055218 * 2 ^ 59
def prefixEnd_8055218 : Nat := 4983230072969 + 3 ^ 40 * 8055218 * 2
def baseEnd_8055218 : Nat := 4136198610748770156229733

theorem tailTrace_8055218 : CollatzResearch.WordTrace tailWord_8055218 prefixEnd_8055218 4136198610748770156229733 := by
  unfold tailWord_8055218
  simp only [CollatzResearch.WordTrace]
  refine ⟨73449484232832095638177577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195865291287552255035140205 73449484232832095638177577)
  ·
    refine ⟨55087113174624071728633183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73449484232832095638177577 55087113174624071728633183)
    ·
      refine ⟨82630669761936107592949775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55087113174624071728633183 82630669761936107592949775)
      ·
        refine ⟨123946004642904161389424663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82630669761936107592949775 123946004642904161389424663)
        ·
          refine ⟨185919006964356242084136995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123946004642904161389424663 185919006964356242084136995)
          ·
            refine ⟨278878510446534363126205493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185919006964356242084136995 278878510446534363126205493)
            ·
              refine ⟨26144860354362596543081765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 278878510446534363126205493 26144860354362596543081765)
              ·
                refine ⟨4902161316442986851827831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26144860354362596543081765 4902161316442986851827831)
                ·
                  refine ⟨7353241974664480277741747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4902161316442986851827831 7353241974664480277741747)
                  ·
                    refine ⟨11029862961996720416612621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7353241974664480277741747 11029862961996720416612621)
                    ·
                      refine ⟨4136198610748770156229733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11029862961996720416612621 4136198610748770156229733)
                      ·
                        rfl

theorem cell23_8055218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3].length) (baseStart_8055218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055218 prefixEnd_8055218 := by exact prefixLift 8055218
  have htrace : WordTrace (prefixWord ++ tailWord_8055218) baseStart_8055218 baseEnd_8055218 := by
    simpa [prefixWord, tailWord_8055218, baseEnd_8055218] using wordTrace_append hprefix tailTrace_8055218
  have hstable : (prefixWord ++ tailWord_8055218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055218).length < 2 ^ (prefixWord ++ tailWord_8055218).sum := by decide
  have hdescent : baseEnd_8055218 < baseStart_8055218 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055224 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 2, 6, 2]
def baseStart_8055224 : Nat := 118140960795 + 8055224 * 2 ^ 59
def prefixEnd_8055224 : Nat := 4983230072969 + 3 ^ 40 * 8055224 * 2
def baseEnd_8055224 : Nat := 4136201691632697132754705

theorem tailTrace_8055224 : CollatzResearch.WordTrace tailWord_8055224 prefixEnd_8055224 4136201691632697132754705 := by
  unfold tailWord_8055224
  simp only [CollatzResearch.WordTrace]
  refine ⟨146899077884653322788714363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195865437179537763718285817 146899077884653322788714363)
  ·
    refine ⟨220348616826979984183071545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146899077884653322788714363 220348616826979984183071545)
    ·
      refine ⟨165261462620234988137303659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220348616826979984183071545 165261462620234988137303659)
      ·
        refine ⟨247892193930352482205955489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165261462620234988137303659 247892193930352482205955489)
        ·
          refine ⟨185919145447764361654466617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247892193930352482205955489 185919145447764361654466617)
          ·
            refine ⟨139439359085823271240849963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185919145447764361654466617 139439359085823271240849963)
            ·
              refine ⟨209159038628734906861274945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139439359085823271240849963 209159038628734906861274945)
              ·
                refine ⟨156869278971551180145956209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209159038628734906861274945 156869278971551180145956209)
                ·
                  refine ⟨117651959228663385109467157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156869278971551180145956209 117651959228663385109467157)
                  ·
                    refine ⟨5514935588843596177006273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 117651959228663385109467157 5514935588843596177006273)
                    ·
                      refine ⟨4136201691632697132754705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5514935588843596177006273 4136201691632697132754705)
                      ·
                        rfl

theorem cell23_8055224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 6, 2].length) (baseStart_8055224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055224 prefixEnd_8055224 := by exact prefixLift 8055224
  have htrace : WordTrace (prefixWord ++ tailWord_8055224) baseStart_8055224 baseEnd_8055224 := by
    simpa [prefixWord, tailWord_8055224, baseEnd_8055224] using wordTrace_append hprefix tailTrace_8055224
  have hstable : (prefixWord ++ tailWord_8055224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055224).length < 2 ^ (prefixWord ++ tailWord_8055224).sum := by decide
  have hdescent : baseEnd_8055224 < baseStart_8055224 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055241 : List Nat := [1, 2, 1, 1, 2, 1, 5, 1, 5, 2, 2]
def baseStart_8055241 : Nat := 118140960795 + 8055241 * 2 ^ 59
def prefixEnd_8055241 : Nat := 4983230072969 + 3 ^ 40 * 8055241 * 2
def baseEnd_8055241 : Nat := 4136210420803823566242127

theorem tailTrace_8055241 : CollatzResearch.WordTrace tailWord_8055241 prefixEnd_8055241 4136210420803823566242127 := by
  unfold tailWord_8055241
  simp only [CollatzResearch.WordTrace]
  refine ⟨293798775810245057480797577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195865850540163371653865051 293798775810245057480797577)
  ·
    refine ⟨220349081857683793110598183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293798775810245057480797577 220349081857683793110598183)
    ·
      refine ⟨330523622786525689665897275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220349081857683793110598183 330523622786525689665897275)
      ·
        refine ⟨495785434179788534498845913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330523622786525689665897275 495785434179788534498845913)
        ·
          refine ⟨371839075634841400874134435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 495785434179788534498845913 371839075634841400874134435)
          ·
            refine ⟨557758613452262101311201653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371839075634841400874134435 557758613452262101311201653)
            ·
              refine ⟨52289870011149571997925155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 557758613452262101311201653 52289870011149571997925155)
              ·
                refine ⟨78434805016724357996887733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52289870011149571997925155 78434805016724357996887733)
                ·
                  refine ⟨7353262970317908562208225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78434805016724357996887733 7353262970317908562208225)
                  ·
                    refine ⟨5514947227738431421656169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7353262970317908562208225 5514947227738431421656169)
                    ·
                      refine ⟨4136210420803823566242127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5514947227738431421656169 4136210420803823566242127)
                      ·
                        rfl

theorem cell23_8055241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 5, 2, 2].length) (baseStart_8055241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055241 prefixEnd_8055241 := by exact prefixLift 8055241
  have htrace : WordTrace (prefixWord ++ tailWord_8055241) baseStart_8055241 baseEnd_8055241 := by
    simpa [prefixWord, tailWord_8055241, baseEnd_8055241] using wordTrace_append hprefix tailTrace_8055241
  have hstable : (prefixWord ++ tailWord_8055241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055241).length < 2 ^ (prefixWord ++ tailWord_8055241).sum := by decide
  have hdescent : baseEnd_8055241 < baseStart_8055241 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055285 : List Nat := [1, 3, 5, 1, 3, 1, 1, 1, 1, 6]
def baseStart_8055285 : Nat := 118140960795 + 8055285 * 2 ^ 59
def prefixEnd_8055285 : Nat := 4983230072969 + 3 ^ 40 * 8055285 * 2
def baseEnd_8055285 : Nat := 1378744337984207131363975

theorem tailTrace_8055285 : CollatzResearch.WordTrace tailWord_8055285 prefixEnd_8055285 1378744337984207131363975 := by
  unfold tailWord_8055285
  simp only [CollatzResearch.WordTrace]
  refine ⟨293800380622085652995399309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195866920414723768663599539 293800380622085652995399309)
  ·
    refine ⟨110175142733282119873274741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293800380622085652995399309 110175142733282119873274741)
    ·
      refine ⟨10328919631245198738119507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110175142733282119873274741 10328919631245198738119507)
      ·
        refine ⟨15493379446867798107179261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10328919631245198738119507 15493379446867798107179261)
        ·
          refine ⟨5810017292575424290192223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15493379446867798107179261 5810017292575424290192223)
          ·
            refine ⟨8715025938863136435288335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5810017292575424290192223 8715025938863136435288335)
            ·
              refine ⟨13072538908294704652932503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8715025938863136435288335 13072538908294704652932503)
              ·
                refine ⟨19608808362442056979398755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13072538908294704652932503 19608808362442056979398755)
                ·
                  refine ⟨29413212543663085469098133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19608808362442056979398755 29413212543663085469098133)
                  ·
                    refine ⟨1378744337984207131363975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29413212543663085469098133 1378744337984207131363975)
                    ·
                      rfl

theorem cell23_8055285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_8055285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055285 prefixEnd_8055285 := by exact prefixLift 8055285
  have htrace : WordTrace (prefixWord ++ tailWord_8055285) baseStart_8055285 baseEnd_8055285 := by
    simpa [prefixWord, tailWord_8055285, baseEnd_8055285] using wordTrace_append hprefix tailTrace_8055285
  have hstable : (prefixWord ++ tailWord_8055285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055285).length < 2 ^ (prefixWord ++ tailWord_8055285).sum := by decide
  have hdescent : baseEnd_8055285 < baseStart_8055285 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055301 : List Nat := [1, 3, 1, 1, 2, 2, 2, 3, 3, 3, 2]
def baseStart_8055301 : Nat := 118140960795 + 8055301 * 2 ^ 59
def prefixEnd_8055301 : Nat := 4983230072969 + 3 ^ 40 * 8055301 * 2
def baseEnd_8055301 : Nat := 4136241229643093331491851

theorem tailTrace_8055301 : CollatzResearch.WordTrace tailWord_8055301 prefixEnd_8055301 4136241229643093331491851 := by
  unfold tailWord_8055301
  simp only [CollatzResearch.WordTrace]
  refine ⟨293800964190027687727981757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195867309460018458485321171 293800964190027687727981757)
  ·
    refine ⟨110175361571260382897993159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293800964190027687727981757 110175361571260382897993159)
    ·
      refine ⟨165263042356890574346989739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110175361571260382897993159 165263042356890574346989739)
      ·
        refine ⟨247894563535335861520484609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165263042356890574346989739 247894563535335861520484609)
        ·
          refine ⟨185920922651501896140363457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247894563535335861520484609 185920922651501896140363457)
          ·
            refine ⟨139440691988626422105272593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185920922651501896140363457 139440691988626422105272593)
            ·
              refine ⟨104580518991469816578954445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139440691988626422105272593 104580518991469816578954445)
              ·
                refine ⟨39217694621801181217107917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104580518991469816578954445 39217694621801181217107917)
                ·
                  refine ⟨14706635483175442956415469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39217694621801181217107917 14706635483175442956415469)
                  ·
                    refine ⟨5514988306190791108655801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14706635483175442956415469 5514988306190791108655801)
                    ·
                      refine ⟨4136241229643093331491851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5514988306190791108655801 4136241229643093331491851)
                      ·
                        rfl

theorem cell23_8055301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 3, 2].length) (baseStart_8055301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055301 prefixEnd_8055301 := by exact prefixLift 8055301
  have htrace : WordTrace (prefixWord ++ tailWord_8055301) baseStart_8055301 baseEnd_8055301 := by
    simpa [prefixWord, tailWord_8055301, baseEnd_8055301] using wordTrace_append hprefix tailTrace_8055301
  have hstable : (prefixWord ++ tailWord_8055301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055301).length < 2 ^ (prefixWord ++ tailWord_8055301).sum := by decide
  have hdescent : baseEnd_8055301 < baseStart_8055301 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055344 : List Nat := [2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 4]
def baseStart_8055344 : Nat := 118140960795 + 8055344 * 2 ^ 59
def prefixEnd_8055344 : Nat := 4983230072969 + 3 ^ 40 * 8055344 * 2
def baseEnd_8055344 : Nat := 4136263309311236663254153

theorem tailTrace_8055344 : CollatzResearch.WordTrace tailWord_8055344 prefixEnd_8055344 4136263309311236663254153 := by
  unfold tailWord_8055344
  simp only [CollatzResearch.WordTrace]
  refine ⟨146901266264435953035898543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195868355019247937381198057 146901266264435953035898543)
  ·
    refine ⟨220351899396653929553847815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146901266264435953035898543 220351899396653929553847815)
    ·
      refine ⟨330527849094980894330771723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220351899396653929553847815 330527849094980894330771723)
      ·
        refine ⟨495791773642471341496157585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330527849094980894330771723 495791773642471341496157585)
        ·
          refine ⟨371843830231853506122118189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 495791773642471341496157585 371843830231853506122118189)
          ·
            refine ⟨139441436336945064795794321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 371843830231853506122118189 139441436336945064795794321)
            ·
              refine ⟨104581077252708798596845741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139441436336945064795794321 104581077252708798596845741)
              ·
                refine ⟨39217903969765799473817153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104581077252708798596845741 39217903969765799473817153)
                ·
                  refine ⟨29413427977324349605362865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39217903969765799473817153 29413427977324349605362865)
                  ·
                    refine ⟨22060070982993262204022149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29413427977324349605362865 22060070982993262204022149)
                    ·
                      refine ⟨4136263309311236663254153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22060070982993262204022149 4136263309311236663254153)
                      ·
                        rfl

theorem cell23_8055344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 4].length) (baseStart_8055344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055344 prefixEnd_8055344 := by exact prefixLift 8055344
  have htrace : WordTrace (prefixWord ++ tailWord_8055344) baseStart_8055344 baseEnd_8055344 := by
    simpa [prefixWord, tailWord_8055344, baseEnd_8055344] using wordTrace_append hprefix tailTrace_8055344
  have hstable : (prefixWord ++ tailWord_8055344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055344).length < 2 ^ (prefixWord ++ tailWord_8055344).sum := by decide
  have hdescent : baseEnd_8055344 < baseStart_8055344 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055431 : List Nat := [1, 1, 4, 2, 1, 2, 1, 2, 5, 4]
def baseStart_8055431 : Nat := 118140960795 + 8055431 * 2 ^ 59
def prefixEnd_8055431 : Nat := 4983230072969 + 3 ^ 40 * 8055431 * 2
def baseEnd_8055431 : Nat := 1378769327376059274288751

theorem tailTrace_8055431 : CollatzResearch.WordTrace tailWord_8055431 prefixEnd_8055431 1378769327376059274288751 := by
  unfold tailWord_8055431
  simp only [CollatzResearch.WordTrace]
  refine ⟨293805705679556719930214147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195870470453037813286809431 293805705679556719930214147)
  ·
    refine ⟨440708558519335079895321221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293805705679556719930214147 440708558519335079895321221)
    ·
      refine ⟨82632854722375327480372729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 440708558519335079895321221 82632854722375327480372729)
      ·
        refine ⟨61974641041781495610279547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82632854722375327480372729 61974641041781495610279547)
        ·
          refine ⟨92961961562672243415419321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61974641041781495610279547 92961961562672243415419321)
          ·
            refine ⟨69721471172004182561564491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92961961562672243415419321 69721471172004182561564491)
            ·
              refine ⟨104582206758006273842346737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69721471172004182561564491 104582206758006273842346737)
              ·
                refine ⟨78436655068504705381760053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104582206758006273842346737 78436655068504705381760053)
                ·
                  refine ⟨7353436412672316129540005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78436655068504705381760053 7353436412672316129540005)
                  ·
                    refine ⟨1378769327376059274288751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7353436412672316129540005 1378769327376059274288751)
                    ·
                      rfl

theorem cell23_8055431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 5, 4].length) (baseStart_8055431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055431 prefixEnd_8055431 := by exact prefixLift 8055431
  have htrace : WordTrace (prefixWord ++ tailWord_8055431) baseStart_8055431 baseEnd_8055431 := by
    simpa [prefixWord, tailWord_8055431, baseEnd_8055431] using wordTrace_append hprefix tailTrace_8055431
  have hstable : (prefixWord ++ tailWord_8055431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055431).length < 2 ^ (prefixWord ++ tailWord_8055431).sum := by decide
  have hdescent : baseEnd_8055431 < baseStart_8055431 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055438 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2]
def baseStart_8055438 : Nat := 118140960795 + 8055438 * 2 ^ 59
def prefixEnd_8055438 : Nat := 4983230072969 + 3 ^ 40 * 8055438 * 2
def baseEnd_8055438 : Nat := 4136311576492759295478721

theorem tailTrace_8055438 : CollatzResearch.WordTrace tailWord_8055438 prefixEnd_8055438 4136311576492759295478721 := by
  unfold tailWord_8055438
  simp only [CollatzResearch.WordTrace]
  refine ⟨36725745123816420015714871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195870640660354240083812645 36725745123816420015714871)
  ·
    refine ⟨55088617685724630023572307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36725745123816420015714871 55088617685724630023572307)
    ·
      refine ⟨82632926528586945035358461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55088617685724630023572307 82632926528586945035358461)
      ·
        refine ⟨30987347448220104388259423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82632926528586945035358461 30987347448220104388259423)
        ·
          refine ⟨46481021172330156582389135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30987347448220104388259423 46481021172330156582389135)
          ·
            refine ⟨69721531758495234873583703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46481021172330156582389135 69721531758495234873583703)
            ·
              refine ⟨104582297637742852310375555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69721531758495234873583703 104582297637742852310375555)
              ·
                refine ⟨156873446456614278465563333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104582297637742852310375555 156873446456614278465563333)
                ·
                  refine ⟨29413771210615177212293125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156873446456614278465563333 29413771210615177212293125)
                  ·
                    refine ⟨5515082101990345727304961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29413771210615177212293125 5515082101990345727304961)
                    ·
                      refine ⟨4136311576492759295478721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5515082101990345727304961 4136311576492759295478721)
                      ·
                        rfl

theorem cell23_8055438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_8055438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055438 prefixEnd_8055438 := by exact prefixLift 8055438
  have htrace : WordTrace (prefixWord ++ tailWord_8055438) baseStart_8055438 baseEnd_8055438 := by
    simpa [prefixWord, tailWord_8055438, baseEnd_8055438] using wordTrace_append hprefix tailTrace_8055438
  have hstable : (prefixWord ++ tailWord_8055438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055438).length < 2 ^ (prefixWord ++ tailWord_8055438).sum := by decide
  have hdescent : baseEnd_8055438 < baseStart_8055438 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055448 : List Nat := [2, 1, 2, 4, 1, 1, 4, 1, 3, 4]
def baseStart_8055448 : Nat := 118140960795 + 8055448 * 2 ^ 59
def prefixEnd_8055448 : Nat := 4983230072969 + 3 ^ 40 * 8055448 * 2
def baseEnd_8055448 : Nat := 1378772237099768085451225

theorem tailTrace_8055448 : CollatzResearch.WordTrace tailWord_8055448 prefixEnd_8055448 1378772237099768085451225 := by
  unfold tailWord_8055448
  simp only [CollatzResearch.WordTrace]
  refine ⟨146903162860247565916791499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195870883813663421222388665 146903162860247565916791499)
  ·
    refine ⟨220354744290371348875187249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146903162860247565916791499 220354744290371348875187249)
    ·
      refine ⟨165266058217778511656390437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220354744290371348875187249 165266058217778511656390437)
      ·
        refine ⟨30987385915833470935573207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165266058217778511656390437 30987385915833470935573207)
        ·
          refine ⟨46481078873750206403359811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30987385915833470935573207 46481078873750206403359811)
          ·
            refine ⟨69721618310625309605039717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46481078873750206403359811 69721618310625309605039717)
            ·
              refine ⟨13072803433242245550944947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69721618310625309605039717 13072803433242245550944947)
              ·
                refine ⟨19609205149863368326417421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13072803433242245550944947 19609205149863368326417421)
                ·
                  refine ⟨7353451931198763122406533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19609205149863368326417421 7353451931198763122406533)
                  ·
                    refine ⟨1378772237099768085451225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7353451931198763122406533 1378772237099768085451225)
                    ·
                      rfl

theorem cell23_8055448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 3, 4].length) (baseStart_8055448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055448 prefixEnd_8055448 := by exact prefixLift 8055448
  have htrace : WordTrace (prefixWord ++ tailWord_8055448) baseStart_8055448 baseEnd_8055448 := by
    simpa [prefixWord, tailWord_8055448, baseEnd_8055448] using wordTrace_append hprefix tailTrace_8055448
  have hstable : (prefixWord ++ tailWord_8055448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055448).length < 2 ^ (prefixWord ++ tailWord_8055448).sum := by decide
  have hdescent : baseEnd_8055448 < baseStart_8055448 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055525 : List Nat := [1, 3, 1, 4, 1, 4, 1, 2, 1, 5]
def baseStart_8055525 : Nat := 118140960795 + 8055525 * 2 ^ 59
def prefixEnd_8055525 : Nat := 4983230072969 + 3 ^ 40 * 8055525 * 2
def baseEnd_8055525 : Nat := 1378785416436566818363607

theorem tailTrace_8055525 : CollatzResearch.WordTrace tailWord_8055525 prefixEnd_8055525 1378785416436566818363607 := by
  unfold tailWord_8055525
  simp only [CollatzResearch.WordTrace]
  refine ⟨293809134141216173984136029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195872756094144115989424019 293809134141216173984136029)
  ·
    refine ⟨110178425302956065244051011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293809134141216173984136029 110178425302956065244051011)
    ·
      refine ⟨165267637954434097866076517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110178425302956065244051011 165267637954434097866076517)
      ·
        refine ⟨30987682116456393349889347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165267637954434097866076517 30987682116456393349889347)
        ·
          refine ⟨46481523174684590024834021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30987682116456393349889347 46481523174684590024834021)
          ·
            refine ⟨8715285595253360629656379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46481523174684590024834021 8715285595253360629656379)
            ·
              refine ⟨13072928392880040944484569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8715285595253360629656379 13072928392880040944484569)
              ·
                refine ⟨9804696294660030708363427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13072928392880040944484569 9804696294660030708363427)
                ·
                  refine ⟨14707044441990046062545141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9804696294660030708363427 14707044441990046062545141)
                  ·
                    refine ⟨1378785416436566818363607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14707044441990046062545141 1378785416436566818363607)
                    ·
                      rfl

theorem cell23_8055525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 5].length) (baseStart_8055525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055525 prefixEnd_8055525 := by exact prefixLift 8055525
  have htrace : WordTrace (prefixWord ++ tailWord_8055525) baseStart_8055525 baseEnd_8055525 := by
    simpa [prefixWord, tailWord_8055525, baseEnd_8055525] using wordTrace_append hprefix tailTrace_8055525
  have hstable : (prefixWord ++ tailWord_8055525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055525).length < 2 ^ (prefixWord ++ tailWord_8055525).sum := by decide
  have hdescent : baseEnd_8055525 < baseStart_8055525 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055538 : List Nat := [3, 2, 1, 3, 1, 3, 1, 2, 1, 6]
def baseStart_8055538 : Nat := 118140960795 + 8055538 * 2 ^ 59
def prefixEnd_8055538 : Nat := 4983230072969 + 3 ^ 40 * 8055538 * 2
def baseEnd_8055538 : Nat := 1378787641519402968076087

theorem tailTrace_8055538 : CollatzResearch.WordTrace tailWord_8055538 prefixEnd_8055538 1378787641519402968076087 := by
  unfold tailWord_8055538
  simp only [CollatzResearch.WordTrace]
  refine ⟨73452402072542269301089817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195873072193446051469572845 73452402072542269301089817)
  ·
    refine ⟨55089301554406701975817363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73452402072542269301089817 55089301554406701975817363)
    ·
      refine ⟨82633952331610052963726045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55089301554406701975817363 82633952331610052963726045)
      ·
        refine ⟨30987732124353769861397267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82633952331610052963726045 30987732124353769861397267)
        ·
          refine ⟨46481598186530654792095901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30987732124353769861397267 46481598186530654792095901)
          ·
            refine ⟨17430599319948995547035963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46481598186530654792095901 17430599319948995547035963)
            ·
              refine ⟨26145898979923493320553945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17430599319948995547035963 26145898979923493320553945)
              ·
                refine ⟨19609424234942619990415459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26145898979923493320553945 19609424234942619990415459)
                ·
                  refine ⟨29414136352413929985623189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19609424234942619990415459 29414136352413929985623189)
                  ·
                    refine ⟨1378787641519402968076087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29414136352413929985623189 1378787641519402968076087)
                    ·
                      rfl

theorem cell23_8055538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_8055538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055538 prefixEnd_8055538 := by exact prefixLift 8055538
  have htrace : WordTrace (prefixWord ++ tailWord_8055538) baseStart_8055538 baseEnd_8055538 := by
    simpa [prefixWord, tailWord_8055538, baseEnd_8055538] using wordTrace_append hprefix tailTrace_8055538
  have hstable : (prefixWord ++ tailWord_8055538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055538).length < 2 ^ (prefixWord ++ tailWord_8055538).sum := by decide
  have hdescent : baseEnd_8055538 < baseStart_8055538 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055548 : List Nat := [2, 2, 2, 1, 3, 2, 3, 1, 1, 1, 5]
def baseStart_8055548 : Nat := 118140960795 + 8055548 * 2 ^ 59
def prefixEnd_8055548 : Nat := 4983230072969 + 3 ^ 40 * 8055548 * 2
def baseEnd_8055548 : Nat := 4136368059364753865103215

theorem tailTrace_8055548 : CollatzResearch.WordTrace tailWord_8055548 prefixEnd_8055548 4136368059364753865103215 := by
  unfold tailWord_8055548
  simp only [CollatzResearch.WordTrace]
  refine ⟨146904986510066424456111649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195873315346755232608148865 146904986510066424456111649)
  ·
    refine ⟨110178739882549818342083737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146904986510066424456111649 110178739882549818342083737)
    ·
      refine ⟨82634054911912363756562803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110178739882549818342083737 82634054911912363756562803)
      ·
        refine ⟨123951082367868545634844205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82634054911912363756562803 123951082367868545634844205)
        ·
          refine ⟨46481655887950704613066577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123951082367868545634844205 46481655887950704613066577)
          ·
            refine ⟨34861241915963028459799933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46481655887950704613066577 34861241915963028459799933)
            ·
              refine ⟨13072965718486135672424975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34861241915963028459799933 13072965718486135672424975)
              ·
                refine ⟨19609448577729203508637463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13072965718486135672424975 19609448577729203508637463)
                ·
                  refine ⟨29414172866593805262956195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19609448577729203508637463 29414172866593805262956195)
                  ·
                    refine ⟨44121259299890707894434293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29414172866593805262956195 44121259299890707894434293)
                    ·
                      refine ⟨4136368059364753865103215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44121259299890707894434293 4136368059364753865103215)
                      ·
                        rfl

theorem cell23_8055548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 1, 1, 5].length) (baseStart_8055548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055548 prefixEnd_8055548 := by exact prefixLift 8055548
  have htrace : WordTrace (prefixWord ++ tailWord_8055548) baseStart_8055548 baseEnd_8055548 := by
    simpa [prefixWord, tailWord_8055548, baseEnd_8055548] using wordTrace_append hprefix tailTrace_8055548
  have hstable : (prefixWord ++ tailWord_8055548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055548).length < 2 ^ (prefixWord ++ tailWord_8055548).sum := by decide
  have hdescent : baseEnd_8055548 < baseStart_8055548 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055575 : List Nat := [1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 4]
def baseStart_8055575 : Nat := 118140960795 + 8055575 * 2 ^ 59
def prefixEnd_8055575 : Nat := 4983230072969 + 3 ^ 40 * 8055575 * 2
def baseEnd_8055575 : Nat := 4136381923342425259465591

theorem tailTrace_8055575 : CollatzResearch.WordTrace tailWord_8055575 prefixEnd_8055575 4136381923342425259465591 := by
  unfold tailWord_8055575
  simp only [CollatzResearch.WordTrace]
  refine ⟨293810957791035032523456179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195873971860690021682304119 293810957791035032523456179)
  ·
    refine ⟨440716436686552548785184269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293810957791035032523456179 440716436686552548785184269)
    ·
      refine ⟨165268663757457205794444101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 440716436686552548785184269 165268663757457205794444101)
      ·
        refine ⟨30987874454523226086458269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165268663757457205794444101 30987874454523226086458269)
        ·
          refine ⟨11620452920446209782421851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30987874454523226086458269 11620452920446209782421851)
          ·
            refine ⟨17430679380669314673632777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11620452920446209782421851 17430679380669314673632777)
            ·
              refine ⟨13073009535501986005224583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17430679380669314673632777 13073009535501986005224583)
              ·
                refine ⟨19609514303252979007836875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13073009535501986005224583 19609514303252979007836875)
                ·
                  refine ⟨29414271454879468511755313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19609514303252979007836875 29414271454879468511755313)
                  ·
                    refine ⟨22060703591159601383816485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29414271454879468511755313 22060703591159601383816485)
                    ·
                      refine ⟨4136381923342425259465591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22060703591159601383816485 4136381923342425259465591)
                      ·
                        rfl

theorem cell23_8055575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_8055575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055575 prefixEnd_8055575 := by exact prefixLift 8055575
  have htrace : WordTrace (prefixWord ++ tailWord_8055575) baseStart_8055575 baseEnd_8055575 := by
    simpa [prefixWord, tailWord_8055575, baseEnd_8055575] using wordTrace_append hprefix tailTrace_8055575
  have hstable : (prefixWord ++ tailWord_8055575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055575).length < 2 ^ (prefixWord ++ tailWord_8055575).sum := by decide
  have hdescent : baseEnd_8055575 < baseStart_8055575 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055606 : List Nat := [5, 1, 2, 2, 3, 1, 1, 2, 2, 4]
def baseStart_8055606 : Nat := 118140960795 + 8055606 * 2 ^ 59
def prefixEnd_8055606 : Nat := 4983230072969 + 3 ^ 40 * 8055606 * 2
def baseEnd_8055606 : Nat := 1378799280414238212725983

theorem tailTrace_8055606 : CollatzResearch.WordTrace tailWord_8055606 prefixEnd_8055606 1378799280414238212725983 := by
  unfold tailWord_8055606
  simp only [CollatzResearch.WordTrace]
  refine ⟨18363255528370170301114667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195874725635948483211889781 18363255528370170301114667)
  ·
    refine ⟨27544883292555255451672001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18363255528370170301114667 27544883292555255451672001)
    ·
      refine ⟨20658662469416441588754001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27544883292555255451672001 20658662469416441588754001)
      ·
        refine ⟨15493996852062331191565501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20658662469416441588754001 15493996852062331191565501)
        ·
          refine ⟨5810248819523374196837063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15493996852062331191565501 5810248819523374196837063)
          ·
            refine ⟨8715373229285061295255595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5810248819523374196837063 8715373229285061295255595)
            ·
              refine ⟨13073059843927591942883393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8715373229285061295255595 13073059843927591942883393)
              ·
                refine ⟨9804794882945693957162545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13073059843927591942883393 9804794882945693957162545)
                ·
                  refine ⟨7353596162209270467871909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9804794882945693957162545 7353596162209270467871909)
                  ·
                    refine ⟨1378799280414238212725983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7353596162209270467871909 1378799280414238212725983)
                    ·
                      rfl

theorem cell23_8055606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_8055606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055606 prefixEnd_8055606 := by exact prefixLift 8055606
  have htrace : WordTrace (prefixWord ++ tailWord_8055606) baseStart_8055606 baseEnd_8055606 := by
    simpa [prefixWord, tailWord_8055606, baseEnd_8055606] using wordTrace_append hprefix tailTrace_8055606
  have hstable : (prefixWord ++ tailWord_8055606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055606).length < 2 ^ (prefixWord ++ tailWord_8055606).sum := by decide
  have hdescent : baseEnd_8055606 < baseStart_8055606 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055621 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 3, 3, 5]
def baseStart_8055621 : Nat := 118140960795 + 8055621 * 2 ^ 59
def prefixEnd_8055621 : Nat := 4983230072969 + 3 ^ 40 * 8055621 * 2
def baseEnd_8055621 : Nat := 4136405543452532079490379

theorem tailTrace_8055621 : CollatzResearch.WordTrace tailWord_8055621 prefixEnd_8055621 4136405543452532079490379 := by
  unfold tailWord_8055621
  simp only [CollatzResearch.WordTrace]
  refine ⟨293812635548868382379630717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195875090365912254919753811 293812635548868382379630717)
  ·
    refine ⟨110179738330825643392361519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293812635548868382379630717 110179738330825643392361519)
    ·
      refine ⟨165269607496238465088542279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110179738330825643392361519 165269607496238465088542279)
      ·
        refine ⟨247904411244357697632813419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165269607496238465088542279 247904411244357697632813419)
        ·
          refine ⟨371856616866536546449220129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247904411244357697632813419 371856616866536546449220129)
          ·
            refine ⟨278892462649902409836915097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371856616866536546449220129 278892462649902409836915097)
            ·
              refine ⟨209169346987426807377686323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278892462649902409836915097 209169346987426807377686323)
              ·
                refine ⟨313754020481140211066529485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209169346987426807377686323 313754020481140211066529485)
                ·
                  refine ⟨117657757680427579149948557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 313754020481140211066529485 117657757680427579149948557)
                  ·
                    refine ⟨44121659130160342181230709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117657757680427579149948557 44121659130160342181230709)
                    ·
                      refine ⟨4136405543452532079490379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44121659130160342181230709 4136405543452532079490379)
                      ·
                        rfl

theorem cell23_8055621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_8055621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055621 prefixEnd_8055621 := by exact prefixLift 8055621
  have htrace : WordTrace (prefixWord ++ tailWord_8055621) baseStart_8055621 baseEnd_8055621 := by
    simpa [prefixWord, tailWord_8055621, baseEnd_8055621] using wordTrace_append hprefix tailTrace_8055621
  have hstable : (prefixWord ++ tailWord_8055621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055621).length < 2 ^ (prefixWord ++ tailWord_8055621).sum := by decide
  have hdescent : baseEnd_8055621 < baseStart_8055621 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055628 : List Nat := [2, 2, 1, 3, 3, 1, 2, 1, 2, 6]
def baseStart_8055628 : Nat := 118140960795 + 8055628 * 2 ^ 59
def prefixEnd_8055628 : Nat := 4983230072969 + 3 ^ 40 * 8055628 * 2
def baseEnd_8055628 : Nat := 1378803045939037850700949

theorem tailTrace_8055628 : CollatzResearch.WordTrace tailWord_8055628 prefixEnd_8055628 1378803045939037850700949 := by
  unfold tailWord_8055628
  simp only [CollatzResearch.WordTrace]
  refine ⟨146906445429921511287567769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195875260573228681716757025 146906445429921511287567769)
  ·
    refine ⟨110179834072441133465675827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146906445429921511287567769 110179834072441133465675827)
    ·
      refine ⟨165269751108661700198513741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110179834072441133465675827 165269751108661700198513741)
      ·
        refine ⟨61976156665748137574442653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165269751108661700198513741 61976156665748137574442653)
        ·
          refine ⟨23241058749655551590415995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61976156665748137574442653 23241058749655551590415995)
          ·
            refine ⟨34861588124483327385623993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23241058749655551590415995 34861588124483327385623993)
            ·
              refine ⟨26146191093362495539217995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34861588124483327385623993 26146191093362495539217995)
              ·
                refine ⟨39219286640043743308826993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26146191093362495539217995 39219286640043743308826993)
                ·
                  refine ⟨29414464980032807481620245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39219286640043743308826993 29414464980032807481620245)
                  ·
                    refine ⟨1378803045939037850700949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29414464980032807481620245 1378803045939037850700949)
                    ·
                      rfl

theorem cell23_8055628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 2, 6].length) (baseStart_8055628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055628 prefixEnd_8055628 := by exact prefixLift 8055628
  have htrace : WordTrace (prefixWord ++ tailWord_8055628) baseStart_8055628 baseEnd_8055628 := by
    simpa [prefixWord, tailWord_8055628, baseEnd_8055628] using wordTrace_append hprefix tailTrace_8055628
  have hstable : (prefixWord ++ tailWord_8055628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055628).length < 2 ^ (prefixWord ++ tailWord_8055628).sum := by decide
  have hdescent : baseEnd_8055628 < baseStart_8055628 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055629 : List Nat := [1, 6, 1, 2, 2, 2, 1, 1, 1, 3, 3]
def baseStart_8055629 : Nat := 118140960795 + 8055629 * 2 ^ 59
def prefixEnd_8055629 : Nat := 4983230072969 + 3 ^ 40 * 8055629 * 2
def baseEnd_8055629 : Nat := 4136409651297768048190343

theorem tailTrace_8055629 : CollatzResearch.WordTrace tailWord_8055629 prefixEnd_8055629 4136409651297768048190343 := by
  unfold tailWord_8055629
  simp only [CollatzResearch.WordTrace]
  refine ⟨293812927332839399745921941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195875284888559599830614627 293812927332839399745921941)
  ·
    refine ⟨13772480968726846863090091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 293812927332839399745921941 13772480968726846863090091)
    ·
      refine ⟨20658721453090270294635137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13772480968726846863090091 20658721453090270294635137)
      ·
        refine ⟨15494041089817702720976353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20658721453090270294635137 15494041089817702720976353)
        ·
          refine ⟨11620530817363277040732265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15494041089817702720976353 11620530817363277040732265)
          ·
            refine ⟨8715398113022457780549199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11620530817363277040732265 8715398113022457780549199)
            ·
              refine ⟨13073097169533686670823799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8715398113022457780549199 13073097169533686670823799)
              ·
                refine ⟨19609645754300530006235699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13073097169533686670823799 19609645754300530006235699)
                ·
                  refine ⟨29414468631450795009353549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19609645754300530006235699 29414468631450795009353549)
                  ·
                    refine ⟨11030425736794048128507581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29414468631450795009353549 11030425736794048128507581)
                    ·
                      refine ⟨4136409651297768048190343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11030425736794048128507581 4136409651297768048190343)
                      ·
                        rfl

theorem cell23_8055629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_8055629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055629 prefixEnd_8055629 := by exact prefixLift 8055629
  have htrace : WordTrace (prefixWord ++ tailWord_8055629) baseStart_8055629 baseEnd_8055629 := by
    simpa [prefixWord, tailWord_8055629, baseEnd_8055629] using wordTrace_append hprefix tailTrace_8055629
  have hstable : (prefixWord ++ tailWord_8055629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055629).length < 2 ^ (prefixWord ++ tailWord_8055629).sum := by decide
  have hdescent : baseEnd_8055629 < baseStart_8055629 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055652 : List Nat := [2, 3, 1, 1, 4, 1, 1, 2, 4, 2, 2]
def baseStart_8055652 : Nat := 118140960795 + 8055652 * 2 ^ 59
def prefixEnd_8055652 : Nat := 4983230072969 + 3 ^ 40 * 8055652 * 2
def baseEnd_8055652 : Nat := 4136421461352821458202737

theorem tailTrace_8055652 : CollatzResearch.WordTrace tailWord_8055652 prefixEnd_8055652 4136421461352821458202737 := by
  unfold tailWord_8055652
  simp only [CollatzResearch.WordTrace]
  refine ⟨146906883105878037337004605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195875844141170716449339473 146906883105878037337004605)
  ·
    refine ⟨55090081164704264001376727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146906883105878037337004605 55090081164704264001376727)
    ·
      refine ⟨82635121747056396002065091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55090081164704264001376727 82635121747056396002065091)
      ·
        refine ⟨123952682620584594003097637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82635121747056396002065091 123952682620584594003097637)
        ·
          refine ⟨23241127991359611375580807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123952682620584594003097637 23241127991359611375580807)
          ·
            refine ⟨34861691987039417063371211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23241127991359611375580807 34861691987039417063371211)
            ·
              refine ⟨52292537980559125595056817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34861691987039417063371211 52292537980559125595056817)
              ·
                refine ⟨39219403485419344196292613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52292537980559125595056817 39219403485419344196292613)
                ·
                  refine ⟨7353638153516127036804865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39219403485419344196292613 7353638153516127036804865)
                  ·
                    refine ⟨5515228615137095277603649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7353638153516127036804865 5515228615137095277603649)
                    ·
                      refine ⟨4136421461352821458202737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5515228615137095277603649 4136421461352821458202737)
                      ·
                        rfl

theorem cell23_8055652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 4, 2, 2].length) (baseStart_8055652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055652 prefixEnd_8055652 := by exact prefixLift 8055652
  have htrace : WordTrace (prefixWord ++ tailWord_8055652) baseStart_8055652 baseEnd_8055652 := by
    simpa [prefixWord, tailWord_8055652, baseEnd_8055652] using wordTrace_append hprefix tailTrace_8055652
  have hstable : (prefixWord ++ tailWord_8055652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055652).length < 2 ^ (prefixWord ++ tailWord_8055652).sum := by decide
  have hdescent : baseEnd_8055652 < baseStart_8055652 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055732 : List Nat := [2, 5, 2, 1, 1, 1, 2, 1, 1, 2, 5]
def baseStart_8055732 : Nat := 118140960795 + 8055732 * 2 ^ 59
def prefixEnd_8055732 : Nat := 4983230072969 + 3 ^ 40 * 8055732 * 2
def baseEnd_8055732 : Nat := 4136462539805181145202369

theorem tailTrace_8055732 : CollatzResearch.WordTrace tailWord_8055732 prefixEnd_8055732 4136462539805181145202369 := by
  unfold tailWord_8055732
  simp only [CollatzResearch.WordTrace]
  refine ⟨146908342025733124168460725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195877789367644165557947633 146908342025733124168460725)
  ·
    refine ⟨13772657064912480390793193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146908342025733124168460725 13772657064912480390793193)
    ·
      refine ⟨10329492798684360293094895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13772657064912480390793193 10329492798684360293094895)
      ·
        refine ⟨15494239198026540439642343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10329492798684360293094895 15494239198026540439642343)
        ·
          refine ⟨23241358797039810659463515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15494239198026540439642343 23241358797039810659463515)
          ·
            refine ⟨34862038195559715989195273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23241358797039810659463515 34862038195559715989195273)
            ·
              refine ⟨26146528646669786991896455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34862038195559715989195273 26146528646669786991896455)
              ·
                refine ⟨39219792970004680487844683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26146528646669786991896455 39219792970004680487844683)
                ·
                  refine ⟨58829689455007020731767025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39219792970004680487844683 58829689455007020731767025)
                  ·
                    refine ⟨44122267091255265548825269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58829689455007020731767025 44122267091255265548825269)
                    ·
                      refine ⟨4136462539805181145202369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44122267091255265548825269 4136462539805181145202369)
                      ·
                        rfl

theorem cell23_8055732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_8055732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055732 prefixEnd_8055732 := by exact prefixLift 8055732
  have htrace : WordTrace (prefixWord ++ tailWord_8055732) baseStart_8055732 baseEnd_8055732 := by
    simpa [prefixWord, tailWord_8055732, baseEnd_8055732] using wordTrace_append hprefix tailTrace_8055732
  have hstable : (prefixWord ++ tailWord_8055732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055732).length < 2 ^ (prefixWord ++ tailWord_8055732).sum := by decide
  have hdescent : baseEnd_8055732 < baseStart_8055732 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055742 : List Nat := [4, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2]
def baseStart_8055742 : Nat := 118140960795 + 8055742 * 2 ^ 59
def prefixEnd_8055742 : Nat := 4983230072969 + 3 ^ 40 * 8055742 * 2
def baseEnd_8055742 : Nat := 4136467674611726106077323

theorem tailTrace_8055742 : CollatzResearch.WordTrace tailWord_8055742 prefixEnd_8055742 4136467674611726106077323 := by
  unfold tailWord_8055742
  simp only [CollatzResearch.WordTrace]
  refine ⟨36727131097678752505598185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195878032520953346696523653 36727131097678752505598185)
  ·
    refine ⟨27545348323259064379198639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36727131097678752505598185 27545348323259064379198639)
    ·
      refine ⟨41318022484888596568797959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27545348323259064379198639 41318022484888596568797959)
      ·
        refine ⟨61977033727332894853196939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41318022484888596568797959 61977033727332894853196939)
        ·
          refine ⟨92965550590999342279795409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61977033727332894853196939 92965550590999342279795409)
          ·
            refine ⟨69724162943249506709846557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92965550590999342279795409 69724162943249506709846557)
            ·
              refine ⟨26146561103718565016192459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69724162943249506709846557 26146561103718565016192459)
              ·
                refine ⟨39219841655577847524288689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26146561103718565016192459 39219841655577847524288689)
                ·
                  refine ⟨29414881241683385643216517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39219841655577847524288689 29414881241683385643216517)
                  ·
                    refine ⟨5515290232815634808103097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29414881241683385643216517 5515290232815634808103097)
                    ·
                      refine ⟨4136467674611726106077323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5515290232815634808103097 4136467674611726106077323)
                      ·
                        rfl

theorem cell23_8055742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_8055742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055742 prefixEnd_8055742 := by exact prefixLift 8055742
  have htrace : WordTrace (prefixWord ++ tailWord_8055742) baseStart_8055742 baseEnd_8055742 := by
    simpa [prefixWord, tailWord_8055742, baseEnd_8055742] using wordTrace_append hprefix tailTrace_8055742
  have hstable : (prefixWord ++ tailWord_8055742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055742).length < 2 ^ (prefixWord ++ tailWord_8055742).sum := by decide
  have hdescent : baseEnd_8055742 < baseStart_8055742 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055752 : List Nat := [2, 1, 3, 1, 5, 1, 1, 2, 3, 4]
def baseStart_8055752 : Nat := 118140960795 + 8055752 * 2 ^ 59
def prefixEnd_8055752 : Nat := 4983230072969 + 3 ^ 40 * 8055752 * 2
def baseEnd_8055752 : Nat := 1378824269806090355650759

theorem tailTrace_8055752 : CollatzResearch.WordTrace tailWord_8055752 prefixEnd_8055752 1378824269806090355650759 := by
  unfold tailWord_8055752
  simp only [CollatzResearch.WordTrace]
  refine ⟨146908706755696895876324755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195878275674262527835099673 146908706755696895876324755)
  ·
    refine ⟨220363060133545343814487133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146908706755696895876324755 220363060133545343814487133)
    ·
      refine ⟨82636147550079503930432675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220363060133545343814487133 82636147550079503930432675)
      ·
        refine ⟨123954221325119255895649013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82636147550079503930432675 123954221325119255895649013)
        ·
          refine ⟨11620708249229930240217095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123954221325119255895649013 11620708249229930240217095)
          ·
            refine ⟨17431062373844895360325643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11620708249229930240217095 17431062373844895360325643)
            ·
              refine ⟨26146593560767343040488465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17431062373844895360325643 26146593560767343040488465)
              ·
                refine ⟨19609945170575507280366349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26146593560767343040488465 19609945170575507280366349)
                ·
                  refine ⟨7353729438965815230137381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19609945170575507280366349 7353729438965815230137381)
                  ·
                    refine ⟨1378824269806090355650759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7353729438965815230137381 1378824269806090355650759)
                    ·
                      rfl

theorem cell23_8055752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 3, 4].length) (baseStart_8055752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055752 prefixEnd_8055752 := by exact prefixLift 8055752
  have htrace : WordTrace (prefixWord ++ tailWord_8055752) baseStart_8055752 baseEnd_8055752 := by
    simpa [prefixWord, tailWord_8055752, baseEnd_8055752] using wordTrace_append hprefix tailTrace_8055752
  have hstable : (prefixWord ++ tailWord_8055752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055752).length < 2 ^ (prefixWord ++ tailWord_8055752).sum := by decide
  have hdescent : baseEnd_8055752 < baseStart_8055752 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055762 : List Nat := [3, 2, 2, 3, 1, 2, 1, 1, 1, 4, 3]
def baseStart_8055762 : Nat := 118140960795 + 8055762 * 2 ^ 59
def prefixEnd_8055762 : Nat := 4983230072969 + 3 ^ 40 * 8055762 * 2
def baseEnd_8055762 : Nat := 4136477944224816027827231

theorem tailTrace_8055762 : CollatzResearch.WordTrace tailWord_8055762 prefixEnd_8055762 4136477944224816027827231 := by
  unfold tailWord_8055762
  simp only [CollatzResearch.WordTrace]
  refine ⟨73454444560339390865128385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195878518827571708973675693 73454444560339390865128385)
  ·
    refine ⟨55090833420254543148846289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73454444560339390865128385 55090833420254543148846289)
    ·
      refine ⟨41318125065190907361634717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55090833420254543148846289 41318125065190907361634717)
      ·
        refine ⟨15494296899446590260613019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41318125065190907361634717 15494296899446590260613019)
        ·
          refine ⟨23241445349169885390919529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15494296899446590260613019 23241445349169885390919529)
          ·
            refine ⟨17431084011877414043189647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23241445349169885390919529 17431084011877414043189647)
            ·
              refine ⟨26146626017816121064784471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17431084011877414043189647 26146626017816121064784471)
              ·
                refine ⟨39219939026724181597176707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26146626017816121064784471 39219939026724181597176707)
                ·
                  refine ⟨58829908540086272395765061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39219939026724181597176707 58829908540086272395765061)
                  ·
                    refine ⟨11030607851266176074205949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58829908540086272395765061 11030607851266176074205949)
                    ·
                      refine ⟨4136477944224816027827231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11030607851266176074205949 4136477944224816027827231)
                      ·
                        rfl

theorem cell23_8055762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_8055762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055762 prefixEnd_8055762 := by exact prefixLift 8055762
  have htrace : WordTrace (prefixWord ++ tailWord_8055762) baseStart_8055762 baseEnd_8055762 := by
    simpa [prefixWord, tailWord_8055762, baseEnd_8055762] using wordTrace_append hprefix tailTrace_8055762
  have hstable : (prefixWord ++ tailWord_8055762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055762).length < 2 ^ (prefixWord ++ tailWord_8055762).sum := by decide
  have hdescent : baseEnd_8055762 < baseStart_8055762 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055769 : List Nat := [1, 2, 1, 2, 5, 2, 2, 3, 1, 4]
def baseStart_8055769 : Nat := 118140960795 + 8055769 * 2 ^ 59
def prefixEnd_8055769 : Nat := 4983230072969 + 3 ^ 40 * 8055769 * 2
def baseEnd_8055769 : Nat := 1378827179529799166813233

theorem tailTrace_8055769 : CollatzResearch.WordTrace tailWord_8055769 prefixEnd_8055769 1378827179529799166813233 := by
  unfold tailWord_8055769
  simp only [CollatzResearch.WordTrace]
  refine ⟨293818033552332203656018361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195878689034888135770678907 293818033552332203656018361)
  ·
    refine ⟨220363525164249152742013771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293818033552332203656018361 220363525164249152742013771)
    ·
      refine ⟨330545287746373729113020657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220363525164249152742013771 330545287746373729113020657)
      ·
        refine ⟨247908965809780296834765493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330545287746373729113020657 247908965809780296834765493)
        ·
          refine ⟨23241465544666902828259265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 247908965809780296834765493 23241465544666902828259265)
          ·
            refine ⟨17431099158500177121194449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23241465544666902828259265 17431099158500177121194449)
            ·
              refine ⟨13073324368875132840895837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17431099158500177121194449 13073324368875132840895837)
              ·
                refine ⟨4902496638328174815335939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13073324368875132840895837 4902496638328174815335939)
                ·
                  refine ⟨7353744957492262223003909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4902496638328174815335939 7353744957492262223003909)
                  ·
                    refine ⟨1378827179529799166813233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7353744957492262223003909 1378827179529799166813233)
                    ·
                      rfl

theorem cell23_8055769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 3, 1, 4].length) (baseStart_8055769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055769 prefixEnd_8055769 := by exact prefixLift 8055769
  have htrace : WordTrace (prefixWord ++ tailWord_8055769) baseStart_8055769 baseEnd_8055769 := by
    simpa [prefixWord, tailWord_8055769, baseEnd_8055769] using wordTrace_append hprefix tailTrace_8055769
  have hstable : (prefixWord ++ tailWord_8055769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055769).length < 2 ^ (prefixWord ++ tailWord_8055769).sum := by decide
  have hdescent : baseEnd_8055769 < baseStart_8055769 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055832 : List Nat := [2, 1, 2, 3, 2, 2, 2, 3, 1, 1, 4]
def baseStart_8055832 : Nat := 118140960795 + 8055832 * 2 ^ 59
def prefixEnd_8055832 : Nat := 4983230072969 + 3 ^ 40 * 8055832 * 2
def baseEnd_8055832 : Nat := 4136513887870630753951909

theorem tailTrace_8055832 : CollatzResearch.WordTrace tailWord_8055832 prefixEnd_8055832 4136513887870630753951909 := by
  unfold tailWord_8055832
  simp only [CollatzResearch.WordTrace]
  refine ⟨146910165675551982707780875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195880220900735976943707833 146910165675551982707780875)
  ·
    refine ⟨220365248513327974061671313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146910165675551982707780875 220365248513327974061671313)
    ·
      refine ⟨165273936384995980546253485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220365248513327974061671313 165273936384995980546253485)
      ·
        refine ⟨61977726144373492704845057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165273936384995980546253485 61977726144373492704845057)
        ·
          refine ⟨46483294608280119528633793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61977726144373492704845057 46483294608280119528633793)
          ·
            refine ⟨34862470956210089646475345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46483294608280119528633793 34862470956210089646475345)
            ·
              refine ⟨26146853217157567234856509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34862470956210089646475345 26146853217157567234856509)
              ·
                refine ⟨9805069956434087713071191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26146853217157567234856509 9805069956434087713071191)
                ·
                  refine ⟨14707604934651131569606787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9805069956434087713071191 14707604934651131569606787)
                  ·
                    refine ⟨22061407401976697354410181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14707604934651131569606787 22061407401976697354410181)
                    ·
                      refine ⟨4136513887870630753951909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22061407401976697354410181 4136513887870630753951909)
                      ·
                        rfl

theorem cell23_8055832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_8055832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055832 prefixEnd_8055832 := by exact prefixLift 8055832
  have htrace : WordTrace (prefixWord ++ tailWord_8055832) baseStart_8055832 baseEnd_8055832 := by
    simpa [prefixWord, tailWord_8055832, baseEnd_8055832] using wordTrace_append hprefix tailTrace_8055832
  have hstable : (prefixWord ++ tailWord_8055832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055832).length < 2 ^ (prefixWord ++ tailWord_8055832).sum := by decide
  have hdescent : baseEnd_8055832 < baseStart_8055832 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055842 : List Nat := [3, 3, 1, 1, 1, 3, 2, 1, 4, 4]
def baseStart_8055842 : Nat := 118140960795 + 8055842 * 2 ^ 59
def prefixEnd_8055842 : Nat := 4983230072969 + 3 ^ 40 * 8055842 * 2
def baseEnd_8055842 : Nat := 1378839674225725238275621

theorem tailTrace_8055842 : CollatzResearch.WordTrace tailWord_8055842 prefixEnd_8055842 1378839674225725238275621 := by
  unfold tailWord_8055842
  simp only [CollatzResearch.WordTrace]
  refine ⟨73455174020266934280856445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195880464054045158082283853 73455174020266934280856445)
  ·
    refine ⟨27545690257600100355321167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73455174020266934280856445 27545690257600100355321167)
    ·
      refine ⟨41318535386400150532981751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27545690257600100355321167 41318535386400150532981751)
      ·
        refine ⟨61977803079600225799472627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41318535386400150532981751 61977803079600225799472627)
        ·
          refine ⟨92966704619400338699208941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61977803079600225799472627 92966704619400338699208941)
          ·
            refine ⟨34862514232275127012203353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92966704619400338699208941 34862514232275127012203353)
            ·
              refine ⟨26146885674206345259152515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34862514232275127012203353 26146885674206345259152515)
              ·
                refine ⟨39220328511309517888728773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26146885674206345259152515 39220328511309517888728773)
                ·
                  refine ⟨7353811595870534604136645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39220328511309517888728773 7353811595870534604136645)
                  ·
                    refine ⟨1378839674225725238275621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7353811595870534604136645 1378839674225725238275621)
                    ·
                      rfl

theorem cell23_8055842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_8055842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055842 prefixEnd_8055842 := by exact prefixLift 8055842
  have htrace : WordTrace (prefixWord ++ tailWord_8055842) baseStart_8055842 baseEnd_8055842 := by
    simpa [prefixWord, tailWord_8055842, baseEnd_8055842] using wordTrace_append hprefix tailTrace_8055842
  have hstable : (prefixWord ++ tailWord_8055842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055842).length < 2 ^ (prefixWord ++ tailWord_8055842).sum := by decide
  have hdescent : baseEnd_8055842 < baseStart_8055842 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055862 : List Nat := [5, 1, 2, 1, 1, 2, 2, 1, 1, 1, 6]
def baseStart_8055862 : Nat := 118140960795 + 8055862 * 2 ^ 59
def prefixEnd_8055862 : Nat := 4983230072969 + 3 ^ 40 * 8055862 * 2
def baseEnd_8055862 : Nat := 4136529292290265636576771

theorem tailTrace_8055862 : CollatzResearch.WordTrace tailWord_8055862 prefixEnd_8055862 4136529292290265636576771 := by
  unfold tailWord_8055862
  simp only [CollatzResearch.WordTrace]
  refine ⟨18363839096312205033697115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195880950360663520359435893 18363839096312205033697115)
  ·
    refine ⟨27545758644468307550545673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18363839096312205033697115 27545758644468307550545673)
    ·
      refine ⟨20659318983351230662909255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27545758644468307550545673 20659318983351230662909255)
      ·
        refine ⟨30988978475026845994363883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20659318983351230662909255 30988978475026845994363883)
        ·
          refine ⟨46483467712540268991545825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30988978475026845994363883 46483467712540268991545825)
          ·
            refine ⟨34862600784405201743659369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46483467712540268991545825 34862600784405201743659369)
            ·
              refine ⟨26146950588303901307744527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34862600784405201743659369 26146950588303901307744527)
              ·
                refine ⟨39220425882455851961616791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26146950588303901307744527 39220425882455851961616791)
                ·
                  refine ⟨58830638823683777942425187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39220425882455851961616791 58830638823683777942425187)
                  ·
                    refine ⟨88245958235525666913637781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58830638823683777942425187 88245958235525666913637781)
                    ·
                      refine ⟨4136529292290265636576771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88245958235525666913637781 4136529292290265636576771)
                      ·
                        rfl

theorem cell23_8055862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_8055862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055862 prefixEnd_8055862 := by exact prefixLift 8055862
  have htrace : WordTrace (prefixWord ++ tailWord_8055862) baseStart_8055862 baseEnd_8055862 := by
    simpa [prefixWord, tailWord_8055862, baseEnd_8055862] using wordTrace_append hprefix tailTrace_8055862
  have hstable : (prefixWord ++ tailWord_8055862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055862).length < 2 ^ (prefixWord ++ tailWord_8055862).sum := by decide
  have hdescent : baseEnd_8055862 < baseStart_8055862 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055869 : List Nat := [1, 4, 1, 3, 1, 2, 3, 2, 1, 2, 3]
def baseStart_8055869 : Nat := 118140960795 + 8055869 * 2 ^ 59
def prefixEnd_8055869 : Nat := 4983230072969 + 3 ^ 40 * 8055869 * 2
def baseEnd_8055869 : Nat := 4136532886654847109189239

theorem tailTrace_8055869 : CollatzResearch.WordTrace tailWord_8055869 prefixEnd_8055869 4136532886654847109189239 := by
  unfold tailWord_8055869
  simp only [CollatzResearch.WordTrace]
  refine ⟨293821680851969920734658661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195881120567979947156439107 293821680851969920734658661)
  ·
    refine ⟨55091565159744360137748499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293821680851969920734658661 55091565159744360137748499)
    ·
      refine ⟨82637347739616540206622749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55091565159744360137748499 82637347739616540206622749)
      ·
        refine ⟨30989005402356202577483531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82637347739616540206622749 30989005402356202577483531)
        ·
          refine ⟨46483508103534303866225297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30989005402356202577483531 46483508103534303866225297)
          ·
            refine ⟨34862631077650727899668973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46483508103534303866225297 34862631077650727899668973)
            ·
              refine ⟨13073486654119022962375865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34862631077650727899668973 13073486654119022962375865)
              ·
                refine ⟨9805114990589267221781899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13073486654119022962375865 9805114990589267221781899)
                ·
                  refine ⟨14707672485883900832672849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9805114990589267221781899 14707672485883900832672849)
                  ·
                    refine ⟨11030754364412925624504637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14707672485883900832672849 11030754364412925624504637)
                    ·
                      refine ⟨4136532886654847109189239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11030754364412925624504637 4136532886654847109189239)
                      ·
                        rfl

theorem cell23_8055869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_8055869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055869 prefixEnd_8055869 := by exact prefixLift 8055869
  have htrace : WordTrace (prefixWord ++ tailWord_8055869) baseStart_8055869 baseEnd_8055869 := by
    simpa [prefixWord, tailWord_8055869, baseEnd_8055869] using wordTrace_append hprefix tailTrace_8055869
  have hstable : (prefixWord ++ tailWord_8055869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055869).length < 2 ^ (prefixWord ++ tailWord_8055869).sum := by decide
  have hdescent : baseEnd_8055869 < baseStart_8055869 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055882 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 6, 1, 3]
def baseStart_8055882 : Nat := 118140960795 + 8055882 * 2 ^ 59
def prefixEnd_8055882 : Nat := 4983230072969 + 3 ^ 40 * 8055882 * 2
def baseEnd_8055882 : Nat := 4136539561903355558326679

theorem tailTrace_8055882 : CollatzResearch.WordTrace tailWord_8055882 prefixEnd_8055882 4136539561903355558326679 := by
  unfold tailWord_8055882
  simp only [CollatzResearch.WordTrace]
  refine ⟨73455538750230705988720475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195881436667281882636587933 73455538750230705988720475)
  ·
    refine ⟨110183308125346058983080713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73455538750230705988720475 110183308125346058983080713)
    ·
      refine ⟨82637481094009544237310535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110183308125346058983080713 82637481094009544237310535)
      ·
        refine ⟨123956221641014316355965803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82637481094009544237310535 123956221641014316355965803)
        ·
          refine ⟨185934332461521474533948705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123956221641014316355965803 185934332461521474533948705)
          ·
            refine ⟨139450749346141105900461529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185934332461521474533948705 139450749346141105900461529)
            ·
              refine ⟨104588062009605829425346147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139450749346141105900461529 104588062009605829425346147)
              ·
                refine ⟨156882093014408744138019221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104588062009605829425346147 156882093014408744138019221)
                ·
                  refine ⟨7353848110050409881469651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 156882093014408744138019221 7353848110050409881469651)
                  ·
                    refine ⟨11030772165075614822204477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7353848110050409881469651 11030772165075614822204477)
                    ·
                      refine ⟨4136539561903355558326679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11030772165075614822204477 4136539561903355558326679)
                      ·
                        rfl

theorem cell23_8055882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 6, 1, 3].length) (baseStart_8055882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055882 prefixEnd_8055882 := by exact prefixLift 8055882
  have htrace : WordTrace (prefixWord ++ tailWord_8055882) baseStart_8055882 baseEnd_8055882 := by
    simpa [prefixWord, tailWord_8055882, baseEnd_8055882] using wordTrace_append hprefix tailTrace_8055882
  have hstable : (prefixWord ++ tailWord_8055882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055882).length < 2 ^ (prefixWord ++ tailWord_8055882).sum := by decide
  have hdescent : baseEnd_8055882 < baseStart_8055882 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055894 : List Nat := [5, 2, 2, 1, 3, 1, 2, 2, 1, 1, 3]
def baseStart_8055894 : Nat := 118140960795 + 8055894 * 2 ^ 59
def prefixEnd_8055894 : Nat := 4983230072969 + 3 ^ 40 * 8055894 * 2
def baseEnd_8055894 : Nat := 4136545723671209511376625

theorem tailTrace_8055894 : CollatzResearch.WordTrace tailWord_8055894 prefixEnd_8055894 4136545723671209511376625 := by
  unfold tailWord_8055894
  simp only [CollatzResearch.WordTrace]
  refine ⟨18363912042304959375269921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195881728451252900002879157 18363912042304959375269921)
  ·
    refine ⟨13772934031728719531452441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18363912042304959375269921 13772934031728719531452441)
    ·
      refine ⟨10329700523796539648589331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13772934031728719531452441 10329700523796539648589331)
      ·
        refine ⟨15494550785694809472883997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10329700523796539648589331 15494550785694809472883997)
        ·
          refine ⟨5810456544635553552331499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15494550785694809472883997 5810456544635553552331499)
          ·
            refine ⟨8715684816953330328497249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5810456544635553552331499 8715684816953330328497249)
            ·
              refine ⟨6536763612714997746372937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8715684816953330328497249 6536763612714997746372937)
              ·
                refine ⟨4902572709536248309779703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6536763612714997746372937 4902572709536248309779703)
                ·
                  refine ⟨7353859064304372464669555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4902572709536248309779703 7353859064304372464669555)
                  ·
                    refine ⟨11030788596456558697004333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7353859064304372464669555 11030788596456558697004333)
                    ·
                      refine ⟨4136545723671209511376625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11030788596456558697004333 4136545723671209511376625)
                      ·
                        rfl

theorem cell23_8055894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_8055894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055894 prefixEnd_8055894 := by exact prefixLift 8055894
  have htrace : WordTrace (prefixWord ++ tailWord_8055894) baseStart_8055894 baseEnd_8055894 := by
    simpa [prefixWord, tailWord_8055894, baseEnd_8055894] using wordTrace_append hprefix tailTrace_8055894
  have hstable : (prefixWord ++ tailWord_8055894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055894).length < 2 ^ (prefixWord ++ tailWord_8055894).sum := by decide
  have hdescent : baseEnd_8055894 < baseStart_8055894 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055905 : List Nat := [1, 2, 3, 1, 1, 2, 3, 1, 2, 3, 4]
def baseStart_8055905 : Nat := 118140960795 + 8055905 * 2 ^ 59
def prefixEnd_8055905 : Nat := 4983230072969 + 3 ^ 40 * 8055905 * 2
def baseEnd_8055905 : Nat := 4136551371958408968339073

theorem tailTrace_8055905 : CollatzResearch.WordTrace tailWord_8055905 prefixEnd_8055905 4136551371958408968339073 := by
  unfold tailWord_8055905
  simp only [CollatzResearch.WordTrace]
  refine ⟨293822993879839498882969169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195881995919892999255312779 293822993879839498882969169)
  ·
    refine ⟨220367245409879624162226877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293822993879839498882969169 220367245409879624162226877)
    ·
      refine ⟨82637717028704859060835079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220367245409879624162226877 82637717028704859060835079)
      ·
        refine ⟨123956575543057288591252619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82637717028704859060835079 123956575543057288591252619)
        ·
          refine ⟨185934863314585932886878929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123956575543057288591252619 185934863314585932886878929)
          ·
            refine ⟨139451147485939449665159197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185934863314585932886878929 139451147485939449665159197)
            ·
              refine ⟨52294180307227293624434699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139451147485939449665159197 52294180307227293624434699)
              ·
                refine ⟨78441270460840940436652049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52294180307227293624434699 78441270460840940436652049)
                ·
                  refine ⟨58830952845630705327489037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78441270460840940436652049 58830952845630705327489037)
                  ·
                    refine ⟨22061607317111514497808389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58830952845630705327489037 22061607317111514497808389)
                    ·
                      refine ⟨4136551371958408968339073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22061607317111514497808389 4136551371958408968339073)
                      ·
                        rfl

theorem cell23_8055905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_8055905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055905 prefixEnd_8055905 := by exact prefixLift 8055905
  have htrace : WordTrace (prefixWord ++ tailWord_8055905) baseStart_8055905 baseEnd_8055905 := by
    simpa [prefixWord, tailWord_8055905, baseEnd_8055905] using wordTrace_append hprefix tailTrace_8055905
  have hstable : (prefixWord ++ tailWord_8055905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055905).length < 2 ^ (prefixWord ++ tailWord_8055905).sum := by decide
  have hdescent : baseEnd_8055905 < baseStart_8055905 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055926 : List Nat := [5, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2]
def baseStart_8055926 : Nat := 118140960795 + 8055926 * 2 ^ 59
def prefixEnd_8055926 : Nat := 4983230072969 + 3 ^ 40 * 8055926 * 2
def baseEnd_8055926 : Nat := 4136562155052153386176477

theorem tailTrace_8055926 : CollatzResearch.WordTrace tailWord_8055926 prefixEnd_8055926 4136562155052153386176477 := by
  unfold tailWord_8055926
  simp only [CollatzResearch.WordTrace]
  refine ⟨18363984988297713716842727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195882506541842279646322421 18363984988297713716842727)
  ·
    refine ⟨27545977482446570575264091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18363984988297713716842727 27545977482446570575264091)
    ·
      refine ⟨41318966223669855862896137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27545977482446570575264091 41318966223669855862896137)
      ·
        refine ⟨30989224667752391897172103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41318966223669855862896137 30989224667752391897172103)
        ·
          refine ⟨46483837001628587845758155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30989224667752391897172103 46483837001628587845758155)
          ·
            refine ⟨69725755502442881768637233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46483837001628587845758155 69725755502442881768637233)
            ·
              refine ⟨52294316626832161326477925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69725755502442881768637233 52294316626832161326477925)
              ·
                refine ⟨9805184367531030248714611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52294316626832161326477925 9805184367531030248714611)
                ·
                  refine ⟨14707776551296545373071917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9805184367531030248714611 14707776551296545373071917)
                  ·
                    refine ⟨5515416206736204514901969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14707776551296545373071917 5515416206736204514901969)
                    ·
                      refine ⟨4136562155052153386176477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5515416206736204514901969 4136562155052153386176477)
                      ·
                        rfl

theorem cell23_8055926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_8055926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055926 prefixEnd_8055926 := by exact prefixLift 8055926
  have htrace : WordTrace (prefixWord ++ tailWord_8055926) baseStart_8055926 baseEnd_8055926 := by
    simpa [prefixWord, tailWord_8055926, baseEnd_8055926] using wordTrace_append hprefix tailTrace_8055926
  have hstable : (prefixWord ++ tailWord_8055926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055926).length < 2 ^ (prefixWord ++ tailWord_8055926).sum := by decide
  have hdescent : baseEnd_8055926 < baseStart_8055926 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055934 : List Nat := [4, 2, 4, 1, 1, 1, 2, 3, 1, 2, 2]
def baseStart_8055934 : Nat := 118140960795 + 8055934 * 2 ^ 59
def prefixEnd_8055934 : Nat := 4983230072969 + 3 ^ 40 * 8055934 * 2
def baseEnd_8055934 : Nat := 4136566262897389354876441

theorem tailTrace_8055934 : CollatzResearch.WordTrace tailWord_8055934 prefixEnd_8055934 4136566262897389354876441 := by
  unfold tailWord_8055934
  simp only [CollatzResearch.WordTrace]
  refine ⟨36728006449591804604471857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195882701064489624557183237 36728006449591804604471857)
  ·
    refine ⟨27546004837193853453353893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36728006449591804604471857 27546004837193853453353893)
    ·
      refine ⟨5164875906973847522503855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27546004837193853453353893 5164875906973847522503855)
      ·
        refine ⟨7747313860460771283755783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5164875906973847522503855 7747313860460771283755783)
        ·
          refine ⟨11620970790691156925633675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7747313860460771283755783 11620970790691156925633675)
          ·
            refine ⟨17431456186036735388450513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11620970790691156925633675 17431456186036735388450513)
            ·
              refine ⟨13073592139527551541337885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17431456186036735388450513 13073592139527551541337885)
              ·
                refine ⟨4902597052322831828001707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13073592139527551541337885 4902597052322831828001707)
                ·
                  refine ⟨7353895578484247742002561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4902597052322831828001707 7353895578484247742002561)
                  ·
                    refine ⟨5515421683863185806501921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7353895578484247742002561 5515421683863185806501921)
                    ·
                      refine ⟨4136566262897389354876441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5515421683863185806501921 4136566262897389354876441)
                      ·
                        rfl

theorem cell23_8055934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_8055934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055934 prefixEnd_8055934 := by exact prefixLift 8055934
  have htrace : WordTrace (prefixWord ++ tailWord_8055934) baseStart_8055934 baseEnd_8055934 := by
    simpa [prefixWord, tailWord_8055934, baseEnd_8055934] using wordTrace_append hprefix tailTrace_8055934
  have hstable : (prefixWord ++ tailWord_8055934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055934).length < 2 ^ (prefixWord ++ tailWord_8055934).sum := by decide
  have hdescent : baseEnd_8055934 < baseStart_8055934 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055939 : List Nat := [1, 1, 1, 3, 3, 2, 2, 2, 4, 2, 2]
def baseStart_8055939 : Nat := 118140960795 + 8055939 * 2 ^ 59
def prefixEnd_8055939 : Nat := 4983230072969 + 3 ^ 40 * 8055939 * 2
def baseEnd_8055939 : Nat := 4136568830300661835313917

theorem tailTrace_8055939 : CollatzResearch.WordTrace tailWord_8055939 prefixEnd_8055939 4136568830300661835313917 := by
  unfold tailWord_8055939
  simp only [CollatzResearch.WordTrace]
  refine ⟨293824233961716322689706871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195882822641144215126471247 293824233961716322689706871)
  ·
    refine ⟨440736350942574484034560307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293824233961716322689706871 440736350942574484034560307)
    ·
      refine ⟨661104526413861726051840461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440736350942574484034560307 661104526413861726051840461)
      ·
        refine ⟨247914197405198147269440173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 661104526413861726051840461 247914197405198147269440173)
        ·
          refine ⟨92967824026949305226040065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247914197405198147269440173 92967824026949305226040065)
          ·
            refine ⟨69725868020211978919530049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92967824026949305226040065 69725868020211978919530049)
            ·
              refine ⟨52294401015158984189647537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69725868020211978919530049 52294401015158984189647537)
              ·
                refine ⟨39220800761369238142235653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52294401015158984189647537 39220800761369238142235653)
                ·
                  refine ⟨7353900142756732151669185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39220800761369238142235653 7353900142756732151669185)
                  ·
                    refine ⟨5515425107067549113751889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7353900142756732151669185 5515425107067549113751889)
                    ·
                      refine ⟨4136568830300661835313917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5515425107067549113751889 4136568830300661835313917)
                      ·
                        rfl

theorem cell23_8055939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 4, 2, 2].length) (baseStart_8055939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055939 prefixEnd_8055939 := by exact prefixLift 8055939
  have htrace : WordTrace (prefixWord ++ tailWord_8055939) baseStart_8055939 baseEnd_8055939 := by
    simpa [prefixWord, tailWord_8055939, baseEnd_8055939] using wordTrace_append hprefix tailTrace_8055939
  have hstable : (prefixWord ++ tailWord_8055939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055939).length < 2 ^ (prefixWord ++ tailWord_8055939).sum := by decide
  have hdescent : baseEnd_8055939 < baseStart_8055939 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055962 : List Nat := [3, 1, 1, 5, 1, 1, 1, 3, 7]
def baseStart_8055962 : Nat := 118140960795 + 8055962 * 2 ^ 59
def prefixEnd_8055962 : Nat := 4983230072969 + 3 ^ 40 * 8055962 * 2
def baseEnd_8055962 : Nat := 459620071150635027258479

theorem tailTrace_8055962 : CollatzResearch.WordTrace tailWord_8055962 prefixEnd_8055962 459620071150635027258479 := by
  unfold tailWord_8055962
  simp only [CollatzResearch.WordTrace]
  refine ⟨73456268210158249404448535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195883381893755331745196093 73456268210158249404448535)
  ·
    refine ⟨110184402315237374106672803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73456268210158249404448535 110184402315237374106672803)
    ·
      refine ⟨165276603472856061160009205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110184402315237374106672803 165276603472856061160009205)
      ·
        refine ⟨15494681575580255733750863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165276603472856061160009205 15494681575580255733750863)
        ·
          refine ⟨23242022363370383600626295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15494681575580255733750863 23242022363370383600626295)
          ·
            refine ⟨34863033545055575400939443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23242022363370383600626295 34863033545055575400939443)
            ·
              refine ⟨52294550317583363101409165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34863033545055575400939443 52294550317583363101409165)
              ·
                refine ⟨19610456369093761163028437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52294550317583363101409165 19610456369093761163028437)
                ·
                  refine ⟨459620071150635027258479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19610456369093761163028437 459620071150635027258479)
                  ·
                    rfl

theorem cell23_8055962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 7].length) (baseStart_8055962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055962 prefixEnd_8055962 := by exact prefixLift 8055962
  have htrace : WordTrace (prefixWord ++ tailWord_8055962) baseStart_8055962 baseEnd_8055962 := by
    simpa [prefixWord, tailWord_8055962, baseEnd_8055962] using wordTrace_append hprefix tailTrace_8055962
  have hstable : (prefixWord ++ tailWord_8055962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055962).length < 2 ^ (prefixWord ++ tailWord_8055962).sum := by decide
  have hdescent : baseEnd_8055962 < baseStart_8055962 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055973 : List Nat := [1, 3, 1, 2, 1, 5, 3, 1, 2, 2, 2]
def baseStart_8055973 : Nat := 118140960795 + 8055973 * 2 ^ 59
def prefixEnd_8055973 : Nat := 4983230072969 + 3 ^ 40 * 8055973 * 2
def baseEnd_8055973 : Nat := 4136586288642914702288761

theorem tailTrace_8055973 : CollatzResearch.WordTrace tailWord_8055973 prefixEnd_8055973 4136586288642914702288761 := by
  unfold tailWord_8055973
  simp only [CollatzResearch.WordTrace]
  refine ⟨293825474043593146496444573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195883649362395430997629715 293825474043593146496444573)
  ·
    refine ⟨110184552766347429936166715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293825474043593146496444573 110184552766347429936166715)
    ·
      refine ⟨165276829149521144904250073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110184552766347429936166715 165276829149521144904250073)
      ·
        refine ⟨123957621862140858678187555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165276829149521144904250073 123957621862140858678187555)
        ·
          refine ⟨185936432793211288017281333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123957621862140858678187555 185936432793211288017281333)
          ·
            refine ⟨17431540574363558251620125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 185936432793211288017281333 17431540574363558251620125)
            ·
              refine ⟨6536827715386334344357547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17431540574363558251620125 6536827715386334344357547)
              ·
                refine ⟨9805241573079501516536321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6536827715386334344357547 9805241573079501516536321)
                ·
                  refine ⟨7353931179809626137402241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9805241573079501516536321 7353931179809626137402241)
                  ·
                    refine ⟨5515448384857219603051681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7353931179809626137402241 5515448384857219603051681)
                    ·
                      refine ⟨4136586288642914702288761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5515448384857219603051681 4136586288642914702288761)
                      ·
                        rfl

theorem cell23_8055973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 2, 2, 2].length) (baseStart_8055973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055973 prefixEnd_8055973 := by exact prefixLift 8055973
  have htrace : WordTrace (prefixWord ++ tailWord_8055973) baseStart_8055973 baseEnd_8055973 := by
    simpa [prefixWord, tailWord_8055973, baseEnd_8055973] using wordTrace_append hprefix tailTrace_8055973
  have hstable : (prefixWord ++ tailWord_8055973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055973).length < 2 ^ (prefixWord ++ tailWord_8055973).sum := by decide
  have hdescent : baseEnd_8055973 < baseStart_8055973 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8055996 : List Nat := [2, 2, 2, 3, 2, 3, 1, 3, 5]
def baseStart_8055996 : Nat := 118140960795 + 8055996 * 2 ^ 59
def prefixEnd_8055996 : Nat := 4983230072969 + 3 ^ 40 * 8055996 * 2
def baseEnd_8055996 : Nat := 459622010966440901366795

theorem tailTrace_8055996 : CollatzResearch.WordTrace tailWord_8055996 prefixEnd_8055996 459622010966440901366795 := by
  unfold tailWord_8055996
  simp only [CollatzResearch.WordTrace]
  refine ⟨146913156461254910712265921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195884208615006547616354561 146913156461254910712265921)
  ·
    refine ⟨110184867345941183034199441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146913156461254910712265921 110184867345941183034199441)
    ·
      refine ⟨82638650509455887275649581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110184867345941183034199441 82638650509455887275649581)
      ·
        refine ⟨30989493941045957728368593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82638650509455887275649581 30989493941045957728368593)
        ·
          refine ⟨23242120455784468296276445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30989493941045957728368593 23242120455784468296276445)
          ·
            refine ⟨8715795170919175611103667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23242120455784468296276445 8715795170919175611103667)
            ·
              refine ⟨13073692756378763416655501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8715795170919175611103667 13073692756378763416655501)
              ·
                refine ⟨4902634783642036281245813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13073692756378763416655501 4902634783642036281245813)
                ·
                  refine ⟨459622010966440901366795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4902634783642036281245813 459622010966440901366795)
                  ·
                    rfl

theorem cell23_8055996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 3, 5].length) (baseStart_8055996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8055996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8055996 prefixEnd_8055996 := by exact prefixLift 8055996
  have htrace : WordTrace (prefixWord ++ tailWord_8055996) baseStart_8055996 baseEnd_8055996 := by
    simpa [prefixWord, tailWord_8055996, baseEnd_8055996] using wordTrace_append hprefix tailTrace_8055996
  have hstable : (prefixWord ++ tailWord_8055996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8055996).length < 2 ^ (prefixWord ++ tailWord_8055996).sum := by decide
  have hdescent : baseEnd_8055996 < baseStart_8055996 := by decide
  rcases family_descends (prefixWord ++ tailWord_8055996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056013 : List Nat := [1, 6, 2, 2, 1, 2, 1, 1, 7]
def baseStart_8056013 : Nat := 118140960795 + 8056013 * 2 ^ 59
def prefixEnd_8056013 : Nat := 4983230072969 + 3 ^ 40 * 8056013 * 2
def baseEnd_8056013 : Nat := 459622980874343838420953

theorem tailTrace_8056013 : CollatzResearch.WordTrace tailWord_8056013 prefixEnd_8056013 459622980874343838420953 := by
  unfold tailWord_8056013
  simp only [CollatzResearch.WordTrace]
  refine ⟨293826932963448233327900693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195884621975632155551933795 293826932963448233327900693)
  ·
    refine ⟨13773137482661635937245345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 293826932963448233327900693 13773137482661635937245345)
    ·
      refine ⟨10329853111996226952934009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13773137482661635937245345 10329853111996226952934009)
      ·
        refine ⟨7747389833997170214700507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10329853111996226952934009 7747389833997170214700507)
        ·
          refine ⟨11621084750995755322050761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7747389833997170214700507 11621084750995755322050761)
          ·
            refine ⟨8715813563246816491538071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11621084750995755322050761 8715813563246816491538071)
            ·
              refine ⟨13073720344870224737307107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8715813563246816491538071 13073720344870224737307107)
              ·
                refine ⟨19610580517305337105960661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13073720344870224737307107 19610580517305337105960661)
                ·
                  refine ⟨459622980874343838420953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19610580517305337105960661 459622980874343838420953)
                  ·
                    rfl

theorem cell23_8056013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_8056013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056013 prefixEnd_8056013 := by exact prefixLift 8056013
  have htrace : WordTrace (prefixWord ++ tailWord_8056013) baseStart_8056013 baseEnd_8056013 := by
    simpa [prefixWord, tailWord_8056013, baseEnd_8056013] using wordTrace_append hprefix tailTrace_8056013
  have hstable : (prefixWord ++ tailWord_8056013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056013).length < 2 ^ (prefixWord ++ tailWord_8056013).sum := by decide
  have hdescent : baseEnd_8056013 < baseStart_8056013 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056015 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 5]
def baseStart_8056015 : Nat := 118140960795 + 8056015 * 2 ^ 59
def prefixEnd_8056015 : Nat := 4983230072969 + 3 ^ 40 * 8056015 * 2
def baseEnd_8056015 : Nat := 4136607854830403537963567

theorem tailTrace_8056015 : CollatzResearch.WordTrace tailWord_8056015 prefixEnd_8056015 4136607854830403537963567 := by
  unfold tailWord_8056015
  simp only [CollatzResearch.WordTrace]
  refine ⟨293827005909440987669473499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195884670606293991779648999 293827005909440987669473499)
  ·
    refine ⟨440740508864161481504210249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293827005909440987669473499 440740508864161481504210249)
    ·
      refine ⟨330555381648121111128157687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440740508864161481504210249 330555381648121111128157687)
      ·
        refine ⟨495833072472181666692236531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330555381648121111128157687 495833072472181666692236531)
        ·
          refine ⟨743749608708272500038354797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495833072472181666692236531 743749608708272500038354797)
          ·
            refine ⟨278906103265602187514383049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 743749608708272500038354797 278906103265602187514383049)
            ·
              refine ⟨209179577449201640635787287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278906103265602187514383049 209179577449201640635787287)
              ·
                refine ⟨313769366173802460953680931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209179577449201640635787287 313769366173802460953680931)
                ·
                  refine ⟨470654049260703691430521397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 313769366173802460953680931 470654049260703691430521397)
                  ·
                    refine ⟨44123817118190971071611381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 470654049260703691430521397 44123817118190971071611381)
                    ·
                      refine ⟨4136607854830403537963567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44123817118190971071611381 4136607854830403537963567)
                      ·
                        rfl

theorem cell23_8056015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 5].length) (baseStart_8056015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056015 prefixEnd_8056015 := by exact prefixLift 8056015
  have htrace : WordTrace (prefixWord ++ tailWord_8056015) baseStart_8056015 baseEnd_8056015 := by
    simpa [prefixWord, tailWord_8056015, baseEnd_8056015] using wordTrace_append hprefix tailTrace_8056015
  have hstable : (prefixWord ++ tailWord_8056015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056015).length < 2 ^ (prefixWord ++ tailWord_8056015).sum := by decide
  have hdescent : baseEnd_8056015 < baseStart_8056015 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056112 : List Nat := [2, 1, 1, 1, 2, 2, 3, 4, 1, 6]
def baseStart_8056112 : Nat := 118140960795 + 8056112 * 2 ^ 59
def prefixEnd_8056112 : Nat := 4983230072969 + 3 ^ 40 * 8056112 * 2
def baseEnd_8056112 : Nat := 1378885887484629886150207

theorem tailTrace_8056112 : CollatzResearch.WordTrace tailWord_8056112 prefixEnd_8056112 1378885887484629886150207 := by
  unfold tailWord_8056112
  simp only [CollatzResearch.WordTrace]
  refine ⟨146915271895044786617877295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195887029193393048823836393 146915271895044786617877295)
  ·
    refine ⟨220372907842567179926815943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146915271895044786617877295 220372907842567179926815943)
    ·
      refine ⟨330559361763850769890223915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220372907842567179926815943 330559361763850769890223915)
      ·
        refine ⟨495839042645776154835335873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330559361763850769890223915 495839042645776154835335873)
        ·
          refine ⟨371879281984332116126501905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 495839042645776154835335873 371879281984332116126501905)
          ·
            refine ⟨278909461488249087094876429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371879281984332116126501905 278909461488249087094876429)
            ·
              refine ⟨104591048058093407660578661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 278909461488249087094876429 104591048058093407660578661)
              ·
                refine ⟨19610821510892513936358499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104591048058093407660578661 19610821510892513936358499)
                ·
                  refine ⟨29416232266338770904537749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19610821510892513936358499 29416232266338770904537749)
                  ·
                    refine ⟨1378885887484629886150207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29416232266338770904537749 1378885887484629886150207)
                    ·
                      rfl

theorem cell23_8056112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 1, 6].length) (baseStart_8056112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056112 prefixEnd_8056112 := by exact prefixLift 8056112
  have htrace : WordTrace (prefixWord ++ tailWord_8056112) baseStart_8056112 baseEnd_8056112 := by
    simpa [prefixWord, tailWord_8056112, baseEnd_8056112] using wordTrace_append hprefix tailTrace_8056112
  have hstable : (prefixWord ++ tailWord_8056112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056112).length < 2 ^ (prefixWord ++ tailWord_8056112).sum := by decide
  have hdescent : baseEnd_8056112 < baseStart_8056112 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056113 : List Nat := [1, 2, 2, 3, 3, 1, 1, 5, 1, 1, 3]
def baseStart_8056113 : Nat := 118140960795 + 8056113 * 2 ^ 59
def prefixEnd_8056113 : Nat := 4983230072969 + 3 ^ 40 * 8056113 * 2
def baseEnd_8056113 : Nat := 4136658175934544154538117

theorem tailTrace_8056113 : CollatzResearch.WordTrace tailWord_8056113 prefixEnd_8056113 4136658175934544154538117 := by
  unfold tailWord_8056113
  simp only [CollatzResearch.WordTrace]
  refine ⟨293830580263085950406540993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195887053508723966937693995 293830580263085950406540993)
  ·
    refine ⟨220372935197314462804905745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293830580263085950406540993 220372935197314462804905745)
    ·
      refine ⟨165279701397985847103679309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220372935197314462804905745 165279701397985847103679309)
      ·
        refine ⟨61979888024244692663879741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165279701397985847103679309 61979888024244692663879741)
        ·
          refine ⟨23242458009091759748954903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61979888024244692663879741 23242458009091759748954903)
          ·
            refine ⟨34863687013637639623432355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23242458009091759748954903 34863687013637639623432355)
            ·
              refine ⟨52295530520456459435148533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34863687013637639623432355 52295530520456459435148533)
              ·
                refine ⟨4902705986292793072045175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52295530520456459435148533 4902705986292793072045175)
                ·
                  refine ⟨7354058979439189608067763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4902705986292793072045175 7354058979439189608067763)
                  ·
                    refine ⟨11031088469158784412101645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7354058979439189608067763 11031088469158784412101645)
                    ·
                      refine ⟨4136658175934544154538117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11031088469158784412101645 4136658175934544154538117)
                      ·
                        rfl

theorem cell23_8056113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 5, 1, 1, 3].length) (baseStart_8056113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056113 prefixEnd_8056113 := by exact prefixLift 8056113
  have htrace : WordTrace (prefixWord ++ tailWord_8056113) baseStart_8056113 baseEnd_8056113 := by
    simpa [prefixWord, tailWord_8056113, baseEnd_8056113] using wordTrace_append hprefix tailTrace_8056113
  have hstable : (prefixWord ++ tailWord_8056113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056113).length < 2 ^ (prefixWord ++ tailWord_8056113).sum := by decide
  have hdescent : baseEnd_8056113 < baseStart_8056113 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056116 : List Nat := [2, 5, 1, 1, 1, 1, 3, 3, 1, 5]
def baseStart_8056116 : Nat := 118140960795 + 8056116 * 2 ^ 59
def prefixEnd_8056116 : Nat := 4983230072969 + 3 ^ 40 * 8056116 * 2
def baseEnd_8056116 : Nat := 1378886572125502547600201

theorem tailTrace_8056116 : CollatzResearch.WordTrace tailWord_8056116 prefixEnd_8056116 1378886572125502547600201 := by
  unfold tailWord_8056116
  simp only [CollatzResearch.WordTrace]
  refine ⟨146915344841037540959450101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195887126454716721279266801 146915344841037540959450101)
  ·
    refine ⟨13773313578847269464948447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146915344841037540959450101 13773313578847269464948447)
    ·
      refine ⟨20659970368270904197422671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13773313578847269464948447 20659970368270904197422671)
      ·
        refine ⟨30989955552406356296134007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20659970368270904197422671 30989955552406356296134007)
        ·
          refine ⟨46484933328609534444201011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30989955552406356296134007 46484933328609534444201011)
          ·
            refine ⟨69727399992914301666301517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46484933328609534444201011 69727399992914301666301517)
            ·
              refine ⟨26147774997342863124863069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69727399992914301666301517 26147774997342863124863069)
              ·
                refine ⟨9805415624003573671823651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26147774997342863124863069 9805415624003573671823651)
                ·
                  refine ⟨14708123436005360507735477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9805415624003573671823651 14708123436005360507735477)
                  ·
                    refine ⟨1378886572125502547600201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14708123436005360507735477 1378886572125502547600201)
                    ·
                      rfl

theorem cell23_8056116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_8056116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056116 prefixEnd_8056116 := by exact prefixLift 8056116
  have htrace : WordTrace (prefixWord ++ tailWord_8056116) baseStart_8056116 baseEnd_8056116 := by
    simpa [prefixWord, tailWord_8056116, baseEnd_8056116] using wordTrace_append hprefix tailTrace_8056116
  have hstable : (prefixWord ++ tailWord_8056116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056116).length < 2 ^ (prefixWord ++ tailWord_8056116).sum := by decide
  have hdescent : baseEnd_8056116 < baseStart_8056116 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056142 : List Nat := [4, 1, 1, 1, 1, 1, 4, 10]
def baseStart_8056142 : Nat := 118140960795 + 8056142 * 2 ^ 59
def prefixEnd_8056142 : Nat := 4983230072969 + 3 ^ 40 * 8056142 * 2
def baseEnd_8056142 : Nat := 153210113587908316336129

theorem tailTrace_8056142 : CollatzResearch.WordTrace tailWord_8056142 prefixEnd_8056142 153210113587908316336129 := by
  unfold tailWord_8056142
  simp only [CollatzResearch.WordTrace]
  refine ⟨36728954747497611044918335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195887758653320592239564453 36728954747497611044918335)
  ·
    refine ⟨55093432121246416567377503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36728954747497611044918335 55093432121246416567377503)
    ·
      refine ⟨82640148181869624851066255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55093432121246416567377503 82640148181869624851066255)
      ·
        refine ⟨123960222272804437276599383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82640148181869624851066255 123960222272804437276599383)
        ·
          refine ⟨185940333409206655914899075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123960222272804437276599383 185940333409206655914899075)
          ·
            refine ⟨278910500113809983872348613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185940333409206655914899075 278910500113809983872348613)
            ·
              refine ⟨52295718771339371976065365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 278910500113809983872348613 52295718771339371976065365)
              ·
                refine ⟨153210113587908316336129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 52295718771339371976065365 153210113587908316336129)
                ·
                  rfl

theorem cell23_8056142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 10].length) (baseStart_8056142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056142 prefixEnd_8056142 := by exact prefixLift 8056142
  have htrace : WordTrace (prefixWord ++ tailWord_8056142) baseStart_8056142 baseEnd_8056142 := by
    simpa [prefixWord, tailWord_8056142, baseEnd_8056142] using wordTrace_append hprefix tailTrace_8056142
  have hstable : (prefixWord ++ tailWord_8056142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056142).length < 2 ^ (prefixWord ++ tailWord_8056142).sum := by decide
  have hdescent : baseEnd_8056142 < baseStart_8056142 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056149 : List Nat := [1, 3, 2, 2, 3, 2, 1, 1, 1, 1, 6]
def baseStart_8056149 : Nat := 118140960795 + 8056149 * 2 ^ 59
def prefixEnd_8056149 : Nat := 4983230072969 + 3 ^ 40 * 8056149 * 2
def baseEnd_8056149 : Nat := 4136676661238106013687951

theorem tailTrace_8056149 : CollatzResearch.WordTrace tailWord_8056149 prefixEnd_8056149 4136676661238106013687951 := by
  unfold tailWord_8056149
  simp only [CollatzResearch.WordTrace]
  refine ⟨293831893290955528554851501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195887928860637019036567667 293831893290955528554851501)
  ·
    refine ⟨110186959984108323208069313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293831893290955528554851501 110186959984108323208069313)
    ·
      refine ⟨82640219988081242406051985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110186959984108323208069313 82640219988081242406051985)
      ·
        refine ⟨61980164991060931804538989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82640219988081242406051985 61980164991060931804538989)
        ·
          refine ⟨23242561871647849426702121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61980164991060931804538989 23242561871647849426702121)
          ·
            refine ⟨17431921403735887070026591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23242561871647849426702121 17431921403735887070026591)
            ·
              refine ⟨26147882105603830605039887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17431921403735887070026591 26147882105603830605039887)
              ·
                refine ⟨39221823158405745907559831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26147882105603830605039887 39221823158405745907559831)
                ·
                  refine ⟨58832734737608618861339747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39221823158405745907559831 58832734737608618861339747)
                  ·
                    refine ⟨88249102106412928292009621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58832734737608618861339747 88249102106412928292009621)
                    ·
                      refine ⟨4136676661238106013687951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88249102106412928292009621 4136676661238106013687951)
                      ·
                        rfl

theorem cell23_8056149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_8056149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056149 prefixEnd_8056149 := by exact prefixLift 8056149
  have htrace : WordTrace (prefixWord ++ tailWord_8056149) baseStart_8056149 baseEnd_8056149 := by
    simpa [prefixWord, tailWord_8056149, baseEnd_8056149] using wordTrace_append hprefix tailTrace_8056149
  have hstable : (prefixWord ++ tailWord_8056149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056149).length < 2 ^ (prefixWord ++ tailWord_8056149).sum := by decide
  have hdescent : baseEnd_8056149 < baseStart_8056149 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056213 : List Nat := [1, 3, 2, 1, 1, 2, 5, 2, 1, 3, 2]
def baseStart_8056213 : Nat := 118140960795 + 8056213 * 2 ^ 59
def prefixEnd_8056213 : Nat := 4983230072969 + 3 ^ 40 * 8056213 * 2
def baseEnd_8056213 : Nat := 4136709523999993763287657

theorem tailTrace_8056213 : CollatzResearch.WordTrace tailWord_8056213 prefixEnd_8056213 4136709523999993763287657 := by
  unfold tailWord_8056213
  simp only [CollatzResearch.WordTrace]
  refine ⟨293834227562723667485181293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195889485041815778323454195 293834227562723667485181293)
  ·
    refine ⟨110187835336021375306942985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293834227562723667485181293 110187835336021375306942985)
    ·
      refine ⟨82640876502016031480207239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110187835336021375306942985 82640876502016031480207239)
      ·
        refine ⟨123961314753024047220310859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82640876502016031480207239 123961314753024047220310859)
        ·
          refine ⟨185941972129536070830466289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123961314753024047220310859 185941972129536070830466289)
          ·
            refine ⟨139456479097152053122849717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185941972129536070830466289 139456479097152053122849717)
            ·
              refine ⟨13074044915358004980267161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 139456479097152053122849717 13074044915358004980267161)
              ·
                refine ⟨9805533686518503735200371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13074044915358004980267161 9805533686518503735200371)
                ·
                  refine ⟨14708300529777755602800557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9805533686518503735200371 14708300529777755602800557)
                  ·
                    refine ⟨5515612698666658351050209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14708300529777755602800557 5515612698666658351050209)
                    ·
                      refine ⟨4136709523999993763287657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5515612698666658351050209 4136709523999993763287657)
                      ·
                        rfl

theorem cell23_8056213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 3, 2].length) (baseStart_8056213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056213 prefixEnd_8056213 := by exact prefixLift 8056213
  have htrace : WordTrace (prefixWord ++ tailWord_8056213) baseStart_8056213 baseEnd_8056213 := by
    simpa [prefixWord, tailWord_8056213, baseEnd_8056213] using wordTrace_append hprefix tailTrace_8056213
  have hstable : (prefixWord ++ tailWord_8056213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056213).length < 2 ^ (prefixWord ++ tailWord_8056213).sum := by decide
  have hdescent : baseEnd_8056213 < baseStart_8056213 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056259 : List Nat := [1, 1, 1, 3, 1, 1, 5, 1, 1, 5, 3]
def baseStart_8056259 : Nat := 118140960795 + 8056259 * 2 ^ 59
def prefixEnd_8056259 : Nat := 4983230072969 + 3 ^ 40 * 8056259 * 2
def baseEnd_8056259 : Nat := 4136733144110100583312445

theorem tailTrace_8056259 : CollatzResearch.WordTrace tailWord_8056259 prefixEnd_8056259 4136733144110100583312445 := by
  unfold tailWord_8056259
  simp only [CollatzResearch.WordTrace]
  refine ⟨293835905320557017341355831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195890603547038011560903887 293835905320557017341355831)
  ·
    refine ⟨440753857980835526012033747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293835905320557017341355831 440753857980835526012033747)
    ·
      refine ⟨661130786971253289018050621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440753857980835526012033747 661130786971253289018050621)
      ·
        refine ⟨247924045114219983381768983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 661130786971253289018050621 247924045114219983381768983)
        ·
          refine ⟨371886067671329975072653475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247924045114219983381768983 371886067671329975072653475)
          ·
            refine ⟨557829101506994962608980213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371886067671329975072653475 557829101506994962608980213)
            ·
              refine ⟨52296478266280777744591895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 557829101506994962608980213 52296478266280777744591895)
              ·
                refine ⟨78444717399421166616887843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52296478266280777744591895 78444717399421166616887843)
                ·
                  refine ⟨117667076099131749925331765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78444717399421166616887843 117667076099131749925331765)
                  ·
                    refine ⟨11031288384293601555499853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117667076099131749925331765 11031288384293601555499853)
                    ·
                      refine ⟨4136733144110100583312445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11031288384293601555499853 4136733144110100583312445)
                      ·
                        rfl

theorem cell23_8056259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 5, 3].length) (baseStart_8056259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056259 prefixEnd_8056259 := by exact prefixLift 8056259
  have htrace : WordTrace (prefixWord ++ tailWord_8056259) baseStart_8056259 baseEnd_8056259 := by
    simpa [prefixWord, tailWord_8056259, baseEnd_8056259] using wordTrace_append hprefix tailTrace_8056259
  have hstable : (prefixWord ++ tailWord_8056259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056259).length < 2 ^ (prefixWord ++ tailWord_8056259).sum := by decide
  have hdescent : baseEnd_8056259 < baseStart_8056259 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056260 : List Nat := [2, 3, 3, 2, 1, 2, 2, 1, 1, 4, 2]
def baseStart_8056260 : Nat := 118140960795 + 8056260 * 2 ^ 59
def prefixEnd_8056260 : Nat := 4983230072969 + 3 ^ 40 * 8056260 * 2
def baseEnd_8056260 : Nat := 4136733657590755079399941

theorem tailTrace_8056260 : CollatzResearch.WordTrace tailWord_8056260 prefixEnd_8056260 4136733657590755079399941 := by
  unfold tailWord_8056260
  simp only [CollatzResearch.WordTrace]
  refine ⟨146917970896776697256071117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195890627862368929674761489 146917970896776697256071117)
  ·
    refine ⟨55094239086291261471026669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146917970896776697256071117 55094239086291261471026669)
    ·
      refine ⟨20660339657359223051635001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55094239086291261471026669 20660339657359223051635001)
      ·
        refine ⟨15495254743019417288726251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20660339657359223051635001 15495254743019417288726251)
        ·
          refine ⟨23242882114529125933089377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15495254743019417288726251 23242882114529125933089377)
          ·
            refine ⟨17432161585896844449817033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23242882114529125933089377 17432161585896844449817033)
            ·
              refine ⟨13074121189422633337362775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17432161585896844449817033 13074121189422633337362775)
              ·
                refine ⟨19611181784133950006044163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13074121189422633337362775 19611181784133950006044163)
                ·
                  refine ⟨29416772676200925009066245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19611181784133950006044163 29416772676200925009066245)
                  ·
                    refine ⟨5515644876787673439199921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29416772676200925009066245 5515644876787673439199921)
                    ·
                      refine ⟨4136733657590755079399941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5515644876787673439199921 4136733657590755079399941)
                      ·
                        rfl

theorem cell23_8056260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_8056260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056260 prefixEnd_8056260 := by exact prefixLift 8056260
  have htrace : WordTrace (prefixWord ++ tailWord_8056260) baseStart_8056260 baseEnd_8056260 := by
    simpa [prefixWord, tailWord_8056260, baseEnd_8056260] using wordTrace_append hprefix tailTrace_8056260
  have hstable : (prefixWord ++ tailWord_8056260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056260).length < 2 ^ (prefixWord ++ tailWord_8056260).sum := by decide
  have hdescent : baseEnd_8056260 < baseStart_8056260 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056329 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 2, 4, 4]
def baseStart_8056329 : Nat := 118140960795 + 8056329 * 2 ^ 59
def prefixEnd_8056329 : Nat := 4983230072969 + 3 ^ 40 * 8056329 * 2
def baseEnd_8056329 : Nat := 4136769087755915309437123

theorem tailTrace_8056329 : CollatzResearch.WordTrace tailWord_8056329 prefixEnd_8056329 4136769087755915309437123 := by
  unfold tailWord_8056329
  simp only [CollatzResearch.WordTrace]
  refine ⟨293838458430303419296404041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195892305620202279530936027 293838458430303419296404041)
  ·
    refine ⟨220378843822727564472303031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293838458430303419296404041 220378843822727564472303031)
    ·
      refine ⟨330568265734091346708454547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220378843822727564472303031 330568265734091346708454547)
      ·
        refine ⟨495852398601137020062681821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330568265734091346708454547 495852398601137020062681821)
        ·
          refine ⟨185944649475426382523505683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 495852398601137020062681821 185944649475426382523505683)
          ·
            refine ⟨278916974213139573785258525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185944649475426382523505683 278916974213139573785258525)
            ·
              refine ⟨104593865329927340169471947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 278916974213139573785258525 104593865329927340169471947)
              ·
                refine ⟨156890797994891010254207921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104593865329927340169471947 156890797994891010254207921)
                ·
                  refine ⟨117668098496168257690655941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156890797994891010254207921 117668098496168257690655941)
                  ·
                    refine ⟨22062768468031548316997989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 117668098496168257690655941 22062768468031548316997989)
                    ·
                      refine ⟨4136769087755915309437123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22062768468031548316997989 4136769087755915309437123)
                      ·
                        rfl

theorem cell23_8056329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 4, 4].length) (baseStart_8056329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056329 prefixEnd_8056329 := by exact prefixLift 8056329
  have htrace : WordTrace (prefixWord ++ tailWord_8056329) baseStart_8056329 baseEnd_8056329 := by
    simpa [prefixWord, tailWord_8056329, baseEnd_8056329] using wordTrace_append hprefix tailTrace_8056329
  have hstable : (prefixWord ++ tailWord_8056329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056329).length < 2 ^ (prefixWord ++ tailWord_8056329).sum := by decide
  have hdescent : baseEnd_8056329 < baseStart_8056329 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056339 : List Nat := [1, 1, 1, 2, 1, 6, 1, 2, 8]
def baseStart_8056339 : Nat := 118140960795 + 8056339 * 2 ^ 59
def prefixEnd_8056339 : Nat := 4983230072969 + 3 ^ 40 * 8056339 * 2
def baseEnd_8056339 : Nat := 459641580284717807812453

theorem tailTrace_8056339 : CollatzResearch.WordTrace tailWord_8056339 prefixEnd_8056339 459641580284717807812453 := by
  unfold tailWord_8056339
  simp only [CollatzResearch.WordTrace]
  refine ⟨293838823160267191004268071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195892548773511460669512047 293838823160267191004268071)
  ·
    refine ⟨440758234740400786506402107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293838823160267191004268071 440758234740400786506402107)
    ·
      refine ⟨661137352110601179759603161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440758234740400786506402107 661137352110601179759603161)
      ·
        refine ⟨495853014082950884819702371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 661137352110601179759603161 495853014082950884819702371)
        ·
          refine ⟨743779521124426327229553557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495853014082950884819702371 743779521124426327229553557)
          ·
            refine ⟨34864665052707484088885323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 743779521124426327229553557 34864665052707484088885323)
            ·
              refine ⟨52296997579061226133327985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34864665052707484088885323 52296997579061226133327985)
              ·
                refine ⟨39222748184295919599995989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52296997579061226133327985 39222748184295919599995989)
                ·
                  refine ⟨459641580284717807812453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39222748184295919599995989 459641580284717807812453)
                  ·
                    rfl

theorem cell23_8056339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 8].length) (baseStart_8056339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056339 prefixEnd_8056339 := by exact prefixLift 8056339
  have htrace : WordTrace (prefixWord ++ tailWord_8056339) baseStart_8056339 baseEnd_8056339 := by
    simpa [prefixWord, tailWord_8056339, baseEnd_8056339] using wordTrace_append hprefix tailTrace_8056339
  have hstable : (prefixWord ++ tailWord_8056339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056339).length < 2 ^ (prefixWord ++ tailWord_8056339).sum := by decide
  have hdescent : baseEnd_8056339 < baseStart_8056339 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056353 : List Nat := [1, 2, 3, 2, 2, 3, 1, 2, 2, 2, 3]
def baseStart_8056353 : Nat := 118140960795 + 8056353 * 2 ^ 59
def prefixEnd_8056353 : Nat := 4983230072969 + 3 ^ 40 * 8056353 * 2
def baseEnd_8056353 : Nat := 4136781411291623215537013

theorem tailTrace_8056353 : CollatzResearch.WordTrace tailWord_8056353 prefixEnd_8056353 4136781411291623215537013 := by
  unfold tailWord_8056353
  simp only [CollatzResearch.WordTrace]
  refine ⟨293839333782216471395277713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195892889188144314263518475 293839333782216471395277713)
  ·
    refine ⟨220379500336662353546458285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293839333782216471395277713 220379500336662353546458285)
    ·
      refine ⟨82642312626248382579921857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220379500336662353546458285 82642312626248382579921857)
      ·
        refine ⟨61981734469686286934941393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82642312626248382579921857 61981734469686286934941393)
        ·
          refine ⟨46486300852264715201206045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61981734469686286934941393 46486300852264715201206045)
          ·
            refine ⟨17432362819599268200452267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46486300852264715201206045 17432362819599268200452267)
            ·
              refine ⟨26148544229398902300678401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17432362819599268200452267 26148544229398902300678401)
              ·
                refine ⟨19611408172049176725508801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26148544229398902300678401 19611408172049176725508801)
                ·
                  refine ⟨14708556129036882544131601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19611408172049176725508801 14708556129036882544131601)
                  ·
                    refine ⟨11031417096777661908098701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14708556129036882544131601 11031417096777661908098701)
                    ·
                      refine ⟨4136781411291623215537013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11031417096777661908098701 4136781411291623215537013)
                      ·
                        rfl

theorem cell23_8056353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_8056353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056353 prefixEnd_8056353 := by exact prefixLift 8056353
  have htrace : WordTrace (prefixWord ++ tailWord_8056353) baseStart_8056353 baseEnd_8056353 := by
    simpa [prefixWord, tailWord_8056353, baseEnd_8056353] using wordTrace_append hprefix tailTrace_8056353
  have hstable : (prefixWord ++ tailWord_8056353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056353).length < 2 ^ (prefixWord ++ tailWord_8056353).sum := by decide
  have hdescent : baseEnd_8056353 < baseStart_8056353 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056369 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 2, 9]
def baseStart_8056369 : Nat := 118140960795 + 8056369 * 2 ^ 59
def prefixEnd_8056369 : Nat := 4983230072969 + 3 ^ 40 * 8056369 * 2
def baseEnd_8056369 : Nat := 1378929875660698384312313

theorem tailTrace_8056369 : CollatzResearch.WordTrace tailWord_8056369 prefixEnd_8056369 1378929875660698384312313 := by
  unfold tailWord_8056369
  simp only [CollatzResearch.WordTrace]
  refine ⟨293839917350158506127860161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195893278233439004085240107 293839917350158506127860161)
  ·
    refine ⟨220379938012618879595895121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293839917350158506127860161 220379938012618879595895121)
    ·
      refine ⟨165284953509464159696921341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220379938012618879595895121 165284953509464159696921341)
      ·
        refine ⟨61981857566049059886345503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165284953509464159696921341 61981857566049059886345503)
        ·
          refine ⟨92972786349073589829518255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61981857566049059886345503 92972786349073589829518255)
          ·
            refine ⟨139459179523610384744277383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92972786349073589829518255 139459179523610384744277383)
            ·
              refine ⟨209188769285415577116416075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139459179523610384744277383 209188769285415577116416075)
              ·
                refine ⟨313783153928123365674624113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209188769285415577116416075 313783153928123365674624113)
                ·
                  refine ⟨235337365446092524255968085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 313783153928123365674624113 235337365446092524255968085)
                  ·
                    refine ⟨1378929875660698384312313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 235337365446092524255968085 1378929875660698384312313)
                    ·
                      rfl

theorem cell23_8056369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 9].length) (baseStart_8056369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056369 prefixEnd_8056369 := by exact prefixLift 8056369
  have htrace : WordTrace (prefixWord ++ tailWord_8056369) baseStart_8056369 baseEnd_8056369 := by
    simpa [prefixWord, tailWord_8056369, baseEnd_8056369] using wordTrace_append hprefix tailTrace_8056369
  have hstable : (prefixWord ++ tailWord_8056369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056369).length < 2 ^ (prefixWord ++ tailWord_8056369).sum := by decide
  have hdescent : baseEnd_8056369 < baseStart_8056369 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056373 : List Nat := [1, 3, 3, 1, 1, 3, 4, 1, 6]
def baseStart_8056373 : Nat := 118140960795 + 8056373 * 2 ^ 59
def prefixEnd_8056373 : Nat := 4983230072969 + 3 ^ 40 * 8056373 * 2
def baseEnd_8056373 : Nat := 459643520100523681920769

theorem tailTrace_8056373 : CollatzResearch.WordTrace tailWord_8056373 prefixEnd_8056373 459643520100523681920769 := by
  unfold tailWord_8056373
  simp only [CollatzResearch.WordTrace]
  refine ⟨293840063242144014811005773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195893375494762676540670515 293840063242144014811005773)
  ·
    refine ⟨110190023715804005554127165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293840063242144014811005773 110190023715804005554127165)
    ·
      refine ⟨41321258893426502082797687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110190023715804005554127165 41321258893426502082797687)
      ·
        refine ⟨61981888340139753124196531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41321258893426502082797687 61981888340139753124196531)
        ·
          refine ⟨92972832510209629686294797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61981888340139753124196531 92972832510209629686294797)
          ·
            refine ⟨34864812191328611132360549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92972832510209629686294797 34864812191328611132360549)
            ·
              refine ⟨6537152285874114587317603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34864812191328611132360549 6537152285874114587317603)
              ·
                refine ⟨9805728428811171880976405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6537152285874114587317603 9805728428811171880976405)
                ·
                  refine ⟨459643520100523681920769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9805728428811171880976405 459643520100523681920769)
                  ·
                    rfl

theorem cell23_8056373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 6].length) (baseStart_8056373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056373 prefixEnd_8056373 := by exact prefixLift 8056373
  have htrace : WordTrace (prefixWord ++ tailWord_8056373) baseStart_8056373 baseEnd_8056373 := by
    simpa [prefixWord, tailWord_8056373, baseEnd_8056373] using wordTrace_append hprefix tailTrace_8056373
  have hstable : (prefixWord ++ tailWord_8056373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056373).length < 2 ^ (prefixWord ++ tailWord_8056373).sum := by decide
  have hdescent : baseEnd_8056373 < baseStart_8056373 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056400 : List Nat := [2, 1, 1, 1, 1, 3, 4, 5, 1, 1, 3]
def baseStart_8056400 : Nat := 118140960795 + 8056400 * 2 ^ 59
def prefixEnd_8056400 : Nat := 4983230072969 + 3 ^ 40 * 8056400 * 2
def baseEnd_8056400 : Nat := 4136805544882384531649297

theorem tailTrace_8056400 : CollatzResearch.WordTrace tailWord_8056400 prefixEnd_8056400 4136805544882384531649297 := by
  unfold tailWord_8056400
  simp only [CollatzResearch.WordTrace]
  refine ⟨146920524006523099211119327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195894032008697465614825769 146920524006523099211119327)
  ·
    refine ⟨220380786009784648816678991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146920524006523099211119327 220380786009784648816678991)
    ·
      refine ⟨330571179014676973225018487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220380786009784648816678991 330571179014676973225018487)
      ·
        refine ⟨495856768522015459837527731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330571179014676973225018487 495856768522015459837527731)
        ·
          refine ⟨743785152783023189756291597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495856768522015459837527731 743785152783023189756291597)
          ·
            refine ⟨278919432293633696158609349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 743785152783023189756291597 278919432293633696158609349)
            ·
              refine ⟨52297393555056318029739253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 278919432293633696158609349 52297393555056318029739253)
              ·
                refine ⟨4902880645786529815288055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52297393555056318029739253 4902880645786529815288055)
                ·
                  refine ⟨7354320968679794722932083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4902880645786529815288055 7354320968679794722932083)
                  ·
                    refine ⟨11031481453019692084398125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7354320968679794722932083 11031481453019692084398125)
                    ·
                      refine ⟨4136805544882384531649297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11031481453019692084398125 4136805544882384531649297)
                      ·
                        rfl

theorem cell23_8056400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 5, 1, 1, 3].length) (baseStart_8056400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056400 prefixEnd_8056400 := by exact prefixLift 8056400
  have htrace : WordTrace (prefixWord ++ tailWord_8056400) baseStart_8056400 baseEnd_8056400 := by
    simpa [prefixWord, tailWord_8056400, baseEnd_8056400] using wordTrace_append hprefix tailTrace_8056400
  have hstable : (prefixWord ++ tailWord_8056400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056400).length < 2 ^ (prefixWord ++ tailWord_8056400).sum := by decide
  have hdescent : baseEnd_8056400 < baseStart_8056400 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056443 : List Nat := [1, 1, 1, 1, 1, 4, 4, 4, 1, 2, 3]
def baseStart_8056443 : Nat := 118140960795 + 8056443 * 2 ^ 59
def prefixEnd_8056443 : Nat := 4983230072969 + 3 ^ 40 * 8056443 * 2
def baseEnd_8056443 : Nat := 4136827624550527863411599

theorem tailTrace_8056443 : CollatzResearch.WordTrace tailWord_8056443 prefixEnd_8056443 4136827624550527863411599 := by
  unfold tailWord_8056443
  simp only [CollatzResearch.WordTrace]
  refine ⟨293842616351890416766053983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195895077567926944510702655 293842616351890416766053983)
  ·
    refine ⟨440763924527835625149080975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293842616351890416766053983 440763924527835625149080975)
    ·
      refine ⟨661145886791753437723621463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440763924527835625149080975 661145886791753437723621463)
      ·
        refine ⟨991718830187630156585432195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661145886791753437723621463 991718830187630156585432195)
        ·
          refine ⟨1487578245281445234878148293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 991718830187630156585432195 1487578245281445234878148293)
          ·
            refine ⟨278920920990270981539652805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1487578245281445234878148293 278920920990270981539652805)
            ·
              refine ⟨52297672685675809038684901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 278920920990270981539652805 52297672685675809038684901)
              ·
                refine ⟨9805813628564214194753419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52297672685675809038684901 9805813628564214194753419)
                ·
                  refine ⟨14708720442846321292130129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9805813628564214194753419 14708720442846321292130129)
                  ·
                    refine ⟨11031540332134740969097597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14708720442846321292130129 11031540332134740969097597)
                    ·
                      refine ⟨4136827624550527863411599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11031540332134740969097597 4136827624550527863411599)
                      ·
                        rfl

theorem cell23_8056443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 2, 3].length) (baseStart_8056443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056443 prefixEnd_8056443 := by exact prefixLift 8056443
  have htrace : WordTrace (prefixWord ++ tailWord_8056443) baseStart_8056443 baseEnd_8056443 := by
    simpa [prefixWord, tailWord_8056443, baseEnd_8056443] using wordTrace_append hprefix tailTrace_8056443
  have hstable : (prefixWord ++ tailWord_8056443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056443).length < 2 ^ (prefixWord ++ tailWord_8056443).sum := by decide
  have hdescent : baseEnd_8056443 < baseStart_8056443 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056457 : List Nat := [1, 2, 1, 1, 4, 1, 3, 5, 1, 2, 2]
def baseStart_8056457 : Nat := 118140960795 + 8056457 * 2 ^ 59
def prefixEnd_8056457 : Nat := 4983230072969 + 3 ^ 40 * 8056457 * 2
def baseEnd_8056457 : Nat := 4136834813279690808636535

theorem tailTrace_8056457 : CollatzResearch.WordTrace tailWord_8056457 prefixEnd_8056457 4136834813279690808636535 := by
  unfold tailWord_8056457
  simp only [CollatzResearch.WordTrace]
  refine ⟨293843126973839697157063625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195895417982559798104709083 293843126973839697157063625)
  ·
    refine ⟨220382345230379772867797719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293843126973839697157063625 220382345230379772867797719)
    ·
      refine ⟨330573517845569659301696579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220382345230379772867797719 330573517845569659301696579)
      ·
        refine ⟨495860276768354488952544869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330573517845569659301696579 495860276768354488952544869)
        ·
          refine ⟨92973801894066466678602163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 495860276768354488952544869 92973801894066466678602163)
          ·
            refine ⟨139460702841099700017903245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92973801894066466678602163 139460702841099700017903245)
            ·
              refine ⟨52297763565412387506713717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139460702841099700017903245 52297763565412387506713717)
              ·
                refine ⟨4902915334257411328754411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52297763565412387506713717 4902915334257411328754411)
                ·
                  refine ⟨7354373001386116993131617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4902915334257411328754411 7354373001386116993131617)
                  ·
                    refine ⟨5515779751039587744848713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7354373001386116993131617 5515779751039587744848713)
                    ·
                      refine ⟨4136834813279690808636535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5515779751039587744848713 4136834813279690808636535)
                      ·
                        rfl

theorem cell23_8056457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 5, 1, 2, 2].length) (baseStart_8056457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056457 prefixEnd_8056457 := by exact prefixLift 8056457
  have htrace : WordTrace (prefixWord ++ tailWord_8056457) baseStart_8056457 baseEnd_8056457 := by
    simpa [prefixWord, tailWord_8056457, baseEnd_8056457] using wordTrace_append hprefix tailTrace_8056457
  have hstable : (prefixWord ++ tailWord_8056457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056457).length < 2 ^ (prefixWord ++ tailWord_8056457).sum := by decide
  have hdescent : baseEnd_8056457 < baseStart_8056457 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056494 : List Nat := [4, 1, 4, 1, 2, 1, 2, 2, 1, 2, 3]
def baseStart_8056494 : Nat := 118140960795 + 8056494 * 2 ^ 59
def prefixEnd_8056494 : Nat := 4983230072969 + 3 ^ 40 * 8056494 * 2
def baseEnd_8056494 : Nat := 4136853812063907163873865

theorem tailTrace_8056494 : CollatzResearch.WordTrace tailWord_8056494 prefixEnd_8056494 4136853812063907163873865 := by
  unfold tailWord_8056494
  simp only [CollatzResearch.WordTrace]
  refine ⟨36730559559338206559520067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195896317649803768317440357 36730559559338206559520067)
  ·
    refine ⟨55095839339007309839280101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36730559559338206559520067 55095839339007309839280101)
    ·
      refine ⟨10330469876063870594865019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55095839339007309839280101 10330469876063870594865019)
      ·
        refine ⟨15495704814095805892297529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10330469876063870594865019 15495704814095805892297529)
        ·
          refine ⟨11621778610571854419223147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15495704814095805892297529 11621778610571854419223147)
          ·
            refine ⟨17432667915857781628834721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11621778610571854419223147 17432667915857781628834721)
            ·
              refine ⟨13074500936893336221626041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17432667915857781628834721 13074500936893336221626041)
              ·
                refine ⟨9805875702670002166219531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13074500936893336221626041 9805875702670002166219531)
                ·
                  refine ⟨14708813554005003249329297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9805875702670002166219531 14708813554005003249329297)
                  ·
                    refine ⟨11031610165503752436996973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14708813554005003249329297 11031610165503752436996973)
                    ·
                      refine ⟨4136853812063907163873865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11031610165503752436996973 4136853812063907163873865)
                      ·
                        rfl

theorem cell23_8056494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_8056494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056494 prefixEnd_8056494 := by exact prefixLift 8056494
  have htrace : WordTrace (prefixWord ++ tailWord_8056494) baseStart_8056494 baseEnd_8056494 := by
    simpa [prefixWord, tailWord_8056494, baseEnd_8056494] using wordTrace_append hprefix tailTrace_8056494
  have hstable : (prefixWord ++ tailWord_8056494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056494).length < 2 ^ (prefixWord ++ tailWord_8056494).sum := by decide
  have hdescent : baseEnd_8056494 < baseStart_8056494 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056496 : List Nat := [2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 4]
def baseStart_8056496 : Nat := 118140960795 + 8056496 * 2 ^ 59
def prefixEnd_8056496 : Nat := 4983230072969 + 3 ^ 40 * 8056496 * 2
def baseEnd_8056496 : Nat := 4136854839025216156048855

theorem tailTrace_8056496 : CollatzResearch.WordTrace tailWord_8056496 prefixEnd_8056496 4136854839025216156048855 := by
  unfold tailWord_8056496
  simp only [CollatzResearch.WordTrace]
  refine ⟨146922274710349203408866671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195896366280465604545155561 146922274710349203408866671)
  ·
    refine ⟨220383412065523805113300007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146922274710349203408866671 220383412065523805113300007)
    ·
      refine ⟨330575118098285707669950011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220383412065523805113300007 330575118098285707669950011)
      ·
        refine ⟨495862677147428561504925017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330575118098285707669950011 495862677147428561504925017)
        ·
          refine ⟨371897007860571421128693763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 495862677147428561504925017 371897007860571421128693763)
          ·
            refine ⟨557845511790857131693040645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371897007860571421128693763 557845511790857131693040645)
            ·
              refine ⟨104596033460785712192445121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 557845511790857131693040645 104596033460785712192445121)
              ·
                refine ⟨78447025095589284144333841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104596033460785712192445121 78447025095589284144333841)
                ·
                  refine ⟨58835268821691963108250381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78447025095589284144333841 58835268821691963108250381)
                  ·
                    refine ⟨22063225808134486165593893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58835268821691963108250381 22063225808134486165593893)
                    ·
                      refine ⟨4136854839025216156048855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22063225808134486165593893 4136854839025216156048855)
                      ·
                        rfl

theorem cell23_8056496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 4].length) (baseStart_8056496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056496 prefixEnd_8056496 := by exact prefixLift 8056496
  have htrace : WordTrace (prefixWord ++ tailWord_8056496) baseStart_8056496 baseEnd_8056496 := by
    simpa [prefixWord, tailWord_8056496, baseEnd_8056496] using wordTrace_append hprefix tailTrace_8056496
  have hstable : (prefixWord ++ tailWord_8056496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056496).length < 2 ^ (prefixWord ++ tailWord_8056496).sum := by decide
  have hdescent : baseEnd_8056496 < baseStart_8056496 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056514 : List Nat := [3, 5, 1, 2, 2, 1, 9]
def baseStart_8056514 : Nat := 118140960795 + 8056514 * 2 ^ 59
def prefixEnd_8056514 : Nat := 4983230072969 + 3 ^ 40 * 8056514 * 2
def baseEnd_8056514 : Nat := 51072396070086383773133

theorem tailTrace_8056514 : CollatzResearch.WordTrace tailWord_8056514 prefixEnd_8056514 51072396070086383773133 := by
  unfold tailWord_8056514
  simp only [CollatzResearch.WordTrace]
  refine ⟨73461301483658298972972149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195896803956422130594592397 73461301483658298972972149)
  ·
    refine ⟨6886997014092965528716139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73461301483658298972972149 6886997014092965528716139)
    ·
      refine ⟨10330495521139448293074209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6886997014092965528716139 10330495521139448293074209)
      ·
        refine ⟨7747871640854586219805657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10330495521139448293074209 7747871640854586219805657)
        ·
          refine ⟨5810903730640939664854243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7747871640854586219805657 5810903730640939664854243)
          ·
            refine ⟨8716355595961409497281365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5810903730640939664854243 8716355595961409497281365)
            ·
              refine ⟨51072396070086383773133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8716355595961409497281365 51072396070086383773133)
              ·
                rfl

theorem cell23_8056514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 9].length) (baseStart_8056514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056514 prefixEnd_8056514 := by exact prefixLift 8056514
  have htrace : WordTrace (prefixWord ++ tailWord_8056514) baseStart_8056514 baseEnd_8056514 := by
    simpa [prefixWord, tailWord_8056514, baseEnd_8056514] using wordTrace_append hprefix tailTrace_8056514
  have hstable : (prefixWord ++ tailWord_8056514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056514).length < 2 ^ (prefixWord ++ tailWord_8056514).sum := by decide
  have hdescent : baseEnd_8056514 < baseStart_8056514 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056551 : List Nat := [1, 1, 5, 4, 1, 2, 1, 2, 1, 3, 2]
def baseStart_8056551 : Nat := 118140960795 + 8056551 * 2 ^ 59
def prefixEnd_8056551 : Nat := 4983230072969 + 3 ^ 40 * 8056551 * 2
def baseEnd_8056551 : Nat := 4136883080461213440861103

theorem tailTrace_8056551 : CollatzResearch.WordTrace tailWord_8056551 prefixEnd_8056551 4136883080461213440861103 := by
  unfold tailWord_8056551
  simp only [CollatzResearch.WordTrace]
  refine ⟨293846555435499151210985507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195897703623666100807323671 293846555435499151210985507)
  ·
    refine ⟨440769833153248726816478261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293846555435499151210985507 440769833153248726816478261)
    ·
      refine ⟨41322171858117068139044837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 440769833153248726816478261 41322171858117068139044837)
      ·
        refine ⟨7747907223396950276070907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41322171858117068139044837 7747907223396950276070907)
        ·
          refine ⟨11621860835095425414106361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7747907223396950276070907 11621860835095425414106361)
          ·
            refine ⟨8716395626321569060579771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11621860835095425414106361 8716395626321569060579771)
            ·
              refine ⟨13074593439482353590869657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8716395626321569060579771 13074593439482353590869657)
              ·
                refine ⟨9805945079611765193152243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13074593439482353590869657 9805945079611765193152243)
                ·
                  refine ⟨14708917619417647789728365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9805945079611765193152243 14708917619417647789728365)
                  ·
                    refine ⟨5515844107281617921148137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14708917619417647789728365 5515844107281617921148137)
                    ·
                      refine ⟨4136883080461213440861103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5515844107281617921148137 4136883080461213440861103)
                      ·
                        rfl

theorem cell23_8056551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_8056551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056551 prefixEnd_8056551 := by exact prefixLift 8056551
  have htrace : WordTrace (prefixWord ++ tailWord_8056551) baseStart_8056551 baseEnd_8056551 := by
    simpa [prefixWord, tailWord_8056551, baseEnd_8056551] using wordTrace_append hprefix tailTrace_8056551
  have hstable : (prefixWord ++ tailWord_8056551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056551).length < 2 ^ (prefixWord ++ tailWord_8056551).sum := by decide
  have hdescent : baseEnd_8056551 < baseStart_8056551 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056564 : List Nat := [2, 6, 1, 1, 1, 1, 1, 1, 3, 4, 2]
def baseStart_8056564 : Nat := 118140960795 + 8056564 * 2 ^ 59
def prefixEnd_8056564 : Nat := 4983230072969 + 3 ^ 40 * 8056564 * 2
def baseEnd_8056564 : Nat := 4136889755709721889998543

theorem tailTrace_8056564 : CollatzResearch.WordTrace tailWord_8056564 prefixEnd_8056564 4136889755709721889998543 := by
  unfold tailWord_8056564
  simp only [CollatzResearch.WordTrace]
  refine ⟨146923514792226027215604373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195898019722968036287472497 146923514792226027215604373)
  ·
    refine ⟨6887039755885595025731455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 146923514792226027215604373 6887039755885595025731455)
    ·
      refine ⟨10330559633828392538597183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6887039755885595025731455 10330559633828392538597183)
      ·
        refine ⟨15495839450742588807895775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10330559633828392538597183 15495839450742588807895775)
        ·
          refine ⟨23243759176113883211843663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15495839450742588807895775 23243759176113883211843663)
          ·
            refine ⟨34865638764170824817765495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23243759176113883211843663 34865638764170824817765495)
            ·
              refine ⟨52298458146256237226648243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34865638764170824817765495 52298458146256237226648243)
              ·
                refine ⟨78447687219384355839972365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52298458146256237226648243 78447687219384355839972365)
                ·
                  refine ⟨29417882707269133439989637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78447687219384355839972365 29417882707269133439989637)
                  ·
                    refine ⟨5515853007612962519998057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29417882707269133439989637 5515853007612962519998057)
                    ·
                      refine ⟨4136889755709721889998543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5515853007612962519998057 4136889755709721889998543)
                      ·
                        rfl

theorem cell23_8056564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_8056564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056564 prefixEnd_8056564 := by exact prefixLift 8056564
  have htrace : WordTrace (prefixWord ++ tailWord_8056564) baseStart_8056564 baseEnd_8056564 := by
    simpa [prefixWord, tailWord_8056564, baseEnd_8056564] using wordTrace_append hprefix tailTrace_8056564
  have hstable : (prefixWord ++ tailWord_8056564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056564).length < 2 ^ (prefixWord ++ tailWord_8056564).sum := by decide
  have hdescent : baseEnd_8056564 < baseStart_8056564 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056576 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 7]
def baseStart_8056576 : Nat := 118140960795 + 8056576 * 2 ^ 59
def prefixEnd_8056576 : Nat := 4983230072969 + 3 ^ 40 * 8056576 * 2
def baseEnd_8056576 : Nat := 4136895917477575843048487

theorem tailTrace_8056576 : CollatzResearch.WordTrace tailWord_8056576 prefixEnd_8056576 4136895917477575843048487 := by
  unfold tailWord_8056576
  simp only [CollatzResearch.WordTrace]
  refine ⟨146923733630204290240322791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195898311506939053653763721 146923733630204290240322791)
  ·
    refine ⟨220385600445306435360484187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146923733630204290240322791 220385600445306435360484187)
    ·
      refine ⟨330578400667959653040726281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220385600445306435360484187 330578400667959653040726281)
      ·
        refine ⟨247933800500969739780544711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330578400667959653040726281 247933800500969739780544711)
        ·
          refine ⟨371900700751454609670817067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247933800500969739780544711 371900700751454609670817067)
          ·
            refine ⟨557851051127181914506225601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371900700751454609670817067 557851051127181914506225601)
            ·
              refine ⟨418388288345386435879669201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 557851051127181914506225601 418388288345386435879669201)
              ·
                refine ⟨313791216259039826909751901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 418388288345386435879669201 313791216259039826909751901)
                ·
                  refine ⟨117671706097139935091156963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 313791216259039826909751901 117671706097139935091156963)
                  ·
                    refine ⟨176507559145709902636735445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 117671706097139935091156963 176507559145709902636735445)
                    ·
                      refine ⟨4136895917477575843048487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 176507559145709902636735445 4136895917477575843048487)
                      ·
                        rfl

theorem cell23_8056576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_8056576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056576 prefixEnd_8056576 := by exact prefixLift 8056576
  have htrace : WordTrace (prefixWord ++ tailWord_8056576) baseStart_8056576 baseEnd_8056576 := by
    simpa [prefixWord, tailWord_8056576, baseEnd_8056576] using wordTrace_append hprefix tailTrace_8056576
  have hstable : (prefixWord ++ tailWord_8056576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056576).length < 2 ^ (prefixWord ++ tailWord_8056576).sum := by decide
  have hdescent : baseEnd_8056576 < baseStart_8056576 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056590 : List Nat := [4, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2]
def baseStart_8056590 : Nat := 118140960795 + 8056590 * 2 ^ 59
def prefixEnd_8056590 : Nat := 4983230072969 + 3 ^ 40 * 8056590 * 2
def baseEnd_8056590 : Nat := 4136903106206738788273423

theorem tailTrace_8056590 : CollatzResearch.WordTrace tailWord_8056590 prefixEnd_8056590 4136903106206738788273423 := by
  unfold tailWord_8056590
  simp only [CollatzResearch.WordTrace]
  refine ⟨36730997235294732608956903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195898651921571907247770149 36730997235294732608956903)
  ·
    refine ⟨55096495852942098913435355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36730997235294732608956903 55096495852942098913435355)
    ·
      refine ⟨82644743779413148370153033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55096495852942098913435355 82644743779413148370153033)
      ·
        refine ⟨61983557834559861277614775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82644743779413148370153033 61983557834559861277614775)
        ·
          refine ⟨92975336751839791916422163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61983557834559861277614775 92975336751839791916422163)
          ·
            refine ⟨139463005127759687874633245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92975336751839791916422163 139463005127759687874633245)
            ·
              refine ⟨52298626922909882952987467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139463005127759687874633245 52298626922909882952987467)
              ·
                refine ⟨78447940384364824429481201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52298626922909882952987467 78447940384364824429481201)
                ·
                  refine ⟨58835955288273618322110901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78447940384364824429481201 58835955288273618322110901)
                  ·
                    refine ⟨5515870808275651717697897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58835955288273618322110901 5515870808275651717697897)
                    ·
                      refine ⟨4136903106206738788273423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5515870808275651717697897 4136903106206738788273423)
                      ·
                        rfl

theorem cell23_8056590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_8056590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056590 prefixEnd_8056590 := by exact prefixLift 8056590
  have htrace : WordTrace (prefixWord ++ tailWord_8056590) baseStart_8056590 baseEnd_8056590 := by
    simpa [prefixWord, tailWord_8056590, baseEnd_8056590] using wordTrace_append hprefix tailTrace_8056590
  have hstable : (prefixWord ++ tailWord_8056590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056590).length < 2 ^ (prefixWord ++ tailWord_8056590).sum := by decide
  have hdescent : baseEnd_8056590 < baseStart_8056590 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056620 : List Nat := [2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 4]
def baseStart_8056620 : Nat := 118140960795 + 8056620 * 2 ^ 59
def prefixEnd_8056620 : Nat := 4983230072969 + 3 ^ 40 * 8056620 * 2
def baseEnd_8056620 : Nat := 4136918510626373670898285

theorem tailTrace_8056620 : CollatzResearch.WordTrace tailWord_8056620 prefixEnd_8056620 4136918510626373670898285 := by
  unfold tailWord_8056620
  simp only [CollatzResearch.WordTrace]
  refine ⟨146924536036124587997623657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195899381381499450663498209 146924536036124587997623657)
  ·
    refine ⟨110193402027093440998217743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146924536036124587997623657 110193402027093440998217743)
    ·
      refine ⟨165290103040640161497326615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110193402027093440998217743 165290103040640161497326615)
      ·
        refine ⟨247935154560960242245989923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165290103040640161497326615 247935154560960242245989923)
        ·
          refine ⟨371902731841440363368984885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247935154560960242245989923 371902731841440363368984885)
          ·
            refine ⟨34865881110135034065842333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 371902731841440363368984885 34865881110135034065842333)
            ·
              refine ⟨13074705416300637774690875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34865881110135034065842333 13074705416300637774690875)
              ·
                refine ⟨19612058124450956662036313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13074705416300637774690875 19612058124450956662036313)
                ·
                  refine ⟨14709043593338217496527235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19612058124450956662036313 14709043593338217496527235)
                  ·
                    refine ⟨22063565390007326244790853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14709043593338217496527235 22063565390007326244790853)
                    ·
                      refine ⟨4136918510626373670898285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22063565390007326244790853 4136918510626373670898285)
                      ·
                        rfl

theorem cell23_8056620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 4].length) (baseStart_8056620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056620 prefixEnd_8056620 := by exact prefixLift 8056620
  have htrace : WordTrace (prefixWord ++ tailWord_8056620) baseStart_8056620 baseEnd_8056620 := by
    simpa [prefixWord, tailWord_8056620, baseEnd_8056620] using wordTrace_append hprefix tailTrace_8056620
  have hstable : (prefixWord ++ tailWord_8056620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056620).length < 2 ^ (prefixWord ++ tailWord_8056620).sum := by decide
  have hdescent : baseEnd_8056620 < baseStart_8056620 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056623 : List Nat := [1, 1, 2, 1, 2, 1, 2, 5, 1, 4, 3]
def baseStart_8056623 : Nat := 118140960795 + 8056623 * 2 ^ 59
def prefixEnd_8056623 : Nat := 4983230072969 + 3 ^ 40 * 8056623 * 2
def baseEnd_8056623 : Nat := 4136920051068337159160771

theorem tailTrace_8056623 : CollatzResearch.WordTrace tailWord_8056623 prefixEnd_8056623 4136920051068337159160771 := by
  unfold tailWord_8056623
  simp only [CollatzResearch.WordTrace]
  refine ⟨293849181491238307507606523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195899454327492205005071015 293849181491238307507606523)
  ·
    refine ⟨440773772236857461261409785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293849181491238307507606523 440773772236857461261409785)
    ·
      refine ⟨330580329177643095946057339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440773772236857461261409785 330580329177643095946057339)
      ·
        refine ⟨495870493766464643919086009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330580329177643095946057339 495870493766464643919086009)
        ·
          refine ⟨371902870324848482939314507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 495870493766464643919086009 371902870324848482939314507)
          ·
            refine ⟨557854305487272724408971761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371902870324848482939314507 557854305487272724408971761)
            ·
              refine ⟨418390729115454543306728821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 557854305487272724408971761 418390729115454543306728821)
              ·
                refine ⟨39224130854573863435005827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 418390729115454543306728821 39224130854573863435005827)
                ·
                  refine ⟨58836196281860795152508741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39224130854573863435005827 58836196281860795152508741)
                  ·
                    refine ⟨11031786802848899091095389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58836196281860795152508741 11031786802848899091095389)
                    ·
                      refine ⟨4136920051068337159160771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11031786802848899091095389 4136920051068337159160771)
                      ·
                        rfl

theorem cell23_8056623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 4, 3].length) (baseStart_8056623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056623 prefixEnd_8056623 := by exact prefixLift 8056623
  have htrace : WordTrace (prefixWord ++ tailWord_8056623) baseStart_8056623 baseEnd_8056623 := by
    simpa [prefixWord, tailWord_8056623, baseEnd_8056623] using wordTrace_append hprefix tailTrace_8056623
  have hstable : (prefixWord ++ tailWord_8056623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056623).length < 2 ^ (prefixWord ++ tailWord_8056623).sum := by decide
  have hdescent : baseEnd_8056623 < baseStart_8056623 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056637 : List Nat := [1, 4, 1, 4, 1, 1, 1, 2, 2, 4, 2]
def baseStart_8056637 : Nat := 118140960795 + 8056637 * 2 ^ 59
def prefixEnd_8056637 : Nat := 4983230072969 + 3 ^ 40 * 8056637 * 2
def baseEnd_8056637 : Nat := 4136927239797500104385707

theorem tailTrace_8056637 : CollatzResearch.WordTrace tailWord_8056637 prefixEnd_8056637 4136927239797500104385707 := by
  unfold tailWord_8056637
  simp only [CollatzResearch.WordTrace]
  refine ⟨293849692113187587898616165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195899794742125058599077443 293849692113187587898616165)
  ·
    refine ⟨55096817271222672730990531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293849692113187587898616165 55096817271222672730990531)
    ·
      refine ⟨82645225906834009096485797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55096817271222672730990531 82645225906834009096485797)
      ·
        refine ⟨15495979857531376705591087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82645225906834009096485797 15495979857531376705591087)
        ·
          refine ⟨23243969786297065058386631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15495979857531376705591087 23243969786297065058386631)
          ·
            refine ⟨34865954679445597587579947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23243969786297065058386631 34865954679445597587579947)
            ·
              refine ⟨52298932019168396381369921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34865954679445597587579947 52298932019168396381369921)
              ·
                refine ⟨39224199014376297286027441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52298932019168396381369921 39224199014376297286027441)
                ·
                  refine ⟨29418149260782222964520581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39224199014376297286027441 29418149260782222964520581)
                  ·
                    refine ⟨5515902986396666805847609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29418149260782222964520581 5515902986396666805847609)
                    ·
                      refine ⟨4136927239797500104385707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5515902986396666805847609 4136927239797500104385707)
                      ·
                        rfl

theorem cell23_8056637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_8056637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056637 prefixEnd_8056637 := by exact prefixLift 8056637
  have htrace : WordTrace (prefixWord ++ tailWord_8056637) baseStart_8056637 baseEnd_8056637 := by
    simpa [prefixWord, tailWord_8056637, baseEnd_8056637] using wordTrace_append hprefix tailTrace_8056637
  have hstable : (prefixWord ++ tailWord_8056637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056637).length < 2 ^ (prefixWord ++ tailWord_8056637).sum := by decide
  have hdescent : baseEnd_8056637 < baseStart_8056637 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056643 : List Nat := [1, 1, 1, 3, 1, 6, 1, 1, 8]
def baseStart_8056643 : Nat := 118140960795 + 8056643 * 2 ^ 59
def prefixEnd_8056643 : Nat := 4983230072969 + 3 ^ 40 * 8056643 * 2
def baseEnd_8056643 : Nat := 459658924520158564545631

theorem tailTrace_8056643 : CollatzResearch.WordTrace tailWord_8056643 prefixEnd_8056643 459658924520158564545631 := by
  unfold tailWord_8056643
  simp only [CollatzResearch.WordTrace]
  refine ⟨293849910951165850923334583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195899940634110567282223055 293849910951165850923334583)
  ·
    refine ⟨440774866426748776385001875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293849910951165850923334583 440774866426748776385001875)
    ·
      refine ⟨661162299640123164577502813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440774866426748776385001875 661162299640123164577502813)
      ·
        refine ⟨247935862365046186716563555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 661162299640123164577502813 247935862365046186716563555)
        ·
          refine ⟨371903793547569280074845333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247935862365046186716563555 371903793547569280074845333)
          ·
            refine ⟨17432990322542310003508375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 371903793547569280074845333 17432990322542310003508375)
            ·
              refine ⟨26149485483813465005262563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17432990322542310003508375 26149485483813465005262563)
              ·
                refine ⟨39224228225720197507893845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26149485483813465005262563 39224228225720197507893845)
                ·
                  refine ⟨459658924520158564545631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39224228225720197507893845 459658924520158564545631)
                  ·
                    rfl

theorem cell23_8056643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 8].length) (baseStart_8056643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056643 prefixEnd_8056643 := by exact prefixLift 8056643
  have htrace : WordTrace (prefixWord ++ tailWord_8056643) baseStart_8056643 baseEnd_8056643 := by
    simpa [prefixWord, tailWord_8056643, baseEnd_8056643] using wordTrace_append hprefix tailTrace_8056643
  have hstable : (prefixWord ++ tailWord_8056643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056643).length < 2 ^ (prefixWord ++ tailWord_8056643).sum := by decide
  have hdescent : baseEnd_8056643 < baseStart_8056643 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056647 : List Nat := [1, 1, 4, 1, 2, 1, 4, 4, 1, 4]
def baseStart_8056647 : Nat := 118140960795 + 8056647 * 2 ^ 59
def prefixEnd_8056647 : Nat := 4983230072969 + 3 ^ 40 * 8056647 * 2
def baseEnd_8056647 : Nat := 1378977458201348355086887

theorem tailTrace_8056647 : CollatzResearch.WordTrace tailWord_8056647 prefixEnd_8056647 1378977458201348355086887 := by
  unfold tailWord_8056647
  simp only [CollatzResearch.WordTrace]
  refine ⟨293850056843151359606480195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195900037895434239737653463 293850056843151359606480195)
  ·
    refine ⟨440775085264727039409720293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293850056843151359606480195 440775085264727039409720293)
    ·
      refine ⟨82645328487136319889322555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 440775085264727039409720293 82645328487136319889322555)
      ·
        refine ⟨123967992730704479833983833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82645328487136319889322555 123967992730704479833983833)
        ·
          refine ⟨92975994548028359875487875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123967992730704479833983833 92975994548028359875487875)
          ·
            refine ⟨139463991822042539813231813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92975994548028359875487875 139463991822042539813231813)
            ·
              refine ⟨26149498466632976214980965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139463991822042539813231813 26149498466632976214980965)
              ·
                refine ⟨4903030962493683040308931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26149498466632976214980965 4903030962493683040308931)
                ·
                  refine ⟨7354546443740524560463397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4903030962493683040308931 7354546443740524560463397)
                  ·
                    refine ⟨1378977458201348355086887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7354546443740524560463397 1378977458201348355086887)
                    ·
                      rfl

theorem cell23_8056647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 4, 1, 4].length) (baseStart_8056647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056647 prefixEnd_8056647 := by exact prefixLift 8056647
  have htrace : WordTrace (prefixWord ++ tailWord_8056647) baseStart_8056647 baseEnd_8056647 := by
    simpa [prefixWord, tailWord_8056647, baseEnd_8056647] using wordTrace_append hprefix tailTrace_8056647
  have hstable : (prefixWord ++ tailWord_8056647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056647).length < 2 ^ (prefixWord ++ tailWord_8056647).sum := by decide
  have hdescent : baseEnd_8056647 < baseStart_8056647 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056697 : List Nat := [1, 2, 1, 3, 2, 2, 3, 2, 2, 3, 2]
def baseStart_8056697 : Nat := 118140960795 + 8056697 * 2 ^ 59
def prefixEnd_8056697 : Nat := 4983230072969 + 3 ^ 40 * 8056697 * 2
def baseEnd_8056697 : Nat := 4136958048636769869635431

theorem tailTrace_8056697 : CollatzResearch.WordTrace tailWord_8056697 prefixEnd_8056697 4136958048636769869635431 := by
  unfold tailWord_8056697
  simp only [CollatzResearch.WordTrace]
  refine ⟨293851880492970218145800345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195901253661980145430533563 293851880492970218145800345)
  ·
    refine ⟨220388910369727663609350259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293851880492970218145800345 220388910369727663609350259)
    ·
      refine ⟨330583365554591495414025389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220388910369727663609350259 330583365554591495414025389)
      ·
        refine ⟨123968762082971810780259521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330583365554591495414025389 123968762082971810780259521)
        ·
          refine ⟨92976571562228858085194641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123968762082971810780259521 92976571562228858085194641)
          ·
            refine ⟨69732428671671643563895981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92976571562228858085194641 69732428671671643563895981)
            ·
              refine ⟨26149660751876866336460993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69732428671671643563895981 26149660751876866336460993)
              ·
                refine ⟨19612245563907649752345745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26149660751876866336460993 19612245563907649752345745)
                ·
                  refine ⟨14709184172930737314259309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19612245563907649752345745 14709184172930737314259309)
                  ·
                    refine ⟨5515944064849026492847241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14709184172930737314259309 5515944064849026492847241)
                    ·
                      refine ⟨4136958048636769869635431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5515944064849026492847241 4136958048636769869635431)
                      ·
                        rfl

theorem cell23_8056697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 3, 2].length) (baseStart_8056697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056697 prefixEnd_8056697 := by exact prefixLift 8056697
  have htrace : WordTrace (prefixWord ++ tailWord_8056697) baseStart_8056697 baseEnd_8056697 := by
    simpa [prefixWord, tailWord_8056697, baseEnd_8056697] using wordTrace_append hprefix tailTrace_8056697
  have hstable : (prefixWord ++ tailWord_8056697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056697).length < 2 ^ (prefixWord ++ tailWord_8056697).sum := by decide
  have hdescent : baseEnd_8056697 < baseStart_8056697 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056724 : List Nat := [2, 4, 2, 1, 1, 4, 1, 2, 1, 5]
def baseStart_8056724 : Nat := 118140960795 + 8056724 * 2 ^ 59
def prefixEnd_8056724 : Nat := 4983230072969 + 3 ^ 40 * 8056724 * 2
def baseEnd_8056724 : Nat := 1378990637538147087999269

theorem tailTrace_8056724 : CollatzResearch.WordTrace tailWord_8056724 prefixEnd_8056724 1378990637538147087999269 := by
  unfold tailWord_8056724
  simp only [CollatzResearch.WordTrace]
  refine ⟨146926432631936200878516613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195901910175914934504688817 146926432631936200878516613)
  ·
    refine ⟨27548706118488037664721865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146926432631936200878516613 27548706118488037664721865)
    ·
      refine ⟨20661529588866028248541399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27548706118488037664721865 20661529588866028248541399)
      ·
        refine ⟨30992294383299042372812099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20661529588866028248541399 30992294383299042372812099)
        ·
          refine ⟨46488441574948563559218149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30992294383299042372812099 46488441574948563559218149)
          ·
            refine ⟨8716582795302855667353403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46488441574948563559218149 8716582795302855667353403)
            ·
              refine ⟨13074874192954283501030105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8716582795302855667353403 13074874192954283501030105)
              ·
                refine ⟨9806155644715712625772579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13074874192954283501030105 9806155644715712625772579)
                ·
                  refine ⟨14709233467073568938658869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9806155644715712625772579 14709233467073568938658869)
                  ·
                    refine ⟨1378990637538147087999269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14709233467073568938658869 1378990637538147087999269)
                    ·
                      rfl

theorem cell23_8056724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_8056724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056724 prefixEnd_8056724 := by exact prefixLift 8056724
  have htrace : WordTrace (prefixWord ++ tailWord_8056724) baseStart_8056724 baseEnd_8056724 := by
    simpa [prefixWord, tailWord_8056724, baseEnd_8056724] using wordTrace_append hprefix tailTrace_8056724
  have hstable : (prefixWord ++ tailWord_8056724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056724).length < 2 ^ (prefixWord ++ tailWord_8056724).sum := by decide
  have hdescent : baseEnd_8056724 < baseStart_8056724 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056727 : List Nat := [1, 1, 3, 3, 1, 3, 3, 2, 1, 1, 4]
def baseStart_8056727 : Nat := 118140960795 + 8056727 * 2 ^ 59
def prefixEnd_8056727 : Nat := 4983230072969 + 3 ^ 40 * 8056727 * 2
def baseEnd_8056727 : Nat := 4136973453056404752260293

theorem tailTrace_8056727 : CollatzResearch.WordTrace tailWord_8056727 prefixEnd_8056727 4136973453056404752260293 := by
  unfold tailWord_8056727
  simp only [CollatzResearch.WordTrace]
  refine ⟨293852974682861533269392435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195901983121907688846261623 293852974682861533269392435)
  ·
    refine ⟨440779462024292299904088653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293852974682861533269392435 440779462024292299904088653)
    ·
      refine ⟨165292298259109612464033245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 440779462024292299904088653 165292298259109612464033245)
      ·
        refine ⟨61984611847166104674012467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165292298259109612464033245 61984611847166104674012467)
        ·
          refine ⟨92976917770749157011018701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61984611847166104674012467 92976917770749157011018701)
          ·
            refine ⟨34866344164030933879132013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92976917770749157011018701 34866344164030933879132013)
            ·
              refine ⟨13074879061511600204674505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34866344164030933879132013 13074879061511600204674505)
              ·
                refine ⟨9806159296133700153505879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13074879061511600204674505 9806159296133700153505879)
                ·
                  refine ⟨14709238944200550230258819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9806159296133700153505879 14709238944200550230258819)
                  ·
                    refine ⟨22063858416300825345388229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14709238944200550230258819 22063858416300825345388229)
                    ·
                      refine ⟨4136973453056404752260293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22063858416300825345388229 4136973453056404752260293)
                      ·
                        rfl

theorem cell23_8056727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_8056727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056727 prefixEnd_8056727 := by exact prefixLift 8056727
  have htrace : WordTrace (prefixWord ++ tailWord_8056727) baseStart_8056727 baseEnd_8056727 := by
    simpa [prefixWord, tailWord_8056727, baseEnd_8056727] using wordTrace_append hprefix tailTrace_8056727
  have hstable : (prefixWord ++ tailWord_8056727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056727).length < 2 ^ (prefixWord ++ tailWord_8056727).sum := by decide
  have hdescent : baseEnd_8056727 < baseStart_8056727 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056737 : List Nat := [1, 2, 3, 4, 2, 1, 1, 2, 1, 6]
def baseStart_8056737 : Nat := 118140960795 + 8056737 * 2 ^ 59
def prefixEnd_8056737 : Nat := 4983230072969 + 3 ^ 40 * 8056737 * 2
def baseEnd_8056737 : Nat := 1378992862620983237711749

theorem tailTrace_8056737 : CollatzResearch.WordTrace tailWord_8056737 prefixEnd_8056737 1378992862620983237711749 := by
  unfold tailWord_8056737
  simp only [CollatzResearch.WordTrace]
  refine ⟨293853339412825304977256465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195902226275216869984837643 293853339412825304977256465)
  ·
    refine ⟨220390004559618978732942349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293853339412825304977256465 220390004559618978732942349)
    ·
      refine ⟨82646251709857117024853381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220390004559618978732942349 82646251709857117024853381)
      ·
        refine ⟨15496172195598209442160009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82646251709857117024853381 15496172195598209442160009)
        ·
          refine ⟨11622129146698657081620007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15496172195598209442160009 11622129146698657081620007)
          ·
            refine ⟨17433193720047985622430011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11622129146698657081620007 17433193720047985622430011)
            ·
              refine ⟨26149790580071978433645017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17433193720047985622430011 26149790580071978433645017)
              ·
                refine ⟨19612342935053983825233763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26149790580071978433645017 19612342935053983825233763)
                ·
                  refine ⟨29418514402580975737850645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19612342935053983825233763 29418514402580975737850645)
                  ·
                    refine ⟨1378992862620983237711749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29418514402580975737850645 1378992862620983237711749)
                    ·
                      rfl

theorem cell23_8056737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 6].length) (baseStart_8056737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056737 prefixEnd_8056737 := by exact prefixLift 8056737
  have htrace : WordTrace (prefixWord ++ tailWord_8056737) baseStart_8056737 baseEnd_8056737 := by
    simpa [prefixWord, tailWord_8056737, baseEnd_8056737] using wordTrace_append hprefix tailTrace_8056737
  have hstable : (prefixWord ++ tailWord_8056737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056737).length < 2 ^ (prefixWord ++ tailWord_8056737).sum := by decide
  have hdescent : baseEnd_8056737 < baseStart_8056737 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056740 : List Nat := [2, 3, 1, 2, 1, 3, 1, 1, 3, 2, 4]
def baseStart_8056740 : Nat := 118140960795 + 8056740 * 2 ^ 59
def prefixEnd_8056740 : Nat := 4983230072969 + 3 ^ 40 * 8056740 * 2
def baseEnd_8056740 : Nat := 4136980128304913201397733

theorem tailTrace_8056740 : CollatzResearch.WordTrace tailWord_8056740 prefixEnd_8056740 4136980128304913201397733 := by
  unfold tailWord_8056740
  simp only [CollatzResearch.WordTrace]
  refine ⟨146926724415907218244807837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195902299221209624326410449 146926724415907218244807837)
  ·
    refine ⟨55097521655965206841802939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146926724415907218244807837 55097521655965206841802939)
    ·
      refine ⟨82646282483947810262704409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55097521655965206841802939 82646282483947810262704409)
      ·
        refine ⟨61984711862960857697028307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82646282483947810262704409 61984711862960857697028307)
        ·
          refine ⟨92977067794441286545542461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61984711862960857697028307 92977067794441286545542461)
          ·
            refine ⟨34866400422915482454578423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92977067794441286545542461 34866400422915482454578423)
            ·
              refine ⟨52299600634373223681867635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34866400422915482454578423 52299600634373223681867635)
              ·
                refine ⟨78449400951559835522801453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52299600634373223681867635 78449400951559835522801453)
                ·
                  refine ⟨29418525356834938321050545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78449400951559835522801453 29418525356834938321050545)
                  ·
                    refine ⟨22063894017626203740787909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29418525356834938321050545 22063894017626203740787909)
                    ·
                      refine ⟨4136980128304913201397733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22063894017626203740787909 4136980128304913201397733)
                      ·
                        rfl

theorem cell23_8056740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_8056740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056740 prefixEnd_8056740 := by exact prefixLift 8056740
  have htrace : WordTrace (prefixWord ++ tailWord_8056740) baseStart_8056740 baseEnd_8056740 := by
    simpa [prefixWord, tailWord_8056740, baseEnd_8056740] using wordTrace_append hprefix tailTrace_8056740
  have hstable : (prefixWord ++ tailWord_8056740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056740).length < 2 ^ (prefixWord ++ tailWord_8056740).sum := by decide
  have hdescent : baseEnd_8056740 < baseStart_8056740 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056760 : List Nat := [2, 1, 2, 1, 2, 3, 1, 2, 3, 3, 3]
def baseStart_8056760 : Nat := 118140960795 + 8056760 * 2 ^ 59
def prefixEnd_8056760 : Nat := 4983230072969 + 3 ^ 40 * 8056760 * 2
def baseEnd_8056760 : Nat := 4136990397918003123147641

theorem tailTrace_8056760 : CollatzResearch.WordTrace tailWord_8056760 prefixEnd_8056760 4136990397918003123147641 := by
  unfold tailWord_8056760
  simp only [CollatzResearch.WordTrace]
  refine ⟨146927089145870989952671867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195902785527827986603562489 146927089145870989952671867)
  ·
    refine ⟨220390633718806484929007801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146927089145870989952671867 220390633718806484929007801)
    ·
      refine ⟨165292975289104863696755851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220390633718806484929007801 165292975289104863696755851)
      ·
        refine ⟨247939462933657295545133777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165292975289104863696755851 247939462933657295545133777)
        ·
          refine ⟨185954597200242971658850333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247939462933657295545133777 185954597200242971658850333)
          ·
            refine ⟨69732973950091114372068875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185954597200242971658850333 69732973950091114372068875)
            ·
              refine ⟨104599460925136671558103313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69732973950091114372068875 104599460925136671558103313)
              ·
                refine ⟨78449595693852503668577485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104599460925136671558103313 78449595693852503668577485)
                ·
                  refine ⟨29418598385194688875716557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78449595693852503668577485 29418598385194688875716557)
                  ·
                    refine ⟨11031974394448008328393709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29418598385194688875716557 11031974394448008328393709)
                    ·
                      refine ⟨4136990397918003123147641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11031974394448008328393709 4136990397918003123147641)
                      ·
                        rfl

theorem cell23_8056760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 3, 3, 3].length) (baseStart_8056760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056760 prefixEnd_8056760 := by exact prefixLift 8056760
  have htrace : WordTrace (prefixWord ++ tailWord_8056760) baseStart_8056760 baseEnd_8056760 := by
    simpa [prefixWord, tailWord_8056760, baseEnd_8056760] using wordTrace_append hprefix tailTrace_8056760
  have hstable : (prefixWord ++ tailWord_8056760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056760).length < 2 ^ (prefixWord ++ tailWord_8056760).sum := by decide
  have hdescent : baseEnd_8056760 < baseStart_8056760 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056761 : List Nat := [1, 2, 1, 4, 2, 1, 3, 4, 1, 2, 2]
def baseStart_8056761 : Nat := 118140960795 + 8056761 * 2 ^ 59
def prefixEnd_8056761 : Nat := 4983230072969 + 3 ^ 40 * 8056761 * 2
def baseEnd_8056761 : Nat := 4136990911398657619235137

theorem tailTrace_8056761 : CollatzResearch.WordTrace tailWord_8056761 prefixEnd_8056761 4136990911398657619235137 := by
  unfold tailWord_8056761
  simp only [CollatzResearch.WordTrace]
  refine ⟨293854214764738357076130137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195902809843158904717420091 293854214764738357076130137)
  ·
    refine ⟨220390661073553767807097603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293854214764738357076130137 220390661073553767807097603)
    ·
      refine ⟨330585991610330651710646405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220390661073553767807097603 330585991610330651710646405)
      ·
        refine ⟨61984873426936997195746201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 330585991610330651710646405 61984873426936997195746201)
        ·
          refine ⟨46488655070202747896809651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61984873426936997195746201 46488655070202747896809651)
          ·
            refine ⟨69732982605304121845214477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46488655070202747896809651 69732982605304121845214477)
            ·
              refine ⟨26149868476989045691955429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69732982605304121845214477 26149868476989045691955429)
              ·
                refine ⟨4903100339435446067241643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26149868476989045691955429 4903100339435446067241643)
                ·
                  refine ⟨7354650509153169100862465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4903100339435446067241643 7354650509153169100862465)
                  ·
                    refine ⟨5515987881864876825646849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7354650509153169100862465 5515987881864876825646849)
                    ·
                      refine ⟨4136990911398657619235137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5515987881864876825646849 4136990911398657619235137)
                      ·
                        rfl

theorem cell23_8056761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 4, 1, 2, 2].length) (baseStart_8056761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056761 prefixEnd_8056761 := by exact prefixLift 8056761
  have htrace : WordTrace (prefixWord ++ tailWord_8056761) baseStart_8056761 baseEnd_8056761 := by
    simpa [prefixWord, tailWord_8056761, baseEnd_8056761] using wordTrace_append hprefix tailTrace_8056761
  have hstable : (prefixWord ++ tailWord_8056761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056761).length < 2 ^ (prefixWord ++ tailWord_8056761).sum := by decide
  have hdescent : baseEnd_8056761 < baseStart_8056761 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056763 : List Nat := [1, 1, 1, 1, 1, 2, 2, 5, 2, 7]
def baseStart_8056763 : Nat := 118140960795 + 8056763 * 2 ^ 59
def prefixEnd_8056763 : Nat := 4983230072969 + 3 ^ 40 * 8056763 * 2
def baseEnd_8056763 : Nat := 1378997312786655537136709

theorem tailTrace_8056763 : CollatzResearch.WordTrace tailWord_8056763 prefixEnd_8056763 1378997312786655537136709 := by
  unfold tailWord_8056763
  simp only [CollatzResearch.WordTrace]
  refine ⟨293854287710731111417702943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195902858473820740945135295 293854287710731111417702943)
  ·
    refine ⟨440781431566096667126554415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293854287710731111417702943 440781431566096667126554415)
    ·
      refine ⟨661172147349145000689831623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440781431566096667126554415 661172147349145000689831623)
      ·
        refine ⟨991758221023717501034747435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661172147349145000689831623 991758221023717501034747435)
        ·
          refine ⟨1487637331535576251552121153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 991758221023717501034747435 1487637331535576251552121153)
          ·
            refine ⟨1115727998651682188664090865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1487637331535576251552121153 1115727998651682188664090865)
            ·
              refine ⟨836795998988761641498068149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1115727998651682188664090865 836795998988761641498068149)
              ·
                refine ⟨78449624905196403890443889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 836795998988761641498068149 78449624905196403890443889)
                ·
                  refine ⟨58837218678897302917832917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78449624905196403890443889 58837218678897302917832917)
                  ·
                    refine ⟨1378997312786655537136709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58837218678897302917832917 1378997312786655537136709)
                    ·
                      rfl

theorem cell23_8056763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 7].length) (baseStart_8056763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056763 prefixEnd_8056763 := by exact prefixLift 8056763
  have htrace : WordTrace (prefixWord ++ tailWord_8056763) baseStart_8056763 baseEnd_8056763 := by
    simpa [prefixWord, tailWord_8056763, baseEnd_8056763] using wordTrace_append hprefix tailTrace_8056763
  have hstable : (prefixWord ++ tailWord_8056763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056763).length < 2 ^ (prefixWord ++ tailWord_8056763).sum := by decide
  have hdescent : baseEnd_8056763 < baseStart_8056763 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056804 : List Nat := [2, 3, 1, 1, 1, 1, 5, 3, 1, 3, 2]
def baseStart_8056804 : Nat := 118140960795 + 8056804 * 2 ^ 59
def prefixEnd_8056804 : Nat := 4983230072969 + 3 ^ 40 * 8056804 * 2
def baseEnd_8056804 : Nat := 4137012991066800950997439

theorem tailTrace_8056804 : CollatzResearch.WordTrace tailWord_8056804 prefixEnd_8056804 4137012991066800950997439 := by
  unfold tailWord_8056804
  simp only [CollatzResearch.WordTrace]
  refine ⟨146927891551791287709972733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195903855402388383613296977 146927891551791287709972733)
  ·
    refine ⟨55097959331921732891239775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146927891551791287709972733 55097959331921732891239775)
    ·
      refine ⟨82646938997882599336859663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55097959331921732891239775 82646938997882599336859663)
      ·
        refine ⟨123970408496823899005289495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82646938997882599336859663 123970408496823899005289495)
        ·
          refine ⟨185955612745235848507934243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123970408496823899005289495 185955612745235848507934243)
          ·
            refine ⟨278933419117853772761901365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185955612745235848507934243 278933419117853772761901365)
            ·
              refine ⟨26150008042298791196428253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 278933419117853772761901365 26150008042298791196428253)
              ·
                refine ⟨9806253015862046698660595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26150008042298791196428253 9806253015862046698660595)
                ·
                  refine ⟨14709379523793070047990893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9806253015862046698660595 14709379523793070047990893)
                  ·
                    refine ⟨5516017321422401267996585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14709379523793070047990893 5516017321422401267996585)
                    ·
                      refine ⟨4137012991066800950997439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5516017321422401267996585 4137012991066800950997439)
                      ·
                        rfl

theorem cell23_8056804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 1, 3, 2].length) (baseStart_8056804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056804 prefixEnd_8056804 := by exact prefixLift 8056804
  have htrace : WordTrace (prefixWord ++ tailWord_8056804) baseStart_8056804 baseEnd_8056804 := by
    simpa [prefixWord, tailWord_8056804, baseEnd_8056804] using wordTrace_append hprefix tailTrace_8056804
  have hstable : (prefixWord ++ tailWord_8056804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056804).length < 2 ^ (prefixWord ++ tailWord_8056804).sum := by decide
  have hdescent : baseEnd_8056804 < baseStart_8056804 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056810 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 4, 6]
def baseStart_8056810 : Nat := 118140960795 + 8056810 * 2 ^ 59
def prefixEnd_8056810 : Nat := 4983230072969 + 3 ^ 40 * 8056810 * 2
def baseEnd_8056810 : Nat := 1379005357316909309174137

theorem tailTrace_8056810 : CollatzResearch.WordTrace tailWord_8056810 prefixEnd_8056810 1379005357316909309174137 := by
  unfold tailWord_8056810
  simp only [CollatzResearch.WordTrace]
  refine ⟨73464000485390209611165971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195904001294373892296442589 73464000485390209611165971)
  ·
    refine ⟨110196000728085314416748957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73464000485390209611165971 110196000728085314416748957)
    ·
      refine ⟨41323500273031992906280859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110196000728085314416748957 41323500273031992906280859)
      ·
        refine ⟨61985250409547989359421289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41323500273031992906280859 61985250409547989359421289)
        ·
          refine ⟨46488937807160992019565967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61985250409547989359421289 46488937807160992019565967)
          ·
            refine ⟨69733406710741488029348951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46488937807160992019565967 69733406710741488029348951)
            ·
              refine ⟨104600110066112232044023427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69733406710741488029348951 104600110066112232044023427)
              ·
                refine ⟨156900165099168348066035141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104600110066112232044023427 156900165099168348066035141)
                ·
                  refine ⟨29418780956094065262381589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156900165099168348066035141 29418780956094065262381589)
                  ·
                    refine ⟨1379005357316909309174137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29418780956094065262381589 1379005357316909309174137)
                    ·
                      rfl

theorem cell23_8056810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_8056810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056810 prefixEnd_8056810 := by exact prefixLift 8056810
  have htrace : WordTrace (prefixWord ++ tailWord_8056810) baseStart_8056810 baseEnd_8056810 := by
    simpa [prefixWord, tailWord_8056810, baseEnd_8056810] using wordTrace_append hprefix tailTrace_8056810
  have hstable : (prefixWord ++ tailWord_8056810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056810).length < 2 ^ (prefixWord ++ tailWord_8056810).sum := by decide
  have hdescent : baseEnd_8056810 < baseStart_8056810 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056840 : List Nat := [2, 1, 3, 2, 1, 2, 1, 4, 7]
def baseStart_8056840 : Nat := 118140960795 + 8056840 * 2 ^ 59
def prefixEnd_8056840 : Nat := 4983230072969 + 3 ^ 40 * 8056840 * 2
def baseEnd_8056840 : Nat := 459670164041151423349697

theorem tailTrace_8056840 : CollatzResearch.WordTrace tailWord_8056840 prefixEnd_8056840 459670164041151423349697 := by
  unfold tailWord_8056840
  simp only [CollatzResearch.WordTrace]
  refine ⟨146928548065726076784127987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195904730754301435712170649 146928548065726076784127987)
  ·
    refine ⟨220392822098589115176191981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146928548065726076784127987 220392822098589115176191981)
    ·
      refine ⟨82647308286970918191071993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220392822098589115176191981 82647308286970918191071993)
      ·
        refine ⟨61985481215228188643303995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82647308286970918191071993 61985481215228188643303995)
        ·
          refine ⟨92978221822842282964955993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61985481215228188643303995 92978221822842282964955993)
          ·
            refine ⟨69733666367131712223716995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92978221822842282964955993 69733666367131712223716995)
            ·
              refine ⟨104600499550697568335575493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69733666367131712223716995 104600499550697568335575493)
              ·
                refine ⟨19612593665755794062920405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104600499550697568335575493 19612593665755794062920405)
                ·
                  refine ⟨459670164041151423349697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19612593665755794062920405 459670164041151423349697)
                  ·
                    rfl

theorem cell23_8056840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 7].length) (baseStart_8056840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056840 prefixEnd_8056840 := by exact prefixLift 8056840
  have htrace : WordTrace (prefixWord ++ tailWord_8056840) baseStart_8056840 baseEnd_8056840 := by
    simpa [prefixWord, tailWord_8056840, baseEnd_8056840] using wordTrace_append hprefix tailTrace_8056840
  have hstable : (prefixWord ++ tailWord_8056840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056840).length < 2 ^ (prefixWord ++ tailWord_8056840).sum := by decide
  have hdescent : baseEnd_8056840 < baseStart_8056840 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056874 : List Nat := [3, 1, 4, 1, 2, 3, 1, 1, 7]
def baseStart_8056874 : Nat := 118140960795 + 8056874 * 2 ^ 59
def prefixEnd_8056874 : Nat := 4983230072969 + 3 ^ 40 * 8056874 * 2
def baseEnd_8056874 : Nat := 459672103856957297458013

theorem tailTrace_8056874 : CollatzResearch.WordTrace tailWord_8056874 prefixEnd_8056874 459672103856957297458013 := by
  unfold tailWord_8056874
  simp only [CollatzResearch.WordTrace]
  refine ⟨73464584053332244343748419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195905557475552651583329117 73464584053332244343748419)
  ·
    refine ⟨110196876079998366515622629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73464584053332244343748419 110196876079998366515622629)
    ·
      refine ⟨20661914264999693721679243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110196876079998366515622629 20661914264999693721679243)
      ·
        refine ⟨30992871397499540582518865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20661914264999693721679243 30992871397499540582518865)
        ·
          refine ⟨23244653548124655436889149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30992871397499540582518865 23244653548124655436889149)
          ·
            refine ⟨8716745080546745788833431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23244653548124655436889149 8716745080546745788833431)
            ·
              refine ⟨13075117620820118683250147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8716745080546745788833431 13075117620820118683250147)
              ·
                refine ⟨19612676431230178024875221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13075117620820118683250147 19612676431230178024875221)
                ·
                  refine ⟨459672103856957297458013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19612676431230178024875221 459672103856957297458013)
                  ·
                    rfl

theorem cell23_8056874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 7].length) (baseStart_8056874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056874 prefixEnd_8056874 := by exact prefixLift 8056874
  have htrace : WordTrace (prefixWord ++ tailWord_8056874) baseStart_8056874 baseEnd_8056874 := by
    simpa [prefixWord, tailWord_8056874, baseEnd_8056874] using wordTrace_append hprefix tailTrace_8056874
  have hstable : (prefixWord ++ tailWord_8056874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056874).length < 2 ^ (prefixWord ++ tailWord_8056874).sum := by decide
  have hdescent : baseEnd_8056874 < baseStart_8056874 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056880 : List Nat := [2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 7]
def baseStart_8056880 : Nat := 118140960795 + 8056880 * 2 ^ 59
def prefixEnd_8056880 : Nat := 4983230072969 + 3 ^ 40 * 8056880 * 2
def baseEnd_8056880 : Nat := 4137052015596542653647089

theorem tailTrace_8056880 : CollatzResearch.WordTrace tailWord_8056880 prefixEnd_8056880 4137052015596542653647089 := by
  unfold tailWord_8056880
  simp only [CollatzResearch.WordTrace]
  refine ⟨146929277525653620199856047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195905703367538160266474729 146929277525653620199856047)
  ·
    refine ⟨220393916288480430299784071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146929277525653620199856047 220393916288480430299784071)
    ·
      refine ⟨330590874432720645449676107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220393916288480430299784071 330590874432720645449676107)
      ·
        refine ⟨495886311649080968174514161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330590874432720645449676107 495886311649080968174514161)
        ·
          refine ⟨371914733736810726130885621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 495886311649080968174514161 371914733736810726130885621)
          ·
            refine ⟨34867006287826005574770527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 371914733736810726130885621 34867006287826005574770527)
            ·
              refine ⟨52300509431739008362155791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34867006287826005574770527 52300509431739008362155791)
              ·
                refine ⟨78450764147608512543233687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52300509431739008362155791 78450764147608512543233687)
                ·
                  refine ⟨117676146221412768814850531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78450764147608512543233687 117676146221412768814850531)
                  ·
                    refine ⟨176514219332119153222275797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 117676146221412768814850531 176514219332119153222275797)
                    ·
                      refine ⟨4137052015596542653647089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 176514219332119153222275797 4137052015596542653647089)
                      ·
                        rfl

theorem cell23_8056880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 7].length) (baseStart_8056880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056880 prefixEnd_8056880 := by exact prefixLift 8056880
  have htrace : WordTrace (prefixWord ++ tailWord_8056880) baseStart_8056880 baseEnd_8056880 := by
    simpa [prefixWord, tailWord_8056880, baseEnd_8056880] using wordTrace_append hprefix tailTrace_8056880
  have hstable : (prefixWord ++ tailWord_8056880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056880).length < 2 ^ (prefixWord ++ tailWord_8056880).sum := by decide
  have hdescent : baseEnd_8056880 < baseStart_8056880 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056907 : List Nat := [1, 1, 1, 1, 3, 1, 2, 4, 1, 6, 2]
def baseStart_8056907 : Nat := 118140960795 + 8056907 * 2 ^ 59
def prefixEnd_8056907 : Nat := 4983230072969 + 3 ^ 40 * 8056907 * 2
def baseEnd_8056907 : Nat := 4137065879574214048009465

theorem tailTrace_8056907 : CollatzResearch.WordTrace tailWord_8056907 prefixEnd_8056907 4137065879574214048009465 := by
  unfold tailWord_8056907
  simp only [CollatzResearch.WordTrace]
  refine ⟨293859539822209424010944975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195906359881472949340629983 293859539822209424010944975)
  ·
    refine ⟨440789309733314136016417463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293859539822209424010944975 440789309733314136016417463)
    ·
      refine ⟨661183964599971204024626195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440789309733314136016417463 661183964599971204024626195)
      ·
        refine ⟨991775946899956806036939293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661183964599971204024626195 991775946899956806036939293)
        ·
          refine ⟨371915980087483802263852235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 991775946899956806036939293 371915980087483802263852235)
          ·
            refine ⟨557873970131225703395778353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371915980087483802263852235 557873970131225703395778353)
            ·
              refine ⟨418405477598419277546833765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 557873970131225703395778353 418405477598419277546833765)
              ·
                refine ⟨78451027049703614540031331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 418405477598419277546833765 78451027049703614540031331)
                ·
                  refine ⟨117676540574555421810046997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78451027049703614540031331 117676540574555421810046997)
                  ·
                    refine ⟨5516087839432285397345953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 117676540574555421810046997 5516087839432285397345953)
                    ·
                      refine ⟨4137065879574214048009465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5516087839432285397345953 4137065879574214048009465)
                      ·
                        rfl

theorem cell23_8056907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 6, 2].length) (baseStart_8056907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056907 prefixEnd_8056907 := by exact prefixLift 8056907
  have htrace : WordTrace (prefixWord ++ tailWord_8056907) baseStart_8056907 baseEnd_8056907 := by
    simpa [prefixWord, tailWord_8056907, baseEnd_8056907] using wordTrace_append hprefix tailTrace_8056907
  have hstable : (prefixWord ++ tailWord_8056907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056907).length < 2 ^ (prefixWord ++ tailWord_8056907).sum := by decide
  have hdescent : baseEnd_8056907 < baseStart_8056907 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056924 : List Nat := [2, 2, 4, 1, 1, 2, 2, 2, 2, 1, 4]
def baseStart_8056924 : Nat := 118140960795 + 8056924 * 2 ^ 59
def prefixEnd_8056924 : Nat := 4983230072969 + 3 ^ 40 * 8056924 * 2
def baseEnd_8056924 : Nat := 4137074608745340481496887

theorem tailTrace_8056924 : CollatzResearch.WordTrace tailWord_8056924 prefixEnd_8056924 4137074608745340481496887 := by
  unfold tailWord_8056924
  simp only [CollatzResearch.WordTrace]
  refine ⟨146930079931573917957156913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195906773242098557276209217 146930079931573917957156913)
  ·
    refine ⟨110197559948680438467867685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146930079931573917957156913 110197559948680438467867685)
    ·
      refine ⟨20662042490377582212725191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110197559948680438467867685 20662042490377582212725191)
      ·
        refine ⟨30993063735566373319087787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20662042490377582212725191 30993063735566373319087787)
        ·
          refine ⟨46489595603349559978631681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30993063735566373319087787 46489595603349559978631681)
          ·
            refine ⟨34867196702512169983973761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46489595603349559978631681 34867196702512169983973761)
            ·
              refine ⟨26150397526884127487980321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34867196702512169983973761 26150397526884127487980321)
              ·
                refine ⟨19612798145163095615985241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26150397526884127487980321 19612798145163095615985241)
                ·
                  refine ⟨14709598608872321711988931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19612798145163095615985241 14709598608872321711988931)
                  ·
                    refine ⟨22064397913308482567983397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14709598608872321711988931 22064397913308482567983397)
                    ·
                      refine ⟨4137074608745340481496887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22064397913308482567983397 4137074608745340481496887)
                      ·
                        rfl

theorem cell23_8056924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_8056924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056924 prefixEnd_8056924 := by exact prefixLift 8056924
  have htrace : WordTrace (prefixWord ++ tailWord_8056924) baseStart_8056924 baseEnd_8056924 := by
    simpa [prefixWord, tailWord_8056924, baseEnd_8056924] using wordTrace_append hprefix tailTrace_8056924
  have hstable : (prefixWord ++ tailWord_8056924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056924).length < 2 ^ (prefixWord ++ tailWord_8056924).sum := by decide
  have hdescent : baseEnd_8056924 < baseStart_8056924 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056927 : List Nat := [1, 1, 2, 3, 1, 1, 2, 3, 4, 2, 3]
def baseStart_8056927 : Nat := 118140960795 + 8056927 * 2 ^ 59
def prefixEnd_8056927 : Nat := 4983230072969 + 3 ^ 40 * 8056927 * 2
def baseEnd_8056927 : Nat := 4137076149187303969759373

theorem tailTrace_8056927 : CollatzResearch.WordTrace tailWord_8056927 prefixEnd_8056927 4137076149187303969759373 := by
  unfold tailWord_8056927
  simp only [CollatzResearch.WordTrace]
  refine ⟨293860269282136967426673035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195906846188091311617782023 293860269282136967426673035)
  ·
    refine ⟨440790403923205451140009553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293860269282136967426673035 440790403923205451140009553)
    ·
      refine ⟨330592802942404088355007165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440790403923205451140009553 330592802942404088355007165)
      ·
        refine ⟨123972301103401533133127687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330592802942404088355007165 123972301103401533133127687)
        ·
          refine ⟨185958451655102299699691531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123972301103401533133127687 185958451655102299699691531)
          ·
            refine ⟨278937677482653449549537297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185958451655102299699691531 278937677482653449549537297)
            ·
              refine ⟨209203258111990087162152973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278937677482653449549537297 209203258111990087162152973)
              ·
                refine ⟨78451221791996282685807365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209203258111990087162152973 78451221791996282685807365)
                ·
                  refine ⟨14709604085999303003588881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78451221791996282685807365 14709604085999303003588881)
                  ·
                    refine ⟨11032203064499477252691661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14709604085999303003588881 11032203064499477252691661)
                    ·
                      refine ⟨4137076149187303969759373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11032203064499477252691661 4137076149187303969759373)
                      ·
                        rfl

theorem cell23_8056927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 2, 3].length) (baseStart_8056927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056927 prefixEnd_8056927 := by exact prefixLift 8056927
  have htrace : WordTrace (prefixWord ++ tailWord_8056927) baseStart_8056927 baseEnd_8056927 := by
    simpa [prefixWord, tailWord_8056927, baseEnd_8056927] using wordTrace_append hprefix tailTrace_8056927
  have hstable : (prefixWord ++ tailWord_8056927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056927).length < 2 ^ (prefixWord ++ tailWord_8056927).sum := by decide
  have hdescent : baseEnd_8056927 < baseStart_8056927 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056968 : List Nat := [2, 1, 3, 4, 1, 2, 2, 3, 1, 4]
def baseStart_8056968 : Nat := 118140960795 + 8056968 * 2 ^ 59
def prefixEnd_8056968 : Nat := 4983230072969 + 3 ^ 40 * 8056968 * 2
def baseEnd_8056968 : Nat := 1379032400631379436448895

theorem tailTrace_8056968 : CollatzResearch.WordTrace tailWord_8056968 prefixEnd_8056968 1379032400631379436448895 := by
  unfold tailWord_8056968
  simp only [CollatzResearch.WordTrace]
  refine ⟨146930882337494215714457779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195907843116658954285943705 146930882337494215714457779)
  ·
    refine ⟨220396323506241323571686669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146930882337494215714457779 220396323506241323571686669)
    ·
      refine ⟨82648621314840496339382501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220396323506241323571686669 82648621314840496339382501)
      ·
        refine ⟨15496616496532593063634219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82648621314840496339382501 15496616496532593063634219)
        ·
          refine ⟨23244924744798889595451329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15496616496532593063634219 23244924744798889595451329)
          ·
            refine ⟨17433693558599167196588497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23244924744798889595451329 17433693558599167196588497)
            ·
              refine ⟨13075270168949375397441373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17433693558599167196588497 13075270168949375397441373)
              ·
                refine ⟨4903226313356015774040515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13075270168949375397441373 4903226313356015774040515)
                ·
                  refine ⟨7354839470034023661060773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4903226313356015774040515 7354839470034023661060773)
                  ·
                    refine ⟨1379032400631379436448895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7354839470034023661060773 1379032400631379436448895)
                    ·
                      rfl

theorem cell23_8056968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 3, 1, 4].length) (baseStart_8056968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056968 prefixEnd_8056968 := by exact prefixLift 8056968
  have htrace : WordTrace (prefixWord ++ tailWord_8056968) baseStart_8056968 baseEnd_8056968 := by
    simpa [prefixWord, tailWord_8056968, baseEnd_8056968] using wordTrace_append hprefix tailTrace_8056968
  have hstable : (prefixWord ++ tailWord_8056968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056968).length < 2 ^ (prefixWord ++ tailWord_8056968).sum := by decide
  have hdescent : baseEnd_8056968 < baseStart_8056968 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8056991 : List Nat := [1, 1, 2, 6, 1, 1, 1, 3, 3, 1, 3]
def baseStart_8056991 : Nat := 118140960795 + 8056991 * 2 ^ 59
def prefixEnd_8056991 : Nat := 4983230072969 + 3 ^ 40 * 8056991 * 2
def baseEnd_8056991 : Nat := 4137109011949191719359079

theorem tailTrace_8056991 : CollatzResearch.WordTrace tailWord_8056991 prefixEnd_8056991 4137109011949191719359079 := by
  unfold tailWord_8056991
  simp only [CollatzResearch.WordTrace]
  refine ⟨293862603553905106357002827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195908402369270070904668551 293862603553905106357002827)
  ·
    refine ⟨440793905330857659535504241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293862603553905106357002827 440793905330857659535504241)
    ·
      refine ⟨330595428998143244651628181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440793905330857659535504241 330595428998143244651628181)
      ·
        refine ⟨15496660734287964593045071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 330595428998143244651628181 15496660734287964593045071)
        ·
          refine ⟨23244991101431946889567607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15496660734287964593045071 23244991101431946889567607)
          ·
            refine ⟨34867486652147920334351411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23244991101431946889567607 34867486652147920334351411)
            ·
              refine ⟨52301229978221880501527117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34867486652147920334351411 52301229978221880501527117)
              ·
                refine ⟨19612961241833205188072669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52301229978221880501527117 19612961241833205188072669)
                ·
                  refine ⟨7354860465687451945527251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19612961241833205188072669 7354860465687451945527251)
                  ·
                    refine ⟨11032290698531177918290877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7354860465687451945527251 11032290698531177918290877)
                    ·
                      refine ⟨4137109011949191719359079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11032290698531177918290877 4137109011949191719359079)
                      ·
                        rfl

theorem cell23_8056991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_8056991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8056991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8056991 prefixEnd_8056991 := by exact prefixLift 8056991
  have htrace : WordTrace (prefixWord ++ tailWord_8056991) baseStart_8056991 baseEnd_8056991 := by
    simpa [prefixWord, tailWord_8056991, baseEnd_8056991] using wordTrace_append hprefix tailTrace_8056991
  have hstable : (prefixWord ++ tailWord_8056991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8056991).length < 2 ^ (prefixWord ++ tailWord_8056991).sum := by decide
  have hdescent : baseEnd_8056991 < baseStart_8056991 := by decide
  rcases family_descends (prefixWord ++ tailWord_8056991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057017 : List Nat := [1, 2, 1, 4, 1, 2, 1, 2, 3, 1, 5]
def baseStart_8057017 : Nat := 118140960795 + 8057017 * 2 ^ 59
def prefixEnd_8057017 : Nat := 4983230072969 + 3 ^ 40 * 8057017 * 2
def baseEnd_8057017 : Nat := 4137122362446208617633959

theorem tailTrace_8057017 : CollatzResearch.WordTrace tailWord_8057017 prefixEnd_8057017 4137122362446208617633959 := by
  unfold tailWord_8057017
  simp only [CollatzResearch.WordTrace]
  refine ⟨293863551851810912797449305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195909034567873941864966203 293863551851810912797449305)
  ·
    refine ⟨220397663888858184598086979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293863551851810912797449305 220397663888858184598086979)
    ·
      refine ⟨330596495833287276897130469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220397663888858184598086979 330596495833287276897130469)
      ·
        refine ⟨61986842968741364418211963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 330596495833287276897130469 61986842968741364418211963)
        ·
          refine ⟨92980264453112046627317945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61986842968741364418211963 92980264453112046627317945)
          ·
            refine ⟨69735198339834034970488459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92980264453112046627317945 69735198339834034970488459)
            ·
              refine ⟨104602797509751052455732689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69735198339834034970488459 104602797509751052455732689)
              ·
                refine ⟨78452098132313289341799517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104602797509751052455732689 78452098132313289341799517)
                ·
                  refine ⟨29419536799617483503174819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78452098132313289341799517 29419536799617483503174819)
                  ·
                    refine ⟨44129305199426225254762229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29419536799617483503174819 44129305199426225254762229)
                    ·
                      refine ⟨4137122362446208617633959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44129305199426225254762229 4137122362446208617633959)
                      ·
                        rfl

theorem cell23_8057017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_8057017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057017 prefixEnd_8057017 := by exact prefixLift 8057017
  have htrace : WordTrace (prefixWord ++ tailWord_8057017) baseStart_8057017 baseEnd_8057017 := by
    simpa [prefixWord, tailWord_8057017, baseEnd_8057017] using wordTrace_append hprefix tailTrace_8057017
  have hstable : (prefixWord ++ tailWord_8057017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057017).length < 2 ^ (prefixWord ++ tailWord_8057017).sum := by decide
  have hdescent : baseEnd_8057017 < baseStart_8057017 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057024 : List Nat := [2, 1, 1, 2, 5, 1, 1, 2, 4, 4]
def baseStart_8057024 : Nat := 118140960795 + 8057024 * 2 ^ 59
def prefixEnd_8057024 : Nat := 4983230072969 + 3 ^ 40 * 8057024 * 2
def baseEnd_8057024 : Nat := 1379041985603596696748809

theorem tailTrace_8057024 : CollatzResearch.WordTrace tailWord_8057024 prefixEnd_8057024 1379041985603596696748809 := by
  unfold tailWord_8057024
  simp only [CollatzResearch.WordTrace]
  refine ⟨146931903581392776496477063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195909204775190368661969417 146931903581392776496477063)
  ·
    refine ⟨220397855372089164744715595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146931903581392776496477063 220397855372089164744715595)
    ·
      refine ⟨330596783058133747117073393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220397855372089164744715595 330596783058133747117073393)
      ·
        refine ⟨247947587293600310337805045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330596783058133747117073393 247947587293600310337805045)
        ·
          refine ⟨23245086308775029094169223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 247947587293600310337805045 23245086308775029094169223)
          ·
            refine ⟨34867629463162543641253835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23245086308775029094169223 34867629463162543641253835)
            ·
              refine ⟨52301444194743815461880753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34867629463162543641253835 52301444194743815461880753)
              ·
                refine ⟨39226083146057861596410565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52301444194743815461880753 39226083146057861596410565)
                ·
                  refine ⟨7354890589885849049326981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39226083146057861596410565 7354890589885849049326981)
                  ·
                    refine ⟨1379041985603596696748809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7354890589885849049326981 1379041985603596696748809)
                    ·
                      rfl

theorem cell23_8057024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 4, 4].length) (baseStart_8057024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057024 prefixEnd_8057024 := by exact prefixLift 8057024
  have htrace : WordTrace (prefixWord ++ tailWord_8057024) baseStart_8057024 baseEnd_8057024 := by
    simpa [prefixWord, tailWord_8057024, baseEnd_8057024] using wordTrace_append hprefix tailTrace_8057024
  have hstable : (prefixWord ++ tailWord_8057024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057024).length < 2 ^ (prefixWord ++ tailWord_8057024).sum := by decide
  have hdescent : baseEnd_8057024 < baseStart_8057024 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057034 : List Nat := [3, 1, 2, 1, 3, 1, 4, 1, 1, 1, 5]
def baseStart_8057034 : Nat := 118140960795 + 8057034 * 2 ^ 59
def prefixEnd_8057034 : Nat := 4983230072969 + 3 ^ 40 * 8057034 * 2
def baseEnd_8057034 : Nat := 4137131091617335051121381

theorem tailTrace_8057034 : CollatzResearch.WordTrace tailWord_8057034 prefixEnd_8057034 4137131091617335051121381 := by
  unfold tailWord_8057034
  simp only [CollatzResearch.WordTrace]
  refine ⟨73466042973187331175204539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195909447928499549800545437 73466042973187331175204539)
  ·
    refine ⟨110199064459780996762806809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73466042973187331175204539 110199064459780996762806809)
    ·
      refine ⟨82649298344835747572105107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110199064459780996762806809 82649298344835747572105107)
      ·
        refine ⟨123973947517253621358157661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82649298344835747572105107 123973947517253621358157661)
        ·
          refine ⟨46490230318970108009309123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123973947517253621358157661 46490230318970108009309123)
          ·
            refine ⟨69735345478455162013963685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46490230318970108009309123 69735345478455162013963685)
            ·
              refine ⟨13075377277210342877618191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69735345478455162013963685 13075377277210342877618191)
              ·
                refine ⟨19613065915815514316427287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13075377277210342877618191 19613065915815514316427287)
                ·
                  refine ⟨29419598873723271474640931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19613065915815514316427287 29419598873723271474640931)
                  ·
                    refine ⟨44129398310584907211961397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29419598873723271474640931 44129398310584907211961397)
                    ·
                      refine ⟨4137131091617335051121381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44129398310584907211961397 4137131091617335051121381)
                      ·
                        rfl

theorem cell23_8057034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 1, 1, 5].length) (baseStart_8057034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057034 prefixEnd_8057034 := by exact prefixLift 8057034
  have htrace : WordTrace (prefixWord ++ tailWord_8057034) baseStart_8057034 baseEnd_8057034 := by
    simpa [prefixWord, tailWord_8057034, baseEnd_8057034] using wordTrace_append hprefix tailTrace_8057034
  have hstable : (prefixWord ++ tailWord_8057034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057034).length < 2 ^ (prefixWord ++ tailWord_8057034).sum := by decide
  have hdescent : baseEnd_8057034 < baseStart_8057034 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057048 : List Nat := [2, 1, 2, 2, 4, 1, 3, 1, 3, 2, 2]
def baseStart_8057048 : Nat := 118140960795 + 8057048 * 2 ^ 59
def prefixEnd_8057048 : Nat := 4983230072969 + 3 ^ 40 * 8057048 * 2
def baseEnd_8057048 : Nat := 4137138280346497996346317

theorem tailTrace_8057048 : CollatzResearch.WordTrace tailWord_8057048 prefixEnd_8057048 4137138280346497996346317 := by
  unfold tailWord_8057048
  simp only [CollatzResearch.WordTrace]
  refine ⟨146932341257349302545913899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195909788343132403394551865 146932341257349302545913899)
  ·
    refine ⟨220398511886023953818870849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146932341257349302545913899 220398511886023953818870849)
    ·
      refine ⟨165298883914517965364153137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220398511886023953818870849 165298883914517965364153137)
      ·
        refine ⟨123974162935888474023114853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165298883914517965364153137 123974162935888474023114853)
        ·
          refine ⟨23245155550479088879334035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123974162935888474023114853 23245155550479088879334035)
          ·
            refine ⟨34867733325718633319001053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23245155550479088879334035 34867733325718633319001053)
            ·
              refine ⟨13075399997144487494625395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34867733325718633319001053 13075399997144487494625395)
              ·
                refine ⟨19613099995716731241938093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13075399997144487494625395 19613099995716731241938093)
                ·
                  refine ⟨7354912498393774215726785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19613099995716731241938093 7354912498393774215726785)
                  ·
                    refine ⟨5516184373795330661795089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7354912498393774215726785 5516184373795330661795089)
                    ·
                      refine ⟨4137138280346497996346317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5516184373795330661795089 4137138280346497996346317)
                      ·
                        rfl

theorem cell23_8057048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 3, 2, 2].length) (baseStart_8057048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057048 prefixEnd_8057048 := by exact prefixLift 8057048
  have htrace : WordTrace (prefixWord ++ tailWord_8057048) baseStart_8057048 baseEnd_8057048 := by
    simpa [prefixWord, tailWord_8057048, baseEnd_8057048] using wordTrace_append hprefix tailTrace_8057048
  have hstable : (prefixWord ++ tailWord_8057048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057048).length < 2 ^ (prefixWord ++ tailWord_8057048).sum := by decide
  have hdescent : baseEnd_8057048 < baseStart_8057048 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057057 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 2, 2, 6]
def baseStart_8057057 : Nat := 118140960795 + 8057057 * 2 ^ 59
def prefixEnd_8057057 : Nat := 4983230072969 + 3 ^ 40 * 8057057 * 2
def baseEnd_8057057 : Nat := 4137142901672388461133775

theorem tailTrace_8057057 : CollatzResearch.WordTrace tailWord_8057057 prefixEnd_8057057 4137142901672388461133775 := by
  unfold tailWord_8057057
  simp only [CollatzResearch.WordTrace]
  refine ⟨293865010771665999628905425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195910007181110666419270283 293865010771665999628905425)
  ·
    refine ⟨220398758078749499721679069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293865010771665999628905425 220398758078749499721679069)
    ·
      refine ⟨82649534279531062395629651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220398758078749499721679069 82649534279531062395629651)
      ·
        refine ⟨123974301419296593593444477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82649534279531062395629651 123974301419296593593444477)
        ·
          refine ⟨46490363032236222597541679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123974301419296593593444477 46490363032236222597541679)
          ·
            refine ⟨69735544548354333896312519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46490363032236222597541679 69735544548354333896312519)
            ·
              refine ⟨104603316822531500844468779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69735544548354333896312519 104603316822531500844468779)
              ·
                refine ⟨156904975233797251266703169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104603316822531500844468779 156904975233797251266703169)
                ·
                  refine ⟨117678731425347938450027377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156904975233797251266703169 117678731425347938450027377)
                  ·
                    refine ⟨88259048569010953837520533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117678731425347938450027377 88259048569010953837520533)
                    ·
                      refine ⟨4137142901672388461133775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88259048569010953837520533 4137142901672388461133775)
                      ·
                        rfl

theorem cell23_8057057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_8057057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057057 prefixEnd_8057057 := by exact prefixLift 8057057
  have htrace : WordTrace (prefixWord ++ tailWord_8057057) baseStart_8057057 baseEnd_8057057 := by
    simpa [prefixWord, tailWord_8057057, baseEnd_8057057] using wordTrace_append hprefix tailTrace_8057057
  have hstable : (prefixWord ++ tailWord_8057057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057057).length < 2 ^ (prefixWord ++ tailWord_8057057).sum := by decide
  have hdescent : baseEnd_8057057 < baseStart_8057057 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057107 : List Nat := [1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 5]
def baseStart_8057107 : Nat := 118140960795 + 8057107 * 2 ^ 59
def prefixEnd_8057107 : Nat := 4983230072969 + 3 ^ 40 * 8057107 * 2
def baseEnd_8057107 : Nat := 4137168575705113265508545

theorem tailTrace_8057107 : CollatzResearch.WordTrace tailWord_8057107 prefixEnd_8057107 4137168575705113265508545 := by
  unfold tailWord_8057107
  simp only [CollatzResearch.WordTrace]
  refine ⟨293866834421484858168225575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195911222947656572112150383 293866834421484858168225575)
  ·
    refine ⟨440800251632227287252338363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293866834421484858168225575 440800251632227287252338363)
    ·
      refine ⟨661200377448340930878507545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440800251632227287252338363 661200377448340930878507545)
      ·
        refine ⟨495900283086255698158880659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 661200377448340930878507545 495900283086255698158880659)
        ·
          refine ⟨743850424629383547238320989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495900283086255698158880659 743850424629383547238320989)
          ·
            refine ⟨278943909236018830214370371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 743850424629383547238320989 278943909236018830214370371)
            ·
              refine ⟨418415863854028245321555557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278943909236018830214370371 418415863854028245321555557)
              ·
                refine ⟨78452974472630295997791667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 418415863854028245321555557 78452974472630295997791667)
                ·
                  refine ⟨117679461708945443996687501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78452974472630295997791667 117679461708945443996687501)
                  ·
                    refine ⟨44129798140854541498757813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117679461708945443996687501 44129798140854541498757813)
                    ·
                      refine ⟨4137168575705113265508545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44129798140854541498757813 4137168575705113265508545)
                      ·
                        rfl

theorem cell23_8057107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 5].length) (baseStart_8057107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057107 prefixEnd_8057107 := by exact prefixLift 8057107
  have htrace : WordTrace (prefixWord ++ tailWord_8057107) baseStart_8057107 baseEnd_8057107 := by
    simpa [prefixWord, tailWord_8057107, baseEnd_8057107] using wordTrace_append hprefix tailTrace_8057107
  have hstable : (prefixWord ++ tailWord_8057107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057107).length < 2 ^ (prefixWord ++ tailWord_8057107).sum := by decide
  have hdescent : baseEnd_8057107 < baseStart_8057107 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057121 : List Nat := [1, 2, 3, 2, 1, 1, 3, 3, 1, 4, 2]
def baseStart_8057121 : Nat := 118140960795 + 8057121 * 2 ^ 59
def prefixEnd_8057121 : Nat := 4983230072969 + 3 ^ 40 * 8057121 * 2
def baseEnd_8057121 : Nat := 4137175764434276210733481

theorem tailTrace_8057121 : CollatzResearch.WordTrace tailWord_8057121 prefixEnd_8057121 4137175764434276210733481 := by
  unfold tailWord_8057121
  simp only [CollatzResearch.WordTrace]
  refine ⟨293867345043434138559235217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195911563362289425706156811 293867345043434138559235217)
  ·
    refine ⟨220400508782575603919426413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293867345043434138559235217 220400508782575603919426413)
    ·
      refine ⟨82650190793465851469784905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220400508782575603919426413 82650190793465851469784905)
      ·
        refine ⟨61987643095099388602338679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82650190793465851469784905 61987643095099388602338679)
        ·
          refine ⟨92981464642649082903508019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61987643095099388602338679 92981464642649082903508019)
          ·
            refine ⟨139472196963973624355262029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92981464642649082903508019 139472196963973624355262029)
            ·
              refine ⟨52302073861490109133223261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139472196963973624355262029 52302073861490109133223261)
              ·
                refine ⟨19613277698058790924958723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52302073861490109133223261 19613277698058790924958723)
                ·
                  refine ⟨29419916547088186387438085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19613277698058790924958723 29419916547088186387438085)
                  ·
                    refine ⟨5516234352579034947644641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29419916547088186387438085 5516234352579034947644641)
                    ·
                      refine ⟨4137175764434276210733481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5516234352579034947644641 4137175764434276210733481)
                      ·
                        rfl

theorem cell23_8057121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_8057121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057121 prefixEnd_8057121 := by exact prefixLift 8057121
  have htrace : WordTrace (prefixWord ++ tailWord_8057121) baseStart_8057121 baseEnd_8057121 := by
    simpa [prefixWord, tailWord_8057121, baseEnd_8057121] using wordTrace_append hprefix tailTrace_8057121
  have hstable : (prefixWord ++ tailWord_8057121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057121).length < 2 ^ (prefixWord ++ tailWord_8057121).sum := by decide
  have hdescent : baseEnd_8057121 < baseStart_8057121 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057172 : List Nat := [2, 4, 1, 1, 2, 3, 3, 1, 2, 2, 2]
def baseStart_8057172 : Nat := 118140960795 + 8057172 * 2 ^ 59
def prefixEnd_8057172 : Nat := 4983230072969 + 3 ^ 40 * 8057172 * 2
def baseEnd_8057172 : Nat := 4137201951947655511195747

theorem tailTrace_8057172 : CollatzResearch.WordTrace tailWord_8057172 prefixEnd_8057172 4137201951947655511195747 := by
  unfold tailWord_8057172
  simp only [CollatzResearch.WordTrace]
  refine ⟨146934602583124687134670885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195912803444166249512894513 146934602583124687134670885)
  ·
    refine ⟨27550237984335878837750791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146934602583124687134670885 27550237984335878837750791)
    ·
      refine ⟨41325356976503818256626187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27550237984335878837750791 41325356976503818256626187)
      ·
        refine ⟨61988035464755727384939281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41325356976503818256626187 61988035464755727384939281)
        ·
          refine ⟨46491026598566795538704461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61988035464755727384939281 46491026598566795538704461)
          ·
            refine ⟨17434134974462548327014173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46491026598566795538704461 17434134974462548327014173)
            ·
              refine ⟨6537800615423455622630315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17434134974462548327014173 6537800615423455622630315)
              ·
                refine ⟨9806700923135183433945473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6537800615423455622630315 9806700923135183433945473)
                ·
                  refine ⟨7355025692351387575459105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9806700923135183433945473 7355025692351387575459105)
                  ·
                    refine ⟨5516269269263540681594329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7355025692351387575459105 5516269269263540681594329)
                    ·
                      refine ⟨4137201951947655511195747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5516269269263540681594329 4137201951947655511195747)
                      ·
                        rfl

theorem cell23_8057172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_8057172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057172 prefixEnd_8057172 := by exact prefixLift 8057172
  have htrace : WordTrace (prefixWord ++ tailWord_8057172) baseStart_8057172 baseEnd_8057172 := by
    simpa [prefixWord, tailWord_8057172, baseEnd_8057172] using wordTrace_append hprefix tailTrace_8057172
  have hstable : (prefixWord ++ tailWord_8057172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057172).length < 2 ^ (prefixWord ++ tailWord_8057172).sum := by decide
  have hdescent : baseEnd_8057172 < baseStart_8057172 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057211 : List Nat := [1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 4]
def baseStart_8057211 : Nat := 118140960795 + 8057211 * 2 ^ 59
def prefixEnd_8057211 : Nat := 4983230072969 + 3 ^ 40 * 8057211 * 2
def baseEnd_8057211 : Nat := 4137221977693180858608067

theorem tailTrace_8057211 : CollatzResearch.WordTrace tailWord_8057211 prefixEnd_8057211 4137221977693180858608067 := by
  unfold tailWord_8057211
  simp only [CollatzResearch.WordTrace]
  refine ⟨293870627613108083930011487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195913751742072055953340991 293870627613108083930011487)
  ·
    refine ⟨440805941419662125895017231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293870627613108083930011487 440805941419662125895017231)
    ·
      refine ⟨661208912129493188842525847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440805941419662125895017231 661208912129493188842525847)
      ·
        refine ⟨991813368194239783263788771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661208912129493188842525847 991813368194239783263788771)
        ·
          refine ⟨1487720052291359674895683157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 991813368194239783263788771 1487720052291359674895683157)
          ·
            refine ⟨17434219362789371190183787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1487720052291359674895683157 17434219362789371190183787)
            ·
              refine ⟨26151329044184056785275681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17434219362789371190183787 26151329044184056785275681)
              ·
                refine ⟨19613496783138042588956761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26151329044184056785275681 19613496783138042588956761)
                ·
                  refine ⟨14710122587353531941717571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19613496783138042588956761 14710122587353531941717571)
                  ·
                    refine ⟨22065183881030297912576357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14710122587353531941717571 22065183881030297912576357)
                    ·
                      refine ⟨4137221977693180858608067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22065183881030297912576357 4137221977693180858608067)
                      ·
                        rfl

theorem cell23_8057211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 4].length) (baseStart_8057211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057211 prefixEnd_8057211 := by exact prefixLift 8057211
  have htrace : WordTrace (prefixWord ++ tailWord_8057211) baseStart_8057211 baseEnd_8057211 := by
    simpa [prefixWord, tailWord_8057211, baseEnd_8057211] using wordTrace_append hprefix tailTrace_8057211
  have hstable : (prefixWord ++ tailWord_8057211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057211).length < 2 ^ (prefixWord ++ tailWord_8057211).sum := by decide
  have hdescent : baseEnd_8057211 < baseStart_8057211 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057248 : List Nat := [2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 3]
def baseStart_8057248 : Nat := 118140960795 + 8057248 * 2 ^ 59
def prefixEnd_8057248 : Nat := 4983230072969 + 3 ^ 40 * 8057248 * 2
def baseEnd_8057248 : Nat := 4137240976477397213845397

theorem tailTrace_8057248 : CollatzResearch.WordTrace tailWord_8057248 prefixEnd_8057248 4137240976477397213845397 := by
  unfold tailWord_8057248
  simp only [CollatzResearch.WordTrace]
  refine ⟨146935988556987019624554199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195914651409316026166072265 146935988556987019624554199)
  ·
    refine ⟨220403982835480529436831299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146935988556987019624554199 220403982835480529436831299)
    ·
      refine ⟨330605974253220794155246949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220403982835480529436831299 330605974253220794155246949)
      ·
        refine ⟨61988620172478898904108803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 330605974253220794155246949 61988620172478898904108803)
        ·
          refine ⟨92982930258718348356163205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61988620172478898904108803 92982930258718348356163205)
          ·
            refine ⟨17434299423509690316780601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92982930258718348356163205 17434299423509690316780601)
            ·
              refine ⟨13075724567632267737585451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17434299423509690316780601 13075724567632267737585451)
              ·
                refine ⟨19613586851448401606378177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13075724567632267737585451 19613586851448401606378177)
                ·
                  refine ⟨14710190138586301204783633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19613586851448401606378177 14710190138586301204783633)
                  ·
                    refine ⟨11032642603939725903587725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14710190138586301204783633 11032642603939725903587725)
                    ·
                      refine ⟨4137240976477397213845397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11032642603939725903587725 4137240976477397213845397)
                      ·
                        rfl

theorem cell23_8057248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_8057248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057248 prefixEnd_8057248 := by exact prefixLift 8057248
  have htrace : WordTrace (prefixWord ++ tailWord_8057248) baseStart_8057248 baseEnd_8057248 := by
    simpa [prefixWord, tailWord_8057248, baseEnd_8057248] using wordTrace_append hprefix tailTrace_8057248
  have hstable : (prefixWord ++ tailWord_8057248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057248).length < 2 ^ (prefixWord ++ tailWord_8057248).sum := by decide
  have hdescent : baseEnd_8057248 < baseStart_8057248 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057274 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 2, 4, 5]
def baseStart_8057274 : Nat := 118140960795 + 8057274 * 2 ^ 59
def prefixEnd_8057274 : Nat := 4983230072969 + 3 ^ 40 * 8057274 * 2
def baseEnd_8057274 : Nat := 4137254326974414112120277

theorem tailTrace_8057274 : CollatzResearch.WordTrace tailWord_8057274 prefixEnd_8057274 4137254326974414112120277 := by
  unfold tailWord_8057274
  simp only [CollatzResearch.WordTrace]
  refine ⟨73468231352969961422388719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195915283607919897126369917 73468231352969961422388719)
  ·
    refine ⟨110202347029454942133583079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73468231352969961422388719 110202347029454942133583079)
    ·
      refine ⟨165303520544182413200374619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110202347029454942133583079 165303520544182413200374619)
      ·
        refine ⟨247955280816273619800561929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165303520544182413200374619 247955280816273619800561929)
        ·
          refine ⟨185966460612205214850421447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247955280816273619800561929 185966460612205214850421447)
          ·
            refine ⟨278949690918307822275632171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185966460612205214850421447 278949690918307822275632171)
            ·
              refine ⟨418424536377461733413448257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278949690918307822275632171 418424536377461733413448257)
              ·
                refine ⟨313818402283096300060086193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 418424536377461733413448257 313818402283096300060086193)
                ·
                  refine ⟨235363801712322225045064645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 313818402283096300060086193 235363801712322225045064645)
                  ·
                    refine ⟨44130712821060417195949621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 235363801712322225045064645 44130712821060417195949621)
                    ·
                      refine ⟨4137254326974414112120277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44130712821060417195949621 4137254326974414112120277)
                      ·
                        rfl

theorem cell23_8057274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_8057274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057274 prefixEnd_8057274 := by exact prefixLift 8057274
  have htrace : WordTrace (prefixWord ++ tailWord_8057274) baseStart_8057274 baseEnd_8057274 := by
    simpa [prefixWord, tailWord_8057274, baseEnd_8057274] using wordTrace_append hprefix tailTrace_8057274
  have hstable : (prefixWord ++ tailWord_8057274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057274).length < 2 ^ (prefixWord ++ tailWord_8057274).sum := by decide
  have hdescent : baseEnd_8057274 < baseStart_8057274 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057311 : List Nat := [1, 1, 2, 3, 3, 2, 2, 2, 1, 6]
def baseStart_8057311 : Nat := 118140960795 + 8057311 * 2 ^ 59
def prefixEnd_8057311 : Nat := 4983230072969 + 3 ^ 40 * 8057311 * 2
def baseEnd_8057311 : Nat := 1379091108586210155785869

theorem tailTrace_8057311 : CollatzResearch.WordTrace tailWord_8057311 prefixEnd_8057311 1379091108586210155785869 := by
  unfold tailWord_8057311
  simp only [CollatzResearch.WordTrace]
  refine ⟨293874274912745801008651787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195916183275163867339101191 293874274912745801008651787)
  ·
    refine ⟨440811412369118701512977681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293874274912745801008651787 440811412369118701512977681)
    ·
      refine ⟨330608559276839026134733261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440811412369118701512977681 330608559276839026134733261)
      ·
        refine ⟨123978209728814634800524973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330608559276839026134733261 123978209728814634800524973)
        ·
          refine ⟨46491828648305488050196865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123978209728814634800524973 46491828648305488050196865)
          ·
            refine ⟨34868871486229116037647649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46491828648305488050196865 34868871486229116037647649)
            ·
              refine ⟨26151653614671837028235737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34868871486229116037647649 26151653614671837028235737)
              ·
                refine ⟨19613740211003877771176803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26151653614671837028235737 19613740211003877771176803)
                ·
                  refine ⟨29420610316505816656765205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19613740211003877771176803 29420610316505816656765205)
                  ·
                    refine ⟨1379091108586210155785869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29420610316505816656765205 1379091108586210155785869)
                    ·
                      rfl

theorem cell23_8057311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 6].length) (baseStart_8057311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057311 prefixEnd_8057311 := by exact prefixLift 8057311
  have htrace : WordTrace (prefixWord ++ tailWord_8057311) baseStart_8057311 baseEnd_8057311 := by
    simpa [prefixWord, tailWord_8057311, baseEnd_8057311] using wordTrace_append hprefix tailTrace_8057311
  have hstable : (prefixWord ++ tailWord_8057311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057311).length < 2 ^ (prefixWord ++ tailWord_8057311).sum := by decide
  have hdescent : baseEnd_8057311 < baseStart_8057311 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057321 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 5, 2, 3]
def baseStart_8057321 : Nat := 118140960795 + 8057321 * 2 ^ 59
def prefixEnd_8057321 : Nat := 4983230072969 + 3 ^ 40 * 8057321 * 2
def baseEnd_8057321 : Nat := 4137278460565175428232561

theorem tailTrace_8057321 : CollatzResearch.WordTrace tailWord_8057321 prefixEnd_8057321 4137278460565175428232561 := by
  unfold tailWord_8057321
  simp only [CollatzResearch.WordTrace]
  refine ⟨293874639642709572716515817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195916426428473048477677211 293874639642709572716515817)
  ·
    refine ⟨220405979732032179537386863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293874639642709572716515817 220405979732032179537386863)
    ·
      refine ⟨330608969598048269306080295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220405979732032179537386863 330608969598048269306080295)
      ·
        refine ⟨495913454397072403959120443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330608969598048269306080295 495913454397072403959120443)
        ·
          refine ⟨743870181595608605938680665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495913454397072403959120443 743870181595608605938680665)
          ·
            refine ⟨557902636196706454454010499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 743870181595608605938680665 557902636196706454454010499)
            ·
              refine ⟨836853954295059681681015749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557902636196706454454010499 836853954295059681681015749)
              ·
                refine ⟨156910116430323690315190453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 836853954295059681681015749 156910116430323690315190453)
                ·
                  refine ⟨14710323415342845967049105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 156910116430323690315190453 14710323415342845967049105)
                  ·
                    refine ⟨11032742561507134475286829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14710323415342845967049105 11032742561507134475286829)
                    ·
                      refine ⟨4137278460565175428232561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11032742561507134475286829 4137278460565175428232561)
                      ·
                        rfl

theorem cell23_8057321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 2, 3].length) (baseStart_8057321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057321 prefixEnd_8057321 := by exact prefixLift 8057321
  have htrace : WordTrace (prefixWord ++ tailWord_8057321) baseStart_8057321 baseEnd_8057321 := by
    simpa [prefixWord, tailWord_8057321, baseEnd_8057321] using wordTrace_append hprefix tailTrace_8057321
  have hstable : (prefixWord ++ tailWord_8057321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057321).length < 2 ^ (prefixWord ++ tailWord_8057321).sum := by decide
  have hdescent : baseEnd_8057321 < baseStart_8057321 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057324 : List Nat := [2, 2, 1, 1, 2, 1, 14]
def baseStart_8057324 : Nat := 118140960795 + 8057324 * 2 ^ 59
def prefixEnd_8057324 : Nat := 4983230072969 + 3 ^ 40 * 8057324 * 2
def baseEnd_8057324 : Nat := 51077530876631344648087

theorem tailTrace_8057324 : CollatzResearch.WordTrace tailWord_8057324 prefixEnd_8057324 51077530876631344648087 := by
  unfold tailWord_8057324
  simp only [CollatzResearch.WordTrace]
  refine ⟨146937374530849352114437513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195916499374465802819250017 146937374530849352114437513)
  ·
    refine ⟨110203030898137014085828135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146937374530849352114437513 110203030898137014085828135)
    ·
      refine ⟨165304546347205521128742203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110203030898137014085828135 165304546347205521128742203)
      ·
        refine ⟨247956819520808281693113305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165304546347205521128742203 247956819520808281693113305)
        ·
          refine ⟨185967614640606211269834979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247956819520808281693113305 185967614640606211269834979)
          ·
            refine ⟨278951421960909316904752469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185967614640606211269834979 278951421960909316904752469)
            ·
              refine ⟨51077530876631344648087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 278951421960909316904752469 51077530876631344648087)
              ·
                rfl

theorem cell23_8057324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 14].length) (baseStart_8057324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057324 prefixEnd_8057324 := by exact prefixLift 8057324
  have htrace : WordTrace (prefixWord ++ tailWord_8057324) baseStart_8057324 baseEnd_8057324 := by
    simpa [prefixWord, tailWord_8057324, baseEnd_8057324] using wordTrace_append hprefix tailTrace_8057324
  have hstable : (prefixWord ++ tailWord_8057324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057324).length < 2 ^ (prefixWord ++ tailWord_8057324).sum := by decide
  have hdescent : baseEnd_8057324 < baseStart_8057324 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057348 : List Nat := [2, 3, 2, 3, 1, 2, 1, 1, 1, 1, 6]
def baseStart_8057348 : Nat := 118140960795 + 8057348 * 2 ^ 59
def prefixEnd_8057348 : Nat := 4983230072969 + 3 ^ 40 * 8057348 * 2
def baseEnd_8057348 : Nat := 4137292324542846822594937

theorem tailTrace_8057348 : CollatzResearch.WordTrace tailWord_8057348 prefixEnd_8057348 4137292324542846822594937 := by
  unfold tailWord_8057348
  simp only [CollatzResearch.WordTrace]
  refine ⟨146937812206805878163874349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195917082942407837551832465 146937812206805878163874349)
  ·
    refine ⟨55101679577552204311452881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146937812206805878163874349 55101679577552204311452881)
    ·
      refine ⟨41326259683164153233589661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55101679577552204311452881 41326259683164153233589661)
      ·
        refine ⟨15497347381186557462596123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41326259683164153233589661 15497347381186557462596123)
        ·
          refine ⟨23246021071779836193894185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15497347381186557462596123 23246021071779836193894185)
          ·
            refine ⟨17434515803834877145420639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23246021071779836193894185 17434515803834877145420639)
            ·
              refine ⟨26151773705752315718130959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17434515803834877145420639 26151773705752315718130959)
              ·
                refine ⟨39227660558628473577196439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26151773705752315718130959 39227660558628473577196439)
                ·
                  refine ⟨58841490837942710365794659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39227660558628473577196439 58841490837942710365794659)
                  ·
                    refine ⟨88262236256914065548691989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58841490837942710365794659 88262236256914065548691989)
                    ·
                      refine ⟨4137292324542846822594937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88262236256914065548691989 4137292324542846822594937)
                      ·
                        rfl

theorem cell23_8057348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_8057348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057348 prefixEnd_8057348 := by exact prefixLift 8057348
  have htrace : WordTrace (prefixWord ++ tailWord_8057348) baseStart_8057348 baseEnd_8057348 := by
    simpa [prefixWord, tailWord_8057348, baseEnd_8057348] using wordTrace_append hprefix tailTrace_8057348
  have hstable : (prefixWord ++ tailWord_8057348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057348).length < 2 ^ (prefixWord ++ tailWord_8057348).sum := by decide
  have hdescent : baseEnd_8057348 < baseStart_8057348 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057355 : List Nat := [1, 1, 1, 1, 7, 2, 2, 2, 1, 2, 3]
def baseStart_8057355 : Nat := 118140960795 + 8057355 * 2 ^ 59
def prefixEnd_8057355 : Nat := 4983230072969 + 3 ^ 40 * 8057355 * 2
def baseEnd_8057355 : Nat := 4137295918907428295207405

theorem tailTrace_8057355 : CollatzResearch.WordTrace tailWord_8057355 prefixEnd_8057355 4137295918907428295207405 := by
  unfold tailWord_8057355
  simp only [CollatzResearch.WordTrace]
  refine ⟨293875879724586396523253519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195917253149724264348835679 293875879724586396523253519)
  ·
    refine ⟨440813819586879594784880279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293875879724586396523253519 440813819586879594784880279)
    ·
      refine ⟨661220729380319392177320419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440813819586879594784880279 661220729380319392177320419)
      ·
        refine ⟨991831094070479088265980629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661220729380319392177320419 991831094070479088265980629)
        ·
          refine ⟨23246041267276853631233921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 991831094070479088265980629 23246041267276853631233921)
          ·
            refine ⟨17434530950457640223425441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23246041267276853631233921 17434530950457640223425441)
            ·
              refine ⟨13075898212843230167569081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17434530950457640223425441 13075898212843230167569081)
              ·
                refine ⟨9806923659632422625676811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13075898212843230167569081 9806923659632422625676811)
                ·
                  refine ⟨14710385489448633938515217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9806923659632422625676811 14710385489448633938515217)
                  ·
                    refine ⟨11032789117086475453886413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14710385489448633938515217 11032789117086475453886413)
                    ·
                      refine ⟨4137295918907428295207405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11032789117086475453886413 4137295918907428295207405)
                      ·
                        rfl

theorem cell23_8057355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 2, 3].length) (baseStart_8057355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057355 prefixEnd_8057355 := by exact prefixLift 8057355
  have htrace : WordTrace (prefixWord ++ tailWord_8057355) baseStart_8057355 baseEnd_8057355 := by
    simpa [prefixWord, tailWord_8057355, baseEnd_8057355] using wordTrace_append hprefix tailTrace_8057355
  have hstable : (prefixWord ++ tailWord_8057355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057355).length < 2 ^ (prefixWord ++ tailWord_8057355).sum := by decide
  have hdescent : baseEnd_8057355 < baseStart_8057355 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057358 : List Nat := [4, 1, 1, 2, 3, 1, 4, 7]
def baseStart_8057358 : Nat := 118140960795 + 8057358 * 2 ^ 59
def prefixEnd_8057358 : Nat := 4983230072969 + 3 ^ 40 * 8057358 * 2
def baseEnd_8057358 : Nat := 153233239235162658647033

theorem tailTrace_8057358 : CollatzResearch.WordTrace tailWord_8057358 prefixEnd_8057358 153233239235162658647033 := by
  unfold tailWord_8057358
  simp only [CollatzResearch.WordTrace]
  refine ⟨36734498642946941004451591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195917326095717018690408485 36734498642946941004451591)
  ·
    refine ⟨55101747964420411506677387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36734498642946941004451591 55101747964420411506677387)
    ·
      refine ⟨82652621946630617260016081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55101747964420411506677387 82652621946630617260016081)
      ·
        refine ⟨61989466459972962945012061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82652621946630617260016081 61989466459972962945012061)
        ·
          refine ⟨23246049922489861104379523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61989466459972962945012061 23246049922489861104379523)
          ·
            refine ⟨34869074883734791656569285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23246049922489861104379523 34869074883734791656569285)
            ·
              refine ⟨6537951540700273435606741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34869074883734791656569285 6537951540700273435606741)
              ·
                refine ⟨153233239235162658647033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6537951540700273435606741 153233239235162658647033)
                ·
                  rfl

theorem cell23_8057358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 7].length) (baseStart_8057358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057358 prefixEnd_8057358 := by exact prefixLift 8057358
  have htrace : WordTrace (prefixWord ++ tailWord_8057358) baseStart_8057358 baseEnd_8057358 := by
    simpa [prefixWord, tailWord_8057358, baseEnd_8057358] using wordTrace_append hprefix tailTrace_8057358
  have hstable : (prefixWord ++ tailWord_8057358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057358).length < 2 ^ (prefixWord ++ tailWord_8057358).sum := by decide
  have hdescent : baseEnd_8057358 < baseStart_8057358 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057386 : List Nat := [3, 1, 4, 1, 1, 3, 3, 2, 1, 2, 2]
def baseStart_8057386 : Nat := 118140960795 + 8057386 * 2 ^ 59
def prefixEnd_8057386 : Nat := 4983230072969 + 3 ^ 40 * 8057386 * 2
def baseEnd_8057386 : Nat := 4137311836807717673919763

theorem tailTrace_8057386 : CollatzResearch.WordTrace tailWord_8057386 prefixEnd_8057386 4137311836807717673919763 := by
  unfold tailWord_8057386
  simp only [CollatzResearch.WordTrace]
  refine ⟨73469252596868522204408003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195918006924982725878421341 73469252596868522204408003)
  ·
    refine ⟨110203878895302783306612005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73469252596868522204408003 110203878895302783306612005)
    ·
      refine ⟨20663227292869271869989751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110203878895302783306612005 20663227292869271869989751)
      ·
        refine ⟨30994840939303907804984627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20663227292869271869989751 30994840939303907804984627)
        ·
          refine ⟨46492261408955861707476941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30994840939303907804984627 46492261408955861707476941)
          ·
            refine ⟨17434598028358448140303853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46492261408955861707476941 17434598028358448140303853)
            ·
              refine ⟨6537974260634418052613945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17434598028358448140303853 6537974260634418052613945)
              ·
                refine ⟨4903480695475813539460459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6537974260634418052613945 4903480695475813539460459)
                ·
                  refine ⟨7355221043213720309190689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4903480695475813539460459 7355221043213720309190689)
                  ·
                    refine ⟨5516415782410290231893017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7355221043213720309190689 5516415782410290231893017)
                    ·
                      refine ⟨4137311836807717673919763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5516415782410290231893017 4137311836807717673919763)
                      ·
                        rfl

theorem cell23_8057386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_8057386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057386 prefixEnd_8057386 := by exact prefixLift 8057386
  have htrace : WordTrace (prefixWord ++ tailWord_8057386) baseStart_8057386 baseEnd_8057386 := by
    simpa [prefixWord, tailWord_8057386, baseEnd_8057386] using wordTrace_append hprefix tailTrace_8057386
  have hstable : (prefixWord ++ tailWord_8057386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057386).length < 2 ^ (prefixWord ++ tailWord_8057386).sum := by decide
  have hdescent : baseEnd_8057386 < baseStart_8057386 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057396 : List Nat := [2, 5, 1, 3, 1, 2, 2, 1, 2, 4]
def baseStart_8057396 : Nat := 118140960795 + 8057396 * 2 ^ 59
def prefixEnd_8057396 : Nat := 4983230072969 + 3 ^ 40 * 8057396 * 2
def baseEnd_8057396 : Nat := 1379105657204754211598239

theorem tailTrace_8057396 : CollatzResearch.WordTrace tailWord_8057396 prefixEnd_8057396 1379105657204754211598239 := by
  unfold tailWord_8057396
  simp only [CollatzResearch.WordTrace]
  refine ⟨146938687558718930262748021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195918250078291907016997361 146938687558718930262748021)
  ·
    refine ⟨13775501958629899712132627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146938687558718930262748021 13775501958629899712132627)
    ·
      refine ⟨20663252937944849568198941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13775501958629899712132627 20663252937944849568198941)
      ·
        refine ⟨7748719851729318588074603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20663252937944849568198941 7748719851729318588074603)
        ·
          refine ⟨11623079777593977882111905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7748719851729318588074603 11623079777593977882111905)
          ·
            refine ⟨8717309833195483411583929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11623079777593977882111905 8717309833195483411583929)
            ·
              refine ⟨6537982374896612558687947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8717309833195483411583929 6537982374896612558687947)
              ·
                refine ⟨9806973562344918838031921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6537982374896612558687947 9806973562344918838031921)
                ·
                  refine ⟨7355230171758689128523941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9806973562344918838031921 7355230171758689128523941)
                  ·
                    refine ⟨1379105657204754211598239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7355230171758689128523941 1379105657204754211598239)
                    ·
                      rfl

theorem cell23_8057396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_8057396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057396 prefixEnd_8057396 := by exact prefixLift 8057396
  have htrace : WordTrace (prefixWord ++ tailWord_8057396) baseStart_8057396 baseEnd_8057396 := by
    simpa [prefixWord, tailWord_8057396, baseEnd_8057396] using wordTrace_append hprefix tailTrace_8057396
  have hstable : (prefixWord ++ tailWord_8057396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057396).length < 2 ^ (prefixWord ++ tailWord_8057396).sum := by decide
  have hdescent : baseEnd_8057396 < baseStart_8057396 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057401 : List Nat := [1, 2, 1, 5, 1, 1, 2, 1, 1, 8]
def baseStart_8057401 : Nat := 118140960795 + 8057401 * 2 ^ 59
def prefixEnd_8057401 : Nat := 4983230072969 + 3 ^ 40 * 8057401 * 2
def baseEnd_8057401 : Nat := 1379106513005845038410731

theorem tailTrace_8057401 : CollatzResearch.WordTrace tailWord_8057401 prefixEnd_8057401 1379106513005845038410731 := by
  unfold tailWord_8057401
  simp only [CollatzResearch.WordTrace]
  refine ⟨293877557482419746379428057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195918371654946497586285371 293877557482419746379428057)
  ·
    refine ⟨220408168111814809784571043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293877557482419746379428057 220408168111814809784571043)
    ·
      refine ⟨330612252167722214676856565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220408168111814809784571043 330612252167722214676856565)
      ·
        refine ⟨30994898640723957625955303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 330612252167722214676856565 30994898640723957625955303)
        ·
          refine ⟨46492347961085936438932955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30994898640723957625955303 46492347961085936438932955)
          ·
            refine ⟨69738521941628904658399433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46492347961085936438932955 69738521941628904658399433)
            ·
              refine ⟨52303891456221678493799575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69738521941628904658399433 52303891456221678493799575)
              ·
                refine ⟨78455837184332517740699363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52303891456221678493799575 78455837184332517740699363)
                ·
                  refine ⟨117683755776498776611049045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78455837184332517740699363 117683755776498776611049045)
                  ·
                    refine ⟨1379106513005845038410731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 117683755776498776611049045 1379106513005845038410731)
                    ·
                      rfl

theorem cell23_8057401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 8].length) (baseStart_8057401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057401 prefixEnd_8057401 := by exact prefixLift 8057401
  have htrace : WordTrace (prefixWord ++ tailWord_8057401) baseStart_8057401 baseEnd_8057401 := by
    simpa [prefixWord, tailWord_8057401, baseEnd_8057401] using wordTrace_append hprefix tailTrace_8057401
  have hstable : (prefixWord ++ tailWord_8057401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057401).length < 2 ^ (prefixWord ++ tailWord_8057401).sum := by decide
  have hdescent : baseEnd_8057401 < baseStart_8057401 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057402 : List Nat := [3, 1, 1, 1, 3, 3, 4, 1, 2, 1, 3]
def baseStart_8057402 : Nat := 118140960795 + 8057402 * 2 ^ 59
def prefixEnd_8057402 : Nat := 4983230072969 + 3 ^ 40 * 8057402 * 2
def baseEnd_8057402 : Nat := 4137320052498189611319689

theorem tailTrace_8057402 : CollatzResearch.WordTrace tailWord_8057402 prefixEnd_8057402 4137320052498189611319689 := by
  unfold tailWord_8057402
  simp only [CollatzResearch.WordTrace]
  refine ⟨73469398488854030887553615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195918395970277415700142973 73469398488854030887553615)
  ·
    refine ⟨110204097733281046331330423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73469398488854030887553615 110204097733281046331330423)
    ·
      refine ⟨165306146599921569496995635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110204097733281046331330423 165306146599921569496995635)
      ·
        refine ⟨247959219899882354245493453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165306146599921569496995635 247959219899882354245493453)
        ·
          refine ⟨92984707462455882842060045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247959219899882354245493453 92984707462455882842060045)
          ·
            refine ⟨34869265298420956065772517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92984707462455882842060045 34869265298420956065772517)
            ·
              refine ⟨6537987243453929262332347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34869265298420956065772517 6537987243453929262332347)
              ·
                refine ⟨9806980865180893893498521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6537987243453929262332347 9806980865180893893498521)
                ·
                  refine ⟨7355235648885670420123891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9806980865180893893498521 7355235648885670420123891)
                  ·
                    refine ⟨11032853473328505630185837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7355235648885670420123891 11032853473328505630185837)
                    ·
                      refine ⟨4137320052498189611319689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11032853473328505630185837 4137320052498189611319689)
                      ·
                        rfl

theorem cell23_8057402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 2, 1, 3].length) (baseStart_8057402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057402 prefixEnd_8057402 := by exact prefixLift 8057402
  have htrace : WordTrace (prefixWord ++ tailWord_8057402) baseStart_8057402 baseEnd_8057402 := by
    simpa [prefixWord, tailWord_8057402, baseEnd_8057402] using wordTrace_append hprefix tailTrace_8057402
  have hstable : (prefixWord ++ tailWord_8057402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057402).length < 2 ^ (prefixWord ++ tailWord_8057402).sum := by decide
  have hdescent : baseEnd_8057402 < baseStart_8057402 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057406 : List Nat := [4, 2, 1, 4, 2, 1, 1, 2, 1, 2, 3]
def baseStart_8057406 : Nat := 118140960795 + 8057406 * 2 ^ 59
def prefixEnd_8057406 : Nat := 4983230072969 + 3 ^ 40 * 8057406 * 2
def baseEnd_8057406 : Nat := 4137322106420807595669671

theorem tailTrace_8057406 : CollatzResearch.WordTrace tailWord_8057406 prefixEnd_8057406 4137322106420807595669671 := by
  unfold tailWord_8057406
  simp only [CollatzResearch.WordTrace]
  refine ⟨36734717480925204029170009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195918493231601088155573381 36734717480925204029170009)
  ·
    refine ⟨27551038110693903021877507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36734717480925204029170009 27551038110693903021877507)
    ·
      refine ⟨41326557166040854532816261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27551038110693903021877507 41326557166040854532816261)
      ·
        refine ⟨7748729468632660224903049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41326557166040854532816261 7748729468632660224903049)
        ·
          refine ⟨5811547101474495168677287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7748729468632660224903049 5811547101474495168677287)
          ·
            refine ⟨8717320652211742753015931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5811547101474495168677287 8717320652211742753015931)
            ·
              refine ⟨13075980978317614129523897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8717320652211742753015931 13075980978317614129523897)
              ·
                refine ⟨9806985733738210597142923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13075980978317614129523897 9806985733738210597142923)
                ·
                  refine ⟨14710478600607315895714385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9806985733738210597142923 14710478600607315895714385)
                  ·
                    refine ⟨11032858950455486921785789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14710478600607315895714385 11032858950455486921785789)
                    ·
                      refine ⟨4137322106420807595669671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11032858950455486921785789 4137322106420807595669671)
                      ·
                        rfl

theorem cell23_8057406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_8057406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057406 prefixEnd_8057406 := by exact prefixLift 8057406
  have htrace : WordTrace (prefixWord ++ tailWord_8057406) baseStart_8057406 baseEnd_8057406 := by
    simpa [prefixWord, tailWord_8057406, baseEnd_8057406] using wordTrace_append hprefix tailTrace_8057406
  have hstable : (prefixWord ++ tailWord_8057406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057406).length < 2 ^ (prefixWord ++ tailWord_8057406).sum := by decide
  have hdescent : baseEnd_8057406 < baseStart_8057406 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057425 : List Nat := [1, 2, 2, 1, 3, 4, 1, 2, 1, 4, 2]
def baseStart_8057425 : Nat := 118140960795 + 8057425 * 2 ^ 59
def prefixEnd_8057425 : Nat := 4983230072969 + 3 ^ 40 * 8057425 * 2
def baseEnd_8057425 : Nat := 4137331862553243021332083

theorem tailTrace_8057425 : CollatzResearch.WordTrace tailWord_8057425 prefixEnd_8057425 4137331862553243021332083 := by
  unfold tailWord_8057425
  simp only [CollatzResearch.WordTrace]
  refine ⟨293878432834332798478301729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195918955222888532318867819 293878432834332798478301729)
  ·
    refine ⟨220408824625749598858726297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293878432834332798478301729 220408824625749598858726297)
    ·
      refine ⟨165306618469312199144044723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220408824625749598858726297 165306618469312199144044723)
      ·
        refine ⟨247959927703968298716067085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165306618469312199144044723 247959927703968298716067085)
        ·
          refine ⟨92984972888988112018525157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247959927703968298716067085 92984972888988112018525157)
          ·
            refine ⟨17434682416685271003473467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92984972888988112018525157 17434682416685271003473467)
            ·
              refine ⟨26152023625027906505210201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17434682416685271003473467 26152023625027906505210201)
              ·
                refine ⟨19614017718770929878907651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26152023625027906505210201 19614017718770929878907651)
                ·
                  refine ⟨29421026578156394818361477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19614017718770929878907651 29421026578156394818361477)
                  ·
                    refine ⟨5516442483404324028442777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29421026578156394818361477 5516442483404324028442777)
                    ·
                      refine ⟨4137331862553243021332083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5516442483404324028442777 4137331862553243021332083)
                      ·
                        rfl

theorem cell23_8057425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 4, 2].length) (baseStart_8057425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057425 prefixEnd_8057425 := by exact prefixLift 8057425
  have htrace : WordTrace (prefixWord ++ tailWord_8057425) baseStart_8057425 baseEnd_8057425 := by
    simpa [prefixWord, tailWord_8057425, baseEnd_8057425] using wordTrace_append hprefix tailTrace_8057425
  have hstable : (prefixWord ++ tailWord_8057425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057425).length < 2 ^ (prefixWord ++ tailWord_8057425).sum := by decide
  have hdescent : baseEnd_8057425 < baseStart_8057425 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057428 : List Nat := [2, 4, 1, 1, 1, 3, 2, 1, 2, 1, 5]
def baseStart_8057428 : Nat := 118140960795 + 8057428 * 2 ^ 59
def prefixEnd_8057428 : Nat := 4983230072969 + 3 ^ 40 * 8057428 * 2
def baseEnd_8057428 : Nat := 4137333402995206509594569

theorem tailTrace_8057428 : CollatzResearch.WordTrace tailWord_8057428 prefixEnd_8057428 4137333402995206509594569 := by
  unfold tailWord_8057428
  simp only [CollatzResearch.WordTrace]
  refine ⟨146939271126660964995330469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195919028168881286660440625 146939271126660964995330469)
  ·
    refine ⟨27551113336248930936624463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146939271126660964995330469 27551113336248930936624463)
    ·
      refine ⟨41326670004373396404936695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27551113336248930936624463 41326670004373396404936695)
      ·
        refine ⟨61990005006560094607405043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41326670004373396404936695 61990005006560094607405043)
        ·
          refine ⟨92985007509840141911107565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61990005006560094607405043 92985007509840141911107565)
          ·
            refine ⟨34869377816190053216665337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92985007509840141911107565 34869377816190053216665337)
            ·
              refine ⟨26152033362142539912499003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34869377816190053216665337 26152033362142539912499003)
              ·
                refine ⟨39228050043213809868748505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26152033362142539912499003 39228050043213809868748505)
                ·
                  refine ⟨29421037532410357401561379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39228050043213809868748505 29421037532410357401561379)
                  ·
                    refine ⟨44131556298615536102342069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29421037532410357401561379 44131556298615536102342069)
                    ·
                      refine ⟨4137333402995206509594569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44131556298615536102342069 4137333402995206509594569)
                      ·
                        rfl

theorem cell23_8057428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_8057428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057428 prefixEnd_8057428 := by exact prefixLift 8057428
  have htrace : WordTrace (prefixWord ++ tailWord_8057428) baseStart_8057428 baseEnd_8057428 := by
    simpa [prefixWord, tailWord_8057428, baseEnd_8057428] using wordTrace_append hprefix tailTrace_8057428
  have hstable : (prefixWord ++ tailWord_8057428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057428).length < 2 ^ (prefixWord ++ tailWord_8057428).sum := by decide
  have hdescent : baseEnd_8057428 < baseStart_8057428 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057471 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 5]
def baseStart_8057471 : Nat := 118140960795 + 8057471 * 2 ^ 59
def prefixEnd_8057471 : Nat := 4983230072969 + 3 ^ 40 * 8057471 * 2
def baseEnd_8057471 : Nat := 4137355482663349841356871

theorem tailTrace_8057471 : CollatzResearch.WordTrace tailWord_8057471 prefixEnd_8057471 4137355482663349841356871 := by
  unfold tailWord_8057471
  simp only [CollatzResearch.WordTrace]
  refine ⟨293880110592166148334476267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195920073728110765556317511 293880110592166148334476267)
  ·
    refine ⟨440820165888249222501714401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293880110592166148334476267 440820165888249222501714401)
    ·
      refine ⟨330615124416186916876285801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440820165888249222501714401 330615124416186916876285801)
      ·
        refine ⟨247961343312140187657214351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330615124416186916876285801 247961343312140187657214351)
        ·
          refine ⟨371942014968210281485821527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247961343312140187657214351 371942014968210281485821527)
          ·
            refine ⟨557913022452315422228732291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371942014968210281485821527 557913022452315422228732291)
            ·
              refine ⟨836869533678473133343098437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557913022452315422228732291 836869533678473133343098437)
              ·
                refine ⟨156913037564713712501830957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 836869533678473133343098437 156913037564713712501830957)
                ·
                  refine ⟨58842389086767642188186609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156913037564713712501830957 58842389086767642188186609)
                  ·
                    refine ⟨44131791815075731641139957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58842389086767642188186609 44131791815075731641139957)
                    ·
                      refine ⟨4137355482663349841356871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44131791815075731641139957 4137355482663349841356871)
                      ·
                        rfl

theorem cell23_8057471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_8057471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057471 prefixEnd_8057471 := by exact prefixLift 8057471
  have htrace : WordTrace (prefixWord ++ tailWord_8057471) baseStart_8057471 baseEnd_8057471 := by
    simpa [prefixWord, tailWord_8057471, baseEnd_8057471] using wordTrace_append hprefix tailTrace_8057471
  have hstable : (prefixWord ++ tailWord_8057471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057471).length < 2 ^ (prefixWord ++ tailWord_8057471).sum := by decide
  have hdescent : baseEnd_8057471 < baseStart_8057471 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057482 : List Nat := [3, 1, 2, 3, 3, 1, 2, 3, 5]
def baseStart_8057482 : Nat := 118140960795 + 8057482 * 2 ^ 59
def prefixEnd_8057482 : Nat := 4983230072969 + 3 ^ 40 * 8057482 * 2
def baseEnd_8057482 : Nat := 459706792327838810924369

theorem tailTrace_8057482 : CollatzResearch.WordTrace tailWord_8057482 prefixEnd_8057482 459706792327838810924369 := by
  unfold tailWord_8057482
  simp only [CollatzResearch.WordTrace]
  refine ⟨73470127948781574303281675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195920341196750864808751133 73470127948781574303281675)
  ·
    refine ⟨110205191923172361454922513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73470127948781574303281675 110205191923172361454922513)
    ·
      refine ⟨82653893942379271091191885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110205191923172361454922513 82653893942379271091191885)
      ·
        refine ⟨30995210228392226659196957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82653893942379271091191885 30995210228392226659196957)
        ·
          refine ⟨11623203835647084997198859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30995210228392226659196957 11623203835647084997198859)
          ·
            refine ⟨17434805753470627495798289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11623203835647084997198859 17434805753470627495798289)
            ·
              refine ⟨13076104315102970621848717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17434805753470627495798289 13076104315102970621848717)
              ·
                refine ⟨4903539118163613983193269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13076104315102970621848717 4903539118163613983193269)
                ·
                  refine ⟨459706792327838810924369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4903539118163613983193269 459706792327838810924369)
                  ·
                    rfl

theorem cell23_8057482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 3, 5].length) (baseStart_8057482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057482 prefixEnd_8057482 := by exact prefixLift 8057482
  have htrace : WordTrace (prefixWord ++ tailWord_8057482) baseStart_8057482 baseEnd_8057482 := by
    simpa [prefixWord, tailWord_8057482, baseEnd_8057482] using wordTrace_append hprefix tailTrace_8057482
  have hstable : (prefixWord ++ tailWord_8057482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057482).length < 2 ^ (prefixWord ++ tailWord_8057482).sum := by decide
  have hdescent : baseEnd_8057482 < baseStart_8057482 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057531 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 9]
def baseStart_8057531 : Nat := 118140960795 + 8057531 * 2 ^ 59
def prefixEnd_8057531 : Nat := 4983230072969 + 3 ^ 40 * 8057531 * 2
def baseEnd_8057531 : Nat := 4137386291502619606606595

theorem tailTrace_8057531 : CollatzResearch.WordTrace tailWord_8057531 prefixEnd_8057531 4137386291502619606606595 := by
  unfold tailWord_8057531
  simp only [CollatzResearch.WordTrace]
  refine ⟨293882298971948778581660447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195921532647965852387773631 293882298971948778581660447)
  ·
    refine ⟨440823448457923167872490671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293882298971948778581660447 440823448457923167872490671)
    ·
      refine ⟨661235172686884751808736007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440823448457923167872490671 661235172686884751808736007)
      ·
        refine ⟨991852759030327127713104011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661235172686884751808736007 991852759030327127713104011)
        ·
          refine ⟨1487779138545490691569656017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 991852759030327127713104011 1487779138545490691569656017)
          ·
            refine ⟨1115834353909118018677242013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1487779138545490691569656017 1115834353909118018677242013)
            ·
              refine ⟨418437882715919257003965755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1115834353909118018677242013 418437882715919257003965755)
              ·
                refine ⟨627656824073878885505948633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418437882715919257003965755 627656824073878885505948633)
                ·
                  refine ⟨470742618055409164129461475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 627656824073878885505948633 470742618055409164129461475)
                  ·
                    refine ⟨706113927083113746194192213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 470742618055409164129461475 706113927083113746194192213)
                    ·
                      refine ⟨4137386291502619606606595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 706113927083113746194192213 4137386291502619606606595)
                      ·
                        rfl

theorem cell23_8057531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 9].length) (baseStart_8057531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057531 prefixEnd_8057531 := by exact prefixLift 8057531
  have htrace : WordTrace (prefixWord ++ tailWord_8057531) baseStart_8057531 baseEnd_8057531 := by
    simpa [prefixWord, tailWord_8057531, baseEnd_8057531] using wordTrace_append hprefix tailTrace_8057531
  have hstable : (prefixWord ++ tailWord_8057531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057531).length < 2 ^ (prefixWord ++ tailWord_8057531).sum := by decide
  have hdescent : baseEnd_8057531 < baseStart_8057531 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057549 : List Nat := [1, 6, 2, 1, 2, 1, 1, 2, 2, 1, 4]
def baseStart_8057549 : Nat := 118140960795 + 8057549 * 2 ^ 59
def prefixEnd_8057549 : Nat := 4983230072969 + 3 ^ 40 * 8057549 * 2
def baseEnd_8057549 : Nat := 4137395534154400536181513

theorem tailTrace_8057549 : CollatzResearch.WordTrace tailWord_8057549 prefixEnd_8057549 4137395534154400536181513 := by
  unfold tailWord_8057549
  simp only [CollatzResearch.WordTrace]
  refine ⟨293882955485883567655815701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195921970323922378437210467 293882955485883567655815701)
  ·
    refine ⟨13775763538400792233866361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 293882955485883567655815701 13775763538400792233866361)
    ·
      refine ⟨10331822653800594175399771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13775763538400792233866361 10331822653800594175399771)
      ·
        refine ⟨15497733980700891263099657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10331822653800594175399771 15497733980700891263099657)
        ·
          refine ⟨11623300485525668447324743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15497733980700891263099657 11623300485525668447324743)
          ·
            refine ⟨17434950728288502670987115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11623300485525668447324743 17434950728288502670987115)
            ·
              refine ⟨26152426092432754006480673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17434950728288502670987115 26152426092432754006480673)
              ·
                refine ⟨19614319569324565504860505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26152426092432754006480673 19614319569324565504860505)
                ·
                  refine ⟨14710739676993424128645379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19614319569324565504860505 14710739676993424128645379)
                  ·
                    refine ⟨22066109515490136192968069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14710739676993424128645379 22066109515490136192968069)
                    ·
                      refine ⟨4137395534154400536181513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22066109515490136192968069 4137395534154400536181513)
                      ·
                        rfl

theorem cell23_8057549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_8057549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057549 prefixEnd_8057549 := by exact prefixLift 8057549
  have htrace : WordTrace (prefixWord ++ tailWord_8057549) baseStart_8057549 baseEnd_8057549 := by
    simpa [prefixWord, tailWord_8057549, baseEnd_8057549] using wordTrace_append hprefix tailTrace_8057549
  have hstable : (prefixWord ++ tailWord_8057549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057549).length < 2 ^ (prefixWord ++ tailWord_8057549).sum := by decide
  have hdescent : baseEnd_8057549 < baseStart_8057549 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057559 : List Nat := [1, 1, 3, 2, 1, 5, 3, 2, 1, 4]
def baseStart_8057559 : Nat := 118140960795 + 8057559 * 2 ^ 59
def prefixEnd_8057559 : Nat := 4983230072969 + 3 ^ 40 * 8057559 * 2
def baseEnd_8057559 : Nat := 1379133556320315165685489

theorem tailTrace_8057559 : CollatzResearch.WordTrace tailWord_8057559 prefixEnd_8057559 1379133556320315165685489 := by
  unfold tailWord_8057559
  simp only [CollatzResearch.WordTrace]
  refine ⟨293883320215847339363679731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195922213477231559575786487 293883320215847339363679731)
  ·
    refine ⟨440824980323771009045519597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293883320215847339363679731 440824980323771009045519597)
    ·
      refine ⟨165309367621414128392069849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 440824980323771009045519597 165309367621414128392069849)
      ·
        refine ⟨123982025716060596294052387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165309367621414128392069849 123982025716060596294052387)
        ·
          refine ⟨185973038574090894441078581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123982025716060596294052387 185973038574090894441078581)
          ·
            refine ⟨17434972366321021353851117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 185973038574090894441078581 17434972366321021353851117)
            ·
              refine ⟨6538114637370383007694169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17434972366321021353851117 6538114637370383007694169)
              ·
                refine ⟨4903585978027787255770627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6538114637370383007694169 4903585978027787255770627)
                ·
                  refine ⟨7355378967041680883655941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4903585978027787255770627 7355378967041680883655941)
                  ·
                    refine ⟨1379133556320315165685489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7355378967041680883655941 1379133556320315165685489)
                    ·
                      rfl

theorem cell23_8057559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 2, 1, 4].length) (baseStart_8057559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057559 prefixEnd_8057559 := by exact prefixLift 8057559
  have htrace : WordTrace (prefixWord ++ tailWord_8057559) baseStart_8057559 baseEnd_8057559 := by
    simpa [prefixWord, tailWord_8057559, baseEnd_8057559] using wordTrace_append hprefix tailTrace_8057559
  have hstable : (prefixWord ++ tailWord_8057559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057559).length < 2 ^ (prefixWord ++ tailWord_8057559).sum := by decide
  have hdescent : baseEnd_8057559 < baseStart_8057559 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057568 : List Nat := [2, 1, 1, 3, 1, 2, 1, 4, 3, 5]
def baseStart_8057568 : Nat := 118140960795 + 8057568 * 2 ^ 59
def prefixEnd_8057568 : Nat := 4983230072969 + 3 ^ 40 * 8057568 * 2
def baseEnd_8057568 : Nat := 1379135096762278653947975

theorem tailTrace_8057568 : CollatzResearch.WordTrace tailWord_8057568 prefixEnd_8057568 1379135096762278653947975 := by
  unfold tailWord_8057568
  simp only [CollatzResearch.WordTrace]
  refine ⟨146941824236407366950378679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195922432315209822600504905 146941824236407366950378679)
  ·
    refine ⟨220412736354611050425568019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146941824236407366950378679 220412736354611050425568019)
    ·
      refine ⟨330619104531916575638352029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220412736354611050425568019 330619104531916575638352029)
      ·
        refine ⟨123982164199468715864382011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330619104531916575638352029 123982164199468715864382011)
        ·
          refine ⟨185973246299203073796573017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123982164199468715864382011 185973246299203073796573017)
          ·
            refine ⟨139479934724402305347429763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185973246299203073796573017 139479934724402305347429763)
            ·
              refine ⟨209219902086603458021144645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139479934724402305347429763 209219902086603458021144645)
              ·
                refine ⟨39228731641238148378964621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 209219902086603458021144645 39228731641238148378964621)
                ·
                  refine ⟨14710774365464305642111733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39228731641238148378964621 14710774365464305642111733)
                  ·
                    refine ⟨1379135096762278653947975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14710774365464305642111733 1379135096762278653947975)
                    ·
                      rfl

theorem cell23_8057568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 3, 5].length) (baseStart_8057568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057568 prefixEnd_8057568 := by exact prefixLift 8057568
  have htrace : WordTrace (prefixWord ++ tailWord_8057568) baseStart_8057568 baseEnd_8057568 := by
    simpa [prefixWord, tailWord_8057568, baseEnd_8057568] using wordTrace_append hprefix tailTrace_8057568
  have hstable : (prefixWord ++ tailWord_8057568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057568).length < 2 ^ (prefixWord ++ tailWord_8057568).sum := by decide
  have hdescent : baseEnd_8057568 < baseStart_8057568 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057572 : List Nat := [2, 3, 1, 1, 1, 6, 2, 1, 6]
def baseStart_8057572 : Nat := 118140960795 + 8057572 * 2 ^ 59
def prefixEnd_8057572 : Nat := 4983230072969 + 3 ^ 40 * 8057572 * 2
def baseEnd_8057572 : Nat := 459711927134383771799323

theorem tailTrace_8057572 : CollatzResearch.WordTrace tailWord_8057572 prefixEnd_8057572 459711927134383771799323 := by
  unfold tailWord_8057572
  simp only [CollatzResearch.WordTrace]
  refine ⟨146941897182400121291951485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195922529576533495055935313 146941897182400121291951485)
  ·
    refine ⟨55103211443400045484481807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146941897182400121291951485 55103211443400045484481807)
    ·
      refine ⟨82654817165100068226722711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55103211443400045484481807 82654817165100068226722711)
      ·
        refine ⟨123982225747650102340084067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82654817165100068226722711 123982225747650102340084067)
        ·
          refine ⟨185973338621475153510126101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123982225747650102340084067 185973338621475153510126101)
          ·
            refine ⟨8717500247881647820787161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 185973338621475153510126101 8717500247881647820787161)
            ·
              refine ⟨6538125185911235865590371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8717500247881647820787161 6538125185911235865590371)
              ·
                refine ⟨9807187778866853798385557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6538125185911235865590371 9807187778866853798385557)
                ·
                  refine ⟨459711927134383771799323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9807187778866853798385557 459711927134383771799323)
                  ·
                    rfl

theorem cell23_8057572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 6].length) (baseStart_8057572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057572 prefixEnd_8057572 := by exact prefixLift 8057572
  have htrace : WordTrace (prefixWord ++ tailWord_8057572) baseStart_8057572 baseEnd_8057572 := by
    simpa [prefixWord, tailWord_8057572, baseEnd_8057572] using wordTrace_append hprefix tailTrace_8057572
  have hstable : (prefixWord ++ tailWord_8057572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057572).length < 2 ^ (prefixWord ++ tailWord_8057572).sum := by decide
  have hdescent : baseEnd_8057572 < baseStart_8057572 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057592 : List Nat := [2, 1, 2, 1, 1, 2, 6, 1, 2, 3, 2]
def baseStart_8057592 : Nat := 118140960795 + 8057592 * 2 ^ 59
def prefixEnd_8057592 : Nat := 4983230072969 + 3 ^ 40 * 8057592 * 2
def baseEnd_8057592 : Nat := 4137417613822543867943815

theorem tailTrace_8057592 : CollatzResearch.WordTrace tailWord_8057592 prefixEnd_8057592 4137417613822543867943815 := by
  unfold tailWord_8057592
  simp only [CollatzResearch.WordTrace]
  refine ⟨146942261912363892999815515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195923015883151857333087353 146942261912363892999815515)
  ·
    refine ⟨220413392868545839499723273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146942261912363892999815515 220413392868545839499723273)
    ·
      refine ⟨165310044651409379624792455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220413392868545839499723273 165310044651409379624792455)
      ·
        refine ⟨247965066977114069437188683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165310044651409379624792455 247965066977114069437188683)
        ·
          refine ⟨371947600465671104155783025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247965066977114069437188683 371947600465671104155783025)
          ·
            refine ⟨278960700349253328116837269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371947600465671104155783025 278960700349253328116837269)
            ·
              refine ⟨13076282828871249755476747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 278960700349253328116837269 13076282828871249755476747)
              ·
                refine ⟨19614424243306874633215121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13076282828871249755476747 19614424243306874633215121)
                ·
                  refine ⟨14710818182480155974911341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19614424243306874633215121 14710818182480155974911341)
                  ·
                    refine ⟨5516556818430058490591753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14710818182480155974911341 5516556818430058490591753)
                    ·
                      refine ⟨4137417613822543867943815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5516556818430058490591753 4137417613822543867943815)
                      ·
                        rfl

theorem cell23_8057592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 2, 3, 2].length) (baseStart_8057592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057592 prefixEnd_8057592 := by exact prefixLift 8057592
  have htrace : WordTrace (prefixWord ++ tailWord_8057592) baseStart_8057592 baseEnd_8057592 := by
    simpa [prefixWord, tailWord_8057592, baseEnd_8057592] using wordTrace_append hprefix tailTrace_8057592
  have hstable : (prefixWord ++ tailWord_8057592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057592).length < 2 ^ (prefixWord ++ tailWord_8057592).sum := by decide
  have hdescent : baseEnd_8057592 < baseStart_8057592 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057605 : List Nat := [1, 3, 1, 1, 2, 1, 1, 7, 1, 1, 4]
def baseStart_8057605 : Nat := 118140960795 + 8057605 * 2 ^ 59
def prefixEnd_8057605 : Nat := 4983230072969 + 3 ^ 40 * 8057605 * 2
def baseEnd_8057605 : Nat := 4137424289071052317081255

theorem tailTrace_8057605 : CollatzResearch.WordTrace tailWord_8057605 prefixEnd_8057605 4137424289071052317081255 := by
  unfold tailWord_8057605
  simp only [CollatzResearch.WordTrace]
  refine ⟨293884997973680689219854269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195923331982453792813236179 293884997973680689219854269)
  ·
    refine ⟨110206874240130258457445351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293884997973680689219854269 110206874240130258457445351)
    ·
      refine ⟨165310311360195387686168027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110206874240130258457445351 165310311360195387686168027)
      ·
        refine ⟨247965467040293081529252041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165310311360195387686168027 247965467040293081529252041)
        ·
          refine ⟨185974100280219811146939031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247965467040293081529252041 185974100280219811146939031)
          ·
            refine ⟨278961150420329716720408547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185974100280219811146939031 278961150420329716720408547)
            ·
              refine ⟨418441725630494575080612821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278961150420329716720408547 418441725630494575080612821)
              ·
                refine ⟨9807227944464716603451863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 418441725630494575080612821 9807227944464716603451863)
                ·
                  refine ⟨14710841916697074905177795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9807227944464716603451863 14710841916697074905177795)
                  ·
                    refine ⟨22066262875045612357766693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14710841916697074905177795 22066262875045612357766693)
                    ·
                      refine ⟨4137424289071052317081255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22066262875045612357766693 4137424289071052317081255)
                      ·
                        rfl

theorem cell23_8057605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 1, 4].length) (baseStart_8057605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057605 prefixEnd_8057605 := by exact prefixLift 8057605
  have htrace : WordTrace (prefixWord ++ tailWord_8057605) baseStart_8057605 baseEnd_8057605 := by
    simpa [prefixWord, tailWord_8057605, baseEnd_8057605] using wordTrace_append hprefix tailTrace_8057605
  have hstable : (prefixWord ++ tailWord_8057605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057605).length < 2 ^ (prefixWord ++ tailWord_8057605).sum := by decide
  have hdescent : baseEnd_8057605 < baseStart_8057605 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057632 : List Nat := [2, 1, 1, 5, 1, 2, 2, 3, 2, 4]
def baseStart_8057632 : Nat := 118140960795 + 8057632 * 2 ^ 59
def prefixEnd_8057632 : Nat := 4983230072969 + 3 ^ 40 * 8057632 * 2
def baseEnd_8057632 : Nat := 1379146051016241237147877

theorem tailTrace_8057632 : CollatzResearch.WordTrace tailWord_8057632 prefixEnd_8057632 1379146051016241237147877 := by
  unfold tailWord_8057632
  simp only [CollatzResearch.WordTrace]
  refine ⟨146942991372291436415543575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195923988496388581887391433 146942991372291436415543575)
  ·
    refine ⟨220414487058437154623315363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146942991372291436415543575 220414487058437154623315363)
    ·
      refine ⟨330621730587655731934973045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220414487058437154623315363 330621730587655731934973045)
      ·
        refine ⟨30995787242592724868903723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 330621730587655731934973045 30995787242592724868903723)
        ·
          refine ⟨46493680863889087303355585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30995787242592724868903723 46493680863889087303355585)
          ·
            refine ⟨34870260647916815477516689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46493680863889087303355585 34870260647916815477516689)
            ·
              refine ⟨26152695485937611608137517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34870260647916815477516689 26152695485937611608137517)
              ·
                refine ⟨9807260807226604353051569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26152695485937611608137517 9807260807226604353051569)
                ·
                  refine ⟨7355445605419953264788677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9807260807226604353051569 7355445605419953264788677)
                  ·
                    refine ⟨1379146051016241237147877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7355445605419953264788677 1379146051016241237147877)
                    ·
                      rfl

theorem cell23_8057632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 2, 4].length) (baseStart_8057632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057632 prefixEnd_8057632 := by exact prefixLift 8057632
  have htrace : WordTrace (prefixWord ++ tailWord_8057632) baseStart_8057632 baseEnd_8057632 := by
    simpa [prefixWord, tailWord_8057632, baseEnd_8057632] using wordTrace_append hprefix tailTrace_8057632
  have hstable : (prefixWord ++ tailWord_8057632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057632).length < 2 ^ (prefixWord ++ tailWord_8057632).sum := by decide
  have hdescent : baseEnd_8057632 < baseStart_8057632 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057655 : List Nat := [1, 1, 3, 1, 2, 1, 3, 4, 1, 3, 3]
def baseStart_8057655 : Nat := 118140960795 + 8057655 * 2 ^ 59
def prefixEnd_8057655 : Nat := 4983230072969 + 3 ^ 40 * 8057655 * 2
def baseEnd_8057655 : Nat := 4137449963103777121456025

theorem tailTrace_8057655 : CollatzResearch.WordTrace tailWord_8057655 prefixEnd_8057655 4137449963103777121456025 := by
  unfold tailWord_8057655
  simp only [CollatzResearch.WordTrace]
  refine ⟨293886821623499547759174419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195924547748999698506116279 293886821623499547759174419)
  ·
    refine ⟨440830232435249321638761629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293886821623499547759174419 440830232435249321638761629)
    ·
      refine ⟨165311337163218495614535611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 440830232435249321638761629 165311337163218495614535611)
      ·
        refine ⟨247967005744827743421803417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165311337163218495614535611 247967005744827743421803417)
        ·
          refine ⟨185975254308620807566352563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247967005744827743421803417 185975254308620807566352563)
          ·
            refine ⟨278962881462931211349528845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185975254308620807566352563 278962881462931211349528845)
            ·
              refine ⟨104611080548599204256073317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 278962881462931211349528845 104611080548599204256073317)
              ·
                refine ⟨19614577602862350798013747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104611080548599204256073317 19614577602862350798013747)
                ·
                  refine ⟨29421866404293526197020621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19614577602862350798013747 29421866404293526197020621)
                  ·
                    refine ⟨11033199901610072323882733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29421866404293526197020621 11033199901610072323882733)
                    ·
                      refine ⟨4137449963103777121456025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11033199901610072323882733 4137449963103777121456025)
                      ·
                        rfl

theorem cell23_8057655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 3, 3].length) (baseStart_8057655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057655 prefixEnd_8057655 := by exact prefixLift 8057655
  have htrace : WordTrace (prefixWord ++ tailWord_8057655) baseStart_8057655 baseEnd_8057655 := by
    simpa [prefixWord, tailWord_8057655, baseEnd_8057655] using wordTrace_append hprefix tailTrace_8057655
  have hstable : (prefixWord ++ tailWord_8057655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057655).length < 2 ^ (prefixWord ++ tailWord_8057655).sum := by decide
  have hdescent : baseEnd_8057655 < baseStart_8057655 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057656 : List Nat := [2, 1, 2, 1, 3, 2, 4, 3, 1, 2, 2]
def baseStart_8057656 : Nat := 118140960795 + 8057656 * 2 ^ 59
def prefixEnd_8057656 : Nat := 4983230072969 + 3 ^ 40 * 8057656 * 2
def baseEnd_8057656 : Nat := 4137450476584431617543521

theorem tailTrace_8057656 : CollatzResearch.WordTrace tailWord_8057656 prefixEnd_8057656 4137450476584431617543521 := by
  unfold tailWord_8057656
  simp only [CollatzResearch.WordTrace]
  refine ⟨146943429048247962464980411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195924572064330616619973881 146943429048247962464980411)
  ·
    refine ⟨220415143572371943697470617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146943429048247962464980411 220415143572371943697470617)
    ·
      refine ⟨165311357679278957773102963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220415143572371943697470617 165311357679278957773102963)
      ·
        refine ⟨247967036518918436659654445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165311357679278957773102963 247967036518918436659654445)
        ·
          refine ⟨92987638694594413747370417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247967036518918436659654445 92987638694594413747370417)
          ·
            refine ⟨69740729020945810310527813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92987638694594413747370417 69740729020945810310527813)
            ·
              refine ⟨13076386691427339433223965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69740729020945810310527813 13076386691427339433223965)
              ·
                refine ⟨4903645009285252287458987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13076386691427339433223965 4903645009285252287458987)
                ·
                  refine ⟨7355467513927878431188481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4903645009285252287458987 7355467513927878431188481)
                  ·
                    refine ⟨5516600635445908823391361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7355467513927878431188481 5516600635445908823391361)
                    ·
                      refine ⟨4137450476584431617543521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5516600635445908823391361 4137450476584431617543521)
                      ·
                        rfl

theorem cell23_8057656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 3, 1, 2, 2].length) (baseStart_8057656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057656 prefixEnd_8057656 := by exact prefixLift 8057656
  have htrace : WordTrace (prefixWord ++ tailWord_8057656) baseStart_8057656 baseEnd_8057656 := by
    simpa [prefixWord, tailWord_8057656, baseEnd_8057656] using wordTrace_append hprefix tailTrace_8057656
  have hstable : (prefixWord ++ tailWord_8057656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057656).length < 2 ^ (prefixWord ++ tailWord_8057656).sum := by decide
  have hdescent : baseEnd_8057656 < baseStart_8057656 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057672 : List Nat := [2, 1, 3, 1, 1, 3, 3, 1, 4, 1, 3]
def baseStart_8057672 : Nat := 118140960795 + 8057672 * 2 ^ 59
def prefixEnd_8057672 : Nat := 4983230072969 + 3 ^ 40 * 8057672 * 2
def baseEnd_8057672 : Nat := 4137458692274903554943447

theorem tailTrace_8057672 : CollatzResearch.WordTrace tailWord_8057672 prefixEnd_8057672 4137458692274903554943447 := by
  unfold tailWord_8057672
  simp only [CollatzResearch.WordTrace]
  refine ⟨146943720832218979831271635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195924961109625306441695513 146943720832218979831271635)
  ·
    refine ⟨220415581248328469746907453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146943720832218979831271635 220415581248328469746907453)
    ·
      refine ⟨82655842968123176155090295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220415581248328469746907453 82655842968123176155090295)
      ·
        refine ⟨123983764452184764232635443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82655842968123176155090295 123983764452184764232635443)
        ·
          refine ⟨185975646678277146348953165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123983764452184764232635443 185975646678277146348953165)
          ·
            refine ⟨69740867504353929880857437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185975646678277146348953165 69740867504353929880857437)
            ·
              refine ⟨26152825314132723705321539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69740867504353929880857437 26152825314132723705321539)
              ·
                refine ⟨39229237971199085557982309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26152825314132723705321539 39229237971199085557982309)
                ·
                  refine ⟨7355482119599828542121683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39229237971199085557982309 7355482119599828542121683)
                  ·
                    refine ⟨11033223179399742813182525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7355482119599828542121683 11033223179399742813182525)
                    ·
                      refine ⟨4137458692274903554943447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11033223179399742813182525 4137458692274903554943447)
                      ·
                        rfl

theorem cell23_8057672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 4, 1, 3].length) (baseStart_8057672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057672 prefixEnd_8057672 := by exact prefixLift 8057672
  have htrace : WordTrace (prefixWord ++ tailWord_8057672) baseStart_8057672 baseEnd_8057672 := by
    simpa [prefixWord, tailWord_8057672, baseEnd_8057672] using wordTrace_append hprefix tailTrace_8057672
  have hstable : (prefixWord ++ tailWord_8057672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057672).length < 2 ^ (prefixWord ++ tailWord_8057672).sum := by decide
  have hdescent : baseEnd_8057672 < baseStart_8057672 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057699 : List Nat := [1, 1, 1, 5, 3, 1, 1, 4, 1, 3, 2]
def baseStart_8057699 : Nat := 118140960795 + 8057699 * 2 ^ 59
def prefixEnd_8057699 : Nat := 4983230072969 + 3 ^ 40 * 8057699 * 2
def baseEnd_8057699 : Nat := 4137472556252574949305823

theorem tailTrace_8057699 : CollatzResearch.WordTrace tailWord_8057699 prefixEnd_8057699 4137472556252574949305823 := by
  unfold tailWord_8057699
  simp only [CollatzResearch.WordTrace]
  refine ⟨293888426435340143273776151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195925617623560095515850767 293888426435340143273776151)
  ·
    refine ⟨440832639653010214910664227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293888426435340143273776151 440832639653010214910664227)
    ·
      refine ⟨661248959479515322365996341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440832639653010214910664227 661248959479515322365996341)
      ·
        refine ⟨61992089951204561471812157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 661248959479515322365996341 61992089951204561471812157)
        ·
          refine ⟨23247033731701710551929559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61992089951204561471812157 23247033731701710551929559)
          ·
            refine ⟨34870550597552565827894339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23247033731701710551929559 34870550597552565827894339)
            ·
              refine ⟨52305825896328848741841509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34870550597552565827894339 52305825896328848741841509)
              ·
                refine ⟨9807342355561659139095283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52305825896328848741841509 9807342355561659139095283)
                ·
                  refine ⟨14711013533342488708642925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9807342355561659139095283 14711013533342488708642925)
                  ·
                    refine ⟨5516630075003433265741097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14711013533342488708642925 5516630075003433265741097)
                    ·
                      refine ⟨4137472556252574949305823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5516630075003433265741097 4137472556252574949305823)
                      ·
                        rfl

theorem cell23_8057699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_8057699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057699 prefixEnd_8057699 := by exact prefixLift 8057699
  have htrace : WordTrace (prefixWord ++ tailWord_8057699) baseStart_8057699 baseEnd_8057699 := by
    simpa [prefixWord, tailWord_8057699, baseEnd_8057699] using wordTrace_append hprefix tailTrace_8057699
  have hstable : (prefixWord ++ tailWord_8057699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057699).length < 2 ^ (prefixWord ++ tailWord_8057699).sum := by decide
  have hdescent : baseEnd_8057699 < baseStart_8057699 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057712 : List Nat := [2, 1, 1, 1, 4, 1, 2, 4, 1, 4, 2]
def baseStart_8057712 : Nat := 118140960795 + 8057712 * 2 ^ 59
def prefixEnd_8057712 : Nat := 4983230072969 + 3 ^ 40 * 8057712 * 2
def baseEnd_8057712 : Nat := 4137479231501083398443263

theorem tailTrace_8057712 : CollatzResearch.WordTrace tailWord_8057712 prefixEnd_8057712 4137479231501083398443263 := by
  unfold tailWord_8057712
  simp only [CollatzResearch.WordTrace]
  refine ⟨146944450292146523246999695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195925933722862030995999593 146944450292146523246999695)
  ·
    refine ⟨220416675438219784870499543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146944450292146523246999695 220416675438219784870499543)
    ·
      refine ⟨330625013157329677305749315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220416675438219784870499543 330625013157329677305749315)
      ·
        refine ⟨495937519735994515958623973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330625013157329677305749315 495937519735994515958623973)
        ·
          refine ⟨92988284950498971742241995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 495937519735994515958623973 92988284950498971742241995)
          ·
            refine ⟨139482427425748457613362993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92988284950498971742241995 139482427425748457613362993)
            ·
              refine ⟨104611820569311343210022245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139482427425748457613362993 104611820569311343210022245)
              ·
                refine ⟨19614716356745876851879171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104611820569311343210022245 19614716356745876851879171)
                ·
                  refine ⟨29422074535118815277818757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19614716356745876851879171 29422074535118815277818757)
                  ·
                    refine ⟨5516638975334777864591017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29422074535118815277818757 5516638975334777864591017)
                    ·
                      refine ⟨4137479231501083398443263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5516638975334777864591017 4137479231501083398443263)
                      ·
                        rfl

theorem cell23_8057712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 1, 4, 2].length) (baseStart_8057712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057712 prefixEnd_8057712 := by exact prefixLift 8057712
  have htrace : WordTrace (prefixWord ++ tailWord_8057712) baseStart_8057712 baseEnd_8057712 := by
    simpa [prefixWord, tailWord_8057712, baseEnd_8057712] using wordTrace_append hprefix tailTrace_8057712
  have hstable : (prefixWord ++ tailWord_8057712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057712).length < 2 ^ (prefixWord ++ tailWord_8057712).sum := by decide
  have hdescent : baseEnd_8057712 < baseStart_8057712 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057725 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 4, 2, 4]
def baseStart_8057725 : Nat := 118140960795 + 8057725 * 2 ^ 59
def prefixEnd_8057725 : Nat := 4983230072969 + 3 ^ 40 * 8057725 * 2
def baseEnd_8057725 : Nat := 4137485906749591847580703

theorem tailTrace_8057725 : CollatzResearch.WordTrace tailWord_8057725 prefixEnd_8057725 4137485906749591847580703 := by
  unfold tailWord_8057725
  simp only [CollatzResearch.WordTrace]
  refine ⟨293889374733245949714222629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195926249822163966476148419 293889374733245949714222629)
  ·
    refine ⟨55104257762483615571416743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293889374733245949714222629 55104257762483615571416743)
    ·
      refine ⟨82656386643725423357125115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55104257762483615571416743 82656386643725423357125115)
      ·
        refine ⟨123984579965588135035687673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82656386643725423357125115 123984579965588135035687673)
        ·
          refine ⟨92988434974191101276765755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123984579965588135035687673 92988434974191101276765755)
          ·
            refine ⟨139482652461286651915148633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92988434974191101276765755 139482652461286651915148633)
            ·
              refine ⟨104611989345964988936361475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139482652461286651915148633 104611989345964988936361475)
              ·
                refine ⟨156917984018947483404542213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104611989345964988936361475 156917984018947483404542213)
                ·
                  refine ⟨29422122003552653138351665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156917984018947483404542213 29422122003552653138351665)
                  ·
                    refine ⟨22066591502664489853763749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29422122003552653138351665 22066591502664489853763749)
                    ·
                      refine ⟨4137485906749591847580703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22066591502664489853763749 4137485906749591847580703)
                      ·
                        rfl

theorem cell23_8057725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_8057725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057725 prefixEnd_8057725 := by exact prefixLift 8057725
  have htrace : WordTrace (prefixWord ++ tailWord_8057725) baseStart_8057725 baseEnd_8057725 := by
    simpa [prefixWord, tailWord_8057725, baseEnd_8057725] using wordTrace_append hprefix tailTrace_8057725
  have hstable : (prefixWord ++ tailWord_8057725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057725).length < 2 ^ (prefixWord ++ tailWord_8057725).sum := by decide
  have hdescent : baseEnd_8057725 < baseStart_8057725 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057745 : List Nat := [1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 3]
def baseStart_8057745 : Nat := 118140960795 + 8057745 * 2 ^ 59
def prefixEnd_8057745 : Nat := 4983230072969 + 3 ^ 40 * 8057745 * 2
def baseEnd_8057745 : Nat := 4137496176362681769330611

theorem tailTrace_8057745 : CollatzResearch.WordTrace tailWord_8057745 prefixEnd_8057745 4137496176362681769330611 := by
  unfold tailWord_8057745
  simp only [CollatzResearch.WordTrace]
  refine ⟨293890104193173493129950689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195926736128782328753300459 293890104193173493129950689)
  ·
    refine ⟨220417578144880119847463017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293890104193173493129950689 220417578144880119847463017)
    ·
      refine ⟨165313183608660089885597263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220417578144880119847463017 165313183608660089885597263)
      ·
        refine ⟨247969775412990134828395895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165313183608660089885597263 247969775412990134828395895)
        ·
          refine ⟨371954663119485202242593843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247969775412990134828395895 371954663119485202242593843)
          ·
            refine ⟨557931994679227803363890765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371954663119485202242593843 557931994679227803363890765)
            ·
              refine ⟨209224498004710426261459037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 557931994679227803363890765 209224498004710426261459037)
              ·
                refine ⟨78459186751766409848047139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209224498004710426261459037 78459186751766409848047139)
                ·
                  refine ⟨117688780127649614772070709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78459186751766409848047139 117688780127649614772070709)
                  ·
                    refine ⟨11033323136967151384881629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117688780127649614772070709 11033323136967151384881629)
                    ·
                      refine ⟨4137496176362681769330611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11033323136967151384881629 4137496176362681769330611)
                      ·
                        rfl

theorem cell23_8057745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 3].length) (baseStart_8057745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057745 prefixEnd_8057745 := by exact prefixLift 8057745
  have htrace : WordTrace (prefixWord ++ tailWord_8057745) baseStart_8057745 baseEnd_8057745 := by
    simpa [prefixWord, tailWord_8057745, baseEnd_8057745] using wordTrace_append hprefix tailTrace_8057745
  have hstable : (prefixWord ++ tailWord_8057745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057745).length < 2 ^ (prefixWord ++ tailWord_8057745).sum := by decide
  have hdescent : baseEnd_8057745 < baseStart_8057745 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057750 : List Nat := [5, 3, 1, 1, 1, 1, 3, 2, 1, 3, 2]
def baseStart_8057750 : Nat := 118140960795 + 8057750 * 2 ^ 59
def prefixEnd_8057750 : Nat := 4983230072969 + 3 ^ 40 * 8057750 * 2
def baseEnd_8057750 : Nat := 4137498743765954249768089

theorem tailTrace_8057750 : CollatzResearch.WordTrace tailWord_8057750 prefixEnd_8057750 4137498743765954249768089 := by
  unfold tailWord_8057750
  simp only [CollatzResearch.WordTrace]
  refine ⟨18368142909884711186492669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195926857705436919322588469 18368142909884711186492669)
  ·
    refine ⟨6888053591206766694934751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18368142909884711186492669 6888053591206766694934751)
    ·
      refine ⟨10332080386810150042402127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6888053591206766694934751 10332080386810150042402127)
      ·
        refine ⟨15498120580215225063603191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10332080386810150042402127 15498120580215225063603191)
        ·
          refine ⟨23247180870322837595404787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15498120580215225063603191 23247180870322837595404787)
          ·
            refine ⟨34870771305484256393107181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23247180870322837595404787 34870771305484256393107181)
            ·
              refine ⟨13076539239556596147415193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34870771305484256393107181 13076539239556596147415193)
              ·
                refine ⟨9807404429667447110561395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13076539239556596147415193 9807404429667447110561395)
                ·
                  refine ⟨14711106644501170665842093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9807404429667447110561395 14711106644501170665842093)
                  ·
                    refine ⟨5516664991687938999690785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14711106644501170665842093 5516664991687938999690785)
                    ·
                      refine ⟨4137498743765954249768089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5516664991687938999690785 4137498743765954249768089)
                      ·
                        rfl

theorem cell23_8057750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_8057750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057750 prefixEnd_8057750 := by exact prefixLift 8057750
  have htrace : WordTrace (prefixWord ++ tailWord_8057750) baseStart_8057750 baseEnd_8057750 := by
    simpa [prefixWord, tailWord_8057750, baseEnd_8057750] using wordTrace_append hprefix tailTrace_8057750
  have hstable : (prefixWord ++ tailWord_8057750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057750).length < 2 ^ (prefixWord ++ tailWord_8057750).sum := by decide
  have hdescent : baseEnd_8057750 < baseStart_8057750 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057780 : List Nat := [2, 5, 2, 1, 1, 2, 2, 2, 2, 2, 2]
def baseStart_8057780 : Nat := 118140960795 + 8057780 * 2 ^ 59
def prefixEnd_8057780 : Nat := 4983230072969 + 3 ^ 40 * 8057780 * 2
def baseEnd_8057780 : Nat := 4137514148185589132392951

theorem tailTrace_8057780 : CollatzResearch.WordTrace tailWord_8057780 prefixEnd_8057780 4137514148185589132392951 := by
  unfold tailWord_8057780
  simp only [CollatzResearch.WordTrace]
  refine ⟨146945690374023347053737397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195927587165364462738316529 146945690374023347053737397)
  ·
    refine ⟨13776158472564688786287881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146945690374023347053737397 13776158472564688786287881)
    ·
      refine ⟨10332118854423516589715911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13776158472564688786287881 10332118854423516589715911)
      ·
        refine ⟨15498178281635274884573867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10332118854423516589715911 15498178281635274884573867)
        ·
          refine ⟨23247267422452912326860801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15498178281635274884573867 23247267422452912326860801)
          ·
            refine ⟨17435450566839684245145601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23247267422452912326860801 17435450566839684245145601)
            ·
              refine ⟨13076587925129763183859201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17435450566839684245145601 13076587925129763183859201)
              ·
                refine ⟨9807440943847322387894401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13076587925129763183859201 9807440943847322387894401)
                ·
                  refine ⟨7355580707885491790920801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9807440943847322387894401 7355580707885491790920801)
                  ·
                    refine ⟨5516685530914118843190601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7355580707885491790920801 5516685530914118843190601)
                    ·
                      refine ⟨4137514148185589132392951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5516685530914118843190601 4137514148185589132392951)
                      ·
                        rfl

theorem cell23_8057780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_8057780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057780 prefixEnd_8057780 := by exact prefixLift 8057780
  have htrace : WordTrace (prefixWord ++ tailWord_8057780) baseStart_8057780 baseEnd_8057780 := by
    simpa [prefixWord, tailWord_8057780, baseEnd_8057780] using wordTrace_append hprefix tailTrace_8057780
  have hstable : (prefixWord ++ tailWord_8057780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057780).length < 2 ^ (prefixWord ++ tailWord_8057780).sum := by decide
  have hdescent : baseEnd_8057780 < baseStart_8057780 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057796 : List Nat := [2, 3, 3, 3, 1, 1, 1, 1, 2, 3, 3]
def baseStart_8057796 : Nat := 118140960795 + 8057796 * 2 ^ 59
def prefixEnd_8057796 : Nat := 4983230072969 + 3 ^ 40 * 8057796 * 2
def baseEnd_8057796 : Nat := 4137522363876061069792877

theorem tailTrace_8057796 : CollatzResearch.WordTrace tailWord_8057796 prefixEnd_8057796 4137522363876061069792877 := by
  unfold tailWord_8057796
  simp only [CollatzResearch.WordTrace]
  refine ⟨146945982157994364420028621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195927976210659152560038161 146945982157994364420028621)
  ·
    refine ⟨55104743309247886657510733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146945982157994364420028621 55104743309247886657510733)
    ·
      refine ⟨20664278740967957496566525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55104743309247886657510733 20664278740967957496566525)
      ·
        refine ⟨7749104527862984061212447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20664278740967957496566525 7749104527862984061212447)
        ·
          refine ⟨11623656791794476091818671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7749104527862984061212447 11623656791794476091818671)
          ·
            refine ⟨17435485187691714137728007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11623656791794476091818671 17435485187691714137728007)
            ·
              refine ⟨26153227781537571206592011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17435485187691714137728007 26153227781537571206592011)
              ·
                refine ⟨39229841672306356809888017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26153227781537571206592011 39229841672306356809888017)
                ·
                  refine ⟨29422381254229767607416013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39229841672306356809888017 29422381254229767607416013)
                  ·
                    refine ⟨11033392970336162852781005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29422381254229767607416013 11033392970336162852781005)
                    ·
                      refine ⟨4137522363876061069792877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11033392970336162852781005 4137522363876061069792877)
                      ·
                        rfl

theorem cell23_8057796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_8057796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057796 prefixEnd_8057796 := by exact prefixLift 8057796
  have htrace : WordTrace (prefixWord ++ tailWord_8057796) baseStart_8057796 baseEnd_8057796 := by
    simpa [prefixWord, tailWord_8057796, baseEnd_8057796] using wordTrace_append hprefix tailTrace_8057796
  have hstable : (prefixWord ++ tailWord_8057796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057796).length < 2 ^ (prefixWord ++ tailWord_8057796).sum := by decide
  have hdescent : baseEnd_8057796 < baseStart_8057796 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057815 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 4]
def baseStart_8057815 : Nat := 118140960795 + 8057815 * 2 ^ 59
def prefixEnd_8057815 : Nat := 4983230072969 + 3 ^ 40 * 8057815 * 2
def baseEnd_8057815 : Nat := 4137532120008496495455289

theorem tailTrace_8057815 : CollatzResearch.WordTrace tailWord_8057815 prefixEnd_8057815 4137532120008496495455289 := by
  unfold tailWord_8057815
  simp only [CollatzResearch.WordTrace]
  refine ⟨293892657302919895084998899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195928438201946596723332599 293892657302919895084998899)
  ·
    refine ⟨440838985954379842627498349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293892657302919895084998899 440838985954379842627498349)
    ·
      refine ⟨165314619732892440985311881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 440838985954379842627498349 165314619732892440985311881)
      ·
        refine ⟨123985964799669330738983911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165314619732892440985311881 123985964799669330738983911)
        ·
          refine ⟨185978947199503996108475867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123985964799669330738983911 185978947199503996108475867)
          ·
            refine ⟨278968420799255994162713801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185978947199503996108475867 278968420799255994162713801)
            ·
              refine ⟨209226315599441995622035351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278968420799255994162713801 209226315599441995622035351)
              ·
                refine ⟨313839473399162993433053027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209226315599441995622035351 313839473399162993433053027)
                ·
                  refine ⟨470759210098744490149579541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 313839473399162993433053027 470759210098744490149579541)
                  ·
                    refine ⟨22066837973378647975761541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 470759210098744490149579541 22066837973378647975761541)
                    ·
                      refine ⟨4137532120008496495455289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22066837973378647975761541 4137532120008496495455289)
                      ·
                        rfl

theorem cell23_8057815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_8057815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057815 prefixEnd_8057815 := by exact prefixLift 8057815
  have htrace : WordTrace (prefixWord ++ tailWord_8057815) baseStart_8057815 baseEnd_8057815 := by
    simpa [prefixWord, tailWord_8057815, baseEnd_8057815] using wordTrace_append hprefix tailTrace_8057815
  have hstable : (prefixWord ++ tailWord_8057815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057815).length < 2 ^ (prefixWord ++ tailWord_8057815).sum := by decide
  have hdescent : baseEnd_8057815 < baseStart_8057815 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057825 : List Nat := [1, 2, 3, 1, 2, 1, 1, 4, 8]
def baseStart_8057825 : Nat := 118140960795 + 8057825 * 2 ^ 59
def prefixEnd_8057825 : Nat := 4983230072969 + 3 ^ 40 * 8057825 * 2
def baseEnd_8057825 : Nat := 459726361646115717370027

theorem tailTrace_8057825 : CollatzResearch.WordTrace tailWord_8057825 prefixEnd_8057825 459726361646115717370027 := by
  unfold tailWord_8057825
  simp only [CollatzResearch.WordTrace]
  refine ⟨293893022032883666792862929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195928681355255777861908619 293893022032883666792862929)
  ·
    refine ⟨220419766524662750094647197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293893022032883666792862929 220419766524662750094647197)
    ·
      refine ⟨82657412446748531285492699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220419766524662750094647197 82657412446748531285492699)
      ·
        refine ⟨123986118670122796928239049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82657412446748531285492699 123986118670122796928239049)
        ·
          refine ⟨92989589002592097696179287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123986118670122796928239049 92989589002592097696179287)
          ·
            refine ⟨139484383503888146544268931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92989589002592097696179287 139484383503888146544268931)
            ·
              refine ⟨209226575255832219816403397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139484383503888146544268931 209226575255832219816403397)
              ·
                refine ⟨39229982860468541215575637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 209226575255832219816403397 39229982860468541215575637)
                ·
                  refine ⟨459726361646115717370027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39229982860468541215575637 459726361646115717370027)
                  ·
                    rfl

theorem cell23_8057825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 8].length) (baseStart_8057825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057825 prefixEnd_8057825 := by exact prefixLift 8057825
  have htrace : WordTrace (prefixWord ++ tailWord_8057825) baseStart_8057825 baseEnd_8057825 := by
    simpa [prefixWord, tailWord_8057825, baseEnd_8057825] using wordTrace_append hprefix tailTrace_8057825
  have hstable : (prefixWord ++ tailWord_8057825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057825).length < 2 ^ (prefixWord ++ tailWord_8057825).sum := by decide
  have hdescent : baseEnd_8057825 < baseStart_8057825 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057846 : List Nat := [5, 1, 1, 1, 3, 2, 2, 1, 3, 4]
def baseStart_8057846 : Nat := 118140960795 + 8057846 * 2 ^ 59
def prefixEnd_8057846 : Nat := 4983230072969 + 3 ^ 40 * 8057846 * 2
def baseEnd_8057846 : Nat := 1379182679302928624722549

theorem tailTrace_8057846 : CollatzResearch.WordTrace tailWord_8057846 prefixEnd_8057846 1379182679302928624722549 := by
  unfold tailWord_8057846
  simp only [CollatzResearch.WordTrace]
  refine ⟨18368361747862974211211087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195929191977205058252918261 18368361747862974211211087)
  ·
    refine ⟨27552542621794461316816631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18368361747862974211211087 27552542621794461316816631)
    ·
      refine ⟨41328813932691691975224947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27552542621794461316816631 41328813932691691975224947)
      ·
        refine ⟨61993220899037537962837421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41328813932691691975224947 61993220899037537962837421)
        ·
          refine ⟨23247457837139076736064033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61993220899037537962837421 23247457837139076736064033)
          ·
            refine ⟨17435593377854307552048025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23247457837139076736064033 17435593377854307552048025)
            ·
              refine ⟨13076695033390730664036019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17435593377854307552048025 13076695033390730664036019)
              ·
                refine ⟨19615042550086095996054029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13076695033390730664036019 19615042550086095996054029)
                ·
                  refine ⟨7355640956282285998520261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19615042550086095996054029 7355640956282285998520261)
                  ·
                    refine ⟨1379182679302928624722549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7355640956282285998520261 1379182679302928624722549)
                    ·
                      rfl

theorem cell23_8057846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_8057846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057846 prefixEnd_8057846 := by exact prefixLift 8057846
  have htrace : WordTrace (prefixWord ++ tailWord_8057846) baseStart_8057846 baseEnd_8057846 := by
    simpa [prefixWord, tailWord_8057846, baseEnd_8057846] using wordTrace_append hprefix tailTrace_8057846
  have hstable : (prefixWord ++ tailWord_8057846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057846).length < 2 ^ (prefixWord ++ tailWord_8057846).sum := by decide
  have hdescent : baseEnd_8057846 < baseStart_8057846 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057865 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 2, 1, 7]
def baseStart_8057865 : Nat := 118140960795 + 8057865 * 2 ^ 59
def prefixEnd_8057865 : Nat := 4983230072969 + 3 ^ 40 * 8057865 * 2
def baseEnd_8057865 : Nat := 4137557794041221299830059

theorem tailTrace_8057865 : CollatzResearch.WordTrace tailWord_8057865 prefixEnd_8057865 4137557794041221299830059 := by
  unfold tailWord_8057865
  simp only [CollatzResearch.WordTrace]
  refine ⟨293894480952738753624319049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195929653968492502416212699 293894480952738753624319049)
  ·
    refine ⟨220420860714554065218239287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293894480952738753624319049 220420860714554065218239287)
    ·
      refine ⟨330631291071831097827358931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220420860714554065218239287 330631291071831097827358931)
      ·
        refine ⟨495946936607746646741038397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330631291071831097827358931 495946936607746646741038397)
        ·
          refine ⟨185980101227904992527889399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 495946936607746646741038397 185980101227904992527889399)
          ·
            refine ⟨278970151841857488791834099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185980101227904992527889399 278970151841857488791834099)
            ·
              refine ⟨418455227762786233187751149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278970151841857488791834099 418455227762786233187751149)
              ·
                refine ⟨156920710411044837445406681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 418455227762786233187751149 156920710411044837445406681)
                ·
                  refine ⟨117690532808283628084055011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156920710411044837445406681 117690532808283628084055011)
                  ·
                    refine ⟨176535799212425442126082517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 117690532808283628084055011 176535799212425442126082517)
                    ·
                      refine ⟨4137557794041221299830059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 176535799212425442126082517 4137557794041221299830059)
                      ·
                        rfl

theorem cell23_8057865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 1, 7].length) (baseStart_8057865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057865 prefixEnd_8057865 := by exact prefixLift 8057865
  have htrace : WordTrace (prefixWord ++ tailWord_8057865) baseStart_8057865 baseEnd_8057865 := by
    simpa [prefixWord, tailWord_8057865, baseEnd_8057865] using wordTrace_append hprefix tailTrace_8057865
  have hstable : (prefixWord ++ tailWord_8057865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057865).length < 2 ^ (prefixWord ++ tailWord_8057865).sum := by decide
  have hdescent : baseEnd_8057865 < baseStart_8057865 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057889 : List Nat := [1, 2, 3, 2, 3, 1, 2, 3, 1, 5]
def baseStart_8057889 : Nat := 118140960795 + 8057889 * 2 ^ 59
def prefixEnd_8057889 : Nat := 4983230072969 + 3 ^ 40 * 8057889 * 2
def baseEnd_8057889 : Nat := 1379190039192309735309983

theorem tailTrace_8057889 : CollatzResearch.WordTrace tailWord_8057889 prefixEnd_8057889 1379190039192309735309983 := by
  unfold tailWord_8057889
  simp only [CollatzResearch.WordTrace]
  refine ⟨293895356304651805723192721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195930237536434537148795147 293895356304651805723192721)
  ·
    refine ⟨220421517228488854292394541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293895356304651805723192721 220421517228488854292394541)
    ·
      refine ⟨82658068960683320359647953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220421517228488854292394541 82658068960683320359647953)
      ·
        refine ⟨61993551720512490269735965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82658068960683320359647953 61993551720512490269735965)
        ·
          refine ⟨23247581895192183851150987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61993551720512490269735965 23247581895192183851150987)
          ·
            refine ⟨34871372842788275776726481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23247581895192183851150987 34871372842788275776726481)
            ·
              refine ⟨26153529632091206832544861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34871372842788275776726481 26153529632091206832544861)
              ·
                refine ⟨9807573612034202562204323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26153529632091206832544861 9807573612034202562204323)
                ·
                  refine ⟨14711360418051303843306485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9807573612034202562204323 14711360418051303843306485)
                  ·
                    refine ⟨1379190039192309735309983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14711360418051303843306485 1379190039192309735309983)
                    ·
                      rfl

theorem cell23_8057889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 5].length) (baseStart_8057889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057889 prefixEnd_8057889 := by exact prefixLift 8057889
  have htrace : WordTrace (prefixWord ++ tailWord_8057889) baseStart_8057889 baseEnd_8057889 := by
    simpa [prefixWord, tailWord_8057889, baseEnd_8057889] using wordTrace_append hprefix tailTrace_8057889
  have hstable : (prefixWord ++ tailWord_8057889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057889).length < 2 ^ (prefixWord ++ tailWord_8057889).sum := by decide
  have hdescent : baseEnd_8057889 < baseStart_8057889 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057929 : List Nat := [1, 2, 1, 1, 2, 2, 2, 6, 1, 2, 3]
def baseStart_8057929 : Nat := 118140960795 + 8057929 * 2 ^ 59
def prefixEnd_8057929 : Nat := 4983230072969 + 3 ^ 40 * 8057929 * 2
def baseEnd_8057929 : Nat := 4137590656803109049429765

theorem tailTrace_8057929 : CollatzResearch.WordTrace tailWord_8057929 prefixEnd_8057929 4137590656803109049429765 := by
  unfold tailWord_8057929
  simp only [CollatzResearch.WordTrace]
  refine ⟨293896815224506892554648841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195931210149671261703099227 293896815224506892554648841)
  ·
    refine ⟨220422611418380169415986631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293896815224506892554648841 220422611418380169415986631)
    ·
      refine ⟨330633917127570254123979947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220422611418380169415986631 330633917127570254123979947)
      ·
        refine ⟨495950875691355381185969921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330633917127570254123979947 495950875691355381185969921)
        ·
          refine ⟨371963156768516535889477441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 495950875691355381185969921 371963156768516535889477441)
          ·
            refine ⟨278972367576387401917108081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371963156768516535889477441 278972367576387401917108081)
            ·
              refine ⟨209229275682290551437831061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278972367576387401917108081 209229275682290551437831061)
              ·
                refine ⟨9807622297607369598648331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 209229275682290551437831061 9807622297607369598648331)
                ·
                  refine ⟨14711433446411054397972497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9807622297607369598648331 14711433446411054397972497)
                  ·
                    refine ⟨11033575084808290798479373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14711433446411054397972497 11033575084808290798479373)
                    ·
                      refine ⟨4137590656803109049429765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11033575084808290798479373 4137590656803109049429765)
                      ·
                        rfl

theorem cell23_8057929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 2, 3].length) (baseStart_8057929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057929 prefixEnd_8057929 := by exact prefixLift 8057929
  have htrace : WordTrace (prefixWord ++ tailWord_8057929) baseStart_8057929 baseEnd_8057929 := by
    simpa [prefixWord, tailWord_8057929, baseEnd_8057929] using wordTrace_append hprefix tailTrace_8057929
  have hstable : (prefixWord ++ tailWord_8057929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057929).length < 2 ^ (prefixWord ++ tailWord_8057929).sum := by decide
  have hdescent : baseEnd_8057929 < baseStart_8057929 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057943 : List Nat := [1, 1, 3, 2, 2, 1, 1, 7, 1, 2, 2]
def baseStart_8057943 : Nat := 118140960795 + 8057943 * 2 ^ 59
def prefixEnd_8057943 : Nat := 4983230072969 + 3 ^ 40 * 8057943 * 2
def baseEnd_8057943 : Nat := 4137597845532271994654701

theorem tailTrace_8057943 : CollatzResearch.WordTrace tailWord_8057943 prefixEnd_8057943 4137597845532271994654701 := by
  unfold tailWord_8057943
  simp only [CollatzResearch.WordTrace]
  refine ⟨293897325846456172945658483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195931550564304115297105655 293897325846456172945658483)
  ·
    refine ⟨440845988769684259418487725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293897325846456172945658483 440845988769684259418487725)
    ·
      refine ⟨165317245788631597281932897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 440845988769684259418487725 165317245788631597281932897)
      ·
        refine ⟨123987934341473697961449673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165317245788631597281932897 123987934341473697961449673)
        ·
          refine ⟨92990950756105273471087255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123987934341473697961449673 92990950756105273471087255)
          ·
            refine ⟨139486426134157910206630883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92990950756105273471087255 139486426134157910206630883)
            ·
              refine ⟨209229639201236865309946325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139486426134157910206630883 209229639201236865309946325)
              ·
                refine ⟨4903819668778989030701867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 209229639201236865309946325 4903819668778989030701867)
                ·
                  refine ⟨7355729503168483546052801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4903819668778989030701867 7355729503168483546052801)
                  ·
                    refine ⟨5516797127376362659539601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7355729503168483546052801 5516797127376362659539601)
                    ·
                      refine ⟨4137597845532271994654701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5516797127376362659539601 4137597845532271994654701)
                      ·
                        rfl

theorem cell23_8057943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 7, 1, 2, 2].length) (baseStart_8057943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057943 prefixEnd_8057943 := by exact prefixLift 8057943
  have htrace : WordTrace (prefixWord ++ tailWord_8057943) baseStart_8057943 baseEnd_8057943 := by
    simpa [prefixWord, tailWord_8057943, baseEnd_8057943] using wordTrace_append hprefix tailTrace_8057943
  have hstable : (prefixWord ++ tailWord_8057943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057943).length < 2 ^ (prefixWord ++ tailWord_8057943).sum := by decide
  have hdescent : baseEnd_8057943 < baseStart_8057943 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057949 : List Nat := [1, 4, 4, 1, 2, 11]
def baseStart_8057949 : Nat := 118140960795 + 8057949 * 2 ^ 59
def prefixEnd_8057949 : Nat := 4983230072969 + 3 ^ 40 * 8057949 * 2
def baseEnd_8057949 : Nat := 17027164306239501939011

theorem tailTrace_8057949 : CollatzResearch.WordTrace tailWord_8057949 prefixEnd_8057949 17027164306239501939011 := by
  unfold tailWord_8057949
  simp only [CollatzResearch.WordTrace]
  refine ⟨293897544684434435970376901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195931696456289623980251267 293897544684434435970376901)
  ·
    refine ⟨55105789628331456744445669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293897544684434435970376901 55105789628331456744445669)
    ·
      refine ⟨10332335555312148139583563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55105789628331456744445669 10332335555312148139583563)
      ·
        refine ⟨15498503332968222209375345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10332335555312148139583563 15498503332968222209375345)
        ·
          refine ⟨11623877499726166657031509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15498503332968222209375345 11623877499726166657031509)
          ·
            refine ⟨17027164306239501939011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11623877499726166657031509 17027164306239501939011)
            ·
              rfl

theorem cell23_8057949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 11].length) (baseStart_8057949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057949 prefixEnd_8057949 := by exact prefixLift 8057949
  have htrace : WordTrace (prefixWord ++ tailWord_8057949) baseStart_8057949 baseEnd_8057949 := by
    simpa [prefixWord, tailWord_8057949, baseEnd_8057949] using wordTrace_append hprefix tailTrace_8057949
  have hstable : (prefixWord ++ tailWord_8057949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057949).length < 2 ^ (prefixWord ++ tailWord_8057949).sum := by decide
  have hdescent : baseEnd_8057949 < baseStart_8057949 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057973 : List Nat := [1, 3, 4, 3, 1, 1, 2, 1, 1, 2, 4]
def baseStart_8057973 : Nat := 118140960795 + 8057973 * 2 ^ 59
def prefixEnd_8057973 : Nat := 4983230072969 + 3 ^ 40 * 8057973 * 2
def baseEnd_8057973 : Nat := 4137613249951906877279563

theorem tailTrace_8057973 : CollatzResearch.WordTrace tailWord_8057973 prefixEnd_8057973 4137613249951906877279563 := by
  unfold tailWord_8057973
  simp only [CollatzResearch.WordTrace]
  refine ⟨293898420036347488069250573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195932280024231658712833715 293898420036347488069250573)
  ·
    refine ⟨110211907513630308025968965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293898420036347488069250573 110211907513630308025968965)
    ·
      refine ⟨20664732658805682754869181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110211907513630308025968965 20664732658805682754869181)
      ·
        refine ⟨7749274747052131033075943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20664732658805682754869181 7749274747052131033075943)
        ·
          refine ⟨11623912120578196549613915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7749274747052131033075943 11623912120578196549613915)
          ·
            refine ⟨17435868180867294824420873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11623912120578196549613915 17435868180867294824420873)
            ·
              refine ⟨13076901135650471118315655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17435868180867294824420873 13076901135650471118315655)
              ·
                refine ⟨19615351703475706677473483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13076901135650471118315655 19615351703475706677473483)
                ·
                  refine ⟨29423027555213560016210225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19615351703475706677473483 29423027555213560016210225)
                  ·
                    refine ⟨22067270666410170012157669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29423027555213560016210225 22067270666410170012157669)
                    ·
                      refine ⟨4137613249951906877279563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22067270666410170012157669 4137613249951906877279563)
                      ·
                        rfl

theorem cell23_8057973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_8057973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057973 prefixEnd_8057973 := by exact prefixLift 8057973
  have htrace : WordTrace (prefixWord ++ tailWord_8057973) baseStart_8057973 baseEnd_8057973 := by
    simpa [prefixWord, tailWord_8057973, baseEnd_8057973] using wordTrace_append hprefix tailTrace_8057973
  have hstable : (prefixWord ++ tailWord_8057973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057973).length < 2 ^ (prefixWord ++ tailWord_8057973).sum := by decide
  have hdescent : baseEnd_8057973 < baseStart_8057973 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057976 : List Nat := [2, 1, 2, 1, 1, 1, 6, 3, 2, 1, 3]
def baseStart_8057976 : Nat := 118140960795 + 8057976 * 2 ^ 59
def prefixEnd_8057976 : Nat := 4983230072969 + 3 ^ 40 * 8057976 * 2
def baseEnd_8057976 : Nat := 4137614790393870365542049

theorem tailTrace_8057976 : CollatzResearch.WordTrace tailWord_8057976 prefixEnd_8057976 4137614790393870365542049 := by
  unfold tailWord_8057976
  simp only [CollatzResearch.WordTrace]
  refine ⟨146949264727668309790804891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195932352970224413054406521 146949264727668309790804891)
  ·
    refine ⟨220423897091502464686207337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146949264727668309790804891 220423897091502464686207337)
    ·
      refine ⟨165317922818626848514655503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220423897091502464686207337 165317922818626848514655503)
      ·
        refine ⟨247976884227940272771983255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165317922818626848514655503 247976884227940272771983255)
        ·
          refine ⟨371965326341910409157974883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247976884227940272771983255 371965326341910409157974883)
          ·
            refine ⟨557947989512865613736962325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371965326341910409157974883 557947989512865613736962325)
            ·
              refine ⟨26153812008415575643920109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 557947989512865613736962325 26153812008415575643920109)
              ·
                refine ⟨9807679503155840866470041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26153812008415575643920109 9807679503155840866470041)
                ·
                  refine ⟨7355759627366880649852531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9807679503155840866470041 7355759627366880649852531)
                  ·
                    refine ⟨11033639441050320974778797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7355759627366880649852531 11033639441050320974778797)
                    ·
                      refine ⟨4137614790393870365542049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11033639441050320974778797 4137614790393870365542049)
                      ·
                        rfl

theorem cell23_8057976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 2, 1, 3].length) (baseStart_8057976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057976 prefixEnd_8057976 := by exact prefixLift 8057976
  have htrace : WordTrace (prefixWord ++ tailWord_8057976) baseStart_8057976 baseEnd_8057976 := by
    simpa [prefixWord, tailWord_8057976, baseEnd_8057976] using wordTrace_append hprefix tailTrace_8057976
  have hstable : (prefixWord ++ tailWord_8057976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057976).length < 2 ^ (prefixWord ++ tailWord_8057976).sum := by decide
  have hdescent : baseEnd_8057976 < baseStart_8057976 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8057999 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 7, 4, 2]
def baseStart_8057999 : Nat := 118140960795 + 8057999 * 2 ^ 59
def prefixEnd_8057999 : Nat := 4983230072969 + 3 ^ 40 * 8057999 * 2
def baseEnd_8057999 : Nat := 4137626600448923775554443

theorem tailTrace_8057999 : CollatzResearch.WordTrace tailWord_8057999 prefixEnd_8057999 4137626600448923775554443 := by
  unfold tailWord_8057999
  simp only [CollatzResearch.WordTrace]
  refine ⟨293899368334253294509697051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195932912222835529673131367 293899368334253294509697051)
  ·
    refine ⟨440849052501379941764545577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293899368334253294509697051 440849052501379941764545577)
    ·
      refine ⟨330636789376034956323409183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440849052501379941764545577 330636789376034956323409183)
      ·
        refine ⟨495955184064052434485113775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330636789376034956323409183 495955184064052434485113775)
        ·
          refine ⟨743932776096078651727670663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495955184064052434485113775 743932776096078651727670663)
          ·
            refine ⟨1115899164144117977591505995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 743932776096078651727670663 1115899164144117977591505995)
            ·
              refine ⟨1673848746216176966387258993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1115899164144117977591505995 1673848746216176966387258993)
              ·
                refine ⟨1255386559662132724790444245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1673848746216176966387258993 1255386559662132724790444245)
                ·
                  refine ⟨29423122492081235737276037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1255386559662132724790444245 29423122492081235737276037)
                  ·
                    refine ⟨5516835467265231700739257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29423122492081235737276037 5516835467265231700739257)
                    ·
                      refine ⟨4137626600448923775554443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5516835467265231700739257 4137626600448923775554443)
                      ·
                        rfl

theorem cell23_8057999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 4, 2].length) (baseStart_8057999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8057999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8057999 prefixEnd_8057999 := by exact prefixLift 8057999
  have htrace : WordTrace (prefixWord ++ tailWord_8057999) baseStart_8057999 baseEnd_8057999 := by
    simpa [prefixWord, tailWord_8057999, baseEnd_8057999] using wordTrace_append hprefix tailTrace_8057999
  have hstable : (prefixWord ++ tailWord_8057999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8057999).length < 2 ^ (prefixWord ++ tailWord_8057999).sum := by decide
  have hdescent : baseEnd_8057999 < baseStart_8057999 := by decide
  rcases family_descends (prefixWord ++ tailWord_8057999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058003 : List Nat := [1, 1, 1, 2, 1, 2, 8, 1, 1, 3, 2]
def baseStart_8058003 : Nat := 118140960795 + 8058003 * 2 ^ 59
def prefixEnd_8058003 : Nat := 4983230072969 + 3 ^ 40 * 8058003 * 2
def baseEnd_8058003 : Nat := 4137628654371541759904425

theorem tailTrace_8058003 : CollatzResearch.WordTrace tailWord_8058003 prefixEnd_8058003 4137628654371541759904425 := by
  unfold tailWord_8058003
  simp only [CollatzResearch.WordTrace]
  refine ⟨293899514226238803192842663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195933009484159202128561775 293899514226238803192842663)
  ·
    refine ⟨440849271339358204789263995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293899514226238803192842663 440849271339358204789263995)
    ·
      refine ⟨661273907009037307183895993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440849271339358204789263995 661273907009037307183895993)
      ·
        refine ⟨495955430256777980387921995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 661273907009037307183895993 495955430256777980387921995)
        ·
          refine ⟨743933145385166970581882993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495955430256777980387921995 743933145385166970581882993)
          ·
            refine ⟨557949859038875227936412245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 743933145385166970581882993 557949859038875227936412245)
            ·
              refine ⟨6538474910611819077379831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 557949859038875227936412245 6538474910611819077379831)
              ·
                refine ⟨9807712365917728616069747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6538474910611819077379831 9807712365917728616069747)
                ·
                  refine ⟨14711568548876592924104621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9807712365917728616069747 14711568548876592924104621)
                  ·
                    refine ⟨5516838205828722346539233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14711568548876592924104621 5516838205828722346539233)
                    ·
                      refine ⟨4137628654371541759904425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5516838205828722346539233 4137628654371541759904425)
                      ·
                        rfl

theorem cell23_8058003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 1, 3, 2].length) (baseStart_8058003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058003 prefixEnd_8058003 := by exact prefixLift 8058003
  have htrace : WordTrace (prefixWord ++ tailWord_8058003) baseStart_8058003 baseEnd_8058003 := by
    simpa [prefixWord, tailWord_8058003, baseEnd_8058003] using wordTrace_append hprefix tailTrace_8058003
  have hstable : (prefixWord ++ tailWord_8058003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058003).length < 2 ^ (prefixWord ++ tailWord_8058003).sum := by decide
  have hdescent : baseEnd_8058003 < baseStart_8058003 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058010 : List Nat := [3, 1, 1, 5, 1, 3, 1, 2, 2, 1, 3]
def baseStart_8058010 : Nat := 118140960795 + 8058010 * 2 ^ 59
def prefixEnd_8058010 : Nat := 4983230072969 + 3 ^ 40 * 8058010 * 2
def baseEnd_8058010 : Nat := 4137632248736123232516893

theorem tailTrace_8058010 : CollatzResearch.WordTrace tailWord_8058010 prefixEnd_8058010 4137632248736123232516893 := by
  unfold tailWord_8058010
  simp only [CollatzResearch.WordTrace]
  refine ⟨73474942384303360847086871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195933179691475628925564989 73474942384303360847086871)
  ·
    refine ⟨110212413576455041270630307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73474942384303360847086871 110212413576455041270630307)
    ·
      refine ⟨165318620364682561905945461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110212413576455041270630307 165318620364682561905945461)
      ·
        refine ⟨15498620659188990178682387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165318620364682561905945461 15498620659188990178682387)
        ·
          refine ⟨23247930988783485268023581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15498620659188990178682387 23247930988783485268023581)
          ·
            refine ⟨8717974120793806975508843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23247930988783485268023581 8717974120793806975508843)
            ·
              refine ⟨13076961181190710463263265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8717974120793806975508843 13076961181190710463263265)
              ·
                refine ⟨9807720885893032847447449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13076961181190710463263265 9807720885893032847447449)
                ·
                  refine ⟨7355790664419774635585587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9807720885893032847447449 7355790664419774635585587)
                  ·
                    refine ⟨11033685996629661953378381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7355790664419774635585587 11033685996629661953378381)
                    ·
                      refine ⟨4137632248736123232516893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11033685996629661953378381 4137632248736123232516893)
                      ·
                        rfl

theorem cell23_8058010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_8058010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058010 prefixEnd_8058010 := by exact prefixLift 8058010
  have htrace : WordTrace (prefixWord ++ tailWord_8058010) baseStart_8058010 baseEnd_8058010 := by
    simpa [prefixWord, tailWord_8058010, baseEnd_8058010] using wordTrace_append hprefix tailTrace_8058010
  have hstable : (prefixWord ++ tailWord_8058010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058010).length < 2 ^ (prefixWord ++ tailWord_8058010).sum := by decide
  have hdescent : baseEnd_8058010 < baseStart_8058010 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058026 : List Nat := [3, 1, 5, 1, 1, 1, 2, 1, 2, 6]
def baseStart_8058026 : Nat := 118140960795 + 8058026 * 2 ^ 59
def prefixEnd_8058026 : Nat := 4983230072969 + 3 ^ 40 * 8058026 * 2
def baseEnd_8058026 : Nat := 1379213488142198389972273

theorem tailTrace_8058026 : CollatzResearch.WordTrace tailWord_8058026 prefixEnd_8058026 1379213488142198389972273 := by
  unfold tailWord_8058026
  simp only [CollatzResearch.WordTrace]
  refine ⟨73475088276288869530232483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195933568736770318747286621 73475088276288869530232483)
  ·
    refine ⟨110212632414433304295348725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73475088276288869530232483 110212632414433304295348725)
    ·
      refine ⟨10332434288853122277688943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110212632414433304295348725 10332434288853122277688943)
      ·
        refine ⟨15498651433279683416533415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10332434288853122277688943 15498651433279683416533415)
        ·
          refine ⟨23247977149919525124800123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15498651433279683416533415 23247977149919525124800123)
          ·
            refine ⟨34871965724879287687200185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23247977149919525124800123 34871965724879287687200185)
            ·
              refine ⟨26153974293659465765400139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34871965724879287687200185 26153974293659465765400139)
              ·
                refine ⟨39230961440489198648100209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26153974293659465765400139 39230961440489198648100209)
                ·
                  refine ⟨29423221080366898986075157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39230961440489198648100209 29423221080366898986075157)
                  ·
                    refine ⟨1379213488142198389972273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29423221080366898986075157 1379213488142198389972273)
                    ·
                      rfl

theorem cell23_8058026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_8058026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058026 prefixEnd_8058026 := by exact prefixLift 8058026
  have htrace : WordTrace (prefixWord ++ tailWord_8058026) baseStart_8058026 baseEnd_8058026 := by
    simpa [prefixWord, tailWord_8058026, baseEnd_8058026] using wordTrace_append hprefix tailTrace_8058026
  have hstable : (prefixWord ++ tailWord_8058026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058026).length < 2 ^ (prefixWord ++ tailWord_8058026).sum := by decide
  have hdescent : baseEnd_8058026 < baseStart_8058026 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058033 : List Nat := [1, 2, 2, 5, 1, 1, 3, 1, 1, 4, 2]
def baseStart_8058033 : Nat := 118140960795 + 8058033 * 2 ^ 59
def prefixEnd_8058033 : Nat := 4983230072969 + 3 ^ 40 * 8058033 * 2
def baseEnd_8058033 : Nat := 4137644058791176642529287

theorem tailTrace_8058033 : CollatzResearch.WordTrace tailWord_8058033 prefixEnd_8058033 4137644058791176642529287 := by
  unfold tailWord_8058033
  simp only [CollatzResearch.WordTrace]
  refine ⟨293900608416130118316434753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195933738944086745544289835 293900608416130118316434753)
  ·
    refine ⟨220425456312097588737326065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293900608416130118316434753 220425456312097588737326065)
    ·
      refine ⟨165319092234073191552994549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220425456312097588737326065 165319092234073191552994549)
      ·
        refine ⟨15498664896944361708093239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165319092234073191552994549 15498664896944361708093239)
        ·
          refine ⟨23247997345416542562139859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15498664896944361708093239 23247997345416542562139859)
          ·
            refine ⟨34871996018124813843209789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23247997345416542562139859 34871996018124813843209789)
            ·
              refine ⟨13076998506796805191203671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34871996018124813843209789 13076998506796805191203671)
              ·
                refine ⟨19615497760195207786805507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13076998506796805191203671 19615497760195207786805507)
                ·
                  refine ⟨29423246640292811680208261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19615497760195207786805507 29423246640292811680208261)
                  ·
                    refine ⟨5516858745054902190039049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29423246640292811680208261 5516858745054902190039049)
                    ·
                      refine ⟨4137644058791176642529287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5516858745054902190039049 4137644058791176642529287)
                      ·
                        rfl

theorem cell23_8058033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_8058033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058033 prefixEnd_8058033 := by exact prefixLift 8058033
  have htrace : WordTrace (prefixWord ++ tailWord_8058033) baseStart_8058033 baseEnd_8058033 := by
    simpa [prefixWord, tailWord_8058033, baseEnd_8058033] using wordTrace_append hprefix tailTrace_8058033
  have hstable : (prefixWord ++ tailWord_8058033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058033).length < 2 ^ (prefixWord ++ tailWord_8058033).sum := by decide
  have hdescent : baseEnd_8058033 < baseStart_8058033 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058056 : List Nat := [2, 1, 3, 1, 2, 1, 5, 3, 5]
def baseStart_8058056 : Nat := 118140960795 + 8058056 * 2 ^ 59
def prefixEnd_8058056 : Nat := 4983230072969 + 3 ^ 40 * 8058056 * 2
def baseEnd_8058056 : Nat := 459739540982914450282409

theorem tailTrace_8058056 : CollatzResearch.WordTrace tailWord_8058056 prefixEnd_8058056 459739540982914450282409 := by
  unfold tailWord_8058056
  simp only [CollatzResearch.WordTrace]
  refine ⟨146950723647523396622261011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195934298196697862163014681 146950723647523396622261011)
  ·
    refine ⟨220426085471285094933391517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146950723647523396622261011 220426085471285094933391517)
    ·
      refine ⟨82659782051731910600021819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220426085471285094933391517 82659782051731910600021819)
      ·
        refine ⟨123989673077597865900032729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82659782051731910600021819 123989673077597865900032729)
        ·
          refine ⟨92992254808198399425024547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123989673077597865900032729 92992254808198399425024547)
          ·
            refine ⟨139488382212297599137536821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92992254808198399425024547 139488382212297599137536821)
            ·
              refine ⟨13077035832402899919144077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 139488382212297599137536821 13077035832402899919144077)
              ·
                refine ⟨4903888437151087469679029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13077035832402899919144077 4903888437151087469679029)
                ·
                  refine ⟨459739540982914450282409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4903888437151087469679029 459739540982914450282409)
                  ·
                    rfl

theorem cell23_8058056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 3, 5].length) (baseStart_8058056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058056 prefixEnd_8058056 := by exact prefixLift 8058056
  have htrace : WordTrace (prefixWord ++ tailWord_8058056) baseStart_8058056 baseEnd_8058056 := by
    simpa [prefixWord, tailWord_8058056, baseEnd_8058056] using wordTrace_append hprefix tailTrace_8058056
  have hstable : (prefixWord ++ tailWord_8058056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058056).length < 2 ^ (prefixWord ++ tailWord_8058056).sum := by decide
  have hdescent : baseEnd_8058056 < baseStart_8058056 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058106 : List Nat := [3, 1, 1, 1, 1, 4, 4, 1, 2, 1, 4]
def baseStart_8058106 : Nat := 118140960795 + 8058106 * 2 ^ 59
def prefixEnd_8058106 : Nat := 4983230072969 + 3 ^ 40 * 8058106 * 2
def baseEnd_8058106 : Nat := 4137681542878954856916451

theorem tailTrace_8058106 : CollatzResearch.WordTrace tailWord_8058106 prefixEnd_8058106 4137681542878954856916451 := by
  unfold tailWord_8058106
  simp only [CollatzResearch.WordTrace]
  refine ⟨73475817736216412945960543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195935513963243767855894781 73475817736216412945960543)
  ·
    refine ⟨110213726604324619418940815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73475817736216412945960543 110213726604324619418940815)
    ·
      refine ⟨165320589906486929128411223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110213726604324619418940815 165320589906486929128411223)
      ·
        refine ⟨247980884859730393692616835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165320589906486929128411223 247980884859730393692616835)
        ·
          refine ⟨371971327289595590538925253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247980884859730393692616835 371971327289595590538925253)
          ·
            refine ⟨69744623866799173226048485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 371971327289595590538925253 69744623866799173226048485)
            ·
              refine ⟨13077116975024844979884091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69744623866799173226048485 13077116975024844979884091)
              ·
                refine ⟨19615675462537267469826137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13077116975024844979884091 19615675462537267469826137)
                ·
                  refine ⟨14711756596902950602369603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19615675462537267469826137 14711756596902950602369603)
                  ·
                    refine ⟨22067634895354425903554405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14711756596902950602369603 22067634895354425903554405)
                    ·
                      refine ⟨4137681542878954856916451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22067634895354425903554405 4137681542878954856916451)
                      ·
                        rfl

theorem cell23_8058106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 2, 1, 4].length) (baseStart_8058106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058106 prefixEnd_8058106 := by exact prefixLift 8058106
  have htrace : WordTrace (prefixWord ++ tailWord_8058106) baseStart_8058106 baseEnd_8058106 := by
    simpa [prefixWord, tailWord_8058106, baseEnd_8058106] using wordTrace_append hprefix tailTrace_8058106
  have hstable : (prefixWord ++ tailWord_8058106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058106).length < 2 ^ (prefixWord ++ tailWord_8058106).sum := by decide
  have hdescent : baseEnd_8058106 < baseStart_8058106 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058139 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 2, 5, 3]
def baseStart_8058139 : Nat := 118140960795 + 8058139 * 2 ^ 59
def prefixEnd_8058139 : Nat := 4983230072969 + 3 ^ 40 * 8058139 * 2
def baseEnd_8058139 : Nat := 4137698487740553227803799

theorem tailTrace_8058139 : CollatzResearch.WordTrace tailWord_8058139 prefixEnd_8058139 4137698487740553227803799 := by
  unfold tailWord_8058139
  simp only [CollatzResearch.WordTrace]
  refine ⟨293904474553746098419793471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195936316369164065613195647 293904474553746098419793471)
  ·
    refine ⟨440856711830619147629690207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293904474553746098419793471 440856711830619147629690207)
    ·
      refine ⟨661285067745928721444535311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440856711830619147629690207 661285067745928721444535311)
      ·
        refine ⟨991927601618893082166802967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661285067745928721444535311 991927601618893082166802967)
        ·
          refine ⟨1487891402428339623250204451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 991927601618893082166802967 1487891402428339623250204451)
          ·
            refine ⟨2231837103642509434875306677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1487891402428339623250204451 2231837103642509434875306677)
            ·
              refine ⟨209234728466485259519560001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2231837103642509434875306677 209234728466485259519560001)
              ·
                refine ⟨156926046349863944639670001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209234728466485259519560001 156926046349863944639670001)
                ·
                  refine ⟨117694534762397958479752501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156926046349863944639670001 117694534762397958479752501)
                  ·
                    refine ⟨11033862633974808607476797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117694534762397958479752501 11033862633974808607476797)
                    ·
                      refine ⟨4137698487740553227803799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11033862633974808607476797 4137698487740553227803799)
                      ·
                        rfl

theorem cell23_8058139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 5, 3].length) (baseStart_8058139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058139 prefixEnd_8058139 := by exact prefixLift 8058139
  have htrace : WordTrace (prefixWord ++ tailWord_8058139) baseStart_8058139 baseEnd_8058139 := by
    simpa [prefixWord, tailWord_8058139, baseEnd_8058139] using wordTrace_append hprefix tailTrace_8058139
  have hstable : (prefixWord ++ tailWord_8058139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058139).length < 2 ^ (prefixWord ++ tailWord_8058139).sum := by decide
  have hdescent : baseEnd_8058139 < baseStart_8058139 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058176 : List Nat := [2, 1, 1, 2, 2, 1, 5, 3, 1, 5]
def baseStart_8058176 : Nat := 118140960795 + 8058176 * 2 ^ 59
def prefixEnd_8058176 : Nat := 4983230072969 + 3 ^ 40 * 8058176 * 2
def baseEnd_8058176 : Nat := 1379239162174923194347043

theorem tailTrace_8058176 : CollatzResearch.WordTrace tailWord_8058176 prefixEnd_8058176 1379239162174923194347043 := by
  unfold tailWord_8058176
  simp only [CollatzResearch.WordTrace]
  refine ⟨146952912027306026869445191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195937216036408035825926921 146952912027306026869445191)
  ·
    refine ⟨220429368040959040304167787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146952912027306026869445191 220429368040959040304167787)
    ·
      refine ⟨330644052061438560456251681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220429368040959040304167787 330644052061438560456251681)
      ·
        refine ⟨247983039046078920342188761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330644052061438560456251681 247983039046078920342188761)
        ·
          refine ⟨185987279284559190256641571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247983039046078920342188761 185987279284559190256641571)
          ·
            refine ⟨278980918926838785384962357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185987279284559190256641571 278980918926838785384962357)
            ·
              refine ⟨26154461149391136129840221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 278980918926838785384962357 26154461149391136129840221)
              ·
                refine ⟨9807922931021676048690083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26154461149391136129840221 9807922931021676048690083)
                ·
                  refine ⟨14711884396532514073035125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9807922931021676048690083 14711884396532514073035125)
                  ·
                    refine ⟨1379239162174923194347043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14711884396532514073035125 1379239162174923194347043)
                    ·
                      rfl

theorem cell23_8058176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 1, 5].length) (baseStart_8058176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058176 prefixEnd_8058176 := by exact prefixLift 8058176
  have htrace : WordTrace (prefixWord ++ tailWord_8058176) baseStart_8058176 baseEnd_8058176 := by
    simpa [prefixWord, tailWord_8058176, baseEnd_8058176] using wordTrace_append hprefix tailTrace_8058176
  have hstable : (prefixWord ++ tailWord_8058176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058176).length < 2 ^ (prefixWord ++ tailWord_8058176).sum := by decide
  have hdescent : baseEnd_8058176 < baseStart_8058176 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058180 : List Nat := [2, 3, 4, 1, 1, 3, 1, 2, 6]
def baseStart_8058180 : Nat := 118140960795 + 8058180 * 2 ^ 59
def prefixEnd_8058180 : Nat := 4983230072969 + 3 ^ 40 * 8058180 * 2
def baseEnd_8058180 : Nat := 459746615605265285265679

theorem tailTrace_8058180 : CollatzResearch.WordTrace tailWord_8058180 prefixEnd_8058180 459746615605265285265679 := by
  unfold tailWord_8058180
  simp only [CollatzResearch.WordTrace]
  refine ⟨146952984973298781211017997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195937313297731708281357329 146952984973298781211017997)
  ·
    refine ⟨55107369364987042954131749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146952984973298781211017997 55107369364987042954131749)
    ·
      refine ⟨10332631755935070553899703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55107369364987042954131749 10332631755935070553899703)
      ·
        refine ⟨15498947633902605830849555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10332631755935070553899703 15498947633902605830849555)
        ·
          refine ⟨23248421450853908746274333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15498947633902605830849555 23248421450853908746274333)
          ·
            refine ⟨8718158044070215779852875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23248421450853908746274333 8718158044070215779852875)
            ·
              refine ⟨13077237066105323669779313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8718158044070215779852875 13077237066105323669779313)
              ·
                refine ⟨9807927799578992752334485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13077237066105323669779313 9807927799578992752334485)
                ·
                  refine ⟨459746615605265285265679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9807927799578992752334485 459746615605265285265679)
                  ·
                    rfl

theorem cell23_8058180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 6].length) (baseStart_8058180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058180 prefixEnd_8058180 := by exact prefixLift 8058180
  have htrace : WordTrace (prefixWord ++ tailWord_8058180) baseStart_8058180 baseEnd_8058180 := by
    simpa [prefixWord, tailWord_8058180, baseEnd_8058180] using wordTrace_append hprefix tailTrace_8058180
  have hstable : (prefixWord ++ tailWord_8058180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058180).length < 2 ^ (prefixWord ++ tailWord_8058180).sum := by decide
  have hdescent : baseEnd_8058180 < baseStart_8058180 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058190 : List Nat := [4, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3]
def baseStart_8058190 : Nat := 118140960795 + 8058190 * 2 ^ 59
def prefixEnd_8058190 : Nat := 4983230072969 + 3 ^ 40 * 8058190 * 2
def baseEnd_8058190 : Nat := 4137724675253932528266065

theorem tailTrace_8058190 : CollatzResearch.WordTrace tailWord_8058190 prefixEnd_8058190 4137724675253932528266065 := by
  unfold tailWord_8058190
  simp only [CollatzResearch.WordTrace]
  refine ⟨36738291834570166766237503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195937556451040889419933349 36738291834570166766237503)
  ·
    refine ⟨55107437751855250149356255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36738291834570166766237503 55107437751855250149356255)
    ·
      refine ⟨82661156627782875224034383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55107437751855250149356255 82661156627782875224034383)
      ·
        refine ⟨123991734941674312836051575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82661156627782875224034383 123991734941674312836051575)
        ·
          refine ⟨185987602412511469254077363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123991734941674312836051575 185987602412511469254077363)
          ·
            refine ⟨278981403618767203881116045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185987602412511469254077363 278981403618767203881116045)
            ·
              refine ⟨104618026357037701455418517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 278981403618767203881116045 104618026357037701455418517)
              ·
                refine ⟨4903969985486142255722743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 104618026357037701455418517 4903969985486142255722743)
                ·
                  refine ⟨7355954978229213383584115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4903969985486142255722743 7355954978229213383584115)
                  ·
                    refine ⟨11033932467343820075376173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7355954978229213383584115 11033932467343820075376173)
                    ·
                      refine ⟨4137724675253932528266065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11033932467343820075376173 4137724675253932528266065)
                      ·
                        rfl

theorem cell23_8058190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3].length) (baseStart_8058190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058190 prefixEnd_8058190 := by exact prefixLift 8058190
  have htrace : WordTrace (prefixWord ++ tailWord_8058190) baseStart_8058190 baseEnd_8058190 := by
    simpa [prefixWord, tailWord_8058190, baseEnd_8058190] using wordTrace_append hprefix tailTrace_8058190
  have hstable : (prefixWord ++ tailWord_8058190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058190).length < 2 ^ (prefixWord ++ tailWord_8058190).sum := by decide
  have hdescent : baseEnd_8058190 < baseStart_8058190 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058213 : List Nat := [1, 3, 1, 3, 1, 2, 4, 2, 1, 1, 4]
def baseStart_8058213 : Nat := 118140960795 + 8058213 * 2 ^ 59
def prefixEnd_8058213 : Nat := 4983230072969 + 3 ^ 40 * 8058213 * 2
def baseEnd_8058213 : Nat := 4137736485308985938278459

theorem tailTrace_8058213 : CollatzResearch.WordTrace tailWord_8058213 prefixEnd_8058213 4137736485308985938278459 := by
  unfold tailWord_8058213
  simp only [CollatzResearch.WordTrace]
  refine ⟨293907173555478009057987293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195938115703652006038658195 293907173555478009057987293)
  ·
    refine ⟨110215190083304253396745235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293907173555478009057987293 110215190083304253396745235)
    ·
      refine ⟨165322785124956380095117853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110215190083304253396745235 165322785124956380095117853)
      ·
        refine ⟨61996044421858642535669195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165322785124956380095117853 61996044421858642535669195)
        ·
          refine ⟨92994066632787963803503793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61996044421858642535669195 92994066632787963803503793)
          ·
            refine ⟨69745549974590972852627845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92994066632787963803503793 69745549974590972852627845)
            ·
              refine ⟨13077290620235807409867721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69745549974590972852627845 13077290620235807409867721)
              ·
                refine ⟨9807967965176855557400791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13077290620235807409867721 9807967965176855557400791)
                ·
                  refine ⟨14711951947765283336101187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9807967965176855557400791 14711951947765283336101187)
                  ·
                    refine ⟨22067927921647925004151781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14711951947765283336101187 22067927921647925004151781)
                    ·
                      refine ⟨4137736485308985938278459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22067927921647925004151781 4137736485308985938278459)
                      ·
                        rfl

theorem cell23_8058213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_8058213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058213 prefixEnd_8058213 := by exact prefixLift 8058213
  have htrace : WordTrace (prefixWord ++ tailWord_8058213) baseStart_8058213 baseEnd_8058213 := by
    simpa [prefixWord, tailWord_8058213, baseEnd_8058213] using wordTrace_append hprefix tailTrace_8058213
  have hstable : (prefixWord ++ tailWord_8058213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058213).length < 2 ^ (prefixWord ++ tailWord_8058213).sum := by decide
  have hdescent : baseEnd_8058213 < baseStart_8058213 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058226 : List Nat := [3, 2, 1, 2, 1, 2, 2, 1, 3, 2, 4]
def baseStart_8058226 : Nat := 118140960795 + 8058226 * 2 ^ 59
def prefixEnd_8058226 : Nat := 4983230072969 + 3 ^ 40 * 8058226 * 2
def baseEnd_8058226 : Nat := 4137743160557494387415899

theorem tailTrace_8058226 : CollatzResearch.WordTrace tailWord_8058226 prefixEnd_8058226 4137743160557494387415899 := by
  unfold tailWord_8058226
  simp only [CollatzResearch.WordTrace]
  refine ⟨73476911926107728069552633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195938431802953941518807021 73476911926107728069552633)
  ·
    refine ⟨55107683944580796052164475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73476911926107728069552633 55107683944580796052164475)
    ·
      refine ⟨82661525916871194078246713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55107683944580796052164475 82661525916871194078246713)
      ·
        refine ⟨61996144437653395558685035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82661525916871194078246713 61996144437653395558685035)
        ·
          refine ⟨92994216656480093338027553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61996144437653395558685035 92994216656480093338027553)
          ·
            refine ⟨69745662492360070003520665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92994216656480093338027553 69745662492360070003520665)
            ·
              refine ⟨52309246869270052502640499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69745662492360070003520665 52309246869270052502640499)
              ·
                refine ⟨78463870303905078753960749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52309246869270052502640499 78463870303905078753960749)
                ·
                  refine ⟨29423951363964404532735281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78463870303905078753960749 29423951363964404532735281)
                  ·
                    refine ⟨22067963522973303399551461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29423951363964404532735281 22067963522973303399551461)
                    ·
                      refine ⟨4137743160557494387415899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22067963522973303399551461 4137743160557494387415899)
                      ·
                        rfl

theorem cell23_8058226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_8058226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058226 prefixEnd_8058226 := by exact prefixLift 8058226
  have htrace : WordTrace (prefixWord ++ tailWord_8058226) baseStart_8058226 baseEnd_8058226 := by
    simpa [prefixWord, tailWord_8058226, baseEnd_8058226] using wordTrace_append hprefix tailTrace_8058226
  have hstable : (prefixWord ++ tailWord_8058226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058226).length < 2 ^ (prefixWord ++ tailWord_8058226).sum := by decide
  have hdescent : baseEnd_8058226 < baseStart_8058226 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058233 : List Nat := [1, 2, 1, 3, 2, 1, 4, 3, 1, 2, 3]
def baseStart_8058233 : Nat := 118140960795 + 8058233 * 2 ^ 59
def prefixEnd_8058233 : Nat := 4983230072969 + 3 ^ 40 * 8058233 * 2
def baseEnd_8058233 : Nat := 4137746754922075860028367

theorem tailTrace_8058233 : CollatzResearch.WordTrace tailWord_8058233 prefixEnd_8058233 4137746754922075860028367 := by
  unfold tailWord_8058233
  simp only [CollatzResearch.WordTrace]
  refine ⟨293907903015405552473715353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195938602010270368315810235 293907903015405552473715353)
  ·
    refine ⟨220430927261554164355286515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293907903015405552473715353 220430927261554164355286515)
    ·
      refine ⟨330646390892331246532929773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220430927261554164355286515 330646390892331246532929773)
      ·
        refine ⟨123992396584624217449848665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330646390892331246532929773 123992396584624217449848665)
        ·
          refine ⟨92994297438468163087386499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123992396584624217449848665 92994297438468163087386499)
          ·
            refine ⟨139491446157702244631079749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92994297438468163087386499 139491446157702244631079749)
            ·
              refine ⟨26154646154569170868327453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139491446157702244631079749 26154646154569170868327453)
              ·
                refine ⟨9807992307963439075622795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26154646154569170868327453 9807992307963439075622795)
                ·
                  refine ⟨14711988461945158613434193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9807992307963439075622795 14711988461945158613434193)
                  ·
                    refine ⟨11033991346458868960075645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14711988461945158613434193 11033991346458868960075645)
                    ·
                      refine ⟨4137746754922075860028367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11033991346458868960075645 4137746754922075860028367)
                      ·
                        rfl

theorem cell23_8058233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 2, 3].length) (baseStart_8058233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058233 prefixEnd_8058233 := by exact prefixLift 8058233
  have htrace : WordTrace (prefixWord ++ tailWord_8058233) baseStart_8058233 baseEnd_8058233 := by
    simpa [prefixWord, tailWord_8058233, baseEnd_8058233] using wordTrace_append hprefix tailTrace_8058233
  have hstable : (prefixWord ++ tailWord_8058233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058233).length < 2 ^ (prefixWord ++ tailWord_8058233).sum := by decide
  have hdescent : baseEnd_8058233 < baseStart_8058233 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058239 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 6]
def baseStart_8058239 : Nat := 118140960795 + 8058239 * 2 ^ 59
def prefixEnd_8058239 : Nat := 4983230072969 + 3 ^ 40 * 8058239 * 2
def baseEnd_8058239 : Nat := 4137749835806002836553339

theorem tailTrace_8058239 : CollatzResearch.WordTrace tailWord_8058239 prefixEnd_8058239 4137749835806002836553339 := by
  unfold tailWord_8058239
  simp only [CollatzResearch.WordTrace]
  refine ⟨293908121853383815498433771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195938747902255876998955847 293908121853383815498433771)
  ·
    refine ⟨440862182780075723247650657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293908121853383815498433771 440862182780075723247650657)
    ·
      refine ⟨330646637085056792435737993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440862182780075723247650657 330646637085056792435737993)
      ·
        refine ⟨247984977813792594326803495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330646637085056792435737993 247984977813792594326803495)
        ·
          refine ⟨371977466720688891490205243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247984977813792594326803495 371977466720688891490205243)
          ·
            refine ⟨557966200081033337235307865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371977466720688891490205243 557966200081033337235307865)
            ·
              refine ⟨418474650060775002926480899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 557966200081033337235307865 418474650060775002926480899)
              ·
                refine ⟨627711975091162504389721349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418474650060775002926480899 627711975091162504389721349)
                ·
                  refine ⟨117695995329592969573072753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 627711975091162504389721349 117695995329592969573072753)
                  ·
                    refine ⟨88271996497194727179804565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117695995329592969573072753 88271996497194727179804565)
                    ·
                      refine ⟨4137749835806002836553339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88271996497194727179804565 4137749835806002836553339)
                      ·
                        rfl

theorem cell23_8058239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_8058239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058239 prefixEnd_8058239 := by exact prefixLift 8058239
  have htrace : WordTrace (prefixWord ++ tailWord_8058239) baseStart_8058239 baseEnd_8058239 := by
    simpa [prefixWord, tailWord_8058239, baseEnd_8058239] using wordTrace_append hprefix tailTrace_8058239
  have hstable : (prefixWord ++ tailWord_8058239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058239).length < 2 ^ (prefixWord ++ tailWord_8058239).sum := by decide
  have hdescent : baseEnd_8058239 < baseStart_8058239 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058247 : List Nat := [1, 1, 4, 2, 2, 4, 1, 1, 3, 2, 2]
def baseStart_8058247 : Nat := 118140960795 + 8058247 * 2 ^ 59
def prefixEnd_8058247 : Nat := 4983230072969 + 3 ^ 40 * 8058247 * 2
def baseEnd_8058247 : Nat := 4137753943651238805253303

theorem tailTrace_8058247 : CollatzResearch.WordTrace tailWord_8058247 prefixEnd_8058247 4137753943651238805253303 := by
  unfold tailWord_8058247
  simp only [CollatzResearch.WordTrace]
  refine ⟨293908413637354832864724995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195938942424903221909816663 293908413637354832864724995)
  ·
    refine ⟨440862620456032249297087493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293908413637354832864724995 440862620456032249297087493)
    ·
      refine ⟨82661741335506046743203905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 440862620456032249297087493 82661741335506046743203905)
      ·
        refine ⟨61996306001629535057402929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82661741335506046743203905 61996306001629535057402929)
        ·
          refine ⟨46497229501222151293052197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61996306001629535057402929 46497229501222151293052197)
          ·
            refine ⟨8718230531479153367447287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46497229501222151293052197 8718230531479153367447287)
            ·
              refine ⟨13077345797218730051170931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8718230531479153367447287 13077345797218730051170931)
              ·
                refine ⟨19616018695828095076756397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13077345797218730051170931 19616018695828095076756397)
                ·
                  refine ⟨7356007010935535653783649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19616018695828095076756397 7356007010935535653783649)
                  ·
                    refine ⟨5517005258201651740337737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7356007010935535653783649 5517005258201651740337737)
                    ·
                      refine ⟨4137753943651238805253303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5517005258201651740337737 4137753943651238805253303)
                      ·
                        rfl

theorem cell23_8058247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_8058247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058247 prefixEnd_8058247 := by exact prefixLift 8058247
  have htrace : WordTrace (prefixWord ++ tailWord_8058247) baseStart_8058247 baseEnd_8058247 := by
    simpa [prefixWord, tailWord_8058247, baseEnd_8058247] using wordTrace_append hprefix tailTrace_8058247
  have hstable : (prefixWord ++ tailWord_8058247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058247).length < 2 ^ (prefixWord ++ tailWord_8058247).sum := by decide
  have hdescent : baseEnd_8058247 < baseStart_8058247 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058297 : List Nat := [1, 2, 1, 4, 4, 1, 2, 2, 2, 1, 3]
def baseStart_8058297 : Nat := 118140960795 + 8058297 * 2 ^ 59
def prefixEnd_8058297 : Nat := 4983230072969 + 3 ^ 40 * 8058297 * 2
def baseEnd_8058297 : Nat := 4137779617683963609628073

theorem tailTrace_8058297 : CollatzResearch.WordTrace tailWord_8058297 prefixEnd_8058297 4137779617683963609628073 := by
  unfold tailWord_8058297
  simp only [CollatzResearch.WordTrace]
  refine ⟨293910237287173691404045145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195940158191449127602696763 293910237287173691404045145)
  ·
    refine ⟨220432677965380268553033859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293910237287173691404045145 220432677965380268553033859)
    ·
      refine ⟨330649016948070402829550789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220432677965380268553033859 330649016948070402829550789)
      ·
        refine ⟨61996690677763200530540773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 330649016948070402829550789 61996690677763200530540773)
        ·
          refine ⟨11624379502080600099476395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61996690677763200530540773 11624379502080600099476395)
          ·
            refine ⟨17436569253120900149214593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11624379502080600099476395 17436569253120900149214593)
            ·
              refine ⟨13077426939840675111910945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17436569253120900149214593 13077426939840675111910945)
              ·
                refine ⟨9808070204880506333933209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13077426939840675111910945 9808070204880506333933209)
                ·
                  refine ⟨7356052653660379750449907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9808070204880506333933209 7356052653660379750449907)
                  ·
                    refine ⟨11034078980490569625674861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7356052653660379750449907 11034078980490569625674861)
                    ·
                      refine ⟨4137779617683963609628073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11034078980490569625674861 4137779617683963609628073)
                      ·
                        rfl

theorem cell23_8058297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_8058297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058297 prefixEnd_8058297 := by exact prefixLift 8058297
  have htrace : WordTrace (prefixWord ++ tailWord_8058297) baseStart_8058297 baseEnd_8058297 := by
    simpa [prefixWord, tailWord_8058297, baseEnd_8058297] using wordTrace_append hprefix tailTrace_8058297
  have hstable : (prefixWord ++ tailWord_8058297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058297).length < 2 ^ (prefixWord ++ tailWord_8058297).sum := by decide
  have hdescent : baseEnd_8058297 < baseStart_8058297 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058353 : List Nat := [1, 2, 2, 2, 3, 2, 1, 2, 2, 3, 3]
def baseStart_8058353 : Nat := 118140960795 + 8058353 * 2 ^ 59
def prefixEnd_8058353 : Nat := 4983230072969 + 3 ^ 40 * 8058353 * 2
def baseEnd_8058353 : Nat := 4137808372600615390527815

theorem tailTrace_8058353 : CollatzResearch.WordTrace tailWord_8058353 prefixEnd_8058353 4137808372600615390527815 := by
  unfold tailWord_8058353
  simp only [CollatzResearch.WordTrace]
  refine ⟨293912279774970812968083713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195941519849980541978722475 293912279774970812968083713)
  ·
    refine ⟨220434209831228109726062785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293912279774970812968083713 220434209831228109726062785)
    ·
      refine ⟨165325657373421082294547089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220434209831228109726062785 165325657373421082294547089)
      ·
        refine ⟨123994243030065811720910317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165325657373421082294547089 123994243030065811720910317)
        ·
          refine ⟨46497841136274679395341369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123994243030065811720910317 46497841136274679395341369)
          ·
            refine ⟨34873380852206009546506027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46497841136274679395341369 34873380852206009546506027)
            ·
              refine ⟨52310071278309014319759041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34873380852206009546506027 52310071278309014319759041)
              ·
                refine ⟨39232553458731760739819281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52310071278309014319759041 39232553458731760739819281)
                ·
                  refine ⟨29424415094048820554864461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39232553458731760739819281 29424415094048820554864461)
                  ·
                    refine ⟨11034155660268307708074173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29424415094048820554864461 11034155660268307708074173)
                    ·
                      refine ⟨4137808372600615390527815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11034155660268307708074173 4137808372600615390527815)
                      ·
                        rfl

theorem cell23_8058353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 3, 3].length) (baseStart_8058353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058353 prefixEnd_8058353 := by exact prefixLift 8058353
  have htrace : WordTrace (prefixWord ++ tailWord_8058353) baseStart_8058353 baseEnd_8058353 := by
    simpa [prefixWord, tailWord_8058353, baseEnd_8058353] using wordTrace_append hprefix tailTrace_8058353
  have hstable : (prefixWord ++ tailWord_8058353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058353).length < 2 ^ (prefixWord ++ tailWord_8058353).sum := by decide
  have hdescent : baseEnd_8058353 < baseStart_8058353 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058354 : List Nat := [3, 2, 1, 4, 1, 1, 3, 2, 2, 2, 2]
def baseStart_8058354 : Nat := 118140960795 + 8058354 * 2 ^ 59
def prefixEnd_8058354 : Nat := 4983230072969 + 3 ^ 40 * 8058354 * 2
def baseEnd_8058354 : Nat := 4137808886081269886615311

theorem tailTrace_8058354 : CollatzResearch.WordTrace tailWord_8058354 prefixEnd_8058354 4137808886081269886615311 := by
  unfold tailWord_8058354
  simp only [CollatzResearch.WordTrace]
  refine ⟨73478079061991797534717529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195941544165311460092580077 73478079061991797534717529)
  ·
    refine ⟨55108559296493848151038147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73478079061991797534717529 55108559296493848151038147)
    ·
      refine ⟨82662838944740772226557221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55108559296493848151038147 82662838944740772226557221)
      ·
        refine ⟨15499282302138894792479479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82662838944740772226557221 15499282302138894792479479)
        ·
          refine ⟨23248923453208342188719219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15499282302138894792479479 23248923453208342188719219)
          ·
            refine ⟨34873385179812513283078829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23248923453208342188719219 34873385179812513283078829)
            ·
              refine ⟨13077519442429692481154561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34873385179812513283078829 13077519442429692481154561)
              ·
                refine ⟨9808139581822269360865921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13077519442429692481154561 9808139581822269360865921)
                ·
                  refine ⟨7356104686366702020649441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9808139581822269360865921 7356104686366702020649441)
                  ·
                    refine ⟨5517078514775026515487081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7356104686366702020649441 5517078514775026515487081)
                    ·
                      refine ⟨4137808886081269886615311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5517078514775026515487081 4137808886081269886615311)
                      ·
                        rfl

theorem cell23_8058354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_8058354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058354 prefixEnd_8058354 := by exact prefixLift 8058354
  have htrace : WordTrace (prefixWord ++ tailWord_8058354) baseStart_8058354 baseEnd_8058354 := by
    simpa [prefixWord, tailWord_8058354, baseEnd_8058354] using wordTrace_append hprefix tailTrace_8058354
  have hstable : (prefixWord ++ tailWord_8058354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058354).length < 2 ^ (prefixWord ++ tailWord_8058354).sum := by decide
  have hdescent : baseEnd_8058354 < baseStart_8058354 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058410 : List Nat := [3, 1, 4, 1, 1, 1, 3, 2, 2, 1, 4]
def baseStart_8058410 : Nat := 118140960795 + 8058410 * 2 ^ 59
def prefixEnd_8058410 : Nat := 4983230072969 + 3 ^ 40 * 8058410 * 2
def baseEnd_8058410 : Nat := 4137837640997921667515053

theorem tailTrace_8058410 : CollatzResearch.WordTrace tailWord_8058410 prefixEnd_8058410 4137837640997921667515053 := by
  unfold tailWord_8058410
  simp only [CollatzResearch.WordTrace]
  refine ⟨73478589683941077925727171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195942905823842874468605789 73478589683941077925727171)
  ·
    refine ⟨110217884525911616888590757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73478589683941077925727171 110217884525911616888590757)
    ·
      refine ⟨20665853348608428166610767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110217884525911616888590757 20665853348608428166610767)
      ·
        refine ⟨30998780022912642249916151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20665853348608428166610767 30998780022912642249916151)
        ·
          refine ⟨46498170034368963374874227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30998780022912642249916151 46498170034368963374874227)
          ·
            refine ⟨69747255051553445062311341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46498170034368963374874227 69747255051553445062311341)
            ·
              refine ⟨26155220644332541898366753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69747255051553445062311341 26155220644332541898366753)
              ·
                refine ⟨19616415483249406423775065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26155220644332541898366753 19616415483249406423775065)
                ·
                  refine ⟨14712311612437054817831299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19616415483249406423775065 14712311612437054817831299)
                  ·
                    refine ⟨22068467418655582226746949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14712311612437054817831299 22068467418655582226746949)
                    ·
                      refine ⟨4137837640997921667515053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22068467418655582226746949 4137837640997921667515053)
                      ·
                        rfl

theorem cell23_8058410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_8058410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058410 prefixEnd_8058410 := by exact prefixLift 8058410
  have htrace : WordTrace (prefixWord ++ tailWord_8058410) baseStart_8058410 baseEnd_8058410 := by
    simpa [prefixWord, tailWord_8058410, baseEnd_8058410] using wordTrace_append hprefix tailTrace_8058410
  have hstable : (prefixWord ++ tailWord_8058410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058410).length < 2 ^ (prefixWord ++ tailWord_8058410).sum := by decide
  have hdescent : baseEnd_8058410 < baseStart_8058410 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058504 : List Nat := [2, 1, 3, 5, 1, 1, 1, 1, 1, 5, 2]
def baseStart_8058504 : Nat := 118140960795 + 8058504 * 2 ^ 59
def prefixEnd_8058504 : Nat := 4983230072969 + 3 ^ 40 * 8058504 * 2
def baseEnd_8058504 : Nat := 4137885908179444299739621

theorem tailTrace_8058504 : CollatzResearch.WordTrace tailWord_8058504 prefixEnd_8058504 4137885908179444299739621 := by
  unfold tailWord_8058504
  simp only [CollatzResearch.WordTrace]
  refine ⟨146958893598711882878415283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195945191464949177171220377 146958893598711882878415283)
  ·
    refine ⟨220438340398067824317622925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146958893598711882878415283 220438340398067824317622925)
    ·
      refine ⟨82664377649275434119108597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220438340398067824317622925 82664377649275434119108597)
      ·
        refine ⟨7749785404619571948666431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82664377649275434119108597 7749785404619571948666431)
        ·
          refine ⟨11624678106929357922999647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7749785404619571948666431 11624678106929357922999647)
          ·
            refine ⟨17437017160394036884499471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11624678106929357922999647 17437017160394036884499471)
            ·
              refine ⟨26155525740591055326749207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17437017160394036884499471 26155525740591055326749207)
              ·
                refine ⟨39233288610886582990123811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26155525740591055326749207 39233288610886582990123811)
                ·
                  refine ⟨58849932916329874485185717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39233288610886582990123811 58849932916329874485185717)
                  ·
                    refine ⟨5517181210905925732986161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58849932916329874485185717 5517181210905925732986161)
                    ·
                      refine ⟨4137885908179444299739621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5517181210905925732986161 4137885908179444299739621)
                      ·
                        rfl

theorem cell23_8058504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_8058504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058504 prefixEnd_8058504 := by exact prefixLift 8058504
  have htrace : WordTrace (prefixWord ++ tailWord_8058504) baseStart_8058504 baseEnd_8058504 := by
    simpa [prefixWord, tailWord_8058504, baseEnd_8058504] using wordTrace_append hprefix tailTrace_8058504
  have hstable : (prefixWord ++ tailWord_8058504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058504).length < 2 ^ (prefixWord ++ tailWord_8058504).sum := by decide
  have hdescent : baseEnd_8058504 < baseStart_8058504 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058510 : List Nat := [4, 1, 1, 3, 1, 2, 2, 2, 1, 6]
def baseStart_8058510 : Nat := 118140960795 + 8058510 * 2 ^ 59
def prefixEnd_8058510 : Nat := 4983230072969 + 3 ^ 40 * 8058510 * 2
def baseEnd_8058510 : Nat := 1379296329687790425421531

theorem tailTrace_8058510 : CollatzResearch.WordTrace tailWord_8058510 prefixEnd_8058510 1379296329687790425421531 := by
  unfold tailWord_8058510
  simp only [CollatzResearch.WordTrace]
  refine ⟨36739750754425253597693623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195945337356934685854365989 36739750754425253597693623)
  ·
    refine ⟨55109626131637880396540435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36739750754425253597693623 55109626131637880396540435)
    ·
      refine ⟨82664439197456820594810653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55109626131637880396540435 82664439197456820594810653)
      ·
        refine ⟨30999164699046307723053995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82664439197456820594810653 30999164699046307723053995)
        ·
          refine ⟨46498747048569461584580993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30999164699046307723053995 46498747048569461584580993)
          ·
            refine ⟨34874060286427096188435745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46498747048569461584580993 34874060286427096188435745)
            ·
              refine ⟨26155545214820322141326809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34874060286427096188435745 26155545214820322141326809)
              ·
                refine ⟨19616658911115241605995107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26155545214820322141326809 19616658911115241605995107)
                ·
                  refine ⟨29424988366672862408992661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19616658911115241605995107 29424988366672862408992661)
                  ·
                    refine ⟨1379296329687790425421531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29424988366672862408992661 1379296329687790425421531)
                    ·
                      rfl

theorem cell23_8058510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_8058510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058510 prefixEnd_8058510 := by exact prefixLift 8058510
  have htrace : WordTrace (prefixWord ++ tailWord_8058510) baseStart_8058510 baseEnd_8058510 := by
    simpa [prefixWord, tailWord_8058510, baseEnd_8058510] using wordTrace_append hprefix tailTrace_8058510
  have hstable : (prefixWord ++ tailWord_8058510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058510).length < 2 ^ (prefixWord ++ tailWord_8058510).sum := by decide
  have hdescent : baseEnd_8058510 < baseStart_8058510 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058513 : List Nat := [1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 4]
def baseStart_8058513 : Nat := 118140960795 + 8058513 * 2 ^ 59
def prefixEnd_8058513 : Nat := 4983230072969 + 3 ^ 40 * 8058513 * 2
def baseEnd_8058513 : Nat := 4137890529505334764527079

theorem tailTrace_8058513 : CollatzResearch.WordTrace tailWord_8058513 prefixEnd_8058513 4137890529505334764527079 := by
  unfold tailWord_8058513
  simp only [CollatzResearch.WordTrace]
  refine ⟨293918115454391160293908193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195945410302927440195938795 293918115454391160293908193)
  ·
    refine ⟨220438586590793370220431145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293918115454391160293908193 220438586590793370220431145)
    ·
      refine ⟨165328939943095027665323359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220438586590793370220431145 165328939943095027665323359)
      ·
        refine ⟨247993409914642541497985039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165328939943095027665323359 247993409914642541497985039)
        ·
          refine ⟨371990114871963812246977559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247993409914642541497985039 371990114871963812246977559)
          ·
            refine ⟨557985172307945718370466339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371990114871963812246977559 557985172307945718370466339)
            ·
              refine ⟨836977758461918577555699509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557985172307945718370466339 836977758461918577555699509)
              ·
                refine ⟨78466664855804866645846829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 836977758461918577555699509 78466664855804866645846829)
                ·
                  refine ⟨29424999320926824992192561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78466664855804866645846829 29424999320926824992192561)
                  ·
                    refine ⟨22068749490695118744144421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29424999320926824992192561 22068749490695118744144421)
                    ·
                      refine ⟨4137890529505334764527079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22068749490695118744144421 4137890529505334764527079)
                      ·
                        rfl

theorem cell23_8058513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 4].length) (baseStart_8058513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058513 prefixEnd_8058513 := by exact prefixLift 8058513
  have htrace : WordTrace (prefixWord ++ tailWord_8058513) baseStart_8058513 baseEnd_8058513 := by
    simpa [prefixWord, tailWord_8058513, baseEnd_8058513] using wordTrace_append hprefix tailTrace_8058513
  have hstable : (prefixWord ++ tailWord_8058513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058513).length < 2 ^ (prefixWord ++ tailWord_8058513).sum := by decide
  have hdescent : baseEnd_8058513 < baseStart_8058513 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058553 : List Nat := [1, 2, 1, 4, 1, 1, 2, 2, 2, 7]
def baseStart_8058553 : Nat := 118140960795 + 8058553 * 2 ^ 59
def prefixEnd_8058553 : Nat := 4983230072969 + 3 ^ 40 * 8058553 * 2
def baseEnd_8058553 : Nat := 1379303689577171536008965

theorem tailTrace_8058553 : CollatzResearch.WordTrace tailWord_8058553 prefixEnd_8058553 1379303689577171536008965 := by
  unfold tailWord_8058553
  simp only [CollatzResearch.WordTrace]
  refine ⟨293919574374246247125364313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195946382916164164750242875 293919574374246247125364313)
  ·
    refine ⟨220439680780684685344023235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293919574374246247125364313 220439680780684685344023235)
    ·
      refine ⟨330659521171027028016034853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220439680780684685344023235 330659521171027028016034853)
      ·
        refine ⟨61998660219567567753006535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 330659521171027028016034853 61998660219567567753006535)
        ·
          refine ⟨92997990329351351629509803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61998660219567567753006535 92997990329351351629509803)
          ·
            refine ⟨139496985494027027444264705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92997990329351351629509803 139496985494027027444264705)
            ·
              refine ⟨104622739120520270583198529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139496985494027027444264705 104622739120520270583198529)
              ·
                refine ⟨78467054340390202937398897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104622739120520270583198529 78467054340390202937398897)
                ·
                  refine ⟨58850290755292652203049173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78467054340390202937398897 58850290755292652203049173)
                  ·
                    refine ⟨1379303689577171536008965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58850290755292652203049173 1379303689577171536008965)
                    ·
                      rfl

theorem cell23_8058553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 7].length) (baseStart_8058553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058553 prefixEnd_8058553 := by exact prefixLift 8058553
  have htrace : WordTrace (prefixWord ++ tailWord_8058553) baseStart_8058553 baseEnd_8058553 := by
    simpa [prefixWord, tailWord_8058553, baseEnd_8058553] using wordTrace_append hprefix tailTrace_8058553
  have hstable : (prefixWord ++ tailWord_8058553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058553).length < 2 ^ (prefixWord ++ tailWord_8058553).sum := by decide
  have hdescent : baseEnd_8058553 < baseStart_8058553 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058562 : List Nat := [3, 5, 1, 2, 1, 2, 1, 3, 1, 1, 3]
def baseStart_8058562 : Nat := 118140960795 + 8058562 * 2 ^ 59
def prefixEnd_8058562 : Nat := 4983230072969 + 3 ^ 40 * 8058562 * 2
def baseEnd_8058562 : Nat := 4137915690057405072814355

theorem tailTrace_8058562 : CollatzResearch.WordTrace tailWord_8058562 prefixEnd_8058562 4137915690057405072814355 := by
  unfold tailWord_8058562
  simp only [CollatzResearch.WordTrace]
  refine ⟨73479975657803410415610485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195946601754142427774961293 73479975657803410415610485)
  ·
    refine ⟨6888747717919069726463483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73479975657803410415610485 6888747717919069726463483)
    ·
      refine ⟨10333121576878604589695225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6888747717919069726463483 10333121576878604589695225)
      ·
        refine ⟨7749841182658953442271419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10333121576878604589695225 7749841182658953442271419)
        ·
          refine ⟨11624761773988430163407129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7749841182658953442271419 11624761773988430163407129)
          ·
            refine ⟨8718571330491322622555347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11624761773988430163407129 8718571330491322622555347)
            ·
              refine ⟨13077856995736983933833021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8718571330491322622555347 13077856995736983933833021)
              ·
                refine ⟨4904196373401368975187383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13077856995736983933833021 4904196373401368975187383)
                ·
                  refine ⟨7356294560102053462781075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4904196373401368975187383 7356294560102053462781075)
                  ·
                    refine ⟨11034441840153080194171613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7356294560102053462781075 11034441840153080194171613)
                    ·
                      refine ⟨4137915690057405072814355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11034441840153080194171613 4137915690057405072814355)
                      ·
                        rfl

theorem cell23_8058562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_8058562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058562 prefixEnd_8058562 := by exact prefixLift 8058562
  have htrace : WordTrace (prefixWord ++ tailWord_8058562) baseStart_8058562 baseEnd_8058562 := by
    simpa [prefixWord, tailWord_8058562, baseEnd_8058562] using wordTrace_append hprefix tailTrace_8058562
  have hstable : (prefixWord ++ tailWord_8058562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058562).length < 2 ^ (prefixWord ++ tailWord_8058562).sum := by decide
  have hdescent : baseEnd_8058562 < baseStart_8058562 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058607 : List Nat := [1, 1, 2, 1, 5, 1, 2, 3, 1, 4, 2]
def baseStart_8058607 : Nat := 118140960795 + 8058607 * 2 ^ 59
def prefixEnd_8058607 : Nat := 4983230072969 + 3 ^ 40 * 8058607 * 2
def baseEnd_8058607 : Nat := 4137938796686857396751647

theorem tailTrace_8058607 : CollatzResearch.WordTrace tailWord_8058607 prefixEnd_8058607 4137938796686857396751647 := by
  unfold tailWord_8058607
  simp only [CollatzResearch.WordTrace]
  refine ⟨293921543916050614347830075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195947695944033742898553383 293921543916050614347830075)
  ·
    refine ⟨440882315874075921521745113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293921543916050614347830075 440882315874075921521745113)
    ·
      refine ⟨330661736905556941141308835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440882315874075921521745113 330661736905556941141308835)
      ·
        refine ⟨495992605358335411711963253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330661736905556941141308835 495992605358335411711963253)
        ·
          refine ⟨46499306752343944847996555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 495992605358335411711963253 46499306752343944847996555)
          ·
            refine ⟨69748960128515917271994833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46499306752343944847996555 69748960128515917271994833)
            ·
              refine ⟨52311720096386937953996125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69748960128515917271994833 52311720096386937953996125)
              ·
                refine ⟨19616895036145101732748547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52311720096386937953996125 19616895036145101732748547)
                ·
                  refine ⟨29425342554217652599122821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19616895036145101732748547 29425342554217652599122821)
                  ·
                    refine ⟨5517251728915809862335529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29425342554217652599122821 5517251728915809862335529)
                    ·
                      refine ⟨4137938796686857396751647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5517251728915809862335529 4137938796686857396751647)
                      ·
                        rfl

theorem cell23_8058607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 4, 2].length) (baseStart_8058607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058607 prefixEnd_8058607 := by exact prefixLift 8058607
  have htrace : WordTrace (prefixWord ++ tailWord_8058607) baseStart_8058607 baseEnd_8058607 := by
    simpa [prefixWord, tailWord_8058607, baseEnd_8058607] using wordTrace_append hprefix tailTrace_8058607
  have hstable : (prefixWord ++ tailWord_8058607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058607).length < 2 ^ (prefixWord ++ tailWord_8058607).sum := by decide
  have hdescent : baseEnd_8058607 < baseStart_8058607 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058610 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 4, 1, 5]
def baseStart_8058610 : Nat := 118140960795 + 8058610 * 2 ^ 59
def prefixEnd_8058610 : Nat := 4983230072969 + 3 ^ 40 * 8058610 * 2
def baseEnd_8058610 : Nat := 4137940337128820885014133

theorem tailTrace_8058610 : CollatzResearch.WordTrace tailWord_8058610 prefixEnd_8058610 4137940337128820885014133 := by
  unfold tailWord_8058610
  simp only [CollatzResearch.WordTrace]
  refine ⟨73480413333759936465047321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195947768890026497240126189 73480413333759936465047321)
  ·
    refine ⟨55110310000319952348785491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73480413333759936465047321 55110310000319952348785491)
    ·
      refine ⟨82665465000479928523178237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55110310000319952348785491 82665465000479928523178237)
      ·
        refine ⟨30999549375179973196191839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82665465000479928523178237 30999549375179973196191839)
        ·
          refine ⟨46499324062769959794287759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30999549375179973196191839 46499324062769959794287759)
          ·
            refine ⟨69748986094154939691431639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46499324062769959794287759 69748986094154939691431639)
            ·
              refine ⟨104623479141232409537147459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69748986094154939691431639 104623479141232409537147459)
              ·
                refine ⟨156935218711848614305721189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104623479141232409537147459 156935218711848614305721189)
                ·
                  refine ⟨29425353508471615182322723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156935218711848614305721189 29425353508471615182322723)
                  ·
                    refine ⟨44138030262707422773484085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29425353508471615182322723 44138030262707422773484085)
                    ·
                      refine ⟨4137940337128820885014133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44138030262707422773484085 4137940337128820885014133)
                      ·
                        rfl

theorem cell23_8058610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_8058610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058610 prefixEnd_8058610 := by exact prefixLift 8058610
  have htrace : WordTrace (prefixWord ++ tailWord_8058610) baseStart_8058610 baseEnd_8058610 := by
    simpa [prefixWord, tailWord_8058610, baseEnd_8058610] using wordTrace_append hprefix tailTrace_8058610
  have hstable : (prefixWord ++ tailWord_8058610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058610).length < 2 ^ (prefixWord ++ tailWord_8058610).sum := by decide
  have hdescent : baseEnd_8058610 < baseStart_8058610 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058657 : List Nat := [1, 2, 3, 2, 1, 4, 1, 1, 2, 3, 3]
def baseStart_8058657 : Nat := 118140960795 + 8058657 * 2 ^ 59
def prefixEnd_8058657 : Nat := 4983230072969 + 3 ^ 40 * 8058657 * 2
def baseEnd_8058657 : Nat := 4137964470719582201126417

theorem tailTrace_8058657 : CollatzResearch.WordTrace tailWord_8058657 prefixEnd_8058657 4137964470719582201126417 := by
  unfold tailWord_8058657
  simp only [CollatzResearch.WordTrace]
  refine ⟨293923367565869472887150225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195948911710579648591433483 293923367565869472887150225)
  ·
    refine ⟨220442525674402104665362669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293923367565869472887150225 220442525674402104665362669)
    ·
      refine ⟨82665947127900789249511001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220442525674402104665362669 82665947127900789249511001)
      ·
        refine ⟨61999460345925591937133251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82665947127900789249511001 61999460345925591937133251)
        ·
          refine ⟨92999190518888387905699877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61999460345925591937133251 92999190518888387905699877)
          ·
            refine ⟨17437348222291572732318727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92999190518888387905699877 17437348222291572732318727)
            ·
              refine ⟨26156022333437359098478091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17437348222291572732318727 26156022333437359098478091)
              ·
                refine ⟨39234033500156038647717137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26156022333437359098478091 39234033500156038647717137)
                ·
                  refine ⟨29425525125117028985787853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39234033500156038647717137 29425525125117028985787853)
                  ·
                    refine ⟨11034571921918885869670445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29425525125117028985787853 11034571921918885869670445)
                    ·
                      refine ⟨4137964470719582201126417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11034571921918885869670445 4137964470719582201126417)
                      ·
                        rfl

theorem cell23_8058657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_8058657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058657 prefixEnd_8058657 := by exact prefixLift 8058657
  have htrace : WordTrace (prefixWord ++ tailWord_8058657) baseStart_8058657 baseEnd_8058657 := by
    simpa [prefixWord, tailWord_8058657, baseEnd_8058657] using wordTrace_append hprefix tailTrace_8058657
  have hstable : (prefixWord ++ tailWord_8058657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058657).length < 2 ^ (prefixWord ++ tailWord_8058657).sum := by decide
  have hdescent : baseEnd_8058657 < baseStart_8058657 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058677 : List Nat := [1, 3, 3, 1, 4, 1, 1, 1, 1, 7]
def baseStart_8058677 : Nat := 118140960795 + 8058677 * 2 ^ 59
def prefixEnd_8058677 : Nat := 4983230072969 + 3 ^ 40 * 8058677 * 2
def baseEnd_8058677 : Nat := 1379324913444224040958775

theorem tailTrace_8058677 : CollatzResearch.WordTrace tailWord_8058677 prefixEnd_8058677 1379324913444224040958775 := by
  unfold tailWord_8058677
  simp only [CollatzResearch.WordTrace]
  refine ⟨293924097025797016302878285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195949398017198010868585523 293924097025797016302878285)
  ·
    refine ⟨110221536384673881113579357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293924097025797016302878285 110221536384673881113579357)
    ·
      refine ⟨41333076144252705417592259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110221536384673881113579357 41333076144252705417592259)
      ·
        refine ⟨61999614216379058126388389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41333076144252705417592259 61999614216379058126388389)
        ·
          refine ⟨11624927665571073398697823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61999614216379058126388389 11624927665571073398697823)
          ·
            refine ⟨17437391498356610098046735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11624927665571073398697823 17437391498356610098046735)
            ·
              refine ⟨26156087247534915147070103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17437391498356610098046735 26156087247534915147070103)
              ·
                refine ⟨39234130871302372720605155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26156087247534915147070103 39234130871302372720605155)
                ·
                  refine ⟨58851196306953559080907733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39234130871302372720605155 58851196306953559080907733)
                  ·
                    refine ⟨1379324913444224040958775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58851196306953559080907733 1379324913444224040958775)
                    ·
                      rfl

theorem cell23_8058677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_8058677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058677 prefixEnd_8058677 := by exact prefixLift 8058677
  have htrace : WordTrace (prefixWord ++ tailWord_8058677) baseStart_8058677 baseEnd_8058677 := by
    simpa [prefixWord, tailWord_8058677, baseEnd_8058677] using wordTrace_append hprefix tailTrace_8058677
  have hstable : (prefixWord ++ tailWord_8058677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058677).length < 2 ^ (prefixWord ++ tailWord_8058677).sum := by decide
  have hdescent : baseEnd_8058677 < baseStart_8058677 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058681 : List Nat := [1, 2, 1, 7, 1, 1, 2, 3, 5]
def baseStart_8058681 : Nat := 118140960795 + 8058681 * 2 ^ 59
def prefixEnd_8058681 : Nat := 4983230072969 + 3 ^ 40 * 8058681 * 2
def baseEnd_8058681 : Nat := 459775199361698900802923

theorem tailTrace_8058681 : CollatzResearch.WordTrace tailWord_8058681 prefixEnd_8058681 459775199361698900802923 := by
  unfold tailWord_8058681
  simp only [CollatzResearch.WordTrace]
  refine ⟨293924242917782524986023897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195949495278521683324015931 293924242917782524986023897)
  ·
    refine ⟨220443182188336893739517923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293924242917782524986023897 220443182188336893739517923)
    ·
      refine ⟨330664773282505340609276885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220443182188336893739517923 330664773282505340609276885)
      ·
        refine ⟨7749955623808718920529927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 330664773282505340609276885 7749955623808718920529927)
        ·
          refine ⟨11624933435713078380794891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7749955623808718920529927 11624933435713078380794891)
          ·
            refine ⟨17437400153569617571192337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11624933435713078380794891 17437400153569617571192337)
            ·
              refine ⟨13078050115177213178394253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17437400153569617571192337 13078050115177213178394253)
              ·
                refine ⟨4904268793191454941897845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13078050115177213178394253 4904268793191454941897845)
                ·
                  refine ⟨459775199361698900802923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4904268793191454941897845 459775199361698900802923)
                  ·
                    rfl

theorem cell23_8058681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 3, 5].length) (baseStart_8058681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058681 prefixEnd_8058681 := by exact prefixLift 8058681
  have htrace : WordTrace (prefixWord ++ tailWord_8058681) baseStart_8058681 baseEnd_8058681 := by
    simpa [prefixWord, tailWord_8058681, baseEnd_8058681] using wordTrace_append hprefix tailTrace_8058681
  have hstable : (prefixWord ++ tailWord_8058681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058681).length < 2 ^ (prefixWord ++ tailWord_8058681).sum := by decide
  have hdescent : baseEnd_8058681 < baseStart_8058681 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058697 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 4, 4, 2]
def baseStart_8058697 : Nat := 118140960795 + 8058697 * 2 ^ 59
def prefixEnd_8058697 : Nat := 4983230072969 + 3 ^ 40 * 8058697 * 2
def baseEnd_8058697 : Nat := 4137985009945762044626233

theorem tailTrace_8058697 : CollatzResearch.WordTrace tailWord_8058697 prefixEnd_8058697 4137985009945762044626233 := by
  unfold tailWord_8058697
  simp only [CollatzResearch.WordTrace]
  refine ⟨293924826485724559718606345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195949884323816373145737563 293924826485724559718606345)
  ·
    refine ⟨220443619864293419788954759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293924826485724559718606345 220443619864293419788954759)
    ·
      refine ⟨330665429796440129683432139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220443619864293419788954759 330665429796440129683432139)
      ·
        refine ⟨495998144694660194525148209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330665429796440129683432139 495998144694660194525148209)
        ·
          refine ⟨371998608520995145893861157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 495998144694660194525148209 371998608520995145893861157)
          ·
            refine ⟨69749739097686589855098967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 371998608520995145893861157 69749739097686589855098967)
            ·
              refine ⟨104624608646529884782648451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69749739097686589855098967 104624608646529884782648451)
              ·
                refine ⟨156936912969794827173972677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104624608646529884782648451 156936912969794827173972677)
                ·
                  refine ⟨29425671181836530095119877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156936912969794827173972677 29425671181836530095119877)
                  ·
                    refine ⟨5517313346594349392834977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29425671181836530095119877 5517313346594349392834977)
                    ·
                      refine ⟨4137985009945762044626233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5517313346594349392834977 4137985009945762044626233)
                      ·
                        rfl

theorem cell23_8058697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 4, 2].length) (baseStart_8058697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058697 prefixEnd_8058697 := by exact prefixLift 8058697
  have htrace : WordTrace (prefixWord ++ tailWord_8058697) baseStart_8058697 baseEnd_8058697 := by
    simpa [prefixWord, tailWord_8058697, baseEnd_8058697] using wordTrace_append hprefix tailTrace_8058697
  have hstable : (prefixWord ++ tailWord_8058697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058697).length < 2 ^ (prefixWord ++ tailWord_8058697).sum := by decide
  have hdescent : baseEnd_8058697 < baseStart_8058697 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058734 : List Nat := [4, 1, 2, 3, 1, 1, 2, 1, 1, 4, 3]
def baseStart_8058734 : Nat := 118140960795 + 8058734 * 2 ^ 59
def prefixEnd_8058734 : Nat := 4983230072969 + 3 ^ 40 * 8058734 * 2
def baseEnd_8058734 : Nat := 4138004008729978399863563

theorem tailTrace_8058734 : CollatzResearch.WordTrace tailWord_8058734 prefixEnd_8058734 4138004008729978399863563 := by
  unfold tailWord_8058734
  simp only [CollatzResearch.WordTrace]
  refine ⟨36740771998323814379712907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195950783991060343358468837 36740771998323814379712907)
  ·
    refine ⟨55111157997485721569569361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36740771998323814379712907 55111157997485721569569361)
    ·
      refine ⟨41333368498114291177177021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55111157997485721569569361 41333368498114291177177021)
      ·
        refine ⟨15500013186792859191441383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41333368498114291177177021 15500013186792859191441383)
        ·
          refine ⟨23250019780189288787162075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15500013186792859191441383 23250019780189288787162075)
          ·
            refine ⟨34875029670283933180743113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23250019780189288787162075 34875029670283933180743113)
            ·
              refine ⟨26156272252712949885557335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34875029670283933180743113 26156272252712949885557335)
              ·
                refine ⟨39234408379069424828336003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26156272252712949885557335 39234408379069424828336003)
                ·
                  refine ⟨58851612568604137242504005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39234408379069424828336003 58851612568604137242504005)
                  ·
                    refine ⟨11034677356613275732969501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58851612568604137242504005 11034677356613275732969501)
                    ·
                      refine ⟨4138004008729978399863563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11034677356613275732969501 4138004008729978399863563)
                      ·
                        rfl

theorem cell23_8058734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_8058734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058734 prefixEnd_8058734 := by exact prefixLift 8058734
  have htrace : WordTrace (prefixWord ++ tailWord_8058734) baseStart_8058734 baseEnd_8058734 := by
    simpa [prefixWord, tailWord_8058734, baseEnd_8058734] using wordTrace_append hprefix tailTrace_8058734
  have hstable : (prefixWord ++ tailWord_8058734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058734).length < 2 ^ (prefixWord ++ tailWord_8058734).sum := by decide
  have hdescent : baseEnd_8058734 < baseStart_8058734 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058791 : List Nat := [1, 1, 6, 1, 2, 1, 1, 3, 2, 3, 2]
def baseStart_8058791 : Nat := 118140960795 + 8058791 * 2 ^ 59
def prefixEnd_8058791 : Nat := 4983230072969 + 3 ^ 40 * 8058791 * 2
def baseEnd_8058791 : Nat := 4138033277127284676850801

theorem tailTrace_8058791 : CollatzResearch.WordTrace tailWord_8058791 prefixEnd_8058791 4138033277127284676850801 := by
  unfold tailWord_8058791
  simp only [CollatzResearch.WordTrace]
  refine ⟨293928254947384013772528227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195952169964922675848352151 293928254947384013772528227)
  ·
    refine ⟨440892382421076020658792341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293928254947384013772528227 440892382421076020658792341)
    ·
      refine ⟨20666830425987938468380891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 440892382421076020658792341 20666830425987938468380891)
      ·
        refine ⟨31000245638981907702571337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20666830425987938468380891 31000245638981907702571337)
        ·
          refine ⟨23250184229236430776928503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31000245638981907702571337 23250184229236430776928503)
          ·
            refine ⟨34875276343854646165392755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23250184229236430776928503 34875276343854646165392755)
            ·
              refine ⟨52312914515781969248089133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34875276343854646165392755 52312914515781969248089133)
              ·
                refine ⟨19617342943418238468033425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52312914515781969248089133 19617342943418238468033425)
                ·
                  refine ⟨14713007207563678851025069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19617342943418238468033425 14713007207563678851025069)
                  ·
                    refine ⟨5517377702836379569134401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14713007207563678851025069 5517377702836379569134401)
                    ·
                      refine ⟨4138033277127284676850801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5517377702836379569134401 4138033277127284676850801)
                      ·
                        rfl

theorem cell23_8058791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_8058791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058791 prefixEnd_8058791 := by exact prefixLift 8058791
  have htrace : WordTrace (prefixWord ++ tailWord_8058791) baseStart_8058791 baseEnd_8058791 := by
    simpa [prefixWord, tailWord_8058791, baseEnd_8058791] using wordTrace_append hprefix tailTrace_8058791
  have hstable : (prefixWord ++ tailWord_8058791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058791).length < 2 ^ (prefixWord ++ tailWord_8058791).sum := by decide
  have hdescent : baseEnd_8058791 < baseStart_8058791 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058800 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 6]
def baseStart_8058800 : Nat := 118140960795 + 8058800 * 2 ^ 59
def prefixEnd_8058800 : Nat := 4983230072969 + 3 ^ 40 * 8058800 * 2
def baseEnd_8058800 : Nat := 4138037898453175141638259

theorem tailTrace_8058800 : CollatzResearch.WordTrace tailWord_8058800 prefixEnd_8058800 4138037898453175141638259 := by
  unfold tailWord_8058800
  simp only [CollatzResearch.WordTrace]
  refine ⟨146964291602175704154802927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195952388802900938873070569 146964291602175704154802927)
  ·
    refine ⟨220446437403263556232204391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146964291602175704154802927 220446437403263556232204391)
    ·
      refine ⟨330669656104895334348306587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220446437403263556232204391 330669656104895334348306587)
      ·
        refine ⟨496004484157343001522459881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330669656104895334348306587 496004484157343001522459881)
        ·
          refine ⟨372003363118007251141844911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 496004484157343001522459881 372003363118007251141844911)
          ·
            refine ⟨558005044677010876712767367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372003363118007251141844911 558005044677010876712767367)
            ·
              refine ⟨837007567015516315069151051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558005044677010876712767367 837007567015516315069151051)
              ·
                refine ⟨1255511350523274472603726577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 837007567015516315069151051 1255511350523274472603726577)
                ·
                  refine ⟨941633512892455854452794933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1255511350523274472603726577 941633512892455854452794933)
                  ·
                    refine ⟨88278141833667736354949525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 941633512892455854452794933 88278141833667736354949525)
                    ·
                      refine ⟨4138037898453175141638259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88278141833667736354949525 4138037898453175141638259)
                      ·
                        rfl

theorem cell23_8058800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 6].length) (baseStart_8058800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058800 prefixEnd_8058800 := by exact prefixLift 8058800
  have htrace : WordTrace (prefixWord ++ tailWord_8058800) baseStart_8058800 baseEnd_8058800 := by
    simpa [prefixWord, tailWord_8058800, baseEnd_8058800] using wordTrace_append hprefix tailTrace_8058800
  have hstable : (prefixWord ++ tailWord_8058800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058800).length < 2 ^ (prefixWord ++ tailWord_8058800).sum := by decide
  have hdescent : baseEnd_8058800 < baseStart_8058800 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058801 : List Nat := [1, 2, 2, 4, 2, 2, 3, 1, 1, 5]
def baseStart_8058801 : Nat := 118140960795 + 8058801 * 2 ^ 59
def prefixEnd_8058801 : Nat := 4983230072969 + 3 ^ 40 * 8058801 * 2
def baseEnd_8058801 : Nat := 1379346137311276545908585

theorem tailTrace_8058801 : CollatzResearch.WordTrace tailWord_8058801 prefixEnd_8058801 1379346137311276545908585 := by
  unfold tailWord_8058801
  simp only [CollatzResearch.WordTrace]
  refine ⟨293928619677347785480392257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195952413118231856986928171 293928619677347785480392257)
  ·
    refine ⟨220446464758010839110294193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293928619677347785480392257 220446464758010839110294193)
    ·
      refine ⟨165334848568508129332720645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220446464758010839110294193 165334848568508129332720645)
      ·
        refine ⟨31000284106595274249885121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165334848568508129332720645 31000284106595274249885121)
        ·
          refine ⟨23250213079946455687413841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31000284106595274249885121 23250213079946455687413841)
          ·
            refine ⟨17437659809959841765560381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23250213079946455687413841 17437659809959841765560381)
            ·
              refine ⟨6539122428734940662085143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17437659809959841765560381 6539122428734940662085143)
              ·
                refine ⟨9808683643102410993127715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6539122428734940662085143 9808683643102410993127715)
                ·
                  refine ⟨14713025464653616489691573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9808683643102410993127715 14713025464653616489691573)
                  ·
                    refine ⟨1379346137311276545908585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14713025464653616489691573 1379346137311276545908585)
                    ·
                      rfl

theorem cell23_8058801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 1, 5].length) (baseStart_8058801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058801 prefixEnd_8058801 := by exact prefixLift 8058801
  have htrace : WordTrace (prefixWord ++ tailWord_8058801) baseStart_8058801 baseEnd_8058801 := by
    simpa [prefixWord, tailWord_8058801, baseEnd_8058801] using wordTrace_append hprefix tailTrace_8058801
  have hstable : (prefixWord ++ tailWord_8058801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058801).length < 2 ^ (prefixWord ++ tailWord_8058801).sum := by decide
  have hdescent : baseEnd_8058801 < baseStart_8058801 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058824 : List Nat := [2, 1, 3, 1, 4, 1, 1, 2, 3, 2, 3]
def baseStart_8058824 : Nat := 118140960795 + 8058824 * 2 ^ 59
def prefixEnd_8058824 : Nat := 4983230072969 + 3 ^ 40 * 8058824 * 2
def baseEnd_8058824 : Nat := 4138050221988883047738149

theorem tailTrace_8058824 : CollatzResearch.WordTrace tailWord_8058824 prefixEnd_8058824 4138050221988883047738149 := by
  unfold tailWord_8058824
  simp only [CollatzResearch.WordTrace]
  refine ⟨146964729278132230204239763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195952972370842973605653017 146964729278132230204239763)
  ·
    refine ⟨220447093917198345306359645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146964729278132230204239763 220447093917198345306359645)
    ·
      refine ⟨82667660218949379489884867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220447093917198345306359645 82667660218949379489884867)
      ·
        refine ⟨124001490328424069234827301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82667660218949379489884867 124001490328424069234827301)
        ·
          refine ⟨23250279436579512981530119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124001490328424069234827301 23250279436579512981530119)
          ·
            refine ⟨34875419154869269472295179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23250279436579512981530119 34875419154869269472295179)
            ·
              refine ⟨52313128732303904208442769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34875419154869269472295179 52313128732303904208442769)
              ·
                refine ⟨39234846549227928156332077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52313128732303904208442769 39234846549227928156332077)
                ·
                  refine ⟨14713067455960473058624529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39234846549227928156332077 14713067455960473058624529)
                  ·
                    refine ⟨11034800591970354793968397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14713067455960473058624529 11034800591970354793968397)
                    ·
                      refine ⟨4138050221988883047738149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11034800591970354793968397 4138050221988883047738149)
                      ·
                        rfl

theorem cell23_8058824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 3, 2, 3].length) (baseStart_8058824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058824 prefixEnd_8058824 := by exact prefixLift 8058824
  have htrace : WordTrace (prefixWord ++ tailWord_8058824) baseStart_8058824 baseEnd_8058824 := by
    simpa [prefixWord, tailWord_8058824, baseEnd_8058824] using wordTrace_append hprefix tailTrace_8058824
  have hstable : (prefixWord ++ tailWord_8058824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058824).length < 2 ^ (prefixWord ++ tailWord_8058824).sum := by decide
  have hdescent : baseEnd_8058824 < baseStart_8058824 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058855 : List Nat := [1, 1, 5, 2, 4, 1, 2, 1, 1, 1, 4]
def baseStart_8058855 : Nat := 118140960795 + 8058855 * 2 ^ 59
def prefixEnd_8058855 : Nat := 4983230072969 + 3 ^ 40 * 8058855 * 2
def baseEnd_8058855 : Nat := 4138066139889172426450507

theorem tailTrace_8058855 : CollatzResearch.WordTrace tailWord_8058855 prefixEnd_8058855 4138066139889172426450507 := by
  unfold tailWord_8058855
  simp only [CollatzResearch.WordTrace]
  refine ⟨293930589219152152702858019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195953726146101435135238679 293930589219152152702858019)
  ·
    refine ⟨440895883828728229054287029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293930589219152152702858019 440895883828728229054287029)
    ·
      refine ⟨41333989108943271473839409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 440895883828728229054287029 41333989108943271473839409)
      ·
        refine ⟨31000491831707453605379557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41333989108943271473839409 31000491831707453605379557)
        ·
          refine ⟨5812592218445147551008667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31000491831707453605379557 5812592218445147551008667)
          ·
            refine ⟨8718888327667721326513001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5812592218445147551008667 8718888327667721326513001)
            ·
              refine ⟨6539166245750790994884751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8718888327667721326513001 6539166245750790994884751)
              ·
                refine ⟨9808749368626186492327127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6539166245750790994884751 9808749368626186492327127)
                ·
                  refine ⟨14713124052939279738490691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9808749368626186492327127 14713124052939279738490691)
                  ·
                    refine ⟨22069686079408919607736037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14713124052939279738490691 22069686079408919607736037)
                    ·
                      refine ⟨4138066139889172426450507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22069686079408919607736037 4138066139889172426450507)
                      ·
                        rfl

theorem cell23_8058855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_8058855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058855 prefixEnd_8058855 := by exact prefixLift 8058855
  have htrace : WordTrace (prefixWord ++ tailWord_8058855) baseStart_8058855 baseEnd_8058855 := by
    simpa [prefixWord, tailWord_8058855, baseEnd_8058855] using wordTrace_append hprefix tailTrace_8058855
  have hstable : (prefixWord ++ tailWord_8058855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058855).length < 2 ^ (prefixWord ++ tailWord_8058855).sum := by decide
  have hdescent : baseEnd_8058855 < baseStart_8058855 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058877 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 1, 5, 4]
def baseStart_8058877 : Nat := 118140960795 + 8058877 * 2 ^ 59
def prefixEnd_8058877 : Nat := 4983230072969 + 3 ^ 40 * 8058877 * 2
def baseEnd_8058877 : Nat := 4138077436463571340375405

theorem tailTrace_8058877 : CollatzResearch.WordTrace tailWord_8058877 prefixEnd_8058877 4138077436463571340375405 := by
  unfold tailWord_8058877
  simp only [CollatzResearch.WordTrace]
  refine ⟨293931391625072450460158885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195954261083381633640105923 293931391625072450460158885)
  ·
    refine ⟨55112135929701084461279791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293931391625072450460158885 55112135929701084461279791)
    ·
      refine ⟨82668203894551626691919687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55112135929701084461279791 82668203894551626691919687)
      ·
        refine ⟨124002305841827440037879531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82668203894551626691919687 124002305841827440037879531)
        ·
          refine ⟨186003458762741160056819297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124002305841827440037879531 186003458762741160056819297)
          ·
            refine ⟨139502594072055870042614473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186003458762741160056819297 139502594072055870042614473)
            ·
              refine ⟨104626945554041902531960855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139502594072055870042614473 104626945554041902531960855)
              ·
                refine ⟨156940418331062853797941283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104626945554041902531960855 156940418331062853797941283)
                ·
                  refine ⟨235410627496594280696911925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156940418331062853797941283 235410627496594280696911925)
                  ·
                    refine ⟨22069746327805713815335493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 235410627496594280696911925 22069746327805713815335493)
                    ·
                      refine ⟨4138077436463571340375405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22069746327805713815335493 4138077436463571340375405)
                      ·
                        rfl

theorem cell23_8058877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_8058877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058877 prefixEnd_8058877 := by exact prefixLift 8058877
  have htrace : WordTrace (prefixWord ++ tailWord_8058877) baseStart_8058877 baseEnd_8058877 := by
    simpa [prefixWord, tailWord_8058877, baseEnd_8058877] using wordTrace_append hprefix tailTrace_8058877
  have hstable : (prefixWord ++ tailWord_8058877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058877).length < 2 ^ (prefixWord ++ tailWord_8058877).sum := by decide
  have hdescent : baseEnd_8058877 < baseStart_8058877 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058888 : List Nat := [2, 1, 3, 2, 1, 2, 5, 1, 2, 1, 3]
def baseStart_8058888 : Nat := 118140960795 + 8058888 * 2 ^ 59
def prefixEnd_8058888 : Nat := 4983230072969 + 3 ^ 40 * 8058888 * 2
def baseEnd_8058888 : Nat := 4138083084750770797337855

theorem tailTrace_8058888 : CollatzResearch.WordTrace tailWord_8058888 prefixEnd_8058888 4138083084750770797337855 := by
  unfold tailWord_8058888
  simp only [CollatzResearch.WordTrace]
  refine ⟨146965896414016299669404659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195954528552021732892539545 146965896414016299669404659)
  ·
    refine ⟨220448844621024449504106989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146965896414016299669404659 220448844621024449504106989)
    ·
      refine ⟨82668316732884168564040121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220448844621024449504106989 82668316732884168564040121)
      ·
        refine ⟨62001237549663126423030091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82668316732884168564040121 62001237549663126423030091)
        ·
          refine ⟨93001856324494689634545137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62001237549663126423030091 93001856324494689634545137)
          ·
            refine ⟨69751392243371017225908853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93001856324494689634545137 69751392243371017225908853)
            ·
              refine ⟨6539193022816032864928955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69751392243371017225908853 6539193022816032864928955)
              ·
                refine ⟨9808789534224049297393433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6539193022816032864928955 9808789534224049297393433)
                ·
                  refine ⟨7356592150668036973045075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9808789534224049297393433 7356592150668036973045075)
                  ·
                    refine ⟨11034888226002055459567613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7356592150668036973045075 11034888226002055459567613)
                    ·
                      refine ⟨4138083084750770797337855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11034888226002055459567613 4138083084750770797337855)
                      ·
                        rfl

theorem cell23_8058888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_8058888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058888 prefixEnd_8058888 := by exact prefixLift 8058888
  have htrace : WordTrace (prefixWord ++ tailWord_8058888) baseStart_8058888 baseEnd_8058888 := by
    simpa [prefixWord, tailWord_8058888, baseEnd_8058888] using wordTrace_append hprefix tailTrace_8058888
  have hstable : (prefixWord ++ tailWord_8058888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058888).length < 2 ^ (prefixWord ++ tailWord_8058888).sum := by decide
  have hdescent : baseEnd_8058888 < baseStart_8058888 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058907 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 4]
def baseStart_8058907 : Nat := 118140960795 + 8058907 * 2 ^ 59
def prefixEnd_8058907 : Nat := 4983230072969 + 3 ^ 40 * 8058907 * 2
def baseEnd_8058907 : Nat := 4138092840883206223000267

theorem tailTrace_8058907 : CollatzResearch.WordTrace tailWord_8058907 prefixEnd_8058907 4138092840883206223000267 := by
  unfold tailWord_8058907
  simp only [CollatzResearch.WordTrace]
  refine ⟨293932485814963765583750975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195954990543309177055833983 293932485814963765583750975)
  ·
    refine ⟨440898728722445648375626463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293932485814963765583750975 440898728722445648375626463)
    ·
      refine ⟨661348093083668472563439695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440898728722445648375626463 661348093083668472563439695)
      ·
        refine ⟨992022139625502708845159543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661348093083668472563439695 992022139625502708845159543)
        ·
          refine ⟨1488033209438254063267739315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 992022139625502708845159543 1488033209438254063267739315)
          ·
            refine ⟨2232049814157381094901608973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1488033209438254063267739315 2232049814157381094901608973)
            ·
              refine ⟨837018680309017910588103365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2232049814157381094901608973 837018680309017910588103365)
              ·
                refine ⟨156941002557940858235269381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 837018680309017910588103365 156941002557940858235269381)
                ·
                  refine ⟨29426437979613910919113009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156941002557940858235269381 29426437979613910919113009)
                  ·
                    refine ⟨22069828484710433189334757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29426437979613910919113009 22069828484710433189334757)
                    ·
                      refine ⟨4138092840883206223000267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22069828484710433189334757 4138092840883206223000267)
                      ·
                        rfl

theorem cell23_8058907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 4].length) (baseStart_8058907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058907 prefixEnd_8058907 := by exact prefixLift 8058907
  have htrace : WordTrace (prefixWord ++ tailWord_8058907) baseStart_8058907 baseEnd_8058907 := by
    simpa [prefixWord, tailWord_8058907, baseEnd_8058907] using wordTrace_append hprefix tailTrace_8058907
  have hstable : (prefixWord ++ tailWord_8058907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058907).length < 2 ^ (prefixWord ++ tailWord_8058907).sum := by decide
  have hdescent : baseEnd_8058907 < baseStart_8058907 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058911 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 6, 2, 2]
def baseStart_8058911 : Nat := 118140960795 + 8058911 * 2 ^ 59
def prefixEnd_8058911 : Nat := 4983230072969 + 3 ^ 40 * 8058911 * 2
def baseEnd_8058911 : Nat := 4138094894805824207350249

theorem tailTrace_8058911 : CollatzResearch.WordTrace tailWord_8058911 prefixEnd_8058911 4138094894805824207350249 := by
  unfold tailWord_8058911
  simp only [CollatzResearch.WordTrace]
  refine ⟨293932631706949274266896587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195955087804632849511264391 293932631706949274266896587)
  ·
    refine ⟨440898947560423911400344881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293932631706949274266896587 440898947560423911400344881)
    ·
      refine ⟨330674210670317933550258661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440898947560423911400344881 330674210670317933550258661)
      ·
        refine ⟨62001414500684612540673499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 330674210670317933550258661 62001414500684612540673499)
        ·
          refine ⟨93002121751026918811010249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62001414500684612540673499 93002121751026918811010249)
          ·
            refine ⟨69751591313270189108257687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93002121751026918811010249 69751591313270189108257687)
            ·
              refine ⟨104627386969905283662386531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69751591313270189108257687 104627386969905283662386531)
              ·
                refine ⟨156941080454857925493579797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104627386969905283662386531 156941080454857925493579797)
                ·
                  refine ⟨7356613146321465257511553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 156941080454857925493579797 7356613146321465257511553)
                  ·
                    refine ⟨5517459859741098943133665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7356613146321465257511553 5517459859741098943133665)
                    ·
                      refine ⟨4138094894805824207350249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5517459859741098943133665 4138094894805824207350249)
                      ·
                        rfl

theorem cell23_8058911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_8058911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058911 prefixEnd_8058911 := by exact prefixLift 8058911
  have htrace : WordTrace (prefixWord ++ tailWord_8058911) baseStart_8058911 baseEnd_8058911 := by
    simpa [prefixWord, tailWord_8058911, baseEnd_8058911] using wordTrace_append hprefix tailTrace_8058911
  have hstable : (prefixWord ++ tailWord_8058911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058911).length < 2 ^ (prefixWord ++ tailWord_8058911).sum := by decide
  have hdescent : baseEnd_8058911 < baseStart_8058911 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058914 : List Nat := [3, 3, 1, 1, 1, 2, 3, 1, 2, 1, 5]
def baseStart_8058914 : Nat := 118140960795 + 8058914 * 2 ^ 59
def prefixEnd_8058914 : Nat := 4983230072969 + 3 ^ 40 * 8058914 * 2
def baseEnd_8058914 : Nat := 4138096435247787695612735

theorem tailTrace_8058914 : CollatzResearch.WordTrace tailWord_8058914 prefixEnd_8058914 4138096435247787695612735 := by
  unfold tailWord_8058914
  simp only [CollatzResearch.WordTrace]
  refine ⟨73483185281484601444813949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195955160750625603852837197 73483185281484601444813949)
  ·
    refine ⟨27556194480556725541805231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73483185281484601444813949 27556194480556725541805231)
    ·
      refine ⟨41334291720835088312707847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27556194480556725541805231 41334291720835088312707847)
      ·
        refine ⟨62001437581252632469061771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41334291720835088312707847 62001437581252632469061771)
        ·
          refine ⟨93002156371878948703592657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62001437581252632469061771 93002156371878948703592657)
          ·
            refine ⟨69751617278909211527694493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93002156371878948703592657 69751617278909211527694493)
            ·
              refine ⟨26156856479590954322885435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69751617278909211527694493 26156856479590954322885435)
              ·
                refine ⟨39235284719386431484328153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26156856479590954322885435 39235284719386431484328153)
                ·
                  refine ⟨29426463539539823613246115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39235284719386431484328153 29426463539539823613246115)
                  ·
                    refine ⟨44139695309309735419869173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29426463539539823613246115 44139695309309735419869173)
                    ·
                      refine ⟨4138096435247787695612735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44139695309309735419869173 4138096435247787695612735)
                      ·
                        rfl

theorem cell23_8058914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_8058914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058914 prefixEnd_8058914 := by exact prefixLift 8058914
  have htrace : WordTrace (prefixWord ++ tailWord_8058914) baseStart_8058914 baseEnd_8058914 := by
    simpa [prefixWord, tailWord_8058914, baseEnd_8058914] using wordTrace_append hprefix tailTrace_8058914
  have hstable : (prefixWord ++ tailWord_8058914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058914).length < 2 ^ (prefixWord ++ tailWord_8058914).sum := by decide
  have hdescent : baseEnd_8058914 < baseStart_8058914 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058945 : List Nat := [1, 2, 5, 1, 2, 2, 1, 3, 2, 2, 2]
def baseStart_8058945 : Nat := 118140960795 + 8058945 * 2 ^ 59
def prefixEnd_8058945 : Nat := 4983230072969 + 3 ^ 40 * 8058945 * 2
def baseEnd_8058945 : Nat := 4138112353148077074325093

theorem tailTrace_8058945 : CollatzResearch.WordTrace tailWord_8058945 prefixEnd_8058945 4138112353148077074325093 := by
  unfold tailWord_8058945
  simp only [CollatzResearch.WordTrace]
  refine ⟨293933871788826098073634289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195955914525884065382422859 293933871788826098073634289)
  ·
    refine ⟨220450403841619573555225717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293933871788826098073634289 220450403841619573555225717)
    ·
      refine ⟨20667225360151835020802411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 220450403841619573555225717 20667225360151835020802411)
      ·
        refine ⟨31000838040227752531203617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20667225360151835020802411 31000838040227752531203617)
        ·
          refine ⟨23250628530170814398402713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31000838040227752531203617 23250628530170814398402713)
          ·
            refine ⟨17437971397628110798802035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23250628530170814398402713 17437971397628110798802035)
            ·
              refine ⟨26156957096442166198203053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17437971397628110798802035 26156957096442166198203053)
              ·
                refine ⟨9808858911165812324326145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26156957096442166198203053 9808858911165812324326145)
                ·
                  refine ⟨7356644183374359243244609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9808858911165812324326145 7356644183374359243244609)
                  ·
                    refine ⟨5517483137530769432433457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7356644183374359243244609 5517483137530769432433457)
                    ·
                      refine ⟨4138112353148077074325093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5517483137530769432433457 4138112353148077074325093)
                      ·
                        rfl

theorem cell23_8058945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_8058945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058945 prefixEnd_8058945 := by exact prefixLift 8058945
  have htrace : WordTrace (prefixWord ++ tailWord_8058945) baseStart_8058945 baseEnd_8058945 := by
    simpa [prefixWord, tailWord_8058945, baseEnd_8058945] using wordTrace_append hprefix tailTrace_8058945
  have hstable : (prefixWord ++ tailWord_8058945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058945).length < 2 ^ (prefixWord ++ tailWord_8058945).sum := by decide
  have hdescent : baseEnd_8058945 < baseStart_8058945 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8058947 : List Nat := [1, 1, 1, 3, 1, 2, 2, 4, 1, 7]
def baseStart_8058947 : Nat := 118140960795 + 8058947 * 2 ^ 59
def prefixEnd_8058947 : Nat := 4983230072969 + 3 ^ 40 * 8058947 * 2
def baseEnd_8058947 : Nat := 1379371126703128688833361

theorem tailTrace_8058947 : CollatzResearch.WordTrace tailWord_8058947 prefixEnd_8058947 1379371126703128688833361 := by
  unfold tailWord_8058947
  simp only [CollatzResearch.WordTrace]
  refine ⟨293933944734818852415207095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195955963156545901610138063 293933944734818852415207095)
  ·
    refine ⟨440900917102228278622810643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293933944734818852415207095 440900917102228278622810643)
    ·
      refine ⟨661351375653342417934215965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440900917102228278622810643 661351375653342417934215965)
      ·
        refine ⟨248006765870003406725330987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 661351375653342417934215965 248006765870003406725330987)
        ·
          refine ⟨372010148805005110087996481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248006765870003406725330987 372010148805005110087996481)
          ·
            refine ⟨279007611603753832565997361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372010148805005110087996481 279007611603753832565997361)
            ·
              refine ⟨209255708702815374424498021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279007611603753832565997361 209255708702815374424498021)
              ·
                refine ⟨39235445381777882704593379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 209255708702815374424498021 39235445381777882704593379)
                ·
                  refine ⟨58853168072666824056890069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39235445381777882704593379 58853168072666824056890069)
                  ·
                    refine ⟨1379371126703128688833361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58853168072666824056890069 1379371126703128688833361)
                    ·
                      rfl

theorem cell23_8058947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 7].length) (baseStart_8058947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8058947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8058947 prefixEnd_8058947 := by exact prefixLift 8058947
  have htrace : WordTrace (prefixWord ++ tailWord_8058947) baseStart_8058947 baseEnd_8058947 := by
    simpa [prefixWord, tailWord_8058947, baseEnd_8058947] using wordTrace_append hprefix tailTrace_8058947
  have hstable : (prefixWord ++ tailWord_8058947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8058947).length < 2 ^ (prefixWord ++ tailWord_8058947).sum := by decide
  have hdescent : baseEnd_8058947 < baseStart_8058947 := by decide
  rcases family_descends (prefixWord ++ tailWord_8058947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059001 : List Nat := [1, 2, 1, 3, 4, 1, 1, 1, 1, 6, 2]
def baseStart_8059001 : Nat := 118140960795 + 8059001 * 2 ^ 59
def prefixEnd_8059001 : Nat := 4983230072969 + 3 ^ 40 * 8059001 * 2
def baseEnd_8059001 : Nat := 4138141108064728855224835

theorem tailTrace_8059001 : CollatzResearch.WordTrace tailWord_8059001 prefixEnd_8059001 4138141108064728855224835 := by
  unfold tailWord_8059001
  simp only [CollatzResearch.WordTrace]
  refine ⟨293935914276623219637672857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195957276184415479758448571 293935914276623219637672857)
  ·
    refine ⟨220451935707467414728254643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293935914276623219637672857 220451935707467414728254643)
    ·
      refine ⟨330677903561201122092381965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220451935707467414728254643 330677903561201122092381965)
      ·
        refine ⟨124004213835450420784643237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330677903561201122092381965 124004213835450420784643237)
        ·
          refine ⟨23250790094146953897120607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124004213835450420784643237 23250790094146953897120607)
          ·
            refine ⟨34876185141220430845680911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23250790094146953897120607 34876185141220430845680911)
            ·
              refine ⟨52314277711830646268521367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34876185141220430845680911 52314277711830646268521367)
              ·
                refine ⟨78471416567745969402782051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52314277711830646268521367 78471416567745969402782051)
                ·
                  refine ⟨117707124851618954104173077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78471416567745969402782051 117707124851618954104173077)
                  ·
                    refine ⟨5517521477419638473633113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 117707124851618954104173077 5517521477419638473633113)
                    ·
                      refine ⟨4138141108064728855224835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5517521477419638473633113 4138141108064728855224835)
                      ·
                        rfl

theorem cell23_8059001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 6, 2].length) (baseStart_8059001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059001 prefixEnd_8059001 := by exact prefixLift 8059001
  have htrace : WordTrace (prefixWord ++ tailWord_8059001) baseStart_8059001 baseEnd_8059001 := by
    simpa [prefixWord, tailWord_8059001, baseEnd_8059001] using wordTrace_append hprefix tailTrace_8059001
  have hstable : (prefixWord ++ tailWord_8059001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059001).length < 2 ^ (prefixWord ++ tailWord_8059001).sum := by decide
  have hdescent : baseEnd_8059001 < baseStart_8059001 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059011 : List Nat := [1, 1, 1, 3, 3, 4, 1, 2, 3, 4]
def baseStart_8059011 : Nat := 118140960795 + 8059011 * 2 ^ 59
def prefixEnd_8059011 : Nat := 4983230072969 + 3 ^ 40 * 8059011 * 2
def baseEnd_8059011 : Nat := 1379382080957091272033263

theorem tailTrace_8059011 : CollatzResearch.WordTrace tailWord_8059011 prefixEnd_8059011 1379382080957091272033263 := by
  unfold tailWord_8059011
  simp only [CollatzResearch.WordTrace]
  refine ⟨293936279006586991345536887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195957519337724660897024591 293936279006586991345536887)
  ·
    refine ⟨440904418509880487018305331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293936279006586991345536887 440904418509880487018305331)
    ·
      refine ⟨661356627764820730527457997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440904418509880487018305331 661356627764820730527457997)
      ·
        refine ⟨248008735411807773947796749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 661356627764820730527457997 248008735411807773947796749)
        ·
          refine ⟨93003275779427915230423781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248008735411807773947796749 93003275779427915230423781)
          ·
            refine ⟨17438114208642734105704459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93003275779427915230423781 17438114208642734105704459)
            ·
              refine ⟨26157171312964101158556689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17438114208642734105704459 26157171312964101158556689)
              ·
                refine ⟨19617878484723075868917517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26157171312964101158556689 19617878484723075868917517)
                ·
                  refine ⟨7356704431771153450844069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19617878484723075868917517 7356704431771153450844069)
                  ·
                    refine ⟨1379382080957091272033263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7356704431771153450844069 1379382080957091272033263)
                    ·
                      rfl

theorem cell23_8059011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 3, 4].length) (baseStart_8059011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059011 prefixEnd_8059011 := by exact prefixLift 8059011
  have htrace : WordTrace (prefixWord ++ tailWord_8059011) baseStart_8059011 baseEnd_8059011 := by
    simpa [prefixWord, tailWord_8059011, baseEnd_8059011] using wordTrace_append hprefix tailTrace_8059011
  have hstable : (prefixWord ++ tailWord_8059011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059011).length < 2 ^ (prefixWord ++ tailWord_8059011).sum := by decide
  have hdescent : baseEnd_8059011 < baseStart_8059011 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059018 : List Nat := [3, 1, 2, 3, 1, 4, 1, 1, 2, 1, 4]
def baseStart_8059018 : Nat := 118140960795 + 8059018 * 2 ^ 59
def prefixEnd_8059018 : Nat := 4983230072969 + 3 ^ 40 * 8059018 * 2
def baseEnd_8059018 : Nat := 4138149837235855288712257

theorem tailTrace_8059018 : CollatzResearch.WordTrace tailWord_8059018 prefixEnd_8059018 4138149837235855288712257 := by
  unfold tailWord_8059018
  simp only [CollatzResearch.WordTrace]
  refine ⟨73484133579390407885260427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195957689545041087694027805 73484133579390407885260427)
  ·
    refine ⟨110226200369085611827890641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73484133579390407885260427 110226200369085611827890641)
    ·
      refine ⟨82669650276814208870917981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110226200369085611827890641 82669650276814208870917981)
      ·
        refine ⟨31001118853805328326594243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82669650276814208870917981 31001118853805328326594243)
        ·
          refine ⟨46501678280707992489891365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31001118853805328326594243 46501678280707992489891365)
          ·
            refine ⟨8719064677632748591854631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46501678280707992489891365 8719064677632748591854631)
            ·
              refine ⟨13078597016449122887781947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8719064677632748591854631 13078597016449122887781947)
              ·
                refine ⟨19617895524673684331672921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13078597016449122887781947 19617895524673684331672921)
                ·
                  refine ⟨14713421643505263248754691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19617895524673684331672921 14713421643505263248754691)
                  ·
                    refine ⟨22070132465257894873132037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14713421643505263248754691 22070132465257894873132037)
                    ·
                      refine ⟨4138149837235855288712257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22070132465257894873132037 4138149837235855288712257)
                      ·
                        rfl

theorem cell23_8059018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_8059018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059018 prefixEnd_8059018 := by exact prefixLift 8059018
  have htrace : WordTrace (prefixWord ++ tailWord_8059018) baseStart_8059018 baseEnd_8059018 := by
    simpa [prefixWord, tailWord_8059018, baseEnd_8059018] using wordTrace_append hprefix tailTrace_8059018
  have hstable : (prefixWord ++ tailWord_8059018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059018).length < 2 ^ (prefixWord ++ tailWord_8059018).sum := by decide
  have hdescent : baseEnd_8059018 < baseStart_8059018 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059030 : List Nat := [5, 3, 2, 1, 2, 1, 1, 2, 2, 2, 2]
def baseStart_8059030 : Nat := 118140960795 + 8059030 * 2 ^ 59
def prefixEnd_8059030 : Nat := 4983230072969 + 3 ^ 40 * 8059030 * 2
def baseEnd_8059030 : Nat := 4138155999003709241762203

theorem tailTrace_8059030 : CollatzResearch.WordTrace tailWord_8059030 prefixEnd_8059030 4138155999003709241762203 := by
  unfold tailWord_8059030
  simp only [CollatzResearch.WordTrace]
  refine ⟨18371060749594884849404909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195957981329012105060319029 18371060749594884849404909)
  ·
    refine ⟨6889147781098081818526841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18371060749594884849404909 6889147781098081818526841)
    ·
      refine ⟨5166860835823561363895131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6889147781098081818526841 5166860835823561363895131)
      ·
        refine ⟨7750291253735342045842697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5166860835823561363895131 7750291253735342045842697)
        ·
          refine ⟨5812718440301506534382023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7750291253735342045842697 5812718440301506534382023)
          ·
            refine ⟨8719077660452259801573035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5812718440301506534382023 8719077660452259801573035)
            ·
              refine ⟨13078616490678389702359553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8719077660452259801573035 13078616490678389702359553)
              ·
                refine ⟨9808962368008792276769665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13078616490678389702359553 9808962368008792276769665)
                ·
                  refine ⟨7356721776006594207577249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9808962368008792276769665 7356721776006594207577249)
                  ·
                    refine ⟨5517541332004945655682937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7356721776006594207577249 5517541332004945655682937)
                    ·
                      refine ⟨4138155999003709241762203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5517541332004945655682937 4138155999003709241762203)
                      ·
                        rfl

theorem cell23_8059030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_8059030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059030 prefixEnd_8059030 := by exact prefixLift 8059030
  have htrace : WordTrace (prefixWord ++ tailWord_8059030) baseStart_8059030 baseEnd_8059030 := by
    simpa [prefixWord, tailWord_8059030, baseEnd_8059030] using wordTrace_append hprefix tailTrace_8059030
  have hstable : (prefixWord ++ tailWord_8059030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059030).length < 2 ^ (prefixWord ++ tailWord_8059030).sum := by decide
  have hdescent : baseEnd_8059030 < baseStart_8059030 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059041 : List Nat := [1, 2, 3, 3, 1, 2, 3, 2, 6]
def baseStart_8059041 : Nat := 118140960795 + 8059041 * 2 ^ 59
def prefixEnd_8059041 : Nat := 4983230072969 + 3 ^ 40 * 8059041 * 2
def baseEnd_8059041 : Nat := 459795738587878744302739

theorem tailTrace_8059041 : CollatzResearch.WordTrace tailWord_8059041 prefixEnd_8059041 459795738587878744302739 := by
  unfold tailWord_8059041
  simp only [CollatzResearch.WordTrace]
  refine ⟨293937373196478306469128977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195958248797652204312752651 293937373196478306469128977)
  ·
    refine ⟨220453029897358729851846733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293937373196478306469128977 220453029897358729851846733)
    ·
      refine ⟨82669886211509523694442525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220453029897358729851846733 82669886211509523694442525)
      ·
        refine ⟨31001207329316071385415947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82669886211509523694442525 31001207329316071385415947)
        ·
          refine ⟨46501810993974107078123921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31001207329316071385415947 46501810993974107078123921)
          ·
            refine ⟨34876358245480580308592941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46501810993974107078123921 34876358245480580308592941)
            ·
              refine ⟨13078634342055217615722353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34876358245480580308592941 13078634342055217615722353)
              ·
                refine ⟨9808975756541413211791765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13078634342055217615722353 9808975756541413211791765)
                ·
                  refine ⟨459795738587878744302739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9808975756541413211791765 459795738587878744302739)
                  ·
                    rfl

theorem cell23_8059041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 6].length) (baseStart_8059041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059041 prefixEnd_8059041 := by exact prefixLift 8059041
  have htrace : WordTrace (prefixWord ++ tailWord_8059041) baseStart_8059041 baseEnd_8059041 := by
    simpa [prefixWord, tailWord_8059041, baseEnd_8059041] using wordTrace_append hprefix tailTrace_8059041
  have hstable : (prefixWord ++ tailWord_8059041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059041).length < 2 ^ (prefixWord ++ tailWord_8059041).sum := by decide
  have hdescent : baseEnd_8059041 < baseStart_8059041 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059104 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 6]
def baseStart_8059104 : Nat := 118140960795 + 8059104 * 2 ^ 59
def prefixEnd_8059104 : Nat := 4983230072969 + 3 ^ 40 * 8059104 * 2
def baseEnd_8059104 : Nat := 4138193996572141952236861

theorem tailTrace_8059104 : CollatzResearch.WordTrace tailWord_8059104 prefixEnd_8059104 4138193996572141952236861 := by
  unfold tailWord_8059104
  simp only [CollatzResearch.WordTrace]
  refine ⟨146969835497625034114336183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195959780663500045485781577 146969835497625034114336183)
  ·
    refine ⟨220454753246437551171504275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146969835497625034114336183 220454753246437551171504275)
    ·
      refine ⟨330682129869656326757256413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220454753246437551171504275 330682129869656326757256413)
      ·
        refine ⟨124005798701121122533971155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330682129869656326757256413 124005798701121122533971155)
        ·
          refine ⟨186008698051681683800956733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124005798701121122533971155 186008698051681683800956733)
          ·
            refine ⟨69753261769380631425358775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186008698051681683800956733 69753261769380631425358775)
            ·
              refine ⟨104629892654070947138038163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69753261769380631425358775 104629892654070947138038163)
              ·
                refine ⟨156944838981106420707057245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104629892654070947138038163 156944838981106420707057245)
                ·
                  refine ⟨58854314617914907765146467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156944838981106420707057245 58854314617914907765146467)
                  ·
                    refine ⟨88281471926872361647719701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58854314617914907765146467 88281471926872361647719701)
                    ·
                      refine ⟨4138193996572141952236861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88281471926872361647719701 4138193996572141952236861)
                      ·
                        rfl

theorem cell23_8059104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_8059104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059104 prefixEnd_8059104 := by exact prefixLift 8059104
  have htrace : WordTrace (prefixWord ++ tailWord_8059104) baseStart_8059104 baseEnd_8059104 := by
    simpa [prefixWord, tailWord_8059104, baseEnd_8059104] using wordTrace_append hprefix tailTrace_8059104
  have hstable : (prefixWord ++ tailWord_8059104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059104).length < 2 ^ (prefixWord ++ tailWord_8059104).sum := by decide
  have hdescent : baseEnd_8059104 < baseStart_8059104 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059138 : List Nat := [3, 4, 1, 1, 2, 1, 1, 1, 3, 2, 4]
def baseStart_8059138 : Nat := 118140960795 + 8059138 * 2 ^ 59
def prefixEnd_8059138 : Nat := 4983230072969 + 3 ^ 40 * 8059138 * 2
def baseEnd_8059138 : Nat := 4138211454914394819211705

theorem tailTrace_8059138 : CollatzResearch.WordTrace tailWord_8059138 prefixEnd_8059138 4138211454914394819211705 := by
  unfold tailWord_8059138
  simp only [CollatzResearch.WordTrace]
  refine ⟨73485227769281723008852517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195960607384751261356940045 73485227769281723008852517)
  ·
    refine ⟨13778480206740323064159847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73485227769281723008852517 13778480206740323064159847)
    ·
      refine ⟨20667720310110484596239771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13778480206740323064159847 20667720310110484596239771)
      ·
        refine ⟨31001580465165726894359657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20667720310110484596239771 31001580465165726894359657)
        ·
          refine ⟨23251185348874295170769743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31001580465165726894359657 23251185348874295170769743)
          ·
            refine ⟨34876778023311442756154615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23251185348874295170769743 34876778023311442756154615)
            ·
              refine ⟨52315167034967164134231923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34876778023311442756154615 52315167034967164134231923)
              ·
                refine ⟨78472750552450746201347885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52315167034967164134231923 78472750552450746201347885)
                ·
                  refine ⟨29427281457169029825505457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78472750552450746201347885 29427281457169029825505457)
                  ·
                    refine ⟨22070461092876772369129093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29427281457169029825505457 22070461092876772369129093)
                    ·
                      refine ⟨4138211454914394819211705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22070461092876772369129093 4138211454914394819211705)
                      ·
                        rfl

theorem cell23_8059138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_8059138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059138 prefixEnd_8059138 := by exact prefixLift 8059138
  have htrace : WordTrace (prefixWord ++ tailWord_8059138) baseStart_8059138 baseEnd_8059138 := by
    simpa [prefixWord, tailWord_8059138, baseEnd_8059138] using wordTrace_append hprefix tailTrace_8059138
  have hstable : (prefixWord ++ tailWord_8059138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059138).length < 2 ^ (prefixWord ++ tailWord_8059138).sum := by decide
  have hdescent : baseEnd_8059138 < baseStart_8059138 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059145 : List Nat := [1, 2, 1, 1, 3, 5, 3, 1, 1, 2, 3]
def baseStart_8059145 : Nat := 118140960795 + 8059145 * 2 ^ 59
def prefixEnd_8059145 : Nat := 4983230072969 + 3 ^ 40 * 8059145 * 2
def baseEnd_8059145 : Nat := 4138215049278976291824173

theorem tailTrace_8059145 : CollatzResearch.WordTrace tailWord_8059145 prefixEnd_8059145 4138215049278976291824173 := by
  unfold tailWord_8059145
  simp only [CollatzResearch.WordTrace]
  refine ⟨293941166388101532230914889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195960777592067688153943259 293941166388101532230914889)
  ·
    refine ⟨220455874791076149173186167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293941166388101532230914889 220455874791076149173186167)
    ·
      refine ⟨330683812186614223759779251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220455874791076149173186167 330683812186614223759779251)
      ·
        refine ⟨496025718279921335639668877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330683812186614223759779251 496025718279921335639668877)
        ·
          refine ⟨186009644354970500864875829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 496025718279921335639668877 186009644354970500864875829)
          ·
            refine ⟨17438404158278484456082109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 186009644354970500864875829 17438404158278484456082109)
            ·
              refine ⟨6539401559354431671030791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17438404158278484456082109 6539401559354431671030791)
              ·
                refine ⟨9809102339031647506546187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6539401559354431671030791 9809102339031647506546187)
                ·
                  refine ⟨14713653508547471259819281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9809102339031647506546187 14713653508547471259819281)
                  ·
                    refine ⟨11035240131410603444864461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14713653508547471259819281 11035240131410603444864461)
                    ·
                      refine ⟨4138215049278976291824173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11035240131410603444864461 4138215049278976291824173)
                      ·
                        rfl

theorem cell23_8059145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 1, 2, 3].length) (baseStart_8059145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059145 prefixEnd_8059145 := by exact prefixLift 8059145
  have htrace : WordTrace (prefixWord ++ tailWord_8059145) baseStart_8059145 baseEnd_8059145 := by
    simpa [prefixWord, tailWord_8059145, baseEnd_8059145] using wordTrace_append hprefix tailTrace_8059145
  have hstable : (prefixWord ++ tailWord_8059145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059145).length < 2 ^ (prefixWord ++ tailWord_8059145).sum := by decide
  have hdescent : baseEnd_8059145 < baseStart_8059145 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059159 : List Nat := [1, 1, 3, 4, 1, 2, 4, 2, 1, 2, 2]
def baseStart_8059159 : Nat := 118140960795 + 8059159 * 2 ^ 59
def prefixEnd_8059159 : Nat := 4983230072969 + 3 ^ 40 * 8059159 * 2
def baseEnd_8059159 : Nat := 4138222238008139237049109

theorem tailTrace_8059159 : CollatzResearch.WordTrace tailWord_8059159 prefixEnd_8059159 4138222238008139237049109 := by
  unfold tailWord_8059159
  simp only [CollatzResearch.WordTrace]
  refine ⟨293941677010050812621924531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195961118006700541747949687 293941677010050812621924531)
  ·
    refine ⟨440912515515076218932886797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293941677010050812621924531 440912515515076218932886797)
    ·
      refine ⟨165342193318153582099832549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 440912515515076218932886797 165342193318153582099832549)
      ·
        refine ⟨31001661247153796643718603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165342193318153582099832549 31001661247153796643718603)
        ·
          refine ⟨46502491870730694965577905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31001661247153796643718603 46502491870730694965577905)
          ·
            refine ⟨34876868903048021224183429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46502491870730694965577905 34876868903048021224183429)
            ·
              refine ⟨6539412919321503979534393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34876868903048021224183429 6539412919321503979534393)
              ·
                refine ⟨4904559689491127984650795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6539412919321503979534393 4904559689491127984650795)
                ·
                  refine ⟨7356839534236691976976193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4904559689491127984650795 7356839534236691976976193)
                  ·
                    refine ⟨5517629650677518982732145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7356839534236691976976193 5517629650677518982732145)
                    ·
                      refine ⟨4138222238008139237049109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5517629650677518982732145 4138222238008139237049109)
                      ·
                        rfl

theorem cell23_8059159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_8059159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059159 prefixEnd_8059159 := by exact prefixLift 8059159
  have htrace : WordTrace (prefixWord ++ tailWord_8059159) baseStart_8059159 baseEnd_8059159 := by
    simpa [prefixWord, tailWord_8059159, baseEnd_8059159] using wordTrace_append hprefix tailTrace_8059159
  have hstable : (prefixWord ++ tailWord_8059159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059159).length < 2 ^ (prefixWord ++ tailWord_8059159).sum := by decide
  have hdescent : baseEnd_8059159 < baseStart_8059159 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059165 : List Nat := [1, 4, 2, 3, 3, 1, 1, 8]
def baseStart_8059165 : Nat := 118140960795 + 8059165 * 2 ^ 59
def prefixEnd_8059165 : Nat := 4983230072969 + 3 ^ 40 * 8059165 * 2
def baseEnd_8059165 : Nat := 153267604403409859762003

theorem tailTrace_8059165 : CollatzResearch.WordTrace tailWord_8059165 prefixEnd_8059165 153267604403409859762003 := by
  unfold tailWord_8059165
  simp only [CollatzResearch.WordTrace]
  refine ⟨293941895848029075646642949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195961263898686050431095299 293941895848029075646642949)
  ·
    refine ⟨55114105471505451683745553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293941895848029075646642949 55114105471505451683745553)
    ·
      refine ⟨41335579103629088762809165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55114105471505451683745553 41335579103629088762809165)
      ·
        refine ⟨15500842163860908286053437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41335579103629088762809165 15500842163860908286053437)
        ·
          refine ⟨5812815811447840607270039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15500842163860908286053437 5812815811447840607270039)
          ·
            refine ⟨8719223717171760910905059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5812815811447840607270039 8719223717171760910905059)
            ·
              refine ⟨13078835575757641366357589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8719223717171760910905059 13078835575757641366357589)
              ·
                refine ⟨153267604403409859762003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13078835575757641366357589 153267604403409859762003)
                ·
                  rfl

theorem cell23_8059165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 8].length) (baseStart_8059165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059165 prefixEnd_8059165 := by exact prefixLift 8059165
  have htrace : WordTrace (prefixWord ++ tailWord_8059165) baseStart_8059165 baseEnd_8059165 := by
    simpa [prefixWord, tailWord_8059165, baseEnd_8059165] using wordTrace_append hprefix tailTrace_8059165
  have hstable : (prefixWord ++ tailWord_8059165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059165).length < 2 ^ (prefixWord ++ tailWord_8059165).sum := by decide
  have hdescent : baseEnd_8059165 < baseStart_8059165 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059215 : List Nat := [1, 1, 2, 1, 1, 2, 1, 8, 2, 2, 2]
def baseStart_8059215 : Nat := 118140960795 + 8059215 * 2 ^ 59
def prefixEnd_8059215 : Nat := 4983230072969 + 3 ^ 40 * 8059215 * 2
def baseEnd_8059215 : Nat := 4138250992924791017948851

theorem tailTrace_8059215 : CollatzResearch.WordTrace tailWord_8059215 prefixEnd_8059215 4138250992924791017948851 := by
  unfold tailWord_8059215
  simp only [CollatzResearch.WordTrace]
  refine ⟨293943719497847934185963099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195962479665231956123975399 293943719497847934185963099)
  ·
    refine ⟨440915579246771901278944649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293943719497847934185963099 440915579246771901278944649)
    ·
      refine ⟨330686684435078925959208487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440915579246771901278944649 330686684435078925959208487)
      ·
        refine ⟨496030026652618388938812731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330686684435078925959208487 496030026652618388938812731)
        ·
          refine ⟨744045039978927583408219097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496030026652618388938812731 744045039978927583408219097)
          ·
            refine ⟨558033779984195687556164323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 744045039978927583408219097 558033779984195687556164323)
            ·
              refine ⟨837050669976293531334246485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558033779984195687556164323 837050669976293531334246485)
              ·
                refine ⟨9809187538784689820323201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 837050669976293531334246485 9809187538784689820323201)
                ·
                  refine ⟨7356890654088517365242401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9809187538784689820323201 7356890654088517365242401)
                  ·
                    refine ⟨5517667990566388023931801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7356890654088517365242401 5517667990566388023931801)
                    ·
                      refine ⟨4138250992924791017948851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5517667990566388023931801 4138250992924791017948851)
                      ·
                        rfl

theorem cell23_8059215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 2, 2, 2].length) (baseStart_8059215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059215 prefixEnd_8059215 := by exact prefixLift 8059215
  have htrace : WordTrace (prefixWord ++ tailWord_8059215) baseStart_8059215 baseEnd_8059215 := by
    simpa [prefixWord, tailWord_8059215, baseEnd_8059215] using wordTrace_append hprefix tailTrace_8059215
  have hstable : (prefixWord ++ tailWord_8059215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059215).length < 2 ^ (prefixWord ++ tailWord_8059215).sum := by decide
  have hdescent : baseEnd_8059215 < baseStart_8059215 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059232 : List Nat := [2, 1, 1, 3, 5, 2, 1, 1, 1, 4, 2]
def baseStart_8059232 : Nat := 118140960795 + 8059232 * 2 ^ 59
def prefixEnd_8059232 : Nat := 4983230072969 + 3 ^ 40 * 8059232 * 2
def baseEnd_8059232 : Nat := 4138259722095917451436273

theorem tailTrace_8059232 : CollatzResearch.WordTrace tailWord_8059232 prefixEnd_8059232 4138259722095917451436273 := by
  unfold tailWord_8059232
  simp only [CollatzResearch.WordTrace]
  refine ⟨146972169769393173044665975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195962893025857564059554633 146972169769393173044665975)
  ·
    refine ⟨220458254654089759566998963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146972169769393173044665975 220458254654089759566998963)
    ·
      refine ⟨330687381981134639350498445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220458254654089759566998963 330687381981134639350498445)
      ·
        refine ⟨124007768242925489756436917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330687381981134639350498445 124007768242925489756436917)
        ·
          refine ⟨11625728272774264664665961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124007768242925489756436917 11625728272774264664665961)
          ·
            refine ⟨8719296204580698498499471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11625728272774264664665961 8719296204580698498499471)
            ·
              refine ⟨13078944306871047747749207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8719296204580698498499471 13078944306871047747749207)
              ·
                refine ⟨19618416460306571621623811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13078944306871047747749207 19618416460306571621623811)
                ·
                  refine ⟨29427624690459857432435717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19618416460306571621623811 29427624690459857432435717)
                  ·
                    refine ⟨5517679629461223268581697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29427624690459857432435717 5517679629461223268581697)
                    ·
                      refine ⟨4138259722095917451436273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5517679629461223268581697 4138259722095917451436273)
                      ·
                        rfl

theorem cell23_8059232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 1, 4, 2].length) (baseStart_8059232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059232 prefixEnd_8059232 := by exact prefixLift 8059232
  have htrace : WordTrace (prefixWord ++ tailWord_8059232) baseStart_8059232 baseEnd_8059232 := by
    simpa [prefixWord, tailWord_8059232, baseEnd_8059232] using wordTrace_append hprefix tailTrace_8059232
  have hstable : (prefixWord ++ tailWord_8059232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059232).length < 2 ^ (prefixWord ++ tailWord_8059232).sum := by decide
  have hdescent : baseEnd_8059232 < baseStart_8059232 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059268 : List Nat := [2, 3, 2, 1, 1, 2, 3, 2, 2, 5]
def baseStart_8059268 : Nat := 118140960795 + 8059268 * 2 ^ 59
def prefixEnd_8059268 : Nat := 4983230072969 + 3 ^ 40 * 8059268 * 2
def baseEnd_8059268 : Nat := 1379426069133159770195369

theorem tailTrace_8059268 : CollatzResearch.WordTrace tailWord_8059268 prefixEnd_8059268 1379426069133159770195369 := by
  unfold tailWord_8059268
  simp only [CollatzResearch.WordTrace]
  refine ⟨146972826283327962118821229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195963768377770616158428305 146972826283327962118821229)
  ·
    refine ⟨55114809856247985794557961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146972826283327962118821229 55114809856247985794557961)
    ·
      refine ⟨41336107392185989345918471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55114809856247985794557961 41336107392185989345918471)
      ·
        refine ⟨62004161088278984018877707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41336107392185989345918471 62004161088278984018877707)
        ·
          refine ⟨93006241632418476028316561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62004161088278984018877707 93006241632418476028316561)
          ·
            refine ⟨69754681224313857021237421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93006241632418476028316561 69754681224313857021237421)
            ·
              refine ⟨26158005459117696382964033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69754681224313857021237421 26158005459117696382964033)
              ·
                refine ⟨19618504094338272287223025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26158005459117696382964033 19618504094338272287223025)
                ·
                  refine ⟨14713878070753704215417269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19618504094338272287223025 14713878070753704215417269)
                  ·
                    refine ⟨1379426069133159770195369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14713878070753704215417269 1379426069133159770195369)
                    ·
                      rfl

theorem cell23_8059268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_8059268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059268 prefixEnd_8059268 := by exact prefixLift 8059268
  have htrace : WordTrace (prefixWord ++ tailWord_8059268) baseStart_8059268 baseEnd_8059268 := by
    simpa [prefixWord, tailWord_8059268, baseEnd_8059268] using wordTrace_append hprefix tailTrace_8059268
  have hstable : (prefixWord ++ tailWord_8059268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059268).length < 2 ^ (prefixWord ++ tailWord_8059268).sum := by decide
  have hdescent : baseEnd_8059268 < baseStart_8059268 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059278 : List Nat := [4, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7]
def baseStart_8059278 : Nat := 118140960795 + 8059278 * 2 ^ 59
def prefixEnd_8059278 : Nat := 4983230072969 + 3 ^ 40 * 8059278 * 2
def baseEnd_8059278 : Nat := 4138283342206024271461061

theorem tailTrace_8059278 : CollatzResearch.WordTrace tailWord_8059278 prefixEnd_8059278 4138283342206024271461061 := by
  unfold tailWord_8059278
  simp only [CollatzResearch.WordTrace]
  refine ⟨36743252162077461993188311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195964011531079797297004325 36743252162077461993188311)
  ·
    refine ⟨55114878243116192989782467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36743252162077461993188311 55114878243116192989782467)
    ·
      refine ⟨82672317364674289484673701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55114878243116192989782467 82672317364674289484673701)
      ·
        refine ⟨15501059505876429278376319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82672317364674289484673701 15501059505876429278376319)
        ·
          refine ⟨23251589258814643917564479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15501059505876429278376319 23251589258814643917564479)
          ·
            refine ⟨34877383888221965876346719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23251589258814643917564479 34877383888221965876346719)
            ·
              refine ⟨52316075832332948814520079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34877383888221965876346719 52316075832332948814520079)
              ·
                refine ⟨78474113748499423221780119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52316075832332948814520079 78474113748499423221780119)
                ·
                  refine ⟨117711170622749134832670179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78474113748499423221780119 117711170622749134832670179)
                  ·
                    refine ⟨176566755934123702249005269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 117711170622749134832670179 176566755934123702249005269)
                    ·
                      refine ⟨4138283342206024271461061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 176566755934123702249005269 4138283342206024271461061)
                      ·
                        rfl

theorem cell23_8059278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_8059278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059278 prefixEnd_8059278 := by exact prefixLift 8059278
  have htrace : WordTrace (prefixWord ++ tailWord_8059278) baseStart_8059278 baseEnd_8059278 := by
    simpa [prefixWord, tailWord_8059278, baseEnd_8059278] using wordTrace_append hprefix tailTrace_8059278
  have hstable : (prefixWord ++ tailWord_8059278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059278).length < 2 ^ (prefixWord ++ tailWord_8059278).sum := by decide
  have hdescent : baseEnd_8059278 < baseStart_8059278 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059325 : List Nat := [1, 4, 1, 2, 2, 2, 2, 2, 2, 2, 3]
def baseStart_8059325 : Nat := 118140960795 + 8059325 * 2 ^ 59
def prefixEnd_8059325 : Nat := 4983230072969 + 3 ^ 40 * 8059325 * 2
def baseEnd_8059325 : Nat := 4138307475796785587573345

theorem tailTrace_8059325 : CollatzResearch.WordTrace tailWord_8059325 prefixEnd_8059325 4138307475796785587573345 := by
  unfold tailWord_8059325
  simp only [CollatzResearch.WordTrace]
  refine ⟨293947731527449422972467429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195965154351632948648311619 293947731527449422972467429)
  ·
    refine ⟨55115199661396766807337643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293947731527449422972467429 55115199661396766807337643)
    ·
      refine ⟨82672799492095150211006465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55115199661396766807337643 82672799492095150211006465)
      ·
        refine ⟨62004599619071362658254849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82672799492095150211006465 62004599619071362658254849)
        ·
          refine ⟨46503449714303521993691137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62004599619071362658254849 46503449714303521993691137)
          ·
            refine ⟨34877587285727641495268353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46503449714303521993691137 34877587285727641495268353)
            ·
              refine ⟨26158190464295731121451265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34877587285727641495268353 26158190464295731121451265)
              ·
                refine ⟨19618642848221798341088449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26158190464295731121451265 19618642848221798341088449)
                ·
                  refine ⟨14713982136166348755816337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19618642848221798341088449 14713982136166348755816337)
                  ·
                    refine ⟨11035486602124761566862253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14713982136166348755816337 11035486602124761566862253)
                    ·
                      refine ⟨4138307475796785587573345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11035486602124761566862253 4138307475796785587573345)
                      ·
                        rfl

theorem cell23_8059325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_8059325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059325 prefixEnd_8059325 := by exact prefixLift 8059325
  have htrace : WordTrace (prefixWord ++ tailWord_8059325) baseStart_8059325 baseEnd_8059325 := by
    simpa [prefixWord, tailWord_8059325, baseEnd_8059325] using wordTrace_append hprefix tailTrace_8059325
  have hstable : (prefixWord ++ tailWord_8059325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059325).length < 2 ^ (prefixWord ++ tailWord_8059325).sum := by decide
  have hdescent : baseEnd_8059325 < baseStart_8059325 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059331 : List Nat := [1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 6]
def baseStart_8059331 : Nat := 118140960795 + 8059331 * 2 ^ 59
def prefixEnd_8059331 : Nat := 4983230072969 + 3 ^ 40 * 8059331 * 2
def baseEnd_8059331 : Nat := 4138310556680712564098317

theorem tailTrace_8059331 : CollatzResearch.WordTrace tailWord_8059331 prefixEnd_8059331 4138310556680712564098317 := by
  unfold tailWord_8059331
  simp only [CollatzResearch.WordTrace]
  refine ⟨293947950365427685997185847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195965300243618457331457231 293947950365427685997185847)
  ·
    refine ⟨440921925548141528995778771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293947950365427685997185847 440921925548141528995778771)
    ·
      refine ⟨661382888322212293493668157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440921925548141528995778771 661382888322212293493668157)
      ·
        refine ⟨248018583120829610060125559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 661382888322212293493668157 248018583120829610060125559)
        ·
          refine ⟨372027874681244415090188339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248018583120829610060125559 372027874681244415090188339)
          ·
            refine ⟨558041812021866622635282509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372027874681244415090188339 558041812021866622635282509)
            ·
              refine ⟨209265679508199983488230941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 558041812021866622635282509 209265679508199983488230941)
              ·
                refine ⟨78474629815574993808086603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209265679508199983488230941 78474629815574993808086603)
                ·
                  refine ⟨117711944723362490712129905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78474629815574993808086603 117711944723362490712129905)
                  ·
                    refine ⟨88283958542521868034097429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117711944723362490712129905 88283958542521868034097429)
                    ·
                      refine ⟨4138310556680712564098317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88283958542521868034097429 4138310556680712564098317)
                      ·
                        rfl

theorem cell23_8059331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_8059331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059331 prefixEnd_8059331 := by exact prefixLift 8059331
  have htrace : WordTrace (prefixWord ++ tailWord_8059331) baseStart_8059331 baseEnd_8059331 := by
    simpa [prefixWord, tailWord_8059331, baseEnd_8059331] using wordTrace_append hprefix tailTrace_8059331
  have hstable : (prefixWord ++ tailWord_8059331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059331).length < 2 ^ (prefixWord ++ tailWord_8059331).sum := by decide
  have hdescent : baseEnd_8059331 < baseStart_8059331 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059382 : List Nat := [5, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2]
def baseStart_8059382 : Nat := 118140960795 + 8059382 * 2 ^ 59
def prefixEnd_8059382 : Nat := 4983230072969 + 3 ^ 40 * 8059382 * 2
def baseEnd_8059382 : Nat := 4138336744194091864560583

theorem tailTrace_8059382 : CollatzResearch.WordTrace tailWord_8059382 prefixEnd_8059382 4138336744194091864560583 := by
  unfold tailWord_8059382
  simp only [CollatzResearch.WordTrace]
  refine ⟨18371863155515182606705775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195966540325495281138194933 18371863155515182606705775)
  ·
    refine ⟨27557794733272773910058663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18371863155515182606705775 27557794733272773910058663)
    ·
      refine ⟨41336692099909160865087995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27557794733272773910058663 41336692099909160865087995)
      ·
        refine ⟨62005038149863741297631993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41336692099909160865087995 62005038149863741297631993)
        ·
          refine ⟨46503778612397805973223995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62005038149863741297631993 46503778612397805973223995)
          ·
            refine ⟨69755667918596708959835993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46503778612397805973223995 69755667918596708959835993)
            ·
              refine ⟨52316750938947531719876995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69755667918596708959835993 52316750938947531719876995)
              ·
                refine ⟨78475126408421297579815493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52316750938947531719876995 78475126408421297579815493)
                ·
                  refine ⟨14714086201578993296215405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78475126408421297579815493 14714086201578993296215405)
                  ·
                    refine ⟨5517782325592122486080777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14714086201578993296215405 5517782325592122486080777)
                    ·
                      refine ⟨4138336744194091864560583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5517782325592122486080777 4138336744194091864560583)
                      ·
                        rfl

theorem cell23_8059382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_8059382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059382 prefixEnd_8059382 := by exact prefixLift 8059382
  have htrace : WordTrace (prefixWord ++ tailWord_8059382) baseStart_8059382 baseEnd_8059382 := by
    simpa [prefixWord, tailWord_8059382, baseEnd_8059382] using wordTrace_append hprefix tailTrace_8059382
  have hstable : (prefixWord ++ tailWord_8059382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059382).length < 2 ^ (prefixWord ++ tailWord_8059382).sum := by decide
  have hdescent : baseEnd_8059382 < baseStart_8059382 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059432 : List Nat := [2, 1, 5, 2, 1, 2, 2, 1, 1, 1, 5]
def baseStart_8059432 : Nat := 118140960795 + 8059432 * 2 ^ 59
def prefixEnd_8059432 : Nat := 4983230072969 + 3 ^ 40 * 8059432 * 2
def baseEnd_8059432 : Nat := 4138362418226816668935353

theorem tailTrace_8059432 : CollatzResearch.WordTrace tailWord_8059432 prefixEnd_8059432 4138362418226816668935353 := by
  unfold tailWord_8059432
  simp only [CollatzResearch.WordTrace]
  refine ⟨146975817069030890123306275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195967756092041186831075033 146975817069030890123306275)
  ·
    refine ⟨220463725603546335184959413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146975817069030890123306275 220463725603546335184959413)
    ·
      refine ⟨20668474275332468923589945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 220463725603546335184959413 20668474275332468923589945)
      ·
        refine ⟨15501355706499351692692459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20668474275332468923589945 15501355706499351692692459)
        ·
          refine ⟨23252033559749027539038689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15501355706499351692692459 23252033559749027539038689)
          ·
            refine ⟨17439025169811770654279017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23252033559749027539038689 17439025169811770654279017)
            ·
              refine ⟨13079268877358827990709263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17439025169811770654279017 13079268877358827990709263)
              ·
                refine ⟨19618903316038241986063895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13079268877358827990709263 19618903316038241986063895)
                ·
                  refine ⟨29428354974057362979095843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19618903316038241986063895 29428354974057362979095843)
                  ·
                    refine ⟨44142532461086044468643765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29428354974057362979095843 44142532461086044468643765)
                    ·
                      refine ⟨4138362418226816668935353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44142532461086044468643765 4138362418226816668935353)
                      ·
                        rfl

theorem cell23_8059432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_8059432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059432 prefixEnd_8059432 := by exact prefixLift 8059432
  have htrace : WordTrace (prefixWord ++ tailWord_8059432) baseStart_8059432 baseEnd_8059432 := by
    simpa [prefixWord, tailWord_8059432, baseEnd_8059432] using wordTrace_append hprefix tailTrace_8059432
  have hstable : (prefixWord ++ tailWord_8059432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059432).length < 2 ^ (prefixWord ++ tailWord_8059432).sum := by decide
  have hdescent : baseEnd_8059432 < baseStart_8059432 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059446 : List Nat := [5, 1, 2, 1, 2, 1, 3, 1, 3, 2, 2]
def baseStart_8059446 : Nat := 118140960795 + 8059446 * 2 ^ 59
def prefixEnd_8059446 : Nat := 4983230072969 + 3 ^ 40 * 8059446 * 2
def baseEnd_8059446 : Nat := 4138369606955979614160289

theorem tailTrace_8059446 : CollatzResearch.WordTrace tailWord_8059446 prefixEnd_8059446 4138369606955979614160289 := by
  unfold tailWord_8059446
  simp only [CollatzResearch.WordTrace]
  refine ⟨18372009047500691289851387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195968096506674040425081461 18372009047500691289851387)
  ·
    refine ⟨27558013571251036934777081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18372009047500691289851387 27558013571251036934777081)
    ·
      refine ⟨20668510178438277701082811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27558013571251036934777081 20668510178438277701082811)
      ·
        refine ⟨31002765267657416551624217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20668510178438277701082811 31002765267657416551624217)
        ·
          refine ⟨23252073950743062413718163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31002765267657416551624217 23252073950743062413718163)
          ·
            refine ⟨34878110926114593620577245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23252073950743062413718163 34878110926114593620577245)
            ·
              refine ⟨13079291597292972607716467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34878110926114593620577245 13079291597292972607716467)
              ·
                refine ⟨19618937395939458911574701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13079291597292972607716467 19618937395939458911574701)
                ·
                  refine ⟨7357101523477297091840513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19618937395939458911574701 7357101523477297091840513)
                  ·
                    refine ⟨5517826142607972818880385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7357101523477297091840513 5517826142607972818880385)
                    ·
                      refine ⟨4138369606955979614160289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5517826142607972818880385 4138369606955979614160289)
                      ·
                        rfl

theorem cell23_8059446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_8059446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059446 prefixEnd_8059446 := by exact prefixLift 8059446
  have htrace : WordTrace (prefixWord ++ tailWord_8059446) baseStart_8059446 baseEnd_8059446 := by
    simpa [prefixWord, tailWord_8059446, baseEnd_8059446] using wordTrace_append hprefix tailTrace_8059446
  have hstable : (prefixWord ++ tailWord_8059446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059446).length < 2 ^ (prefixWord ++ tailWord_8059446).sum := by decide
  have hdescent : baseEnd_8059446 < baseStart_8059446 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059448 : List Nat := [2, 1, 2, 1, 4, 1, 2, 1, 2, 7]
def baseStart_8059448 : Nat := 118140960795 + 8059448 * 2 ^ 59
def prefixEnd_8059448 : Nat := 4983230072969 + 3 ^ 40 * 8059448 * 2
def baseEnd_8059448 : Nat := 1379456877972429535445093

theorem tailTrace_8059448 : CollatzResearch.WordTrace tailWord_8059448 prefixEnd_8059448 1379456877972429535445093 := by
  unfold tailWord_8059448
  simp only [CollatzResearch.WordTrace]
  refine ⟨146976108853001907489597499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195968145137335876652796665 146976108853001907489597499)
  ·
    refine ⟨220464163279502861234396249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146976108853001907489597499 220464163279502861234396249)
    ·
      refine ⟨165348122459627145925797187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220464163279502861234396249 165348122459627145925797187)
      ·
        refine ⟨248022183689440718888695781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165348122459627145925797187 248022183689440718888695781)
        ·
          refine ⟨46504159441770134791630459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 248022183689440718888695781 46504159441770134791630459)
          ·
            refine ⟨69756239162655202187445689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46504159441770134791630459 69756239162655202187445689)
            ·
              refine ⟨52317179371991401640584267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69756239162655202187445689 52317179371991401640584267)
              ·
                refine ⟨78475769057987102460876401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52317179371991401640584267 78475769057987102460876401)
                ·
                  refine ⟨58856826793490326845657301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78475769057987102460876401 58856826793490326845657301)
                  ·
                    refine ⟨1379456877972429535445093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58856826793490326845657301 1379456877972429535445093)
                    ·
                      rfl

theorem cell23_8059448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 2, 7].length) (baseStart_8059448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059448 prefixEnd_8059448 := by exact prefixLift 8059448
  have htrace : WordTrace (prefixWord ++ tailWord_8059448) baseStart_8059448 baseEnd_8059448 := by
    simpa [prefixWord, tailWord_8059448, baseEnd_8059448] using wordTrace_append hprefix tailTrace_8059448
  have hstable : (prefixWord ++ tailWord_8059448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059448).length < 2 ^ (prefixWord ++ tailWord_8059448).sum := by decide
  have hdescent : baseEnd_8059448 < baseStart_8059448 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059472 : List Nat := [2, 1, 1, 1, 1, 3, 2, 6, 1, 3, 2]
def baseStart_8059472 : Nat := 118140960795 + 8059472 * 2 ^ 59
def prefixEnd_8059472 : Nat := 4983230072969 + 3 ^ 40 * 8059472 * 2
def baseEnd_8059472 : Nat := 4138382957452996512435169

theorem tailTrace_8059472 : CollatzResearch.WordTrace tailWord_8059472 prefixEnd_8059472 4138382957452996512435169 := by
  unfold tailWord_8059472
  simp only [CollatzResearch.WordTrace]
  refine ⟨146976546528958433539034335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195968728705277911385379113 146976546528958433539034335)
  ·
    refine ⟨220464819793437650308551503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146976546528958433539034335 220464819793437650308551503)
    ·
      refine ⟨330697229690156475462827255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220464819793437650308551503 330697229690156475462827255)
      ·
        refine ⟨496045844535234713194240883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330697229690156475462827255 496045844535234713194240883)
        ·
          refine ⟨744068766802852069791361325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496045844535234713194240883 744068766802852069791361325)
          ·
            refine ⟨279025787551069526171760497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 744068766802852069791361325 279025787551069526171760497)
            ·
              refine ⟨209269340663302144628820373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279025787551069526171760497 209269340663302144628820373)
              ·
                refine ⟨9809500343592288029475955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 209269340663302144628820373 9809500343592288029475955)
                ·
                  refine ⟨14714250515388432044213933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9809500343592288029475955 14714250515388432044213933)
                  ·
                    refine ⟨5517843943270662016580225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14714250515388432044213933 5517843943270662016580225)
                    ·
                      refine ⟨4138382957452996512435169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5517843943270662016580225 4138382957452996512435169)
                      ·
                        rfl

theorem cell23_8059472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 1, 3, 2].length) (baseStart_8059472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059472 prefixEnd_8059472 := by exact prefixLift 8059472
  have htrace : WordTrace (prefixWord ++ tailWord_8059472) baseStart_8059472 baseEnd_8059472 := by
    simpa [prefixWord, tailWord_8059472, baseEnd_8059472] using wordTrace_append hprefix tailTrace_8059472
  have hstable : (prefixWord ++ tailWord_8059472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059472).length < 2 ^ (prefixWord ++ tailWord_8059472).sum := by decide
  have hdescent : baseEnd_8059472 < baseStart_8059472 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059496 : List Nat := [2, 1, 4, 3, 2, 1, 2, 2, 2, 1, 3]
def baseStart_8059496 : Nat := 118140960795 + 8059496 * 2 ^ 59
def prefixEnd_8059496 : Nat := 4983230072969 + 3 ^ 40 * 8059496 * 2
def baseEnd_8059496 : Nat := 4138395280988704418535059

theorem tailTrace_8059496 : CollatzResearch.WordTrace tailWord_8059496 prefixEnd_8059496 4138395280988704418535059 := by
  unfold tailWord_8059496
  simp only [CollatzResearch.WordTrace]
  refine ⟨146976984204914959588471171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195969312273219946117961561 146976984204914959588471171)
  ·
    refine ⟨220465476307372439382706757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146976984204914959588471171 220465476307372439382706757)
    ·
      refine ⟨41337276807632332384257517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220465476307372439382706757 41337276807632332384257517)
      ·
        refine ⟨15501478802862124644096569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41337276807632332384257517 15501478802862124644096569)
        ·
          refine ⟨11626109102146593483072427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15501478802862124644096569 11626109102146593483072427)
          ·
            refine ⟨17439163653219890224608641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11626109102146593483072427 17439163653219890224608641)
            ·
              refine ⟨13079372739914917668456481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17439163653219890224608641 13079372739914917668456481)
              ·
                refine ⟨9809529554936188251342361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13079372739914917668456481 9809529554936188251342361)
                ·
                  refine ⟨7357147166202141188506771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9809529554936188251342361 7357147166202141188506771)
                  ·
                    refine ⟨11035720749303211782760157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7357147166202141188506771 11035720749303211782760157)
                    ·
                      refine ⟨4138395280988704418535059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11035720749303211782760157 4138395280988704418535059)
                      ·
                        rfl

theorem cell23_8059496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_8059496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059496 prefixEnd_8059496 := by exact prefixLift 8059496
  have htrace : WordTrace (prefixWord ++ tailWord_8059496) baseStart_8059496 baseEnd_8059496 := by
    simpa [prefixWord, tailWord_8059496, baseEnd_8059496] using wordTrace_append hprefix tailTrace_8059496
  have hstable : (prefixWord ++ tailWord_8059496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059496).length < 2 ^ (prefixWord ++ tailWord_8059496).sum := by decide
  have hdescent : baseEnd_8059496 < baseStart_8059496 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059525 : List Nat := [1, 3, 1, 1, 4, 3, 1, 2, 7]
def baseStart_8059525 : Nat := 118140960795 + 8059525 * 2 ^ 59
def prefixEnd_8059525 : Nat := 4983230072969 + 3 ^ 40 * 8059525 * 2
def baseEnd_8059525 : Nat := 459823352436409422785825

theorem tailTrace_8059525 : CollatzResearch.WordTrace tailWord_8059525 prefixEnd_8059525 459823352436409422785825 := by
  unfold tailWord_8059525
  simp only [CollatzResearch.WordTrace]
  refine ⟨293955026126724857129748029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195970017417816571419832019 293955026126724857129748029)
  ·
    refine ⟨110233134797521821423655511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293955026126724857129748029 110233134797521821423655511)
    ·
      refine ⟨165349702196282732135483267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110233134797521821423655511 165349702196282732135483267)
      ·
        refine ⟨248024553294424098203224901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165349702196282732135483267 248024553294424098203224901)
        ·
          refine ⟨46504603742704518413104669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 248024553294424098203224901 46504603742704518413104669)
          ·
            refine ⟨17439226403514194404914251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46504603742704518413104669 17439226403514194404914251)
            ·
              refine ⟨26158839605271291607371377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17439226403514194404914251 26158839605271291607371377)
              ·
                refine ⟨19619129703953468705528533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26158839605271291607371377 19619129703953468705528533)
                ·
                  refine ⟨459823352436409422785825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19619129703953468705528533 459823352436409422785825)
                  ·
                    rfl

theorem cell23_8059525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 7].length) (baseStart_8059525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059525 prefixEnd_8059525 := by exact prefixLift 8059525
  have htrace : WordTrace (prefixWord ++ tailWord_8059525) baseStart_8059525 baseEnd_8059525 := by
    simpa [prefixWord, tailWord_8059525, baseEnd_8059525] using wordTrace_append hprefix tailTrace_8059525
  have hstable : (prefixWord ++ tailWord_8059525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059525).length < 2 ^ (prefixWord ++ tailWord_8059525).sum := by decide
  have hdescent : baseEnd_8059525 < baseStart_8059525 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059553 : List Nat := [1, 2, 3, 3, 3, 2, 1, 2, 2, 2, 2]
def baseStart_8059553 : Nat := 118140960795 + 8059553 * 2 ^ 59
def prefixEnd_8059553 : Nat := 4983230072969 + 3 ^ 40 * 8059553 * 2
def baseEnd_8059553 : Nat := 4138424549386010695522297

theorem tailTrace_8059553 : CollatzResearch.WordTrace tailWord_8059553 prefixEnd_8059553 4138424549386010695522297 := by
  unfold tailWord_8059553
  simp only [CollatzResearch.WordTrace]
  refine ⟨293956047370623417911767313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195970698247082278607844875 293956047370623417911767313)
  ·
    refine ⟨220467035527967563433825485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293956047370623417911767313 220467035527967563433825485)
    ·
      refine ⟨82675138322987836287684557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220467035527967563433825485 82675138322987836287684557)
      ·
        refine ⟨31003176871120438607881709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82675138322987836287684557 31003176871120438607881709)
        ·
          refine ⟨11626191326670164477955641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31003176871120438607881709 11626191326670164477955641)
          ·
            refine ⟨8719643495002623358466731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11626191326670164477955641 8719643495002623358466731)
            ·
              refine ⟨13079465242503935037700097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8719643495002623358466731 13079465242503935037700097)
              ·
                refine ⟨9809598931877951278275073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13079465242503935037700097 9809598931877951278275073)
                ·
                  refine ⟨7357199198908463458706305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9809598931877951278275073 7357199198908463458706305)
                  ·
                    refine ⟨5517899399181347594029729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7357199198908463458706305 5517899399181347594029729)
                    ·
                      refine ⟨4138424549386010695522297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5517899399181347594029729 4138424549386010695522297)
                      ·
                        rfl

theorem cell23_8059553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_8059553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059553 prefixEnd_8059553 := by exact prefixLift 8059553
  have htrace : WordTrace (prefixWord ++ tailWord_8059553) baseStart_8059553 baseEnd_8059553 := by
    simpa [prefixWord, tailWord_8059553, baseEnd_8059553] using wordTrace_append hprefix tailTrace_8059553
  have hstable : (prefixWord ++ tailWord_8059553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059553).length < 2 ^ (prefixWord ++ tailWord_8059553).sum := by decide
  have hdescent : baseEnd_8059553 < baseStart_8059553 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059559 : List Nat := [1, 1, 6, 3, 1, 1, 2, 1, 7]
def baseStart_8059559 : Nat := 118140960795 + 8059559 * 2 ^ 59
def prefixEnd_8059559 : Nat := 4983230072969 + 3 ^ 40 * 8059559 * 2
def baseEnd_8059559 : Nat := 459825292252215296894141

theorem tailTrace_8059559 : CollatzResearch.WordTrace tailWord_8059559 prefixEnd_8059559 459825292252215296894141 := by
  unfold tailWord_8059559
  simp only [CollatzResearch.WordTrace]
  refine ⟨293956266208601680936485731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195970844139067787290990487 293956266208601680936485731)
  ·
    refine ⟨440934399312902521404728597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293956266208601680936485731 440934399312902521404728597)
    ·
      refine ⟨20668799967792305690846653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 440934399312902521404728597 20668799967792305690846653)
      ·
        refine ⟨7750799987922114634067495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20668799967792305690846653 7750799987922114634067495)
        ·
          refine ⟨11626199981883171951101243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7750799987922114634067495 11626199981883171951101243)
          ·
            refine ⟨17439299972824757926651865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11626199981883171951101243 17439299972824757926651865)
            ·
              refine ⟨13079474979618568444988899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17439299972824757926651865 13079474979618568444988899)
              ·
                refine ⟨19619212469427852667483349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13079474979618568444988899 19619212469427852667483349)
                ·
                  refine ⟨459825292252215296894141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19619212469427852667483349 459825292252215296894141)
                  ·
                    rfl

theorem cell23_8059559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 7].length) (baseStart_8059559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059559 prefixEnd_8059559 := by exact prefixLift 8059559
  have htrace : WordTrace (prefixWord ++ tailWord_8059559) baseStart_8059559 baseEnd_8059559 := by
    simpa [prefixWord, tailWord_8059559, baseEnd_8059559] using wordTrace_append hprefix tailTrace_8059559
  have hstable : (prefixWord ++ tailWord_8059559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059559).length < 2 ^ (prefixWord ++ tailWord_8059559).sum := by decide
  have hdescent : baseEnd_8059559 < baseStart_8059559 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059615 : List Nat := [1, 1, 2, 3, 2, 3, 2, 1, 8]
def baseStart_8059615 : Nat := 118140960795 + 8059615 * 2 ^ 59
def prefixEnd_8059615 : Nat := 4983230072969 + 3 ^ 40 * 8059615 * 2
def baseEnd_8059615 : Nat := 459828487242954383660779

theorem tailTrace_8059615 : CollatzResearch.WordTrace tailWord_8059615 prefixEnd_8059615 459828487242954383660779 := by
  unfold tailWord_8059615
  simp only [CollatzResearch.WordTrace]
  refine ⟨293958308696398802500524299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195972205797599201667016199 293958308696398802500524299)
  ·
    refine ⟨440937463044598203750786449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293958308696398802500524299 440937463044598203750786449)
    ·
      refine ⟨330703097283448652813089837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440937463044598203750786449 330703097283448652813089837)
      ·
        refine ⟨124013661481293244804908689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330703097283448652813089837 124013661481293244804908689)
        ·
          refine ⟨93010246110969933603681517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124013661481293244804908689 93010246110969933603681517)
          ·
            refine ⟨34878842291613725101380569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93010246110969933603681517 34878842291613725101380569)
            ·
              refine ⟨26159131718710293826035427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34878842291613725101380569 26159131718710293826035427)
              ·
                refine ⟨39238697578065440739053141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26159131718710293826035427 39238697578065440739053141)
                ·
                  refine ⟨459828487242954383660779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39238697578065440739053141 459828487242954383660779)
                  ·
                    rfl

theorem cell23_8059615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 8].length) (baseStart_8059615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059615 prefixEnd_8059615 := by exact prefixLift 8059615
  have htrace : WordTrace (prefixWord ++ tailWord_8059615) baseStart_8059615 baseEnd_8059615 := by
    simpa [prefixWord, tailWord_8059615, baseEnd_8059615] using wordTrace_append hprefix tailTrace_8059615
  have hstable : (prefixWord ++ tailWord_8059615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059615).length < 2 ^ (prefixWord ++ tailWord_8059615).sum := by decide
  have hdescent : baseEnd_8059615 < baseStart_8059615 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059619 : List Nat := [1, 1, 1, 7, 1, 1, 3, 1, 3, 4]
def baseStart_8059619 : Nat := 118140960795 + 8059619 * 2 ^ 59
def prefixEnd_8059619 : Nat := 4983230072969 + 3 ^ 40 * 8059619 * 2
def baseEnd_8059619 : Nat := 1379486146369735812432331

theorem tailTrace_8059619 : CollatzResearch.WordTrace tailWord_8059619 prefixEnd_8059619 1379486146369735812432331 := by
  unfold tailWord_8059619
  simp only [CollatzResearch.WordTrace]
  refine ⟨293958454588384311183669911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195972303058922874122446607 293958454588384311183669911)
  ·
    refine ⟨440937681882576466775504867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293958454588384311183669911 440937681882576466775504867)
    ·
      refine ⟨661406522823864700163257301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440937681882576466775504867 661406522823864700163257301)
      ·
        refine ⟨15501715378684328910076343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 661406522823864700163257301 15501715378684328910076343)
        ·
          refine ⟨23252573068026493365114515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15501715378684328910076343 23252573068026493365114515)
          ·
            refine ⟨34878859602039740047671773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23252573068026493365114515 34878859602039740047671773)
            ·
              refine ⟨13079572350764902517876915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34878859602039740047671773 13079572350764902517876915)
              ·
                refine ⟨19619358526147353776815373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13079572350764902517876915 19619358526147353776815373)
                ·
                  refine ⟨7357259447305257666305765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19619358526147353776815373 7357259447305257666305765)
                  ·
                    refine ⟨1379486146369735812432331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7357259447305257666305765 1379486146369735812432331)
                    ·
                      rfl

theorem cell23_8059619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 3, 4].length) (baseStart_8059619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059619 prefixEnd_8059619 := by exact prefixLift 8059619
  have htrace : WordTrace (prefixWord ++ tailWord_8059619) baseStart_8059619 baseEnd_8059619 := by
    simpa [prefixWord, tailWord_8059619, baseEnd_8059619] using wordTrace_append hprefix tailTrace_8059619
  have hstable : (prefixWord ++ tailWord_8059619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059619).length < 2 ^ (prefixWord ++ tailWord_8059619).sum := by decide
  have hdescent : baseEnd_8059619 < baseStart_8059619 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059646 : List Nat := [4, 2, 2, 1, 2, 2, 2, 1, 2, 2, 3]
def baseStart_8059646 : Nat := 118140960795 + 8059646 * 2 ^ 59
def prefixEnd_8059646 : Nat := 4983230072969 + 3 ^ 40 * 8059646 * 2
def baseEnd_8059646 : Nat := 4138472303086878831659369

theorem tailTrace_8059646 : CollatzResearch.WordTrace tailWord_8059646 prefixEnd_8059646 4138472303086878831659369 := by
  unfold tailWord_8059646
  simp only [CollatzResearch.WordTrace]
  refine ⟨36744929919910811849362849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195972959572857663196601861 36744929919910811849362849)
  ·
    refine ⟨27558697439933108887022137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36744929919910811849362849 27558697439933108887022137)
    ·
      refine ⟨20669023079949831665266603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27558697439933108887022137 20669023079949831665266603)
      ·
        refine ⟨31003534619924747497899905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20669023079949831665266603 31003534619924747497899905)
        ·
          refine ⟨23252650964943560623424929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31003534619924747497899905 23252650964943560623424929)
          ·
            refine ⟨17439488223707670467568697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23252650964943560623424929 17439488223707670467568697)
            ·
              refine ⟨13079616167780752850676523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17439488223707670467568697 13079616167780752850676523)
              ·
                refine ⟨19619424251671129276014785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13079616167780752850676523 19619424251671129276014785)
                ·
                  refine ⟨14714568188753346957011089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19619424251671129276014785 14714568188753346957011089)
                  ·
                    refine ⟨11035926141565010217758317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14714568188753346957011089 11035926141565010217758317)
                    ·
                      refine ⟨4138472303086878831659369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11035926141565010217758317 4138472303086878831659369)
                      ·
                        rfl

theorem cell23_8059646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_8059646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059646 prefixEnd_8059646 := by exact prefixLift 8059646
  have htrace : WordTrace (prefixWord ++ tailWord_8059646) baseStart_8059646 baseEnd_8059646 := by
    simpa [prefixWord, tailWord_8059646, baseEnd_8059646] using wordTrace_append hprefix tailTrace_8059646
  have hstable : (prefixWord ++ tailWord_8059646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059646).length < 2 ^ (prefixWord ++ tailWord_8059646).sum := by decide
  have hdescent : baseEnd_8059646 < baseStart_8059646 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059666 : List Nat := [3, 2, 4, 1, 2, 1, 2, 2, 6]
def baseStart_8059666 : Nat := 118140960795 + 8059666 * 2 ^ 59
def prefixEnd_8059666 : Nat := 4983230072969 + 3 ^ 40 * 8059666 * 2
def baseEnd_8059666 : Nat := 459831396966663194823253

theorem tailTrace_8059666 : CollatzResearch.WordTrace tailWord_8059666 prefixEnd_8059666 459831396966663194823253 := by
  unfold tailWord_8059666
  simp only [CollatzResearch.WordTrace]
  refine ⟨73490042204803509552657713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195973445879476025473753901 73490042204803509552657713)
  ·
    refine ⟨55117531653602632164493285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73490042204803509552657713 55117531653602632164493285)
    ·
      refine ⟨10334537185050493530842491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55117531653602632164493285 10334537185050493530842491)
      ·
        refine ⟨15501805777575740296263737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10334537185050493530842491 15501805777575740296263737)
        ·
          refine ⟨11626354333181805222197803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15501805777575740296263737 11626354333181805222197803)
          ·
            refine ⟨17439531499772707833296705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11626354333181805222197803 17439531499772707833296705)
            ·
              refine ⟨13079648624829530874972529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17439531499772707833296705 13079648624829530874972529)
              ·
                refine ⟨9809736468622148156229397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13079648624829530874972529 9809736468622148156229397)
                ·
                  refine ⟨459831396966663194823253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9809736468622148156229397 459831396966663194823253)
                  ·
                    rfl

theorem cell23_8059666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 6].length) (baseStart_8059666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059666 prefixEnd_8059666 := by exact prefixLift 8059666
  have htrace : WordTrace (prefixWord ++ tailWord_8059666) baseStart_8059666 baseEnd_8059666 := by
    simpa [prefixWord, tailWord_8059666, baseEnd_8059666] using wordTrace_append hprefix tailTrace_8059666
  have hstable : (prefixWord ++ tailWord_8059666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059666).length < 2 ^ (prefixWord ++ tailWord_8059666).sum := by decide
  have hdescent : baseEnd_8059666 < baseStart_8059666 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059669 : List Nat := [1, 3, 2, 1, 2, 2, 1, 4, 2, 3, 2]
def baseStart_8059669 : Nat := 118140960795 + 8059669 * 2 ^ 59
def prefixEnd_8059669 : Nat := 4983230072969 + 3 ^ 40 * 8059669 * 2
def baseEnd_8059669 : Nat := 4138484113141932241671763

theorem tailTrace_8059669 : CollatzResearch.WordTrace tailWord_8059669 prefixEnd_8059669 4138484113141932241671763 := by
  unfold tailWord_8059669
  simp only [CollatzResearch.WordTrace]
  refine ⟨293960278238203169722990061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195973518825468779815326707 293960278238203169722990061)
  ·
    refine ⟨110235104339326188646121273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293960278238203169722990061 110235104339326188646121273)
    ·
      refine ⟨82676328254494641484590955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110235104339326188646121273 82676328254494641484590955)
      ·
        refine ⟨124014492381741962226886433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82676328254494641484590955 124014492381741962226886433)
        ·
          refine ⟨93010869286306471670164825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124014492381741962226886433 93010869286306471670164825)
          ·
            refine ⟨69758151964729853752623619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93010869286306471670164825 69758151964729853752623619)
            ·
              refine ⟨104637227947094780628935429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69758151964729853752623619 104637227947094780628935429)
              ·
                refine ⟨19619480240080271367925393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104637227947094780628935429 19619480240080271367925393)
                ·
                  refine ⟨14714610180060203525944045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19619480240080271367925393 14714610180060203525944045)
                  ·
                    refine ⟨5517978817522576322229017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14714610180060203525944045 5517978817522576322229017)
                    ·
                      refine ⟨4138484113141932241671763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5517978817522576322229017 4138484113141932241671763)
                      ·
                        rfl

theorem cell23_8059669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 3, 2].length) (baseStart_8059669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059669 prefixEnd_8059669 := by exact prefixLift 8059669
  have htrace : WordTrace (prefixWord ++ tailWord_8059669) baseStart_8059669 baseEnd_8059669 := by
    simpa [prefixWord, tailWord_8059669, baseEnd_8059669] using wordTrace_append hprefix tailTrace_8059669
  have hstable : (prefixWord ++ tailWord_8059669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059669).length < 2 ^ (prefixWord ++ tailWord_8059669).sum := by decide
  have hdescent : baseEnd_8059669 < baseStart_8059669 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059692 : List Nat := [2, 2, 1, 1, 1, 4, 4, 1, 1, 6]
def baseStart_8059692 : Nat := 118140960795 + 8059692 * 2 ^ 59
def prefixEnd_8059692 : Nat := 4983230072969 + 3 ^ 40 * 8059692 * 2
def baseEnd_8059692 : Nat := 1379498641065661883894719

theorem tailTrace_8059692 : CollatzResearch.WordTrace tailWord_8059692 prefixEnd_8059692 1379498641065661883894719 := by
  unfold tailWord_8059692
  simp only [CollatzResearch.WordTrace]
  refine ⟨146980558558559922325538665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195974078078079896434051553 146980558558559922325538665)
  ·
    refine ⟨110235418918919941744153999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146980558558559922325538665 110235418918919941744153999)
    ·
      refine ⟨165353128378379912616230999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110235418918919941744153999 165353128378379912616230999)
      ·
        refine ⟨248029692567569868924346499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165353128378379912616230999 248029692567569868924346499)
        ·
          refine ⟨372044538851354803386519749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248029692567569868924346499 372044538851354803386519749)
          ·
            refine ⟨69758351034629025634972453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 372044538851354803386519749 69758351034629025634972453)
            ·
              refine ⟨13079690818992942306557335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69758351034629025634972453 13079690818992942306557335)
              ·
                refine ⟨19619536228489413459836003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13079690818992942306557335 19619536228489413459836003)
                ·
                  refine ⟨29429304342734120189754005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19619536228489413459836003 29429304342734120189754005)
                  ·
                    refine ⟨1379498641065661883894719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29429304342734120189754005 1379498641065661883894719)
                    ·
                      rfl

theorem cell23_8059692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 6].length) (baseStart_8059692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059692 prefixEnd_8059692 := by exact prefixLift 8059692
  have htrace : WordTrace (prefixWord ++ tailWord_8059692) baseStart_8059692 baseEnd_8059692 := by
    simpa [prefixWord, tailWord_8059692, baseEnd_8059692] using wordTrace_append hprefix tailTrace_8059692
  have hstable : (prefixWord ++ tailWord_8059692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059692).length < 2 ^ (prefixWord ++ tailWord_8059692).sum := by decide
  have hdescent : baseEnd_8059692 < baseStart_8059692 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059710 : List Nat := [4, 2, 1, 2, 3, 1, 2, 3, 1, 1, 3]
def baseStart_8059710 : Nat := 118140960795 + 8059710 * 2 ^ 59
def prefixEnd_8059710 : Nat := 4983230072969 + 3 ^ 40 * 8059710 * 2
def baseEnd_8059710 : Nat := 4138505165848766581259075

theorem tailTrace_8059710 : CollatzResearch.WordTrace tailWord_8059710 prefixEnd_8059710 4138505165848766581259075 := by
  unfold tailWord_8059710
  simp only [CollatzResearch.WordTrace]
  refine ⟨36745221703881829215654073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195974515754036422483488389 36745221703881829215654073)
  ·
    refine ⟨27558916277911371911740555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36745221703881829215654073 27558916277911371911740555)
    ·
      refine ⟨41338374416867057867610833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27558916277911371911740555 41338374416867057867610833)
      ·
        refine ⟨31003780812650293400708125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41338374416867057867610833 31003780812650293400708125)
        ·
          refine ⟨11626417804743860025265547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31003780812650293400708125 11626417804743860025265547)
          ·
            refine ⟨17439626707115790037898321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11626417804743860025265547 17439626707115790037898321)
            ·
              refine ⟨13079720030336842528423741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17439626707115790037898321 13079720030336842528423741)
              ·
                refine ⟨4904895011376315948158903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13079720030336842528423741 4904895011376315948158903)
                ·
                  refine ⟨7357342517064473922238355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4904895011376315948158903 7357342517064473922238355)
                  ·
                    refine ⟨11036013775596710883357533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7357342517064473922238355 11036013775596710883357533)
                    ·
                      refine ⟨4138505165848766581259075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11036013775596710883357533 4138505165848766581259075)
                      ·
                        rfl

theorem cell23_8059710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_8059710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059710 prefixEnd_8059710 := by exact prefixLift 8059710
  have htrace : WordTrace (prefixWord ++ tailWord_8059710) baseStart_8059710 baseEnd_8059710 := by
    simpa [prefixWord, tailWord_8059710, baseEnd_8059710] using wordTrace_append hprefix tailTrace_8059710
  have hstable : (prefixWord ++ tailWord_8059710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059710).length < 2 ^ (prefixWord ++ tailWord_8059710).sum := by decide
  have hdescent : baseEnd_8059710 < baseStart_8059710 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
