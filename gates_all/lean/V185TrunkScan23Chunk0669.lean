import V185TrunkScan23Chunk0668

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3955714 : List Nat := [3, 4, 1, 3, 1, 1, 2, 2, 2, 4]
def baseStart_3955714 : Nat := 118140960795 + 3955714 * 2 ^ 59
def prefixEnd_3955714 : Nat := 4983230072969 + 3 ^ 40 * 3955714 * 2
def baseEnd_3955714 : Nat := 677060871239813828161003

theorem tailTrace_3955714 : CollatzResearch.WordTrace tailWord_3955714 prefixEnd_3955714 677060871239813828161003 := by
  unfold tailWord_3955714
  simp only [CollatzResearch.WordTrace]
  refine ⟨36069185597782808752616549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96184494927420823340310797 36069185597782808752616549)
  ·
    refine ⟨6762972299584276641115603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36069185597782808752616549 6762972299584276641115603)
    ·
      refine ⟨10144458449376414961673405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6762972299584276641115603 10144458449376414961673405)
      ·
        refine ⟨3804171918516155610627527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10144458449376414961673405 3804171918516155610627527)
        ·
          refine ⟨5706257877774233415941291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3804171918516155610627527 5706257877774233415941291)
          ·
            refine ⟨8559386816661350123911937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5706257877774233415941291 8559386816661350123911937)
            ·
              refine ⟨6419540112496012592933953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8559386816661350123911937 6419540112496012592933953)
              ·
                refine ⟨4814655084372009444700465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6419540112496012592933953 4814655084372009444700465)
                ·
                  refine ⟨3610991313279007083525349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4814655084372009444700465 3610991313279007083525349)
                  ·
                    refine ⟨677060871239813828161003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3610991313279007083525349 677060871239813828161003)
                    ·
                      rfl

theorem cell23_3955714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_3955714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955714 prefixEnd_3955714 := by exact prefixLift 3955714
  have htrace : WordTrace (prefixWord ++ tailWord_3955714) baseStart_3955714 baseEnd_3955714 := by
    simpa [prefixWord, tailWord_3955714, baseEnd_3955714] using wordTrace_append hprefix tailTrace_3955714
  have hstable : (prefixWord ++ tailWord_3955714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955714).length < 2 ^ (prefixWord ++ tailWord_3955714).sum := by decide
  have hdescent : baseEnd_3955714 < baseStart_3955714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955720 : List Nat := [2, 1, 3, 2, 1, 3, 1, 4, 2, 1, 3]
def baseStart_3955720 : Nat := 118140960795 + 3955720 * 2 ^ 59
def prefixEnd_3955720 : Nat := 4983230072969 + 3 ^ 40 * 3955720 * 2
def baseEnd_3955720 : Nat := 2031185694603368461007981

theorem tailTrace_3955720 : CollatzResearch.WordTrace tailWord_3955720 prefixEnd_3955720 2031185694603368461007981 := by
  unfold tailWord_3955720
  simp only [CollatzResearch.WordTrace]
  refine ⟨72138480614554749017592307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96184640819406332023456409 72138480614554749017592307)
  ·
    refine ⟨108207720921832123526388461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72138480614554749017592307 108207720921832123526388461)
    ·
      refine ⟨40577895345687046322395673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108207720921832123526388461 40577895345687046322395673)
      ·
        refine ⟨30433421509265284741796755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40577895345687046322395673 30433421509265284741796755)
        ·
          refine ⟨45650132263897927112695133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30433421509265284741796755 45650132263897927112695133)
          ·
            refine ⟨17118799598961722667260675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45650132263897927112695133 17118799598961722667260675)
            ·
              refine ⟨25678199398442584000891013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17118799598961722667260675 25678199398442584000891013)
              ·
                refine ⟨4814662387207984500167065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25678199398442584000891013 4814662387207984500167065)
                ·
                  refine ⟨3610996790405988375125299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4814662387207984500167065 3610996790405988375125299)
                  ·
                    refine ⟨5416495185608982562687949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3610996790405988375125299 5416495185608982562687949)
                    ·
                      refine ⟨2031185694603368461007981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5416495185608982562687949 2031185694603368461007981)
                      ·
                        rfl

theorem cell23_3955720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_3955720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955720 prefixEnd_3955720 := by exact prefixLift 3955720
  have htrace : WordTrace (prefixWord ++ tailWord_3955720) baseStart_3955720 baseEnd_3955720 := by
    simpa [prefixWord, tailWord_3955720, baseEnd_3955720] using wordTrace_append hprefix tailTrace_3955720
  have hstable : (prefixWord ++ tailWord_3955720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955720).length < 2 ^ (prefixWord ++ tailWord_3955720).sum := by decide
  have hdescent : baseEnd_3955720 < baseStart_3955720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955736 : List Nat := [2, 1, 2, 3, 2, 2, 1, 1, 1, 8]
def baseStart_3955736 : Nat := 118140960795 + 3955736 * 2 ^ 59
def prefixEnd_3955736 : Nat := 4983230072969 + 3 ^ 40 * 3955736 * 2
def baseEnd_3955736 : Nat := 677064636764613466135969

theorem tailTrace_3955736 : CollatzResearch.WordTrace tailWord_3955736 prefixEnd_3955736 677064636764613466135969 := by
  unfold tailWord_3955736
  simp only [CollatzResearch.WordTrace]
  refine ⟨72138772398525766383883531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96185029864701021845178041 72138772398525766383883531)
  ·
    refine ⟨108208158597788649575825297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72138772398525766383883531 108208158597788649575825297)
    ·
      refine ⟨81156118948341487181868973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108208158597788649575825297 81156118948341487181868973)
      ·
        refine ⟨30433544605628057693200865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81156118948341487181868973 30433544605628057693200865)
        ·
          refine ⟨22825158454221043269900649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30433544605628057693200865 22825158454221043269900649)
          ·
            refine ⟨17118868840665782452425487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22825158454221043269900649 17118868840665782452425487)
            ·
              refine ⟨25678303260998673678638231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17118868840665782452425487 25678303260998673678638231)
              ·
                refine ⟨38517454891498010517957347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25678303260998673678638231 38517454891498010517957347)
                ·
                  refine ⟨57776182337247015776936021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38517454891498010517957347 57776182337247015776936021)
                  ·
                    refine ⟨677064636764613466135969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57776182337247015776936021 677064636764613466135969)
                    ·
                      rfl

theorem cell23_3955736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 1, 8].length) (baseStart_3955736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955736 prefixEnd_3955736 := by exact prefixLift 3955736
  have htrace : WordTrace (prefixWord ++ tailWord_3955736) baseStart_3955736 baseEnd_3955736 := by
    simpa [prefixWord, tailWord_3955736, baseEnd_3955736] using wordTrace_append hprefix tailTrace_3955736
  have hstable : (prefixWord ++ tailWord_3955736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955736).length < 2 ^ (prefixWord ++ tailWord_3955736).sum := by decide
  have hdescent : baseEnd_3955736 < baseStart_3955736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955756 : List Nat := [2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 4]
def baseStart_3955756 : Nat := 118140960795 + 3955756 * 2 ^ 59
def prefixEnd_3955756 : Nat := 4983230072969 + 3 ^ 40 * 3955756 * 2
def baseEnd_3955756 : Nat := 2031204179906930320157815

theorem tailTrace_3955756 : CollatzResearch.WordTrace tailWord_3955756 prefixEnd_3955756 2031204179906930320157815 := by
  unfold tailWord_3955756
  simp only [CollatzResearch.WordTrace]
  refine ⟨72139137128489538091747561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96185516171319384122330081 72139137128489538091747561)
  ·
    refine ⟨54104352846367153568810671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72139137128489538091747561 54104352846367153568810671)
    ·
      refine ⟨81156529269550730353216007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54104352846367153568810671 81156529269550730353216007)
      ·
        refine ⟨121734793904326095529824011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81156529269550730353216007 121734793904326095529824011)
        ·
          refine ⟨182602190856489143294736017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121734793904326095529824011 182602190856489143294736017)
          ·
            refine ⟨136951643142366857471052013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182602190856489143294736017 136951643142366857471052013)
            ·
              refine ⟨51356866178387571551644505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136951643142366857471052013 51356866178387571551644505)
              ·
                refine ⟨38517649633790678663733379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51356866178387571551644505 38517649633790678663733379)
                ·
                  refine ⟨57776474450686017995600069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38517649633790678663733379 57776474450686017995600069)
                  ·
                    refine ⟨10833088959503628374175013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57776474450686017995600069 10833088959503628374175013)
                    ·
                      refine ⟨2031204179906930320157815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10833088959503628374175013 2031204179906930320157815)
                      ·
                        rfl

theorem cell23_3955756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 4].length) (baseStart_3955756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955756 prefixEnd_3955756 := by exact prefixLift 3955756
  have htrace : WordTrace (prefixWord ++ tailWord_3955756) baseStart_3955756 baseEnd_3955756 := by
    simpa [prefixWord, tailWord_3955756, baseEnd_3955756] using wordTrace_append hprefix tailTrace_3955756
  have hstable : (prefixWord ++ tailWord_3955756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955756).length < 2 ^ (prefixWord ++ tailWord_3955756).sum := by decide
  have hdescent : baseEnd_3955756 < baseStart_3955756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955760 : List Nat := [2, 1, 1, 1, 2, 4, 2, 2, 4, 2, 2]
def baseStart_3955760 : Nat := 118140960795 + 3955760 * 2 ^ 59
def prefixEnd_3955760 : Nat := 4983230072969 + 3 ^ 40 * 3955760 * 2
def baseEnd_3955760 : Nat := 2031206233829548304507797

theorem tailTrace_3955760 : CollatzResearch.WordTrace tailWord_3955760 prefixEnd_3955760 2031206233829548304507797 := by
  unfold tailWord_3955760
  simp only [CollatzResearch.WordTrace]
  refine ⟨72139210074482292433320367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96185613432643056577760489 72139210074482292433320367)
  ·
    refine ⟨108208815111723438649980551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72139210074482292433320367 108208815111723438649980551)
    ·
      refine ⟨162313222667585157974970827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108208815111723438649980551 162313222667585157974970827)
      ·
        refine ⟨243469834001377736962456241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162313222667585157974970827 243469834001377736962456241)
        ·
          refine ⟨182602375501033302721842181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243469834001377736962456241 182602375501033302721842181)
          ·
            refine ⟨34237945406443744260345409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182602375501033302721842181 34237945406443744260345409)
            ·
              refine ⟨25678459054832808195259057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34237945406443744260345409 25678459054832808195259057)
              ·
                refine ⟨19258844291124606146444293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25678459054832808195259057 19258844291124606146444293)
                ·
                  refine ⟨3611033304585863652458305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19258844291124606146444293 3611033304585863652458305)
                  ·
                    refine ⟨2708274978439397739343729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3611033304585863652458305 2708274978439397739343729)
                    ·
                      refine ⟨2031206233829548304507797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2708274978439397739343729 2031206233829548304507797)
                      ·
                        rfl

theorem cell23_3955760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 4, 2, 2].length) (baseStart_3955760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955760 prefixEnd_3955760 := by exact prefixLift 3955760
  have htrace : WordTrace (prefixWord ++ tailWord_3955760) baseStart_3955760 baseEnd_3955760 := by
    simpa [prefixWord, tailWord_3955760, baseEnd_3955760] using wordTrace_append hprefix tailTrace_3955760
  have hstable : (prefixWord ++ tailWord_3955760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955760).length < 2 ^ (prefixWord ++ tailWord_3955760).sum := by decide
  have hdescent : baseEnd_3955760 < baseStart_3955760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955764 : List Nat := [2, 5, 1, 2, 1, 2, 1, 3, 1, 3, 2]
def baseStart_3955764 : Nat := 118140960795 + 3955764 * 2 ^ 59
def prefixEnd_3955764 : Nat := 4983230072969 + 3 ^ 40 * 3955764 * 2
def baseEnd_3955764 : Nat := 2031208287752166288857779

theorem tailTrace_3955764 : CollatzResearch.WordTrace tailWord_3955764 prefixEnd_3955764 2031208287752166288857779 := by
  unfold tailWord_3955764
  simp only [CollatzResearch.WordTrace]
  refine ⟨72139283020475046774893173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96185710693966729033190897 72139283020475046774893173)
  ·
    refine ⟨6763057783169535635146235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72139283020475046774893173 6763057783169535635146235)
    ·
      refine ⟨10144586674754303452719353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6763057783169535635146235 10144586674754303452719353)
      ·
        refine ⟨7608440006065727589539515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10144586674754303452719353 7608440006065727589539515)
        ·
          refine ⟨11412660009098591384309273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7608440006065727589539515 11412660009098591384309273)
          ·
            refine ⟨8559495006823943538231955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11412660009098591384309273 8559495006823943538231955)
            ·
              refine ⟨12839242510235915307347933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8559495006823943538231955 12839242510235915307347933)
              ·
                refine ⟨4814715941338468240255475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12839242510235915307347933 4814715941338468240255475)
                ·
                  refine ⟨7222073912007702360383213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4814715941338468240255475 7222073912007702360383213)
                  ·
                    refine ⟨2708277717002888385143705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7222073912007702360383213 2708277717002888385143705)
                    ·
                      refine ⟨2031208287752166288857779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2708277717002888385143705 2031208287752166288857779)
                      ·
                        rfl

theorem cell23_3955764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_3955764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955764 prefixEnd_3955764 := by exact prefixLift 3955764
  have htrace : WordTrace (prefixWord ++ tailWord_3955764) baseStart_3955764 baseEnd_3955764 := by
    simpa [prefixWord, tailWord_3955764, baseEnd_3955764] using wordTrace_append hprefix tailTrace_3955764
  have hstable : (prefixWord ++ tailWord_3955764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955764).length < 2 ^ (prefixWord ++ tailWord_3955764).sum := by decide
  have hdescent : baseEnd_3955764 < baseStart_3955764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955773 : List Nat := [1, 4, 1, 3, 1, 2, 1, 2, 2, 2, 4]
def baseStart_3955773 : Nat := 118140960795 + 3955773 * 2 ^ 59
def prefixEnd_3955773 : Nat := 4983230072969 + 3 ^ 40 * 3955773 * 2
def baseEnd_3955773 : Nat := 2031212909078056753645237

theorem tailTrace_3955773 : CollatzResearch.WordTrace tailWord_3955773 prefixEnd_3955773 2031212909078056753645237 := by
  unfold tailWord_3955773
  simp only [CollatzResearch.WordTrace]
  refine ⟨144278894297917488086863973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96185929531944992057909315 144278894297917488086863973)
  ·
    refine ⟨27052292680859529016286995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144278894297917488086863973 27052292680859529016286995)
    ·
      refine ⟨40578439021289293524430493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27052292680859529016286995 40578439021289293524430493)
      ·
        refine ⟨15216914632983485071661435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40578439021289293524430493 15216914632983485071661435)
        ·
          refine ⟨22825371949475227607492153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15216914632983485071661435 22825371949475227607492153)
          ·
            refine ⟨17119028962106420705619115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22825371949475227607492153 17119028962106420705619115)
            ·
              refine ⟨25678543443159631058428673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17119028962106420705619115 25678543443159631058428673)
              ·
                refine ⟨19258907582369723293821505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25678543443159631058428673 19258907582369723293821505)
                ·
                  refine ⟨14444180686777292470366129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19258907582369723293821505 14444180686777292470366129)
                  ·
                    refine ⟨10833135515082969352774597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14444180686777292470366129 10833135515082969352774597)
                    ·
                      refine ⟨2031212909078056753645237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10833135515082969352774597 2031212909078056753645237)
                      ·
                        rfl

theorem cell23_3955773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_3955773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955773 prefixEnd_3955773 := by exact prefixLift 3955773
  have htrace : WordTrace (prefixWord ++ tailWord_3955773) baseStart_3955773 baseEnd_3955773 := by
    simpa [prefixWord, tailWord_3955773, baseEnd_3955773] using wordTrace_append hprefix tailTrace_3955773
  have hstable : (prefixWord ++ tailWord_3955773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955773).length < 2 ^ (prefixWord ++ tailWord_3955773).sum := by decide
  have hdescent : baseEnd_3955773 < baseStart_3955773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955783 : List Nat := [1, 1, 4, 1, 3, 3, 2, 1, 7]
def baseStart_3955783 : Nat := 118140960795 + 3955783 * 2 ^ 59
def prefixEnd_3955783 : Nat := 4983230072969 + 3 ^ 40 * 3955783 * 2
def baseEnd_3955783 : Nat := 225690893764955746057799

theorem tailTrace_3955783 : CollatzResearch.WordTrace tailWord_3955783 prefixEnd_3955783 225690893764955746057799 := by
  unfold tailWord_3955783
  simp only [CollatzResearch.WordTrace]
  refine ⟨144279259027881259794728003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96186172685254173196485335 144279259027881259794728003)
  ·
    refine ⟨216418888541821889692092005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144279259027881259794728003 216418888541821889692092005)
    ·
      refine ⟨40578541601591604317267251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216418888541821889692092005 40578541601591604317267251)
      ·
        refine ⟨60867812402387406475900877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40578541601591604317267251 60867812402387406475900877)
        ·
          refine ⟨22825429650895277428462829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60867812402387406475900877 22825429650895277428462829)
          ·
            refine ⟨8559536119085729035673561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22825429650895277428462829 8559536119085729035673561)
            ·
              refine ⟨6419652089314296776755171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8559536119085729035673561 6419652089314296776755171)
              ·
                refine ⟨9629478133971445165132757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6419652089314296776755171 9629478133971445165132757)
                ·
                  refine ⟨225690893764955746057799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9629478133971445165132757 225690893764955746057799)
                  ·
                    rfl

theorem cell23_3955783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 7].length) (baseStart_3955783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955783 prefixEnd_3955783 := by exact prefixLift 3955783
  have htrace : WordTrace (prefixWord ++ tailWord_3955783) baseStart_3955783 baseEnd_3955783 := by
    simpa [prefixWord, tailWord_3955783, baseEnd_3955783] using wordTrace_append hprefix tailTrace_3955783
  have hstable : (prefixWord ++ tailWord_3955783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955783).length < 2 ^ (prefixWord ++ tailWord_3955783).sum := by decide
  have hdescent : baseEnd_3955783 < baseStart_3955783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955793 : List Nat := [1, 2, 2, 1, 3, 1, 4, 1, 2, 3, 3]
def baseStart_3955793 : Nat := 118140960795 + 3955793 * 2 ^ 59
def prefixEnd_3955793 : Nat := 4983230072969 + 3 ^ 40 * 3955793 * 2
def baseEnd_3955793 : Nat := 2031223178691146675395145

theorem tailTrace_3955793 : CollatzResearch.WordTrace tailWord_3955793 prefixEnd_3955793 2031223178691146675395145 := by
  unfold tailWord_3955793
  simp only [CollatzResearch.WordTrace]
  refine ⟨144279623757845031502592033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96186415838563354335061355 144279623757845031502592033)
  ·
    refine ⟨108209717818383773626944025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144279623757845031502592033 108209717818383773626944025)
    ·
      refine ⟨81157288363787830220208019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108209717818383773626944025 81157288363787830220208019)
      ·
        refine ⟨121735932545681745330312029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81157288363787830220208019 121735932545681745330312029)
        ·
          refine ⟨45650974704630654498867011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121735932545681745330312029 45650974704630654498867011)
          ·
            refine ⟨68476462056945981748300517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45650974704630654498867011 68476462056945981748300517)
            ·
              refine ⟨12839336635677371577806347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68476462056945981748300517 12839336635677371577806347)
              ·
                refine ⟨19259004953516057366709521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12839336635677371577806347 19259004953516057366709521)
                ·
                  refine ⟨14444253715137043025032141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19259004953516057366709521 14444253715137043025032141)
                  ·
                    refine ⟨5416595143176391134387053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14444253715137043025032141 5416595143176391134387053)
                    ·
                      refine ⟨2031223178691146675395145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5416595143176391134387053 2031223178691146675395145)
                      ·
                        rfl

theorem cell23_3955793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 3, 3].length) (baseStart_3955793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955793 prefixEnd_3955793 := by exact prefixLift 3955793
  have htrace : WordTrace (prefixWord ++ tailWord_3955793) baseStart_3955793 baseEnd_3955793 := by
    simpa [prefixWord, tailWord_3955793, baseEnd_3955793] using wordTrace_append hprefix tailTrace_3955793
  have hstable : (prefixWord ++ tailWord_3955793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955793).length < 2 ^ (prefixWord ++ tailWord_3955793).sum := by decide
  have hdescent : baseEnd_3955793 < baseStart_3955793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955813 : List Nat := [1, 3, 1, 3, 2, 1, 2, 3, 2, 5]
def baseStart_3955813 : Nat := 118140960795 + 3955813 * 2 ^ 59
def prefixEnd_3955813 : Nat := 4983230072969 + 3 ^ 40 * 3955813 * 2
def baseEnd_3955813 : Nat := 677077816101412199048351

theorem tailTrace_3955813 : CollatzResearch.WordTrace tailWord_3955813 prefixEnd_3955813 677077816101412199048351 := by
  unfold tailWord_3955813
  simp only [CollatzResearch.WordTrace]
  refine ⟨144280353217772574918320093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96186902145181716612213395 144280353217772574918320093)
  ·
    refine ⟨54105132456664715594370035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144280353217772574918320093 54105132456664715594370035)
    ·
      refine ⟨81157698684997073391555053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54105132456664715594370035 81157698684997073391555053)
      ·
        refine ⟨30434137006873902521833145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81157698684997073391555053 30434137006873902521833145)
        ·
          refine ⟨22825602755155426891374859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30434137006873902521833145 22825602755155426891374859)
          ·
            refine ⟨34238404132733140337062289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22825602755155426891374859 34238404132733140337062289)
            ·
              refine ⟨25678803099549855252796717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34238404132733140337062289 25678803099549855252796717)
              ·
                refine ⟨9629551162331195719798769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25678803099549855252796717 9629551162331195719798769)
                ·
                  refine ⟨7222163371748396789849077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9629551162331195719798769 7222163371748396789849077)
                  ·
                    refine ⟨677077816101412199048351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7222163371748396789849077 677077816101412199048351)
                    ·
                      rfl

theorem cell23_3955813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 5].length) (baseStart_3955813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955813 prefixEnd_3955813 := by exact prefixLift 3955813
  have htrace : WordTrace (prefixWord ++ tailWord_3955813) baseStart_3955813 baseEnd_3955813 := by
    simpa [prefixWord, tailWord_3955813, baseEnd_3955813] using wordTrace_append hprefix tailTrace_3955813
  have hstable : (prefixWord ++ tailWord_3955813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955813).length < 2 ^ (prefixWord ++ tailWord_3955813).sum := by decide
  have hdescent : baseEnd_3955813 < baseStart_3955813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955830 : List Nat := [5, 1, 1, 2, 1, 1, 3, 2, 2, 5]
def baseStart_3955830 : Nat := 118140960795 + 3955830 * 2 ^ 59
def prefixEnd_3955830 : Nat := 4983230072969 + 3 ^ 40 * 3955830 * 2
def baseEnd_3955830 : Nat := 677080725825121010210825

theorem tailTrace_3955830 : CollatzResearch.WordTrace tailWord_3955830 prefixEnd_3955830 677080725825121010210825 := by
  unfold tailWord_3955830
  simp only [CollatzResearch.WordTrace]
  refine ⟨9017560828669436676355559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96187315505807324547792629 9017560828669436676355559)
  ·
    refine ⟨13526341243004155014533339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9017560828669436676355559 13526341243004155014533339)
    ·
      refine ⟨20289511864506232521800009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13526341243004155014533339 20289511864506232521800009)
      ·
        refine ⟨15217133898379674391350007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20289511864506232521800009 15217133898379674391350007)
        ·
          refine ⟨22825700847569511587025011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15217133898379674391350007 22825700847569511587025011)
          ·
            refine ⟨34238551271354267380537517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22825700847569511587025011 34238551271354267380537517)
            ·
              refine ⟨12839456726757850267701569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34238551271354267380537517 12839456726757850267701569)
              ·
                refine ⟨9629592545068387700776177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12839456726757850267701569 9629592545068387700776177)
                ·
                  refine ⟨7222194408801290775582133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9629592545068387700776177 7222194408801290775582133)
                  ·
                    refine ⟨677080725825121010210825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7222194408801290775582133 677080725825121010210825)
                    ·
                      rfl

theorem cell23_3955830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_3955830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955830 prefixEnd_3955830 := by exact prefixLift 3955830
  have htrace : WordTrace (prefixWord ++ tailWord_3955830) baseStart_3955830 baseEnd_3955830 := by
    simpa [prefixWord, tailWord_3955830, baseEnd_3955830] using wordTrace_append hprefix tailTrace_3955830
  have hstable : (prefixWord ++ tailWord_3955830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955830).length < 2 ^ (prefixWord ++ tailWord_3955830).sum := by decide
  have hdescent : baseEnd_3955830 < baseStart_3955830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955850 : List Nat := [3, 1, 2, 3, 1, 1, 2, 1, 1, 6, 2]
def baseStart_3955850 : Nat := 118140960795 + 3955850 * 2 ^ 59
def prefixEnd_3955850 : Nat := 4983230072969 + 3 ^ 40 * 3955850 * 2
def baseEnd_3955850 : Nat := 2031252447088452952382383

theorem tailTrace_3955850 : CollatzResearch.WordTrace tailWord_3955850 prefixEnd_3955850 2031252447088452952382383 := by
  unfold tailWord_3955850
  simp only [CollatzResearch.WordTrace]
  refine ⟨36070425679659632559354251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96187801812425686824944669 36070425679659632559354251)
  ·
    refine ⟨54105638519489448839031377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36070425679659632559354251 54105638519489448839031377)
    ·
      refine ⟨40579228889617086629273533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54105638519489448839031377 40579228889617086629273533)
      ·
        refine ⟨15217210833606407485977575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40579228889617086629273533 15217210833606407485977575)
        ·
          refine ⟨22825816250409611228966363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15217210833606407485977575 22825816250409611228966363)
          ·
            refine ⟨34238724375614416843449545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22825816250409611228966363 34238724375614416843449545)
            ·
              refine ⟨25679043281710812632587159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34238724375614416843449545 25679043281710812632587159)
              ·
                refine ⟨38518564922566218948880739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25679043281710812632587159 38518564922566218948880739)
                ·
                  refine ⟨57777847383849328423321109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38518564922566218948880739 57777847383849328423321109)
                  ·
                    refine ⟨2708336596117937269843177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 57777847383849328423321109 2708336596117937269843177)
                    ·
                      refine ⟨2031252447088452952382383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2708336596117937269843177 2031252447088452952382383)
                      ·
                        rfl

theorem cell23_3955850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_3955850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955850 prefixEnd_3955850 := by exact prefixLift 3955850
  have htrace : WordTrace (prefixWord ++ tailWord_3955850) baseStart_3955850 baseEnd_3955850 := by
    simpa [prefixWord, tailWord_3955850, baseEnd_3955850] using wordTrace_append hprefix tailTrace_3955850
  have hstable : (prefixWord ++ tailWord_3955850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955850).length < 2 ^ (prefixWord ++ tailWord_3955850).sum := by decide
  have hdescent : baseEnd_3955850 < baseStart_3955850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955856 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 10]
def baseStart_3955856 : Nat := 118140960795 + 3955856 * 2 ^ 59
def prefixEnd_3955856 : Nat := 4983230072969 + 3 ^ 40 * 3955856 * 2
def baseEnd_3955856 : Nat := 225695058663597769878595

theorem tailTrace_3955856 : CollatzResearch.WordTrace tailWord_3955856 prefixEnd_3955856 225695058663597769878595 := by
  unfold tailWord_3955856
  simp only [CollatzResearch.WordTrace]
  refine ⟨72140960778308396631067711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96187947704411195508090281 72140960778308396631067711)
  ·
    refine ⟨108211441167462594946601567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72140960778308396631067711 108211441167462594946601567)
    ·
      refine ⟨162317161751193892419902351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108211441167462594946601567 162317161751193892419902351)
      ·
        refine ⟨243475742626790838629853527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162317161751193892419902351 243475742626790838629853527)
        ·
          refine ⟨365213613940186257944780291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243475742626790838629853527 365213613940186257944780291)
          ·
            refine ⟨547820420910279386917170437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365213613940186257944780291 547820420910279386917170437)
            ·
              refine ⟨102716328920677385046969457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 547820420910279386917170437 102716328920677385046969457)
              ·
                refine ⟨77037246690508038785227093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102716328920677385046969457 77037246690508038785227093)
                ·
                  refine ⟨225695058663597769878595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 77037246690508038785227093 225695058663597769878595)
                  ·
                    rfl

theorem cell23_3955856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 10].length) (baseStart_3955856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955856 prefixEnd_3955856 := by exact prefixLift 3955856
  have htrace : WordTrace (prefixWord ++ tailWord_3955856) baseStart_3955856 baseEnd_3955856 := by
    simpa [prefixWord, tailWord_3955856, baseEnd_3955856] using wordTrace_append hprefix tailTrace_3955856
  have hstable : (prefixWord ++ tailWord_3955856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955856).length < 2 ^ (prefixWord ++ tailWord_3955856).sum := by decide
  have hdescent : baseEnd_3955856 < baseStart_3955856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955890 : List Nat := [3, 2, 1, 1, 1, 5, 2, 2, 6]
def baseStart_3955890 : Nat := 118140960795 + 3955890 * 2 ^ 59
def prefixEnd_3955890 : Nat := 4983230072969 + 3 ^ 40 * 3955890 * 2
def baseEnd_3955890 : Nat := 225696998479403643986911

theorem tailTrace_3955890 : CollatzResearch.WordTrace tailWord_3955890 prefixEnd_3955890 225696998479403643986911 := by
  unfold tailWord_3955890
  simp only [CollatzResearch.WordTrace]
  refine ⟨36070790409623404267218281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96188774425662411379248749 36070790409623404267218281)
  ·
    refine ⟨27053092807217553200413711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36070790409623404267218281 27053092807217553200413711)
    ·
      refine ⟨40579639210826329800620567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27053092807217553200413711 40579639210826329800620567)
      ·
        refine ⟨60869458816239494700930851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40579639210826329800620567 60869458816239494700930851)
        ·
          refine ⟨91304188224359242051396277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60869458816239494700930851 91304188224359242051396277)
          ·
            refine ⟨8559767646033678942318401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91304188224359242051396277 8559767646033678942318401)
            ·
              refine ⟨6419825734525259206738801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8559767646033678942318401 6419825734525259206738801)
              ·
                refine ⟨4814869300893944405054101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6419825734525259206738801 4814869300893944405054101)
                ·
                  refine ⟨225696998479403643986911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4814869300893944405054101 225696998479403643986911)
                  ·
                    rfl

theorem cell23_3955890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 6].length) (baseStart_3955890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955890 prefixEnd_3955890 := by exact prefixLift 3955890
  have htrace : WordTrace (prefixWord ++ tailWord_3955890) baseStart_3955890 baseEnd_3955890 := by
    simpa [prefixWord, tailWord_3955890, baseEnd_3955890] using wordTrace_append hprefix tailTrace_3955890
  have hstable : (prefixWord ++ tailWord_3955890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955890).length < 2 ^ (prefixWord ++ tailWord_3955890).sum := by decide
  have hdescent : baseEnd_3955890 < baseStart_3955890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955903 : List Nat := [1, 1, 2, 2, 2, 2, 3, 2, 3, 5]
def baseStart_3955903 : Nat := 118140960795 + 3955903 * 2 ^ 59
def prefixEnd_3955903 : Nat := 4983230072969 + 3 ^ 40 * 3955903 * 2
def baseEnd_3955903 : Nat := 677093220521047081673213

theorem tailTrace_3955903 : CollatzResearch.WordTrace tailWord_3955903 prefixEnd_3955903 677093220521047081673213 := by
  unfold tailWord_3955903
  simp only [CollatzResearch.WordTrace]
  refine ⟨144283635787446520289096363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96189090524964346859397575 144283635787446520289096363)
  ·
    refine ⟨216425453681169780433644545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144283635787446520289096363 216425453681169780433644545)
    ·
      refine ⟨162319090260877335325233409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216425453681169780433644545 162319090260877335325233409)
      ·
        refine ⟨121739317695658001493925057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162319090260877335325233409 121739317695658001493925057)
        ·
          refine ⟨91304488271743501120443793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121739317695658001493925057 91304488271743501120443793)
          ·
            refine ⟨68478366203807625840332845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91304488271743501120443793 68478366203807625840332845)
            ·
              refine ⟨25679387326427859690124817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68478366203807625840332845 25679387326427859690124817)
              ·
                refine ⟨19259540494820894767593613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25679387326427859690124817 19259540494820894767593613)
                ·
                  refine ⟨7222327685557835537847605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19259540494820894767593613 7222327685557835537847605)
                  ·
                    refine ⟨677093220521047081673213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7222327685557835537847605 677093220521047081673213)
                    ·
                      rfl

theorem cell23_3955903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 5].length) (baseStart_3955903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955903 prefixEnd_3955903 := by exact prefixLift 3955903
  have htrace : WordTrace (prefixWord ++ tailWord_3955903) baseStart_3955903 baseEnd_3955903 := by
    simpa [prefixWord, tailWord_3955903, baseEnd_3955903] using wordTrace_append hprefix tailTrace_3955903
  have hstable : (prefixWord ++ tailWord_3955903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955903).length < 2 ^ (prefixWord ++ tailWord_3955903).sum := by decide
  have hdescent : baseEnd_3955903 < baseStart_3955903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955927 : List Nat := [1, 1, 3, 2, 1, 2, 5, 1, 2, 3, 2]
def baseStart_3955927 : Nat := 118140960795 + 3955927 * 2 ^ 59
def prefixEnd_3955927 : Nat := 4983230072969 + 3 ^ 40 * 3955927 * 2
def baseEnd_3955927 : Nat := 2031291985098849151119529

theorem tailTrace_3955927 : CollatzResearch.WordTrace tailWord_3955927 prefixEnd_3955927 2031291985098849151119529 := by
  unfold tailWord_3955927
  simp only [CollatzResearch.WordTrace]
  refine ⟨144284511139359572387970035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96189674092906381591980023 144284511139359572387970035)
  ·
    refine ⟨216426766709039358581955053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144284511139359572387970035 216426766709039358581955053)
    ·
      refine ⟨81160037515889759468233145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216426766709039358581955053 81160037515889759468233145)
      ·
        refine ⟨60870028136917319601174859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81160037515889759468233145 60870028136917319601174859)
        ·
          refine ⟨91305042205375979401762289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60870028136917319601174859 91305042205375979401762289)
          ·
            refine ⟨68478781654031984551321717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91305042205375979401762289 68478781654031984551321717)
            ·
              refine ⟨6419885780065498551686411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68478781654031984551321717 6419885780065498551686411)
              ·
                refine ⟨9629828670098247827529617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6419885780065498551686411 9629828670098247827529617)
                ·
                  refine ⟨7222371502573685870647213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9629828670098247827529617 7222371502573685870647213)
                  ·
                    refine ⟨2708389313465132201492705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7222371502573685870647213 2708389313465132201492705)
                    ·
                      refine ⟨2031291985098849151119529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2708389313465132201492705 2031291985098849151119529)
                      ·
                        rfl

theorem cell23_3955927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 3, 2].length) (baseStart_3955927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955927 prefixEnd_3955927 := by exact prefixLift 3955927
  have htrace : WordTrace (prefixWord ++ tailWord_3955927) baseStart_3955927 baseEnd_3955927 := by
    simpa [prefixWord, tailWord_3955927, baseEnd_3955927] using wordTrace_append hprefix tailTrace_3955927
  have hstable : (prefixWord ++ tailWord_3955927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955927).length < 2 ^ (prefixWord ++ tailWord_3955927).sum := by decide
  have hdescent : baseEnd_3955927 < baseStart_3955927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955937 : List Nat := [1, 2, 3, 1, 3, 2, 4, 1, 1, 5]
def baseStart_3955937 : Nat := 118140960795 + 3955937 * 2 ^ 59
def prefixEnd_3955937 : Nat := 4983230072969 + 3 ^ 40 * 3955937 * 2
def baseEnd_3955937 : Nat := 677099039968464703998161

theorem tailTrace_3955937 : CollatzResearch.WordTrace tailWord_3955937 prefixEnd_3955937 677099039968464703998161 := by
  unfold tailWord_3955937
  simp only [CollatzResearch.WordTrace]
  refine ⟨144284875869323344095834065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96189917246215562730556043 144284875869323344095834065)
  ·
    refine ⟨108213656901992508071875549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144284875869323344095834065 108213656901992508071875549)
    ·
      refine ⟨40580121338247190526953331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108213656901992508071875549 40580121338247190526953331)
      ·
        refine ⟨60870182007370785790429997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40580121338247190526953331 60870182007370785790429997)
        ·
          refine ⟨22826318252764044671411249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60870182007370785790429997 22826318252764044671411249)
          ·
            refine ⟨17119738689573033503558437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22826318252764044671411249 17119738689573033503558437)
            ·
              refine ⟨3209951004294943781917207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17119738689573033503558437 3209951004294943781917207)
              ·
                refine ⟨4814926506442415672875811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3209951004294943781917207 4814926506442415672875811)
                ·
                  refine ⟨7222389759663623509313717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4814926506442415672875811 7222389759663623509313717)
                  ·
                    refine ⟨677099039968464703998161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7222389759663623509313717 677099039968464703998161)
                    ·
                      rfl

theorem cell23_3955937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 1, 5].length) (baseStart_3955937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955937 prefixEnd_3955937 := by exact prefixLift 3955937
  have htrace : WordTrace (prefixWord ++ tailWord_3955937) baseStart_3955937 baseEnd_3955937 := by
    simpa [prefixWord, tailWord_3955937, baseEnd_3955937] using wordTrace_append hprefix tailTrace_3955937
  have hstable : (prefixWord ++ tailWord_3955937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955937).length < 2 ^ (prefixWord ++ tailWord_3955937).sum := by decide
  have hdescent : baseEnd_3955937 < baseStart_3955937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955953 : List Nat := [1, 2, 2, 2, 2, 1, 1, 4, 1, 1, 6]
def baseStart_3955953 : Nat := 118140960795 + 3955953 * 2 ^ 59
def prefixEnd_3955953 : Nat := 4983230072969 + 3 ^ 40 * 3955953 * 2
def baseEnd_3955953 : Nat := 2031305335595866049394409

theorem tailTrace_3955953 : CollatzResearch.WordTrace tailWord_3955953 prefixEnd_3955953 2031305335595866049394409 := by
  unfold tailWord_3955953
  simp only [CollatzResearch.WordTrace]
  refine ⟨144285459437265378828416513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96190306291510252552277675 144285459437265378828416513)
  ·
    refine ⟨108214094577949034121312385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144285459437265378828416513 108214094577949034121312385)
    ·
      refine ⟨81160570933461775590984289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108214094577949034121312385 81160570933461775590984289)
      ·
        refine ⟨60870428200096331693238217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81160570933461775590984289 60870428200096331693238217)
        ·
          refine ⟨45652821150072248769928663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60870428200096331693238217 45652821150072248769928663)
          ·
            refine ⟨68479231725108373154892995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45652821150072248769928663 68479231725108373154892995)
            ·
              refine ⟨102718847587662559732339493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68479231725108373154892995 102718847587662559732339493)
              ·
                refine ⟨19259783922686729949813655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102718847587662559732339493 19259783922686729949813655)
                ·
                  refine ⟨28889675884030094924720483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19259783922686729949813655 28889675884030094924720483)
                  ·
                    refine ⟨43334513826045142387080725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28889675884030094924720483 43334513826045142387080725)
                    ·
                      refine ⟨2031305335595866049394409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43334513826045142387080725 2031305335595866049394409)
                      ·
                        rfl

theorem cell23_3955953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_3955953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955953 prefixEnd_3955953 := by exact prefixLift 3955953
  have htrace : WordTrace (prefixWord ++ tailWord_3955953) baseStart_3955953 baseEnd_3955953 := by
    simpa [prefixWord, tailWord_3955953, baseEnd_3955953] using wordTrace_append hprefix tailTrace_3955953
  have hstable : (prefixWord ++ tailWord_3955953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955953).length < 2 ^ (prefixWord ++ tailWord_3955953).sum := by decide
  have hdescent : baseEnd_3955953 < baseStart_3955953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955977 : List Nat := [1, 2, 1, 1, 3, 3, 4, 2, 1, 2, 3]
def baseStart_3955977 : Nat := 118140960795 + 3955977 * 2 ^ 59
def prefixEnd_3955977 : Nat := 4983230072969 + 3 ^ 40 * 3955977 * 2
def baseEnd_3955977 : Nat := 2031317659131573955494299

theorem tailTrace_3955977 : CollatzResearch.WordTrace tailWord_3955977 prefixEnd_3955977 2031317659131573955494299 := by
  unfold tailWord_3955977
  simp only [CollatzResearch.WordTrace]
  refine ⟨144286334789178430927290185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96190889859452287284860123 144286334789178430927290185)
  ·
    refine ⟨108214751091883823195467639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144286334789178430927290185 108214751091883823195467639)
    ·
      refine ⟨162322126637825734793201459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108214751091883823195467639 162322126637825734793201459)
      ·
        refine ⟨243483189956738602189802189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162322126637825734793201459 243483189956738602189802189)
        ·
          refine ⟨91306196233776975821175821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243483189956738602189802189 91306196233776975821175821)
          ·
            refine ⟨34239823587666365932940933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91306196233776975821175821 34239823587666365932940933)
            ·
              refine ⟨6419966922687443612426425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34239823587666365932940933 6419966922687443612426425)
              ·
                refine ⟨4814975192015582709319819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6419966922687443612426425 4814975192015582709319819)
                ·
                  refine ⟨7222462788023374063979729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4814975192015582709319819 7222462788023374063979729)
                  ·
                    refine ⟨5416847091017530547984797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7222462788023374063979729 5416847091017530547984797)
                    ·
                      refine ⟨2031317659131573955494299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5416847091017530547984797 2031317659131573955494299)
                      ·
                        rfl

theorem cell23_3955977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 2, 3].length) (baseStart_3955977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955977 prefixEnd_3955977 := by exact prefixLift 3955977
  have htrace : WordTrace (prefixWord ++ tailWord_3955977) baseStart_3955977 baseEnd_3955977 := by
    simpa [prefixWord, tailWord_3955977, baseEnd_3955977] using wordTrace_append hprefix tailTrace_3955977
  have hstable : (prefixWord ++ tailWord_3955977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955977).length < 2 ^ (prefixWord ++ tailWord_3955977).sum := by decide
  have hdescent : baseEnd_3955977 < baseStart_3955977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955980 : List Nat := [2, 2, 1, 2, 2, 3, 4, 7]
def baseStart_3955980 : Nat := 118140960795 + 3955980 * 2 ^ 59
def prefixEnd_3955980 : Nat := 4983230072969 + 3 ^ 40 * 3955980 * 2
def baseEnd_3955980 : Nat := 75234044428649534953955

theorem tailTrace_3955980 : CollatzResearch.WordTrace tailWord_3955980 prefixEnd_3955980 75234044428649534953955 := by
  unfold tailWord_3955980
  simp only [CollatzResearch.WordTrace]
  refine ⟨72143222104083781219824697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96190962805445041626432929 72143222104083781219824697)
  ·
    refine ⟨54107416578062835914868523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72143222104083781219824697 54107416578062835914868523)
    ·
      refine ⟨81161124867094253872302785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54107416578062835914868523 81161124867094253872302785)
      ·
        refine ⟨60870843650320690404227089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81161124867094253872302785 60870843650320690404227089)
        ·
          refine ⟨45653132737740517803170317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60870843650320690404227089 45653132737740517803170317)
          ·
            refine ⟨17119924776652694176188869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45653132737740517803170317 17119924776652694176188869)
            ·
              refine ⟨3209985895622380158035413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17119924776652694176188869 3209985895622380158035413)
              ·
                refine ⟨75234044428649534953955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3209985895622380158035413 75234044428649534953955)
                ·
                  rfl

theorem cell23_3955980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 7].length) (baseStart_3955980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955980 prefixEnd_3955980 := by exact prefixLift 3955980
  have htrace : WordTrace (prefixWord ++ tailWord_3955980) baseStart_3955980 baseEnd_3955980 := by
    simpa [prefixWord, tailWord_3955980, baseEnd_3955980] using wordTrace_append hprefix tailTrace_3955980
  have hstable : (prefixWord ++ tailWord_3955980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955980).length < 2 ^ (prefixWord ++ tailWord_3955980).sum := by decide
  have hdescent : baseEnd_3955980 < baseStart_3955980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956043 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 6]
def baseStart_3956043 : Nat := 118140960795 + 3956043 * 2 ^ 59
def prefixEnd_3956043 : Nat := 4983230072969 + 3 ^ 40 * 3956043 * 2
def baseEnd_3956043 : Nat := 2031351548854770697268995

theorem tailTrace_3956043 : CollatzResearch.WordTrace tailWord_3956043 prefixEnd_3956043 2031351548854770697268995 := by
  unfold tailWord_3956043
  simp only [CollatzResearch.WordTrace]
  refine ⟨144288742006939324199192783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96192494671292882799461855 144288742006939324199192783)
  ·
    refine ⟨216433113010408986298789175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144288742006939324199192783 216433113010408986298789175)
    ·
      refine ⟨324649669515613479448183763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216433113010408986298789175 324649669515613479448183763)
      ·
        refine ⟨486974504273420219172275645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324649669515613479448183763 486974504273420219172275645)
        ·
          refine ⟨182615439102532582189603367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 486974504273420219172275645 182615439102532582189603367)
          ·
            refine ⟨273923158653798873284405051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182615439102532582189603367 273923158653798873284405051)
            ·
              refine ⟨410884737980698309926607577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273923158653798873284405051 410884737980698309926607577)
              ·
                refine ⟨308163553485523732444955683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 410884737980698309926607577 308163553485523732444955683)
                ·
                  refine ⟨462245330228285598667433525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 308163553485523732444955683 462245330228285598667433525)
                  ·
                    refine ⟨43335499708901774875071893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 462245330228285598667433525 43335499708901774875071893)
                    ·
                      refine ⟨2031351548854770697268995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43335499708901774875071893 2031351548854770697268995)
                      ·
                        rfl

theorem cell23_3956043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 6].length) (baseStart_3956043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3956043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3956043 prefixEnd_3956043 := by exact prefixLift 3956043
  have htrace : WordTrace (prefixWord ++ tailWord_3956043) baseStart_3956043 baseEnd_3956043 := by
    simpa [prefixWord, tailWord_3956043, baseEnd_3956043] using wordTrace_append hprefix tailTrace_3956043
  have hstable : (prefixWord ++ tailWord_3956043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956043).length < 2 ^ (prefixWord ++ tailWord_3956043).sum := by decide
  have hdescent : baseEnd_3956043 < baseStart_3956043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956077 : List Nat := [1, 5, 1, 1, 1, 4, 1, 1, 2, 2, 4]
def baseStart_3956077 : Nat := 118140960795 + 3956077 * 2 ^ 59
def prefixEnd_3956077 : Nat := 4983230072969 + 3 ^ 40 * 3956077 * 2
def baseEnd_3956077 : Nat := 2031369007197023564243839

theorem tailTrace_3956077 : CollatzResearch.WordTrace tailWord_3956077 prefixEnd_3956077 2031369007197023564243839 := by
  unfold tailWord_3956077
  simp only [CollatzResearch.WordTrace]
  refine ⟨144289982088816148005930485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96193321392544098670620323 144289982088816148005930485)
  ·
    refine ⟨13527185820826513875555983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144289982088816148005930485 13527185820826513875555983)
    ·
      refine ⟨20290778731239770813333975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13527185820826513875555983 20290778731239770813333975)
      ·
        refine ⟨30436168096859656220000963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20290778731239770813333975 30436168096859656220000963)
        ·
          refine ⟨45654252145289484330001445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30436168096859656220000963 45654252145289484330001445)
          ·
            refine ⟨8560172277241778311875271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45654252145289484330001445 8560172277241778311875271)
            ·
              refine ⟨12840258415862667467812907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8560172277241778311875271 12840258415862667467812907)
              ·
                refine ⟨19260387623794001201719361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12840258415862667467812907 19260387623794001201719361)
                ·
                  refine ⟨14445290717845500901289521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19260387623794001201719361 14445290717845500901289521)
                  ·
                    refine ⟨10833968038384125675967141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14445290717845500901289521 10833968038384125675967141)
                    ·
                      refine ⟨2031369007197023564243839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10833968038384125675967141 2031369007197023564243839)
                      ·
                        rfl

theorem cell23_3956077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_3956077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3956077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3956077 prefixEnd_3956077 := by exact prefixLift 3956077
  have htrace : WordTrace (prefixWord ++ tailWord_3956077) baseStart_3956077 baseEnd_3956077 := by
    simpa [prefixWord, tailWord_3956077, baseEnd_3956077] using wordTrace_append hprefix tailTrace_3956077
  have hstable : (prefixWord ++ tailWord_3956077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956077).length < 2 ^ (prefixWord ++ tailWord_3956077).sum := by decide
  have hdescent : baseEnd_3956077 < baseStart_3956077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956104 : List Nat := [2, 1, 3, 3, 1, 3, 2, 3, 5]
def baseStart_3956104 : Nat := 118140960795 + 3956104 * 2 ^ 59
def prefixEnd_3956104 : Nat := 4983230072969 + 3 ^ 40 * 3956104 * 2
def baseEnd_3956104 : Nat := 225709207908299439845135

theorem tailTrace_3956104 : CollatzResearch.WordTrace tailWord_3956104 prefixEnd_3956104 225709207908299439845135 := by
  unfold tailWord_3956104
  simp only [CollatzResearch.WordTrace]
  refine ⟨72145483429859165808581683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96193977906478887744775577 72145483429859165808581683)
  ·
    refine ⟨108218225144788748712872525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72145483429859165808581683 108218225144788748712872525)
    ·
      refine ⟨40581834429295780767327197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108218225144788748712872525 40581834429295780767327197)
      ·
        refine ⟨15218187910985917787747699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40581834429295780767327197 15218187910985917787747699)
        ·
          refine ⟨22827281866478876681621549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15218187910985917787747699 22827281866478876681621549)
          ·
            refine ⟨8560230699929578755608081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22827281866478876681621549 8560230699929578755608081)
            ·
              refine ⟨6420173024947184066706061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8560230699929578755608081 6420173024947184066706061)
              ·
                refine ⟨2407564884355194025014773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6420173024947184066706061 2407564884355194025014773)
                ·
                  refine ⟨225709207908299439845135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2407564884355194025014773 225709207908299439845135)
                  ·
                    rfl

theorem cell23_3956104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 3, 5].length) (baseStart_3956104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3956104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3956104 prefixEnd_3956104 := by exact prefixLift 3956104
  have htrace : WordTrace (prefixWord ++ tailWord_3956104) baseStart_3956104 baseEnd_3956104 := by
    simpa [prefixWord, tailWord_3956104, baseEnd_3956104] using wordTrace_append hprefix tailTrace_3956104
  have hstable : (prefixWord ++ tailWord_3956104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956104).length < 2 ^ (prefixWord ++ tailWord_3956104).sum := by decide
  have hdescent : baseEnd_3956104 < baseStart_3956104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956157 : List Nat := [1, 4, 1, 2, 2, 1, 1, 3, 1, 4, 3]
def baseStart_3956157 : Nat := 118140960795 + 3956157 * 2 ^ 59
def prefixEnd_3956157 : Nat := 4983230072969 + 3 ^ 40 * 3956157 * 2
def baseEnd_3956157 : Nat := 2031410085649383251243471

theorem tailTrace_3956157 : CollatzResearch.WordTrace tailWord_3956157 prefixEnd_3956157 2031410085649383251243471 := by
  unfold tailWord_3956157
  simp only [CollatzResearch.WordTrace]
  refine ⟨144292899928526321668842725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96195266619017547779228483 144292899928526321668842725)
  ·
    refine ⟨27054918736598685312908011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144292899928526321668842725 27054918736598685312908011)
    ·
      refine ⟨40582378104898027969362017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27054918736598685312908011 40582378104898027969362017)
      ·
        refine ⟨30436783578673520977021513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40582378104898027969362017 30436783578673520977021513)
        ·
          refine ⟨22827587684005140732766135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30436783578673520977021513 22827587684005140732766135)
          ·
            refine ⟨34241381526007711099149203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22827587684005140732766135 34241381526007711099149203)
            ·
              refine ⟨51362072289011566648723805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34241381526007711099149203 51362072289011566648723805)
              ·
                refine ⟨19260777108379337493271427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51362072289011566648723805 19260777108379337493271427)
                ·
                  refine ⟨28891165662569006239907141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19260777108379337493271427 28891165662569006239907141)
                  ·
                    refine ⟨5417093561731688669982589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28891165662569006239907141 5417093561731688669982589)
                    ·
                      refine ⟨2031410085649383251243471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5417093561731688669982589 2031410085649383251243471)
                      ·
                        rfl

theorem cell23_3956157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_3956157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3956157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3956157 prefixEnd_3956157 := by exact prefixLift 3956157
  have htrace : WordTrace (prefixWord ++ tailWord_3956157) baseStart_3956157 baseEnd_3956157 := by
    simpa [prefixWord, tailWord_3956157, baseEnd_3956157] using wordTrace_append hprefix tailTrace_3956157
  have hstable : (prefixWord ++ tailWord_3956157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956157).length < 2 ^ (prefixWord ++ tailWord_3956157).sum := by decide
  have hdescent : baseEnd_3956157 < baseStart_3956157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956160 : List Nat := [2, 1, 1, 2, 3, 1, 3, 2, 8]
def baseStart_3956160 : Nat := 118140960795 + 3956160 * 2 ^ 59
def prefixEnd_3956160 : Nat := 4983230072969 + 3 ^ 40 * 3956160 * 2
def baseEnd_3956160 : Nat := 225712402899038526611773

theorem tailTrace_3956160 : CollatzResearch.WordTrace tailWord_3956160 prefixEnd_3956160 225712402899038526611773 := by
  unfold tailWord_3956160
  simp only [CollatzResearch.WordTrace]
  refine ⟨72146504673757726590600967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96195339565010302120801289 72146504673757726590600967)
  ·
    refine ⟨108219757010636589885901451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72146504673757726590600967 108219757010636589885901451)
    ·
      refine ⟨162329635515954884828852177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108219757010636589885901451 162329635515954884828852177)
      ·
        refine ⟨121747226636966163621639133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162329635515954884828852177 121747226636966163621639133)
        ·
          refine ⟨45655209988862311358114675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121747226636966163621639133 45655209988862311358114675)
          ·
            refine ⟨68482814983293467037172013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45655209988862311358114675 68482814983293467037172013)
            ·
              refine ⟨25681055618735050138939505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68482814983293467037172013 25681055618735050138939505)
              ·
                refine ⟨19260791714051287604204629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25681055618735050138939505 19260791714051287604204629)
                ·
                  refine ⟨225712402899038526611773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19260791714051287604204629 225712402899038526611773)
                  ·
                    rfl

theorem cell23_3956160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 8].length) (baseStart_3956160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3956160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3956160 prefixEnd_3956160 := by exact prefixLift 3956160
  have htrace : WordTrace (prefixWord ++ tailWord_3956160) baseStart_3956160 baseEnd_3956160 := by
    simpa [prefixWord, tailWord_3956160, baseEnd_3956160] using wordTrace_append hprefix tailTrace_3956160
  have hstable : (prefixWord ++ tailWord_3956160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956160).length < 2 ^ (prefixWord ++ tailWord_3956160).sum := by decide
  have hdescent : baseEnd_3956160 < baseStart_3956160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956231 : List Nat := [1, 1, 4, 3, 2, 1, 2, 2, 2, 3, 2]
def baseStart_3956231 : Nat := 118140960795 + 3956231 * 2 ^ 59
def prefixEnd_3956231 : Nat := 4983230072969 + 3 ^ 40 * 3956231 * 2
def baseEnd_3956231 : Nat := 2031448083217815961718131

theorem tailTrace_3956231 : CollatzResearch.WordTrace tailWord_3956231 prefixEnd_3956231 2031448083217815961718131 := by
  unfold tailWord_3956231
  simp only [CollatzResearch.WordTrace]
  refine ⟨144295598930258232307036547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96197065953505488204691031 144295598930258232307036547)
  ·
    refine ⟨216443398395387348460554821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144295598930258232307036547 216443398395387348460554821)
    ·
      refine ⟨40583137199135127836354029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216443398395387348460554821 40583137199135127836354029)
      ·
        refine ⟨15218676449675672938632761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40583137199135127836354029 15218676449675672938632761)
        ·
          refine ⟨11414007337256754703974571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15218676449675672938632761 11414007337256754703974571)
          ·
            refine ⟨17121011005885132055961857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11414007337256754703974571 17121011005885132055961857)
            ·
              refine ⟨12840758254413849041971393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17121011005885132055961857 12840758254413849041971393)
              ·
                refine ⟨9630568690810386781478545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12840758254413849041971393 9630568690810386781478545)
                ·
                  refine ⟨7222926518107790086108909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9630568690810386781478545 7222926518107790086108909)
                  ·
                    refine ⟨2708597444290421282290841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7222926518107790086108909 2708597444290421282290841)
                    ·
                      refine ⟨2031448083217815961718131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2708597444290421282290841 2031448083217815961718131)
                      ·
                        rfl

theorem cell23_3956231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_3956231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3956231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3956231 prefixEnd_3956231 := by exact prefixLift 3956231
  have htrace : WordTrace (prefixWord ++ tailWord_3956231) baseStart_3956231 baseEnd_3956231 := by
    simpa [prefixWord, tailWord_3956231, baseEnd_3956231] using wordTrace_append hprefix tailTrace_3956231
  have hstable : (prefixWord ++ tailWord_3956231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956231).length < 2 ^ (prefixWord ++ tailWord_3956231).sum := by decide
  have hdescent : baseEnd_3956231 < baseStart_3956231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956278 : List Nat := [5, 1, 2, 1, 3, 1, 1, 3, 1, 1, 4]
def baseStart_3956278 : Nat := 118140960795 + 3956278 * 2 ^ 59
def prefixEnd_3956278 : Nat := 4983230072969 + 3 ^ 40 * 3956278 * 2
def baseEnd_3956278 : Nat := 2031472216808577277830415

theorem tailTrace_3956278 : CollatzResearch.WordTrace tailWord_3956278 prefixEnd_3956278 2031472216808577277830415 := by
  unfold tailWord_3956278
  simp only [CollatzResearch.WordTrace]
  refine ⟨9018582072567997458374843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96198208774058639555998325 9018582072567997458374843)
  ·
    refine ⟨13527873108851996187562265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9018582072567997458374843 13527873108851996187562265)
    ·
      refine ⟨10145904831638997140671699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13527873108851996187562265 10145904831638997140671699)
      ·
        refine ⟨15218857247458495711007549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10145904831638997140671699 15218857247458495711007549)
        ·
          refine ⟨5707071467796935891627831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15218857247458495711007549 5707071467796935891627831)
          ·
            refine ⟨8560607201695403837441747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5707071467796935891627831 8560607201695403837441747)
            ·
              refine ⟨12840910802543105756162621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8560607201695403837441747 12840910802543105756162621)
              ·
                refine ⟨4815341550953664658560983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12840910802543105756162621 4815341550953664658560983)
                ·
                  refine ⟨7223012326430496987841475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4815341550953664658560983 7223012326430496987841475)
                  ·
                    refine ⟨10834518489645745481762213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7223012326430496987841475 10834518489645745481762213)
                    ·
                      refine ⟨2031472216808577277830415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10834518489645745481762213 2031472216808577277830415)
                      ·
                        rfl

theorem cell23_3956278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_3956278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3956278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3956278 prefixEnd_3956278 := by exact prefixLift 3956278
  have htrace : WordTrace (prefixWord ++ tailWord_3956278) baseStart_3956278 baseEnd_3956278 := by
    simpa [prefixWord, tailWord_3956278, baseEnd_3956278] using wordTrace_append hprefix tailTrace_3956278
  have hstable : (prefixWord ++ tailWord_3956278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956278).length < 2 ^ (prefixWord ++ tailWord_3956278).sum := by decide
  have hdescent : baseEnd_3956278 < baseStart_3956278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956281 : List Nat := [1, 2, 1, 5, 1, 3, 1, 3, 1, 2, 3]
def baseStart_3956281 : Nat := 118140960795 + 3956281 * 2 ^ 59
def prefixEnd_3956281 : Nat := 4983230072969 + 3 ^ 40 * 3956281 * 2
def baseEnd_3956281 : Nat := 2031473757250540766092901

theorem tailTrace_3956281 : CollatzResearch.WordTrace tailWord_3956281 prefixEnd_3956281 2031473757250540766092901 := by
  unfold tailWord_3956281
  simp only [CollatzResearch.WordTrace]
  refine ⟨144297422580077090846356697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96198281720051393897571131 144297422580077090846356697)
  ·
    refine ⟨108223066935057818134767523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144297422580077090846356697 108223066935057818134767523)
    ·
      refine ⟨162334600402586727202151285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108223066935057818134767523 162334600402586727202151285)
      ·
        refine ⟨15218868787742505675201683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162334600402586727202151285 15218868787742505675201683)
        ·
          refine ⟨22828303181613758512802525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15218868787742505675201683 22828303181613758512802525)
          ·
            refine ⟨8560613693105159442300947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22828303181613758512802525 8560613693105159442300947)
            ·
              refine ⟨12840920539657739163451421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8560613693105159442300947 12840920539657739163451421)
              ·
                refine ⟨4815345202371652186294283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12840920539657739163451421 4815345202371652186294283)
                ·
                  refine ⟨7223017803557478279441425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4815345202371652186294283 7223017803557478279441425)
                  ·
                    refine ⟨5417263352668108709581069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7223017803557478279441425 5417263352668108709581069)
                    ·
                      refine ⟨2031473757250540766092901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5417263352668108709581069 2031473757250540766092901)
                      ·
                        rfl

theorem cell23_3956281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_3956281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3956281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3956281 prefixEnd_3956281 := by exact prefixLift 3956281
  have htrace : WordTrace (prefixWord ++ tailWord_3956281) baseStart_3956281 baseEnd_3956281 := by
    simpa [prefixWord, tailWord_3956281, baseEnd_3956281] using wordTrace_append hprefix tailTrace_3956281
  have hstable : (prefixWord ++ tailWord_3956281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956281).length < 2 ^ (prefixWord ++ tailWord_3956281).sum := by decide
  have hdescent : baseEnd_3956281 < baseStart_3956281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956311 : List Nat := [1, 1, 3, 2, 2, 5, 1, 1, 1, 3, 3]
def baseStart_3956311 : Nat := 118140960795 + 3956311 * 2 ^ 59
def prefixEnd_3956311 : Nat := 4983230072969 + 3 ^ 40 * 3956311 * 2
def baseEnd_3956311 : Nat := 2031489161670175648717763

theorem tailTrace_3956311 : CollatzResearch.WordTrace tailWord_3956311 prefixEnd_3956311 2031489161670175648717763 := by
  unfold tailWord_3956311
  simp only [CollatzResearch.WordTrace]
  refine ⟨144298516769968405969948787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96199011179978937313299191 144298516769968405969948787)
  ·
    refine ⟨216447775154952608954923181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144298516769968405969948787 216447775154952608954923181)
    ·
      refine ⟨81167915683107228358096193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216447775154952608954923181 81167915683107228358096193)
      ·
        refine ⟨60875936762330421268572145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81167915683107228358096193 60875936762330421268572145)
        ·
          refine ⟨45656952571747815951429109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60875936762330421268572145 45656952571747815951429109)
          ·
            refine ⟨4280339303601357745446479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45656952571747815951429109 4280339303601357745446479)
            ·
              refine ⟨6420508955402036618169719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4280339303601357745446479 6420508955402036618169719)
              ·
                refine ⟨9630763433103054927254579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6420508955402036618169719 9630763433103054927254579)
                ·
                  refine ⟨14446145149654582390881869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9630763433103054927254579 14446145149654582390881869)
                  ·
                    refine ⟨5417304431120468396580701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14446145149654582390881869 5417304431120468396580701)
                    ·
                      refine ⟨2031489161670175648717763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5417304431120468396580701 2031489161670175648717763)
                      ·
                        rfl

theorem cell23_3956311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 3, 3].length) (baseStart_3956311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3956311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3956311 prefixEnd_3956311 := by exact prefixLift 3956311
  have htrace : WordTrace (prefixWord ++ tailWord_3956311) baseStart_3956311 baseEnd_3956311 := by
    simpa [prefixWord, tailWord_3956311, baseEnd_3956311] using wordTrace_append hprefix tailTrace_3956311
  have hstable : (prefixWord ++ tailWord_3956311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956311).length < 2 ^ (prefixWord ++ tailWord_3956311).sum := by decide
  have hdescent : baseEnd_3956311 < baseStart_3956311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956327 : List Nat := [1, 1, 5, 1, 1, 1, 2, 2, 1, 8]
def baseStart_3956327 : Nat := 118140960795 + 3956327 * 2 ^ 59
def prefixEnd_3956327 : Nat := 4983230072969 + 3 ^ 40 * 3956327 * 2
def baseEnd_3956327 : Nat := 677165792453549195372563

theorem tailTrace_3956327 : CollatzResearch.WordTrace tailWord_3956327 prefixEnd_3956327 677165792453549195372563 := by
  unfold tailWord_3956327
  simp only [CollatzResearch.WordTrace]
  refine ⟨144299100337910440702531235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96199400225273627135020823 144299100337910440702531235)
  ·
    refine ⟨216448650506865661053796853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144299100337910440702531235 216448650506865661053796853)
    ·
      refine ⟨20292060985018655723793455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 216448650506865661053796853 20292060985018655723793455)
      ·
        refine ⟨30438091477527983585690183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20292060985018655723793455 30438091477527983585690183)
        ·
          refine ⟨45657137216291975378535275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30438091477527983585690183 45657137216291975378535275)
          ·
            refine ⟨68485705824437963067802913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45657137216291975378535275 68485705824437963067802913)
            ·
              refine ⟨51364279368328472300852185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68485705824437963067802913 51364279368328472300852185)
              ·
                refine ⟨38523209526246354225639139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51364279368328472300852185 38523209526246354225639139)
                ·
                  refine ⟨57784814289369531338458709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38523209526246354225639139 57784814289369531338458709)
                  ·
                    refine ⟨677165792453549195372563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57784814289369531338458709 677165792453549195372563)
                    ·
                      rfl

theorem cell23_3956327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_3956327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3956327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3956327 prefixEnd_3956327 := by exact prefixLift 3956327
  have htrace : WordTrace (prefixWord ++ tailWord_3956327) baseStart_3956327 baseEnd_3956327 := by
    simpa [prefixWord, tailWord_3956327, baseEnd_3956327] using wordTrace_append hprefix tailTrace_3956327
  have hstable : (prefixWord ++ tailWord_3956327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956327).length < 2 ^ (prefixWord ++ tailWord_3956327).sum := by decide
  have hdescent : baseEnd_3956327 < baseStart_3956327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956338 : List Nat := [3, 2, 1, 2, 3, 1, 2, 3, 1, 3, 2]
def baseStart_3956338 : Nat := 118140960795 + 3956338 * 2 ^ 59
def prefixEnd_3956338 : Nat := 4983230072969 + 3 ^ 40 * 3956338 * 2
def baseEnd_3956338 : Nat := 2031503025647847043080139

theorem tailTrace_3956338 : CollatzResearch.WordTrace tailWord_3956338 prefixEnd_3956338 2031503025647847043080139 := by
  unfold tailWord_3956338
  simp only [CollatzResearch.WordTrace]
  refine ⟨36074875385217647395295417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96199667693913726387454445 36074875385217647395295417)
  ·
    refine ⟨27056156538913235546471563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36074875385217647395295417 27056156538913235546471563)
    ·
      refine ⟨40584234808369853319707345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27056156538913235546471563 40584234808369853319707345)
      ·
        refine ⟨30438176106277389989780509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40584234808369853319707345 30438176106277389989780509)
        ·
          refine ⟨11414316039854021246167691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30438176106277389989780509 11414316039854021246167691)
          ·
            refine ⟨17121474059781031869251537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11414316039854021246167691 17121474059781031869251537)
            ·
              refine ⟨12841105544835773901938653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17121474059781031869251537 12841105544835773901938653)
              ·
                refine ⟨4815414579313415213226995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12841105544835773901938653 4815414579313415213226995)
                ·
                  refine ⟨7223121868970122819840493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4815414579313415213226995 7223121868970122819840493)
                  ·
                    refine ⟨2708670700863796057440185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7223121868970122819840493 2708670700863796057440185)
                    ·
                      refine ⟨2031503025647847043080139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2708670700863796057440185 2031503025647847043080139)
                      ·
                        rfl

theorem cell23_3956338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_3956338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3956338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3956338 prefixEnd_3956338 := by exact prefixLift 3956338
  have htrace : WordTrace (prefixWord ++ tailWord_3956338) baseStart_3956338 baseEnd_3956338 := by
    simpa [prefixWord, tailWord_3956338, baseEnd_3956338] using wordTrace_append hprefix tailTrace_3956338
  have hstable : (prefixWord ++ tailWord_3956338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956338).length < 2 ^ (prefixWord ++ tailWord_3956338).sum := by decide
  have hdescent : baseEnd_3956338 < baseStart_3956338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956372 : List Nat := [2, 4, 2, 2, 2, 2, 1, 2, 1, 3, 2]
def baseStart_3956372 : Nat := 118140960795 + 3956372 * 2 ^ 59
def prefixEnd_3956372 : Nat := 4983230072969 + 3 ^ 40 * 3956372 * 2
def baseEnd_3956372 : Nat := 2031520483990099910054983

theorem tailTrace_3956372 : CollatzResearch.WordTrace tailWord_3956372 prefixEnd_3956372 2031520483990099910054983 := by
  unfold tailWord_3956372
  simp only [CollatzResearch.WordTrace]
  refine ⟨72150370811373706693959685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96200494415164942258612913 72150370811373706693959685)
  ·
    refine ⟨13528194527132570005117441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72150370811373706693959685 13528194527132570005117441)
    ·
      refine ⟨10146145895349427503838081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13528194527132570005117441 10146145895349427503838081)
      ·
        refine ⟨7609609421512070627878561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10146145895349427503838081 7609609421512070627878561)
        ·
          refine ⟨5707207066134052970908921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7609609421512070627878561 5707207066134052970908921)
          ·
            refine ⟨4280405299600539728181691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5707207066134052970908921 4280405299600539728181691)
            ·
              refine ⟨6420607949400809592272537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4280405299600539728181691 6420607949400809592272537)
              ·
                refine ⟨4815455962050607194204403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6420607949400809592272537 4815455962050607194204403)
                ·
                  refine ⟨7223183943075910791306605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4815455962050607194204403 7223183943075910791306605)
                  ·
                    refine ⟨2708693978653466546739977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7223183943075910791306605 2708693978653466546739977)
                    ·
                      refine ⟨2031520483990099910054983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2708693978653466546739977 2031520483990099910054983)
                      ·
                        rfl

theorem cell23_3956372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_3956372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3956372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3956372 prefixEnd_3956372 := by exact prefixLift 3956372
  have htrace : WordTrace (prefixWord ++ tailWord_3956372) baseStart_3956372 baseEnd_3956372 := by
    simpa [prefixWord, tailWord_3956372, baseEnd_3956372] using wordTrace_append hprefix tailTrace_3956372
  have hstable : (prefixWord ++ tailWord_3956372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956372).length < 2 ^ (prefixWord ++ tailWord_3956372).sum := by decide
  have hdescent : baseEnd_3956372 < baseStart_3956372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956424 : List Nat := [2, 1, 3, 1, 2, 2, 2, 2, 1, 3, 4]
def baseStart_3956424 : Nat := 118140960795 + 3956424 * 2 ^ 59
def prefixEnd_3956424 : Nat := 4983230072969 + 3 ^ 40 * 3956424 * 2
def baseEnd_3956424 : Nat := 2031547184984133706604743

theorem tailTrace_3956424 : CollatzResearch.WordTrace tailWord_3956424 prefixEnd_3956424 2031547184984133706604743 := by
  unfold tailWord_3956424
  simp only [CollatzResearch.WordTrace]
  refine ⟨72151319109279513134406163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96201758812372684179208217 72151319109279513134406163)
  ·
    refine ⟨108226978663919269701609245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72151319109279513134406163 108226978663919269701609245)
    ·
      refine ⟨40585116998969726138103467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108226978663919269701609245 40585116998969726138103467)
      ·
        refine ⟨60877675498454589207155201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40585116998969726138103467 60877675498454589207155201)
        ·
          refine ⟨45658256623840941905366401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60877675498454589207155201 45658256623840941905366401)
          ·
            refine ⟨34243692467880706429024801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45658256623840941905366401 34243692467880706429024801)
            ·
              refine ⟨25682769350910529821768601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34243692467880706429024801 25682769350910529821768601)
              ·
                refine ⟨19262077013182897366326451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25682769350910529821768601 19262077013182897366326451)
                ·
                  refine ⟨28893115519774346049489677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19262077013182897366326451 28893115519774346049489677)
                  ·
                    refine ⟨10834918319915379768558629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28893115519774346049489677 10834918319915379768558629)
                    ·
                      refine ⟨2031547184984133706604743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10834918319915379768558629 2031547184984133706604743)
                      ·
                        rfl

theorem cell23_3956424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_3956424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3956424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3956424 prefixEnd_3956424 := by exact prefixLift 3956424
  have htrace : WordTrace (prefixWord ++ tailWord_3956424) baseStart_3956424 baseEnd_3956424 := by
    simpa [prefixWord, tailWord_3956424, baseEnd_3956424] using wordTrace_append hprefix tailTrace_3956424
  have hstable : (prefixWord ++ tailWord_3956424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956424).length < 2 ^ (prefixWord ++ tailWord_3956424).sum := by decide
  have hdescent : baseEnd_3956424 < baseStart_3956424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956441 : List Nat := [1, 2, 1, 2, 3, 3, 3, 1, 2, 1, 4]
def baseStart_3956441 : Nat := 118140960795 + 3956441 * 2 ^ 59
def prefixEnd_3956441 : Nat := 4983230072969 + 3 ^ 40 * 3956441 * 2
def baseEnd_3956441 : Nat := 2031555914155260140092165

theorem tailTrace_3956441 : CollatzResearch.WordTrace tailWord_3956441 prefixEnd_3956441 2031555914155260140092165 := by
  unfold tailWord_3956441
  simp only [CollatzResearch.WordTrace]
  refine ⟨144303258259497438172181177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96202172172998292114787451 144303258259497438172181177)
  ·
    refine ⟨108227443694623078629135883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144303258259497438172181177 108227443694623078629135883)
    ·
      refine ⟨162341165541934617943703825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108227443694623078629135883 162341165541934617943703825)
      ·
        refine ⟨121755874156450963457777869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162341165541934617943703825 121755874156450963457777869)
        ·
          refine ⟨45658452808669111296666701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121755874156450963457777869 45658452808669111296666701)
          ·
            refine ⟨17121919803250916736250013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45658452808669111296666701 17121919803250916736250013)
            ·
              refine ⟨6420719926219093776093755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17121919803250916736250013 6420719926219093776093755)
              ·
                refine ⟨9631079889328640664140633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6420719926219093776093755 9631079889328640664140633)
                ·
                  refine ⟨7223309916996480498105475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9631079889328640664140633 7223309916996480498105475)
                  ·
                    refine ⟨10834964875494720747158213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7223309916996480498105475 10834964875494720747158213)
                    ·
                      refine ⟨2031555914155260140092165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10834964875494720747158213 2031555914155260140092165)
                      ·
                        rfl

theorem cell23_3956441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 1, 4].length) (baseStart_3956441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3956441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3956441 prefixEnd_3956441 := by exact prefixLift 3956441
  have htrace : WordTrace (prefixWord ++ tailWord_3956441) baseStart_3956441 baseEnd_3956441 := by
    simpa [prefixWord, tailWord_3956441, baseEnd_3956441] using wordTrace_append hprefix tailTrace_3956441
  have hstable : (prefixWord ++ tailWord_3956441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956441).length < 2 ^ (prefixWord ++ tailWord_3956441).sum := by decide
  have hdescent : baseEnd_3956441 < baseStart_3956441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956464 : List Nat := [2, 1, 1, 1, 3, 1, 2, 6, 6]
def baseStart_3956464 : Nat := 118140960795 + 3956464 * 2 ^ 59
def prefixEnd_3956464 : Nat := 4983230072969 + 3 ^ 40 * 3956464 * 2
def baseEnd_3956464 : Nat := 225729747134479283344951

theorem tailTrace_3956464 : CollatzResearch.WordTrace tailWord_3956464 prefixEnd_3956464 225729747134479283344951 := by
  unfold tailWord_3956464
  simp only [CollatzResearch.WordTrace]
  refine ⟨72152048569207056550134223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96202731425609408733512297 72152048569207056550134223)
  ·
    refine ⟨108228072853810584825201335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72152048569207056550134223 108228072853810584825201335)
    ·
      refine ⟨162342109280715877237802003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108228072853810584825201335 162342109280715877237802003)
      ·
        refine ⟨243513163921073815856703005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162342109280715877237802003 243513163921073815856703005)
        ·
          refine ⟨91317436470402680946263627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243513163921073815856703005 91317436470402680946263627)
          ·
            refine ⟨136976154705604021419395441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91317436470402680946263627 136976154705604021419395441)
            ·
              refine ⟨102732116029203016064546581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136976154705604021419395441 102732116029203016064546581)
              ·
                refine ⟨4815567938868891378025621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102732116029203016064546581 4815567938868891378025621)
                ·
                  refine ⟨225729747134479283344951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4815567938868891378025621 225729747134479283344951)
                  ·
                    rfl

theorem cell23_3956464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 6].length) (baseStart_3956464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3956464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3956464 prefixEnd_3956464 := by exact prefixLift 3956464
  have htrace : WordTrace (prefixWord ++ tailWord_3956464) baseStart_3956464 baseEnd_3956464 := by
    simpa [prefixWord, tailWord_3956464, baseEnd_3956464] using wordTrace_append hprefix tailTrace_3956464
  have hstable : (prefixWord ++ tailWord_3956464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956464).length < 2 ^ (prefixWord ++ tailWord_3956464).sum := by decide
  have hdescent : baseEnd_3956464 < baseStart_3956464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956511 : List Nat := [1, 1, 2, 4, 2, 1, 1, 5, 1, 5]
def baseStart_3956511 : Nat := 118140960795 + 3956511 * 2 ^ 59
def prefixEnd_3956511 : Nat := 4983230072969 + 3 ^ 40 * 3956511 * 2
def baseEnd_3956511 : Nat := 677197285933691622072281

theorem tailTrace_3956511 : CollatzResearch.WordTrace tailWord_3956511 prefixEnd_3956511 677197285933691622072281 := by
  unfold tailWord_3956511
  simp only [CollatzResearch.WordTrace]
  refine ⟨144305811369243840127229387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96203874246162560084819591 144305811369243840127229387)
  ·
    refine ⟨216458717053865760190844081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144305811369243840127229387 216458717053865760190844081)
    ·
      refine ⟨162344037790399320143133061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216458717053865760190844081 162344037790399320143133061)
      ·
        refine ⟨30439507085699872526837449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162344037790399320143133061 30439507085699872526837449)
        ·
          refine ⟨22829630314274904395128087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30439507085699872526837449 22829630314274904395128087)
          ·
            refine ⟨34244445471412356592692131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22829630314274904395128087 34244445471412356592692131)
            ·
              refine ⟨51366668207118534889038197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34244445471412356592692131 51366668207118534889038197)
              ·
                refine ⟨4815625144417362645847331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51366668207118534889038197 4815625144417362645847331)
                ·
                  refine ⟨7223437716626043968770997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4815625144417362645847331 7223437716626043968770997)
                  ·
                    refine ⟨677197285933691622072281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7223437716626043968770997 677197285933691622072281)
                    ·
                      rfl

theorem cell23_3956511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 5].length) (baseStart_3956511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3956511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3956511 prefixEnd_3956511 := by exact prefixLift 3956511
  have htrace : WordTrace (prefixWord ++ tailWord_3956511) baseStart_3956511 baseEnd_3956511 := by
    simpa [prefixWord, tailWord_3956511, baseEnd_3956511] using wordTrace_append hprefix tailTrace_3956511
  have hstable : (prefixWord ++ tailWord_3956511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956511).length < 2 ^ (prefixWord ++ tailWord_3956511).sum := by decide
  have hdescent : baseEnd_3956511 < baseStart_3956511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956554 : List Nat := [3, 1, 2, 1, 1, 1, 3, 11]
def baseStart_3956554 : Nat := 118140960795 + 3956554 * 2 ^ 59
def prefixEnd_3956554 : Nat := 4983230072969 + 3 ^ 40 * 3956554 * 2
def baseEnd_3956554 : Nat := 75244960647008081406635

theorem tailTrace_3956554 : CollatzResearch.WordTrace tailWord_3956554 prefixEnd_3956554 75244960647008081406635 := by
  unfold tailWord_3956554
  simp only [CollatzResearch.WordTrace]
  refine ⟨36076844927022014617761179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96204919805392038980696477 36076844927022014617761179)
  ·
    refine ⟨54115267390533021926641769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36076844927022014617761179 54115267390533021926641769)
    ·
      refine ⟨40586450542899766444981327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54115267390533021926641769 40586450542899766444981327)
      ·
        refine ⟨60879675814349649667471991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40586450542899766444981327 60879675814349649667471991)
        ·
          refine ⟨91319513721524474501207987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60879675814349649667471991 91319513721524474501207987)
          ·
            refine ⟨136979270582286711751811981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91319513721524474501207987 136979270582286711751811981)
            ·
              refine ⟨51367226468357516906929493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136979270582286711751811981 51367226468357516906929493)
              ·
                refine ⟨75244960647008081406635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 51367226468357516906929493 75244960647008081406635)
                ·
                  rfl

theorem cell23_3956554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 11].length) (baseStart_3956554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3956554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3956554 prefixEnd_3956554 := by exact prefixLift 3956554
  have htrace : WordTrace (prefixWord ++ tailWord_3956554) baseStart_3956554 baseEnd_3956554 := by
    simpa [prefixWord, tailWord_3956554, baseEnd_3956554] using wordTrace_append hprefix tailTrace_3956554
  have hstable : (prefixWord ++ tailWord_3956554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956554).length < 2 ^ (prefixWord ++ tailWord_3956554).sum := by decide
  have hdescent : baseEnd_3956554 < baseStart_3956554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956561 : List Nat := [1, 2, 2, 1, 5, 1, 1, 1, 3, 2, 4]
def baseStart_3956561 : Nat := 118140960795 + 3956561 * 2 ^ 59
def prefixEnd_3956561 : Nat := 4983230072969 + 3 ^ 40 * 3956561 * 2
def baseEnd_3956561 : Nat := 2031617531833799670591613

theorem tailTrace_3956561 : CollatzResearch.WordTrace tailWord_3956561 prefixEnd_3956561 2031617531833799670591613 := by
  unfold tailWord_3956561
  simp only [CollatzResearch.WordTrace]
  refine ⟨144307635019062698666549537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96205090012708465777699691 144307635019062698666549537)
  ·
    refine ⟨108230726264297023999912153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144307635019062698666549537 108230726264297023999912153)
    ·
      refine ⟨81173044698222767999934115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108230726264297023999912153 81173044698222767999934115)
      ·
        refine ⟨121759567047334151999901173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81173044698222767999934115 121759567047334151999901173)
        ·
          refine ⟨11414959410687576749990735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121759567047334151999901173 11414959410687576749990735)
          ·
            refine ⟨17122439116031365124986103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11414959410687576749990735 17122439116031365124986103)
            ·
              refine ⟨25683658674047047687479155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17122439116031365124986103 25683658674047047687479155)
              ·
                refine ⟨38525488011070571531218733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25683658674047047687479155 38525488011070571531218733)
                ·
                  refine ⟨14447058004151464324207025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38525488011070571531218733 14447058004151464324207025)
                  ·
                    refine ⟨10835293503113598243155269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14447058004151464324207025 10835293503113598243155269)
                    ·
                      refine ⟨2031617531833799670591613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10835293503113598243155269 2031617531833799670591613)
                      ·
                        rfl

theorem cell23_3956561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 2, 4].length) (baseStart_3956561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3956561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3956561 prefixEnd_3956561 := by exact prefixLift 3956561
  have htrace : WordTrace (prefixWord ++ tailWord_3956561) baseStart_3956561 baseEnd_3956561 := by
    simpa [prefixWord, tailWord_3956561, baseEnd_3956561] using wordTrace_append hprefix tailTrace_3956561
  have hstable : (prefixWord ++ tailWord_3956561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956561).length < 2 ^ (prefixWord ++ tailWord_3956561).sum := by decide
  have hdescent : baseEnd_3956561 < baseStart_3956561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956565 : List Nat := [1, 3, 2, 2, 2, 3, 3, 1, 1, 1, 4]
def baseStart_3956565 : Nat := 118140960795 + 3956565 * 2 ^ 59
def prefixEnd_3956565 : Nat := 4983230072969 + 3 ^ 40 * 3956565 * 2
def baseEnd_3956565 : Nat := 2031619585756417654941595

theorem tailTrace_3956565 : CollatzResearch.WordTrace tailWord_3956565 prefixEnd_3956565 2031619585756417654941595 := by
  unfold tailWord_3956565
  simp only [CollatzResearch.WordTrace]
  refine ⟨144307780911048207349695149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96205187274032138233130099 144307780911048207349695149)
  ·
    refine ⟨54115417841643077756135681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144307780911048207349695149 54115417841643077756135681)
    ·
      refine ⟨40586563381232308317101761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54115417841643077756135681 40586563381232308317101761)
      ·
        refine ⟨30439922535924231237826321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40586563381232308317101761 30439922535924231237826321)
        ·
          refine ⟨22829941901943173428369741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30439922535924231237826321 22829941901943173428369741)
          ·
            refine ⟨8561228213228690035638653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22829941901943173428369741 8561228213228690035638653)
            ·
              refine ⟨3210460579960758763364495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8561228213228690035638653 3210460579960758763364495)
              ·
                refine ⟨4815690869941138145046743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3210460579960758763364495 4815690869941138145046743)
                ·
                  refine ⟨7223536304911707217570115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4815690869941138145046743 7223536304911707217570115)
                  ·
                    refine ⟨10835304457367560826355173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7223536304911707217570115 10835304457367560826355173)
                    ·
                      refine ⟨2031619585756417654941595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10835304457367560826355173 2031619585756417654941595)
                      ·
                        rfl

theorem cell23_3956565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_3956565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3956565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3956565 prefixEnd_3956565 := by exact prefixLift 3956565
  have htrace : WordTrace (prefixWord ++ tailWord_3956565) baseStart_3956565 baseEnd_3956565 := by
    simpa [prefixWord, tailWord_3956565, baseEnd_3956565] using wordTrace_append hprefix tailTrace_3956565
  have hstable : (prefixWord ++ tailWord_3956565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956565).length < 2 ^ (prefixWord ++ tailWord_3956565).sum := by decide
  have hdescent : baseEnd_3956565 < baseStart_3956565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956581 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 5, 3, 3]
def baseStart_3956581 : Nat := 118140960795 + 3956581 * 2 ^ 59
def prefixEnd_3956581 : Nat := 4983230072969 + 3 ^ 40 * 3956581 * 2
def baseEnd_3956581 : Nat := 2031627801446889592341521

theorem tailTrace_3956581 : CollatzResearch.WordTrace tailWord_3956581 prefixEnd_3956581 2031627801446889592341521 := by
  unfold tailWord_3956581
  simp only [CollatzResearch.WordTrace]
  refine ⟨144308364478990242082277597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96205576319326828054851731 144308364478990242082277597)
  ·
    refine ⟨54115636679621340780854099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144308364478990242082277597 54115636679621340780854099)
    ·
      refine ⟨81173455019432011171281149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54115636679621340780854099 81173455019432011171281149)
      ·
        refine ⟨30440045632287004189230431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81173455019432011171281149 30440045632287004189230431)
        ·
          refine ⟨45660068448430506283845647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30440045632287004189230431 45660068448430506283845647)
          ·
            refine ⟨68490102672645759425768471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45660068448430506283845647 68490102672645759425768471)
            ·
              refine ⟨102735154008968639138652707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68490102672645759425768471 102735154008968639138652707)
              ·
                refine ⟨154102731013452958707979061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102735154008968639138652707 154102731013452958707979061)
                ·
                  refine ⟨14447131032511214878873037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 154102731013452958707979061 14447131032511214878873037)
                  ·
                    refine ⟨5417674137191705579577389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14447131032511214878873037 5417674137191705579577389)
                    ·
                      refine ⟨2031627801446889592341521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5417674137191705579577389 2031627801446889592341521)
                      ·
                        rfl

theorem cell23_3956581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_3956581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3956581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3956581 prefixEnd_3956581 := by exact prefixLift 3956581
  have htrace : WordTrace (prefixWord ++ tailWord_3956581) baseStart_3956581 baseEnd_3956581 := by
    simpa [prefixWord, tailWord_3956581, baseEnd_3956581] using wordTrace_append hprefix tailTrace_3956581
  have hstable : (prefixWord ++ tailWord_3956581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956581).length < 2 ^ (prefixWord ++ tailWord_3956581).sum := by decide
  have hdescent : baseEnd_3956581 < baseStart_3956581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956608 : List Nat := [2, 1, 1, 2, 1, 2, 3, 3, 3, 3, 2]
def baseStart_3956608 : Nat := 118140960795 + 3956608 * 2 ^ 59
def prefixEnd_3956608 : Nat := 4983230072969 + 3 ^ 40 * 3956608 * 2
def baseEnd_3956608 : Nat := 2031641665424560986703897

theorem tailTrace_3956608 : CollatzResearch.WordTrace tailWord_3956608 prefixEnd_3956608 2031641665424560986703897 := by
  unfold tailWord_3956608
  simp only [CollatzResearch.WordTrace]
  refine ⟨72154674624946212846755239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96206232833261617129006985 72154674624946212846755239)
  ·
    refine ⟨108232011937419319270132859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72154674624946212846755239 108232011937419319270132859)
    ·
      refine ⟨162348017906128978905199289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108232011937419319270132859 162348017906128978905199289)
      ·
        refine ⟨121761013429596734178899467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162348017906128978905199289 121761013429596734178899467)
        ·
          refine ⟨182641520144395101268349201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121761013429596734178899467 182641520144395101268349201)
          ·
            refine ⟨136981140108296325951261901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182641520144395101268349201 136981140108296325951261901)
            ·
              refine ⟨51367927540611122231723213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136981140108296325951261901 51367927540611122231723213)
              ·
                refine ⟨19262972827729170836896205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51367927540611122231723213 19262972827729170836896205)
                ·
                  refine ⟨7223614810398439063836077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19262972827729170836896205 7223614810398439063836077)
                  ·
                    refine ⟨2708855553899414648938529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7223614810398439063836077 2708855553899414648938529)
                    ·
                      refine ⟨2031641665424560986703897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2708855553899414648938529 2031641665424560986703897)
                      ·
                        rfl

theorem cell23_3956608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 3, 3, 2].length) (baseStart_3956608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3956608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3956608 prefixEnd_3956608 := by exact prefixLift 3956608
  have htrace : WordTrace (prefixWord ++ tailWord_3956608) baseStart_3956608 baseEnd_3956608 := by
    simpa [prefixWord, tailWord_3956608, baseEnd_3956608] using wordTrace_append hprefix tailTrace_3956608
  have hstable : (prefixWord ++ tailWord_3956608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956608).length < 2 ^ (prefixWord ++ tailWord_3956608).sum := by decide
  have hdescent : baseEnd_3956608 < baseStart_3956608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956631 : List Nat := [1, 1, 3, 3, 1, 3, 1, 2, 2, 6]
def baseStart_3956631 : Nat := 118140960795 + 3956631 * 2 ^ 59
def prefixEnd_3956631 : Nat := 4983230072969 + 3 ^ 40 * 3956631 * 2
def baseEnd_3956631 : Nat := 677217825159871465572097

theorem tailTrace_3956631 : CollatzResearch.WordTrace tailWord_3956631 prefixEnd_3956631 677217825159871465572097 := by
  unfold tailWord_3956631
  simp only [CollatzResearch.WordTrace]
  refine ⟨144310188128809100621597747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96206792085872733747731831 144310188128809100621597747)
  ·
    refine ⟨216465282193213650932396621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144310188128809100621597747 216465282193213650932396621)
    ·
      refine ⟨81174480822455119099648733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216465282193213650932396621 81174480822455119099648733)
      ·
        refine ⟨30440430308420669662368275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81174480822455119099648733 30440430308420669662368275)
        ·
          refine ⟨45660645462631004493552413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30440430308420669662368275 45660645462631004493552413)
          ·
            refine ⟨17122742048486626685082155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45660645462631004493552413 17122742048486626685082155)
            ·
              refine ⟨25684113072729940027623233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17122742048486626685082155 25684113072729940027623233)
              ·
                refine ⟨19263084804547455020717425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25684113072729940027623233 19263084804547455020717425)
                ·
                  refine ⟨14447313603410591265538069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19263084804547455020717425 14447313603410591265538069)
                  ·
                    refine ⟨677217825159871465572097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14447313603410591265538069 677217825159871465572097)
                    ·
                      rfl

theorem cell23_3956631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 6].length) (baseStart_3956631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3956631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3956631 prefixEnd_3956631 := by exact prefixLift 3956631
  have htrace : WordTrace (prefixWord ++ tailWord_3956631) baseStart_3956631 baseEnd_3956631 := by
    simpa [prefixWord, tailWord_3956631, baseEnd_3956631] using wordTrace_append hprefix tailTrace_3956631
  have hstable : (prefixWord ++ tailWord_3956631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956631).length < 2 ^ (prefixWord ++ tailWord_3956631).sum := by decide
  have hdescent : baseEnd_3956631 < baseStart_3956631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956632 : List Nat := [2, 1, 2, 6, 1, 1, 1, 1, 4, 1, 3]
def baseStart_3956632 : Nat := 118140960795 + 3956632 * 2 ^ 59
def prefixEnd_3956632 : Nat := 4983230072969 + 3 ^ 40 * 3956632 * 2
def baseEnd_3956632 : Nat := 2031653988960268892803787

theorem tailTrace_3956632 : CollatzResearch.WordTrace tailWord_3956632 prefixEnd_3956632 2031653988960268892803787 := by
  unfold tailWord_3956632
  simp only [CollatzResearch.WordTrace]
  refine ⟨72155112300902738896192075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96206816401203651861589433 72155112300902738896192075)
  ·
    refine ⟨108232668451354108344288113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72155112300902738896192075 108232668451354108344288113)
    ·
      refine ⟨81174501338515581258216085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108232668451354108344288113 81174501338515581258216085)
      ·
        refine ⟨3805054750242917871478879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 81174501338515581258216085 3805054750242917871478879)
        ·
          refine ⟨5707582125364376807218319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3805054750242917871478879 5707582125364376807218319)
          ·
            refine ⟨8561373188046565210827479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5707582125364376807218319 8561373188046565210827479)
            ·
              refine ⟨12842059782069847816241219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8561373188046565210827479 12842059782069847816241219)
              ·
                refine ⟨19263089673104771724361829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12842059782069847816241219 19263089673104771724361829)
                ·
                  refine ⟨3611829313707144698317843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19263089673104771724361829 3611829313707144698317843)
                  ·
                    refine ⟨5417743970560717047476765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3611829313707144698317843 5417743970560717047476765)
                    ·
                      refine ⟨2031653988960268892803787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5417743970560717047476765 2031653988960268892803787)
                      ·
                        rfl

theorem cell23_3956632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_3956632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3956632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3956632 prefixEnd_3956632 := by exact prefixLift 3956632
  have htrace : WordTrace (prefixWord ++ tailWord_3956632) baseStart_3956632 baseEnd_3956632 := by
    simpa [prefixWord, tailWord_3956632, baseEnd_3956632] using wordTrace_append hprefix tailTrace_3956632
  have hstable : (prefixWord ++ tailWord_3956632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956632).length < 2 ^ (prefixWord ++ tailWord_3956632).sum := by decide
  have hdescent : baseEnd_3956632 < baseStart_3956632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956695 : List Nat := [1, 1, 3, 2, 1, 1, 7, 2, 5]
def baseStart_3956695 : Nat := 118140960795 + 3956695 * 2 ^ 59
def prefixEnd_3956695 : Nat := 4983230072969 + 3 ^ 40 * 3956695 * 2
def baseEnd_3956695 : Nat := 225742926471278016257333

theorem tailTrace_3956695 : CollatzResearch.WordTrace tailWord_3956695 prefixEnd_3956695 225742926471278016257333 := by
  unfold tailWord_3956695
  simp only [CollatzResearch.WordTrace]
  refine ⟨144312522400577239551927539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96208348267051493034618359 144312522400577239551927539)
  ·
    refine ⟨216468783600865859327891309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144312522400577239551927539 216468783600865859327891309)
    ·
      refine ⟨81175793850324697247959241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216468783600865859327891309 81175793850324697247959241)
      ·
        refine ⟨60881845387743522935969431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81175793850324697247959241 60881845387743522935969431)
        ·
          refine ⟨91322768081615284403954147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60881845387743522935969431 91322768081615284403954147)
          ·
            refine ⟨136984152122422926605931221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91322768081615284403954147 136984152122422926605931221)
            ·
              refine ⟨3210566065369287342326513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 136984152122422926605931221 3210566065369287342326513)
              ·
                refine ⟨2407924549026965506744885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3210566065369287342326513 2407924549026965506744885)
                ·
                  refine ⟨225742926471278016257333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2407924549026965506744885 225742926471278016257333)
                  ·
                    rfl

theorem cell23_3956695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 2, 5].length) (baseStart_3956695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3956695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3956695 prefixEnd_3956695 := by exact prefixLift 3956695
  have htrace : WordTrace (prefixWord ++ tailWord_3956695) baseStart_3956695 baseEnd_3956695 := by
    simpa [prefixWord, tailWord_3956695, baseEnd_3956695] using wordTrace_append hprefix tailTrace_3956695
  have hstable : (prefixWord ++ tailWord_3956695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956695).length < 2 ^ (prefixWord ++ tailWord_3956695).sum := by decide
  have hdescent : baseEnd_3956695 < baseStart_3956695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956700 : List Nat := [2, 2, 6, 1, 2, 1, 2, 1, 2, 1, 3]
def baseStart_3956700 : Nat := 118140960795 + 3956700 * 2 ^ 59
def prefixEnd_3956700 : Nat := 4983230072969 + 3 ^ 40 * 3956700 * 2
def baseEnd_3956700 : Nat := 2031688905644774626753475

theorem tailTrace_3956700 : CollatzResearch.WordTrace tailWord_3956700 prefixEnd_3956700 2031688905644774626753475 := by
  unfold tailWord_3956700
  simp only [CollatzResearch.WordTrace]
  refine ⟨72156352382779562702929777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96208469843706083603906369 72156352382779562702929777)
  ·
    refine ⟨54117264287084672027197333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72156352382779562702929777 54117264287084672027197333)
    ·
      refine ⟨2536746763457094001274875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 54117264287084672027197333 2536746763457094001274875)
      ·
        refine ⟨3805120145185641001912313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2536746763457094001274875 3805120145185641001912313)
        ·
          refine ⟨2853840108889230751434235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3805120145185641001912313 2853840108889230751434235)
          ·
            refine ⟨4280760163333846127151353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2853840108889230751434235 4280760163333846127151353)
            ·
              refine ⟨3210570122500384595363515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4280760163333846127151353 3210570122500384595363515)
              ·
                refine ⟨4815855183750576893045273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3210570122500384595363515 4815855183750576893045273)
                ·
                  refine ⟨3611891387812932669783955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4815855183750576893045273 3611891387812932669783955)
                  ·
                    refine ⟨5417837081719399004675933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3611891387812932669783955 5417837081719399004675933)
                    ·
                      refine ⟨2031688905644774626753475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5417837081719399004675933 2031688905644774626753475)
                      ·
                        rfl

theorem cell23_3956700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_3956700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3956700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3956700 prefixEnd_3956700 := by exact prefixLift 3956700
  have htrace : WordTrace (prefixWord ++ tailWord_3956700) baseStart_3956700 baseEnd_3956700 := by
    simpa [prefixWord, tailWord_3956700, baseEnd_3956700] using wordTrace_append hprefix tailTrace_3956700
  have hstable : (prefixWord ++ tailWord_3956700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956700).length < 2 ^ (prefixWord ++ tailWord_3956700).sum := by decide
  have hdescent : baseEnd_3956700 < baseStart_3956700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956706 : List Nat := [3, 3, 3, 1, 2, 1, 1, 3, 2, 2, 2]
def baseStart_3956706 : Nat := 118140960795 + 3956706 * 2 ^ 59
def prefixEnd_3956706 : Nat := 4983230072969 + 3 ^ 40 * 3956706 * 2
def baseEnd_3956706 : Nat := 2031691986528701603278447

theorem tailTrace_3956706 : CollatzResearch.WordTrace tailWord_3956706 prefixEnd_3956706 2031691986528701603278447 := by
  unfold tailWord_3956706
  simp only [CollatzResearch.WordTrace]
  refine ⟨36078230900884347107644493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96208615735691592287051981 36078230900884347107644493)
  ·
    refine ⟨13529336587831630165366685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36078230900884347107644493 13529336587831630165366685)
    ·
      refine ⟨5073501220436861312012507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13529336587831630165366685 5073501220436861312012507)
      ·
        refine ⟨7610251830655291968018761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5073501220436861312012507 7610251830655291968018761)
        ·
          refine ⟨5707688872991468976014071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7610251830655291968018761 5707688872991468976014071)
          ·
            refine ⟨8561533309487203464021107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5707688872991468976014071 8561533309487203464021107)
            ·
              refine ⟨12842299964230805196031661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8561533309487203464021107 12842299964230805196031661)
              ·
                refine ⟨4815862486586551948511873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12842299964230805196031661 4815862486586551948511873)
                ·
                  refine ⟨3611896864939913961383905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4815862486586551948511873 3611896864939913961383905)
                  ·
                    refine ⟨2708922648704935471037929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3611896864939913961383905 2708922648704935471037929)
                    ·
                      refine ⟨2031691986528701603278447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2708922648704935471037929 2031691986528701603278447)
                      ·
                        rfl

theorem cell23_3956706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_3956706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3956706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3956706 prefixEnd_3956706 := by exact prefixLift 3956706
  have htrace : WordTrace (prefixWord ++ tailWord_3956706) baseStart_3956706 baseEnd_3956706 := by
    simpa [prefixWord, tailWord_3956706, baseEnd_3956706] using wordTrace_append hprefix tailTrace_3956706
  have hstable : (prefixWord ++ tailWord_3956706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956706).length < 2 ^ (prefixWord ++ tailWord_3956706).sum := by decide
  have hdescent : baseEnd_3956706 < baseStart_3956706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956728 : List Nat := [2, 1, 2, 1, 1, 3, 3, 3, 2, 1, 4]
def baseStart_3956728 : Nat := 118140960795 + 3956728 * 2 ^ 59
def prefixEnd_3956728 : Nat := 4983230072969 + 3 ^ 40 * 3956728 * 2
def baseEnd_3956728 : Nat := 2031703283103100517203345

theorem tailTrace_3956728 : CollatzResearch.WordTrace tailWord_3956728 prefixEnd_3956728 2031703283103100517203345 := by
  unfold tailWord_3956728
  simp only [CollatzResearch.WordTrace]
  refine ⟨72156863004728843093939419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96209150672971790791919225 72156863004728843093939419)
  ·
    refine ⟨108235294507093264640909129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72156863004728843093939419 108235294507093264640909129)
    ·
      refine ⟨81176470880319948480681847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108235294507093264640909129 81176470880319948480681847)
      ·
        refine ⟨121764706320479922721022771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81176470880319948480681847 121764706320479922721022771)
        ·
          refine ⟨182647059480719884081534157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121764706320479922721022771 182647059480719884081534157)
          ·
            refine ⟨68492647305269956530575309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182647059480719884081534157 68492647305269956530575309)
            ·
              refine ⟨25684742739476233698965741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68492647305269956530575309 25684742739476233698965741)
              ·
                refine ⟨9631778527303587637112153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25684742739476233698965741 9631778527303587637112153)
                ·
                  refine ⟨7223833895477690727834115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9631778527303587637112153 7223833895477690727834115)
                  ·
                    refine ⟨10835750843216536091751173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7223833895477690727834115 10835750843216536091751173)
                    ·
                      refine ⟨2031703283103100517203345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10835750843216536091751173 2031703283103100517203345)
                      ·
                        rfl

theorem cell23_3956728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 2, 1, 4].length) (baseStart_3956728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3956728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3956728 prefixEnd_3956728 := by exact prefixLift 3956728
  have htrace : WordTrace (prefixWord ++ tailWord_3956728) baseStart_3956728 baseEnd_3956728 := by
    simpa [prefixWord, tailWord_3956728, baseEnd_3956728] using wordTrace_append hprefix tailTrace_3956728
  have hstable : (prefixWord ++ tailWord_3956728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956728).length < 2 ^ (prefixWord ++ tailWord_3956728).sum := by decide
  have hdescent : baseEnd_3956728 < baseStart_3956728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956772 : List Nat := [2, 3, 1, 4, 2, 1, 1, 2, 3, 4]
def baseStart_3956772 : Nat := 118140960795 + 3956772 * 2 ^ 59
def prefixEnd_3956772 : Nat := 4983230072969 + 3 ^ 40 * 3956772 * 2
def baseEnd_3956772 : Nat := 677241958750632781684381

theorem tailTrace_3956772 : CollatzResearch.WordTrace tailWord_3956772 prefixEnd_3956772 677241958750632781684381 := by
  unfold tailWord_3956772
  simp only [CollatzResearch.WordTrace]
  refine ⟨72157665410649140851240285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96210220547532187801653713 72157665410649140851240285)
  ·
    refine ⟨27059124528993427819215107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72157665410649140851240285 27059124528993427819215107)
    ·
      refine ⟨40588686793490141728822661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27059124528993427819215107 40588686793490141728822661)
      ·
        refine ⟨7610378773779401574154249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40588686793490141728822661 7610378773779401574154249)
        ·
          refine ⟨5707784080334551180615687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7610378773779401574154249 5707784080334551180615687)
          ·
            refine ⟨8561676120501826770923531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5707784080334551180615687 8561676120501826770923531)
            ·
              refine ⟨12842514180752740156385297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8561676120501826770923531 12842514180752740156385297)
              ·
                refine ⟨9631885635564555117288973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12842514180752740156385297 9631885635564555117288973)
                ·
                  refine ⟨3611957113336708168983365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9631885635564555117288973 3611957113336708168983365)
                  ·
                    refine ⟨677241958750632781684381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3611957113336708168983365 677241958750632781684381)
                    ·
                      rfl

theorem cell23_3956772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 3, 4].length) (baseStart_3956772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3956772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3956772 prefixEnd_3956772 := by exact prefixLift 3956772
  have htrace : WordTrace (prefixWord ++ tailWord_3956772) baseStart_3956772 baseEnd_3956772 := by
    simpa [prefixWord, tailWord_3956772, baseEnd_3956772] using wordTrace_append hprefix tailTrace_3956772
  have hstable : (prefixWord ++ tailWord_3956772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956772).length < 2 ^ (prefixWord ++ tailWord_3956772).sum := by decide
  have hdescent : baseEnd_3956772 < baseStart_3956772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956782 : List Nat := [4, 1, 3, 1, 1, 2, 3, 1, 2, 2, 3]
def baseStart_3956782 : Nat := 118140960795 + 3956782 * 2 ^ 59
def prefixEnd_3956782 : Nat := 4983230072969 + 3 ^ 40 * 3956782 * 2
def baseEnd_3956782 : Nat := 2031731011058443305928097

theorem tailTrace_3956782 : CollatzResearch.WordTrace tailWord_3956782 prefixEnd_3956782 2031731011058443305928097 := by
  unfold tailWord_3956782
  simp only [CollatzResearch.WordTrace]
  refine ⟨18039461943907756676293075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96210463700841368940229733 18039461943907756676293075)
  ·
    refine ⟨27059192915861635014439613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18039461943907756676293075 27059192915861635014439613)
    ·
      refine ⟨10147197343448113130414855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27059192915861635014439613 10147197343448113130414855)
      ·
        refine ⟨15220796015172169695622283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10147197343448113130414855 15220796015172169695622283)
        ·
          refine ⟨22831194022758254543433425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15220796015172169695622283 22831194022758254543433425)
          ·
            refine ⟨17123395517068690907575069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22831194022758254543433425 17123395517068690907575069)
            ·
              refine ⟨6421273318900759090340651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17123395517068690907575069 6421273318900759090340651)
              ·
                refine ⟨9631909978351138635510977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6421273318900759090340651 9631909978351138635510977)
                ·
                  refine ⟨7223932483763353976633233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9631909978351138635510977 7223932483763353976633233)
                  ·
                    refine ⟨5417949362822515482474925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7223932483763353976633233 5417949362822515482474925)
                    ·
                      refine ⟨2031731011058443305928097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5417949362822515482474925 2031731011058443305928097)
                      ·
                        rfl

theorem cell23_3956782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_3956782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3956782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3956782 prefixEnd_3956782 := by exact prefixLift 3956782
  have htrace : WordTrace (prefixWord ++ tailWord_3956782) baseStart_3956782 baseEnd_3956782 := by
    simpa [prefixWord, tailWord_3956782, baseEnd_3956782] using wordTrace_append hprefix tailTrace_3956782
  have hstable : (prefixWord ++ tailWord_3956782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956782).length < 2 ^ (prefixWord ++ tailWord_3956782).sum := by decide
  have hdescent : baseEnd_3956782 < baseStart_3956782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956805 : List Nat := [1, 3, 1, 1, 1, 3, 1, 3, 4, 3, 2]
def baseStart_3956805 : Nat := 118140960795 + 3956805 * 2 ^ 59
def prefixEnd_3956805 : Nat := 4983230072969 + 3 ^ 40 * 3956805 * 2
def baseEnd_3956805 : Nat := 2031742821113496715940491

theorem tailTrace_3956805 : CollatzResearch.WordTrace tailWord_3956805 prefixEnd_3956805 2031742821113496715940491 := by
  unfold tailWord_3956805
  simp only [CollatzResearch.WordTrace]
  refine ⟨144316534430178728338431869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96211022953452485558954579 144316534430178728338431869)
  ·
    refine ⟨54118700411317023126911951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144316534430178728338431869 54118700411317023126911951)
    ·
      refine ⟨81178050616975534690367927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54118700411317023126911951 81178050616975534690367927)
      ·
        refine ⟨121767075925463302035551891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81178050616975534690367927 121767075925463302035551891)
        ·
          refine ⟨182650613888194953053327837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121767075925463302035551891 182650613888194953053327837)
          ·
            refine ⟨68493980208073107394997939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182650613888194953053327837 68493980208073107394997939)
            ·
              refine ⟨102740970312109661092496909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68493980208073107394997939 102740970312109661092496909)
              ·
                refine ⟨38527863867041122909686341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102740970312109661092496909 38527863867041122909686341)
                ·
                  refine ⟨7223974475070210545566189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38527863867041122909686341 7223974475070210545566189)
                  ·
                    refine ⟨2708990428151328954587321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7223974475070210545566189 2708990428151328954587321)
                    ·
                      refine ⟨2031742821113496715940491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2708990428151328954587321 2031742821113496715940491)
                      ·
                        rfl

theorem cell23_3956805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 3, 2].length) (baseStart_3956805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3956805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3956805 prefixEnd_3956805 := by exact prefixLift 3956805
  have htrace : WordTrace (prefixWord ++ tailWord_3956805) baseStart_3956805 baseEnd_3956805 := by
    simpa [prefixWord, tailWord_3956805, baseEnd_3956805] using wordTrace_append hprefix tailTrace_3956805
  have hstable : (prefixWord ++ tailWord_3956805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956805).length < 2 ^ (prefixWord ++ tailWord_3956805).sum := by decide
  have hdescent : baseEnd_3956805 < baseStart_3956805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956829 : List Nat := [1, 4, 4, 1, 1, 1, 2, 2, 3, 1, 3]
def baseStart_3956829 : Nat := 118140960795 + 3956829 * 2 ^ 59
def prefixEnd_3956829 : Nat := 4983230072969 + 3 ^ 40 * 3956829 * 2
def baseEnd_3956829 : Nat := 2031755144649204622040381

theorem tailTrace_3956829 : CollatzResearch.WordTrace tailWord_3956829 prefixEnd_3956829 2031755144649204622040381 := by
  unfold tailWord_3956829
  simp only [CollatzResearch.WordTrace]
  refine ⟨144317409782091780437305541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96211606521394520291537027 144317409782091780437305541)
  ·
    refine ⟨27059514334142208831994789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144317409782091780437305541 27059514334142208831994789)
    ·
      refine ⟨5073658937651664155999023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27059514334142208831994789 5073658937651664155999023)
      ·
        refine ⟨7610488406477496233998535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5073658937651664155999023 7610488406477496233998535)
        ·
          refine ⟨11415732609716244350997803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7610488406477496233998535 11415732609716244350997803)
          ·
            refine ⟨17123598914574366526496705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11415732609716244350997803 17123598914574366526496705)
            ·
              refine ⟨12842699185930774894872529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17123598914574366526496705 12842699185930774894872529)
              ·
                refine ⟨9632024389448081171154397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12842699185930774894872529 9632024389448081171154397)
                ·
                  refine ⟨3612009146043030439182899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9632024389448081171154397 3612009146043030439182899)
                  ·
                    refine ⟨5418013719064545658774349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3612009146043030439182899 5418013719064545658774349)
                    ·
                      refine ⟨2031755144649204622040381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5418013719064545658774349 2031755144649204622040381)
                      ·
                        rfl

theorem cell23_3956829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_3956829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3956829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3956829 prefixEnd_3956829 := by exact prefixLift 3956829
  have htrace : WordTrace (prefixWord ++ tailWord_3956829) baseStart_3956829 baseEnd_3956829 := by
    simpa [prefixWord, tailWord_3956829, baseEnd_3956829] using wordTrace_append hprefix tailTrace_3956829
  have hstable : (prefixWord ++ tailWord_3956829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956829).length < 2 ^ (prefixWord ++ tailWord_3956829).sum := by decide
  have hdescent : baseEnd_3956829 < baseStart_3956829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956835 : List Nat := [1, 1, 1, 5, 1, 1, 3, 4, 1, 1, 4]
def baseStart_3956835 : Nat := 118140960795 + 3956835 * 2 ^ 59
def prefixEnd_3956835 : Nat := 4983230072969 + 3 ^ 40 * 3956835 * 2
def baseEnd_3956835 : Nat := 2031758225533131598565353

theorem tailTrace_3956835 : CollatzResearch.WordTrace tailWord_3956835 prefixEnd_3956835 2031758225533131598565353 := by
  unfold tailWord_3956835
  simp only [CollatzResearch.WordTrace]
  refine ⟨144317628620070043462023959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96211752413380028974682639 144317628620070043462023959)
  ·
    refine ⟨216476442930105065193035939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144317628620070043462023959 216476442930105065193035939)
    ·
      refine ⟨324714664395157597789553909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216476442930105065193035939 324714664395157597789553909)
      ·
        refine ⟨30441999787046024792770679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 324714664395157597789553909 30441999787046024792770679)
        ·
          refine ⟨45662999680569037189156019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30441999787046024792770679 45662999680569037189156019)
          ·
            refine ⟨68494499520853555783734029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45662999680569037189156019 68494499520853555783734029)
            ·
              refine ⟨25685437320320083418900261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68494499520853555783734029 25685437320320083418900261)
              ·
                refine ⟨4816019497560015641043799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25685437320320083418900261 4816019497560015641043799)
                ·
                  refine ⟨7224029246340023461565699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4816019497560015641043799 7224029246340023461565699)
                  ·
                    refine ⟨10836043869510035192348549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7224029246340023461565699 10836043869510035192348549)
                    ·
                      refine ⟨2031758225533131598565353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10836043869510035192348549 2031758225533131598565353)
                      ·
                        rfl

theorem cell23_3956835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_3956835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3956835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3956835 prefixEnd_3956835 := by exact prefixLift 3956835
  have htrace : WordTrace (prefixWord ++ tailWord_3956835) baseStart_3956835 baseEnd_3956835 := by
    simpa [prefixWord, tailWord_3956835, baseEnd_3956835] using wordTrace_append hprefix tailTrace_3956835
  have hstable : (prefixWord ++ tailWord_3956835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956835).length < 2 ^ (prefixWord ++ tailWord_3956835).sum := by decide
  have hdescent : baseEnd_3956835 < baseStart_3956835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956845 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 6, 4]
def baseStart_3956845 : Nat := 118140960795 + 3956845 * 2 ^ 59
def prefixEnd_3956845 : Nat := 4983230072969 + 3 ^ 40 * 3956845 * 2
def baseEnd_3956845 : Nat := 677254453446558853146769

theorem tailTrace_3956845 : CollatzResearch.WordTrace tailWord_3956845 prefixEnd_3956845 677254453446558853146769 := by
  unfold tailWord_3956845
  simp only [CollatzResearch.WordTrace]
  refine ⟨144317993350033815169887989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96211995566689210113258659 144317993350033815169887989)
  ·
    refine ⟨13529811876565670172176999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144317993350033815169887989 13529811876565670172176999)
    ·
      refine ⟨20294717814848505258265499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13529811876565670172176999 20294717814848505258265499)
      ·
        refine ⟨30442076722272757887398249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20294717814848505258265499 30442076722272757887398249)
        ·
          refine ⟨22831557541704568415548687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30442076722272757887398249 22831557541704568415548687)
          ·
            refine ⟨34247336312556852623323031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22831557541704568415548687 34247336312556852623323031)
            ·
              refine ⟨51371004468835278934984547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34247336312556852623323031 51371004468835278934984547)
              ·
                refine ⟨77056506703252918402476821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51371004468835278934984547 77056506703252918402476821)
                ·
                  refine ⟨3612023751714980550116101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 77056506703252918402476821 3612023751714980550116101)
                  ·
                    refine ⟨677254453446558853146769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3612023751714980550116101 677254453446558853146769)
                    ·
                      rfl

theorem cell23_3956845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_3956845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3956845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3956845 prefixEnd_3956845 := by exact prefixLift 3956845
  have htrace : WordTrace (prefixWord ++ tailWord_3956845) baseStart_3956845 baseEnd_3956845 := by
    simpa [prefixWord, tailWord_3956845, baseEnd_3956845] using wordTrace_append hprefix tailTrace_3956845
  have hstable : (prefixWord ++ tailWord_3956845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956845).length < 2 ^ (prefixWord ++ tailWord_3956845).sum := by decide
  have hdescent : baseEnd_3956845 < baseStart_3956845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956855 : List Nat := [1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 5]
def baseStart_3956855 : Nat := 118140960795 + 3956855 * 2 ^ 59
def prefixEnd_3956855 : Nat := 4983230072969 + 3 ^ 40 * 3956855 * 2
def baseEnd_3956855 : Nat := 2031768495146221520315261

theorem tailTrace_3956855 : CollatzResearch.WordTrace tailWord_3956855 prefixEnd_3956855 2031768495146221520315261 := by
  unfold tailWord_3956855
  simp only [CollatzResearch.WordTrace]
  refine ⟨144318358079997586877752019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96212238719998391251834679 144318358079997586877752019)
  ·
    refine ⟨216477537119996380316628029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144318358079997586877752019 216477537119996380316628029)
    ·
      refine ⟨81179076419998642618735511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216477537119996380316628029 81179076419998642618735511)
      ·
        refine ⟨121768614629997963928103267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81179076419998642618735511 121768614629997963928103267)
        ·
          refine ⟨182652921944996945892154901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121768614629997963928103267 182652921944996945892154901)
          ·
            refine ⟨8561855716171731838694761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 182652921944996945892154901 8561855716171731838694761)
            ·
              refine ⟨6421391787128798879021071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8561855716171731838694761 6421391787128798879021071)
              ·
                refine ⟨9632087680693198318531607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6421391787128798879021071 9632087680693198318531607)
                ·
                  refine ⟨14448131521039797477797411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9632087680693198318531607 14448131521039797477797411)
                  ·
                    refine ⟨21672197281559696216696117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14448131521039797477797411 21672197281559696216696117)
                    ·
                      refine ⟨2031768495146221520315261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21672197281559696216696117 2031768495146221520315261)
                      ·
                        rfl

theorem cell23_3956855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 5].length) (baseStart_3956855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3956855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3956855 prefixEnd_3956855 := by exact prefixLift 3956855
  have htrace : WordTrace (prefixWord ++ tailWord_3956855) baseStart_3956855 baseEnd_3956855 := by
    simpa [prefixWord, tailWord_3956855, baseEnd_3956855] using wordTrace_append hprefix tailTrace_3956855
  have hstable : (prefixWord ++ tailWord_3956855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956855).length < 2 ^ (prefixWord ++ tailWord_3956855).sum := by decide
  have hdescent : baseEnd_3956855 < baseStart_3956855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956869 : List Nat := [1, 3, 1, 1, 5, 1, 3, 1, 3, 2, 2]
def baseStart_3956869 : Nat := 118140960795 + 3956869 * 2 ^ 59
def prefixEnd_3956869 : Nat := 4983230072969 + 3 ^ 40 * 3956869 * 2
def baseEnd_3956869 : Nat := 2031775683875384465540197

theorem tailTrace_3956869 : CollatzResearch.WordTrace tailWord_3956869 prefixEnd_3956869 2031775683875384465540197 := by
  unfold tailWord_3956869
  simp only [CollatzResearch.WordTrace]
  refine ⟨144318868701946867268761661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96212579134631244845841107 144318868701946867268761661)
  ·
    refine ⟨54119575763230075225785623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144318868701946867268761661 54119575763230075225785623)
    ·
      refine ⟨81179363644845112838678435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54119575763230075225785623 81179363644845112838678435)
      ·
        refine ⟨121769045467267669258017653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81179363644845112838678435 121769045467267669258017653)
        ·
          refine ⟨11415848012556343992939155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121769045467267669258017653 11415848012556343992939155)
          ·
            refine ⟨17123772018834515989408733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11415848012556343992939155 17123772018834515989408733)
            ·
              refine ⟨6421414507062943496028275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17123772018834515989408733 6421414507062943496028275)
              ·
                refine ⟨9632121760594415244042413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6421414507062943496028275 9632121760594415244042413)
                ·
                  refine ⟨3612045660222905716515905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9632121760594415244042413 3612045660222905716515905)
                  ·
                    refine ⟨2709034245167179287386929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3612045660222905716515905 2709034245167179287386929)
                    ·
                      refine ⟨2031775683875384465540197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2709034245167179287386929 2031775683875384465540197)
                      ·
                        rfl

theorem cell23_3956869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 3, 2, 2].length) (baseStart_3956869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3956869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3956869 prefixEnd_3956869 := by exact prefixLift 3956869
  have htrace : WordTrace (prefixWord ++ tailWord_3956869) baseStart_3956869 baseEnd_3956869 := by
    simpa [prefixWord, tailWord_3956869, baseEnd_3956869] using wordTrace_append hprefix tailTrace_3956869
  have hstable : (prefixWord ++ tailWord_3956869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956869).length < 2 ^ (prefixWord ++ tailWord_3956869).sum := by decide
  have hdescent : baseEnd_3956869 < baseStart_3956869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956885 : List Nat := [1, 3, 2, 1, 1, 1, 4, 3, 1, 3, 3]
def baseStart_3956885 : Nat := 118140960795 + 3956885 * 2 ^ 59
def prefixEnd_3956885 : Nat := 4983230072969 + 3 ^ 40 * 3956885 * 2
def baseEnd_3956885 : Nat := 2031783899565856402940123

theorem tailTrace_3956885 : CollatzResearch.WordTrace tailWord_3956885 prefixEnd_3956885 2031783899565856402940123 := by
  unfold tailWord_3956885
  simp only [CollatzResearch.WordTrace]
  refine ⟨144319452269888902001344109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96212968179925934667562739 144319452269888902001344109)
  ·
    refine ⟨54119794601208338250504041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144319452269888902001344109 54119794601208338250504041)
    ·
      refine ⟨40589845950906253687878031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54119794601208338250504041 40589845950906253687878031)
      ·
        refine ⟨60884768926359380531817047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40589845950906253687878031 60884768926359380531817047)
        ·
          refine ⟨91327153389539070797725571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60884768926359380531817047 91327153389539070797725571)
          ·
            refine ⟨136990730084308606196588357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91327153389539070797725571 136990730084308606196588357)
            ·
              refine ⟨25685761890807863661860317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136990730084308606196588357 25685761890807863661860317)
              ·
                refine ⟨9632160709052948873197619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25685761890807863661860317 9632160709052948873197619)
                ·
                  refine ⟨14448241063579423309796429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9632160709052948873197619 14448241063579423309796429)
                  ·
                    refine ⟨5418090398842283741173661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14448241063579423309796429 5418090398842283741173661)
                    ·
                      refine ⟨2031783899565856402940123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5418090398842283741173661 2031783899565856402940123)
                      ·
                        rfl

theorem cell23_3956885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 3, 3].length) (baseStart_3956885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3956885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3956885 prefixEnd_3956885 := by exact prefixLift 3956885
  have htrace : WordTrace (prefixWord ++ tailWord_3956885) baseStart_3956885 baseEnd_3956885 := by
    simpa [prefixWord, tailWord_3956885, baseEnd_3956885] using wordTrace_append hprefix tailTrace_3956885
  have hstable : (prefixWord ++ tailWord_3956885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956885).length < 2 ^ (prefixWord ++ tailWord_3956885).sum := by decide
  have hdescent : baseEnd_3956885 < baseStart_3956885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956906 : List Nat := [3, 1, 5, 1, 3, 1, 1, 1, 1, 1, 5]
def baseStart_3956906 : Nat := 118140960795 + 3956906 * 2 ^ 59
def prefixEnd_3956906 : Nat := 4983230072969 + 3 ^ 40 * 3956906 * 2
def baseEnd_3956906 : Nat := 2031794682659600820777527

theorem tailTrace_3956906 : CollatzResearch.WordTrace tailWord_3956906 prefixEnd_3956906 2031794682659600820777527 := by
  unfold tailWord_3956906
  simp only [CollatzResearch.WordTrace]
  refine ⟨36080054550703205646964643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96213478801875215058572381 36080054550703205646964643)
  ·
    refine ⟨54120081826054808470446965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36080054550703205646964643 54120081826054808470446965)
    ·
      refine ⟨5073757671192638294104403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54120081826054808470446965 5073757671192638294104403)
      ·
        refine ⟨7610636506788957441156605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5073757671192638294104403 7610636506788957441156605)
        ·
          refine ⟨2853988690045859040433727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7610636506788957441156605 2853988690045859040433727)
          ·
            refine ⟨4280983035068788560650591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2853988690045859040433727 4280983035068788560650591)
            ·
              refine ⟨6421474552603182840975887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4280983035068788560650591 6421474552603182840975887)
              ·
                refine ⟨9632211828904774261463831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6421474552603182840975887 9632211828904774261463831)
                ·
                  refine ⟨14448317743357161392195747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9632211828904774261463831 14448317743357161392195747)
                  ·
                    refine ⟨21672476615035742088293621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14448317743357161392195747 21672476615035742088293621)
                    ·
                      refine ⟨2031794682659600820777527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21672476615035742088293621 2031794682659600820777527)
                      ·
                        rfl

theorem cell23_3956906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_3956906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3956906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3956906 prefixEnd_3956906 := by exact prefixLift 3956906
  have htrace : WordTrace (prefixWord ++ tailWord_3956906) baseStart_3956906 baseEnd_3956906 := by
    simpa [prefixWord, tailWord_3956906, baseEnd_3956906] using wordTrace_append hprefix tailTrace_3956906
  have hstable : (prefixWord ++ tailWord_3956906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956906).length < 2 ^ (prefixWord ++ tailWord_3956906).sum := by decide
  have hdescent : baseEnd_3956906 < baseStart_3956906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956919 : List Nat := [1, 1, 3, 1, 4, 3, 2, 2, 2, 1, 3]
def baseStart_3956919 : Nat := 118140960795 + 3956919 * 2 ^ 59
def prefixEnd_3956919 : Nat := 4983230072969 + 3 ^ 40 * 3956919 * 2
def baseEnd_3956919 : Nat := 2031801357908109269914967

theorem tailTrace_3956919 : CollatzResearch.WordTrace tailWord_3956919 prefixEnd_3956919 2031801357908109269914967 := by
  unfold tailWord_3956919
  simp only [CollatzResearch.WordTrace]
  refine ⟨144320692351765725808081811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96213794901177150538721207 144320692351765725808081811)
  ·
    refine ⟨216481038527648588712122717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144320692351765725808081811 216481038527648588712122717)
    ·
      refine ⟨81180389447868220767046019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216481038527648588712122717 81180389447868220767046019)
      ·
        refine ⟨121770584171802331150569029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81180389447868220767046019 121770584171802331150569029)
        ·
          refine ⟨22831984532212937090731693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121770584171802331150569029 22831984532212937090731693)
          ·
            refine ⟨8561994199579851409024385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22831984532212937090731693 8561994199579851409024385)
            ·
              refine ⟨6421495649684888556768289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8561994199579851409024385 6421495649684888556768289)
              ·
                refine ⟨4816121737263666417576217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6421495649684888556768289 4816121737263666417576217)
                ·
                  refine ⟨3612091302947749813182163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4816121737263666417576217 3612091302947749813182163)
                  ·
                    refine ⟨5418136954421624719773245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3612091302947749813182163 5418136954421624719773245)
                    ·
                      refine ⟨2031801357908109269914967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5418136954421624719773245 2031801357908109269914967)
                      ·
                        rfl

theorem cell23_3956919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 2, 1, 3].length) (baseStart_3956919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3956919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3956919 prefixEnd_3956919 := by exact prefixLift 3956919
  have htrace : WordTrace (prefixWord ++ tailWord_3956919) baseStart_3956919 baseEnd_3956919 := by
    simpa [prefixWord, tailWord_3956919, baseEnd_3956919] using wordTrace_append hprefix tailTrace_3956919
  have hstable : (prefixWord ++ tailWord_3956919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956919).length < 2 ^ (prefixWord ++ tailWord_3956919).sum := by decide
  have hdescent : baseEnd_3956919 < baseStart_3956919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957002 : List Nat := [3, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2]
def baseStart_3957002 : Nat := 118140960795 + 3957002 * 2 ^ 59
def prefixEnd_3957002 : Nat := 4983230072969 + 3 ^ 40 * 3957002 * 2
def baseEnd_3957002 : Nat := 2031843976802432445177085

theorem tailTrace_3957002 : CollatzResearch.WordTrace tailWord_3957002 prefixEnd_3957002 2031843976802432445177085 := by
  unfold tailWord_3957002
  simp only [CollatzResearch.WordTrace]
  refine ⟨36080929902616257745838315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96215813073643353988902173 36080929902616257745838315)
  ·
    refine ⟨54121394853924386618757473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36080929902616257745838315 54121394853924386618757473)
    ·
      refine ⟨40591046140443289964068105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54121394853924386618757473 40591046140443289964068105)
      ·
        refine ⟨30443284605332467473051079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40591046140443289964068105 30443284605332467473051079)
        ·
          refine ⟨45664926907998701209576619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30443284605332467473051079 45664926907998701209576619)
          ·
            refine ⟨68497390361998051814364929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45664926907998701209576619 68497390361998051814364929)
            ·
              refine ⟨51373042771498538860773697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68497390361998051814364929 51373042771498538860773697)
              ·
                refine ⟨38529782078623904145580273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51373042771498538860773697 38529782078623904145580273)
                ·
                  refine ⟨28897336558967928109185205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38529782078623904145580273 28897336558967928109185205)
                  ·
                    refine ⟨2709125302403243260236113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28897336558967928109185205 2709125302403243260236113)
                    ·
                      refine ⟨2031843976802432445177085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2709125302403243260236113 2031843976802432445177085)
                      ·
                        rfl

theorem cell23_3957002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_3957002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3957002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3957002 prefixEnd_3957002 := by exact prefixLift 3957002
  have htrace : WordTrace (prefixWord ++ tailWord_3957002) baseStart_3957002 baseEnd_3957002 := by
    simpa [prefixWord, tailWord_3957002, baseEnd_3957002] using wordTrace_append hprefix tailTrace_3957002
  have hstable : (prefixWord ++ tailWord_3957002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957002).length < 2 ^ (prefixWord ++ tailWord_3957002).sum := by decide
  have hdescent : baseEnd_3957002 < baseStart_3957002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957052 : List Nat := [2, 2, 2, 2, 1, 2, 1, 2, 4, 2, 3]
def baseStart_3957052 : Nat := 118140960795 + 3957052 * 2 ^ 59
def prefixEnd_3957052 : Nat := 4983230072969 + 3 ^ 40 * 3957052 * 2
def baseEnd_3957052 : Nat := 2031869650835157249551855

theorem tailTrace_3957052 : CollatzResearch.WordTrace tailWord_3957052 prefixEnd_3957052 2031869650835157249551855 := by
  unfold tailWord_3957052
  simp only [CollatzResearch.WordTrace]
  refine ⟨72162771630141944761336705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96217028840189259681782273 72162771630141944761336705)
  ·
    refine ⟨54122078722606458571002529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72162771630141944761336705 54122078722606458571002529)
    ·
      refine ⟨40591559041954843928251897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54122078722606458571002529 40591559041954843928251897)
      ·
        refine ⟨30443669281466132946188923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40591559041954843928251897 30443669281466132946188923)
        ·
          refine ⟨45665503922199199419283385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30443669281466132946188923 45665503922199199419283385)
          ·
            refine ⟨34249127941649399564462539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45665503922199199419283385 34249127941649399564462539)
            ·
              refine ⟨51373691912474099346693809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34249127941649399564462539 51373691912474099346693809)
              ·
                refine ⟨38530268934355574510020357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51373691912474099346693809 38530268934355574510020357)
                ·
                  refine ⟨7224425425191670220628817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38530268934355574510020357 7224425425191670220628817)
                  ·
                    refine ⟨5418319068893752665471613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7224425425191670220628817 5418319068893752665471613)
                    ·
                      refine ⟨2031869650835157249551855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5418319068893752665471613 2031869650835157249551855)
                      ·
                        rfl

theorem cell23_3957052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_3957052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3957052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3957052 prefixEnd_3957052 := by exact prefixLift 3957052
  have htrace : WordTrace (prefixWord ++ tailWord_3957052) baseStart_3957052 baseEnd_3957052 := by
    simpa [prefixWord, tailWord_3957052, baseEnd_3957052] using wordTrace_append hprefix tailTrace_3957052
  have hstable : (prefixWord ++ tailWord_3957052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957052).length < 2 ^ (prefixWord ++ tailWord_3957052).sum := by decide
  have hdescent : baseEnd_3957052 < baseStart_3957052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957093 : List Nat := [1, 3, 1, 3, 1, 5, 2, 2, 1, 4]
def baseStart_3957093 : Nat := 118140960795 + 3957093 * 2 ^ 59
def prefixEnd_3957093 : Nat := 4983230072969 + 3 ^ 40 * 3957093 * 2
def baseEnd_3957093 : Nat := 677296901180663863046389

theorem tailTrace_3957093 : CollatzResearch.WordTrace tailWord_3957093 prefixEnd_3957093 677296901180663863046389 := by
  unfold tailWord_3957093
  simp only [CollatzResearch.WordTrace]
  refine ⟨144327038653135353524915933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96218025768756902349943955 144327038653135353524915933)
  ·
    refine ⟨54122639494925757571843475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144327038653135353524915933 54122639494925757571843475)
    ·
      refine ⟨81183959242388636357765213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54122639494925757571843475 81183959242388636357765213)
      ·
        refine ⟨30443984715895738634161955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81183959242388636357765213 30443984715895738634161955)
        ·
          refine ⟨45665977073843607951242933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30443984715895738634161955 45665977073843607951242933)
          ·
            refine ⟨4281185350672838245429025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45665977073843607951242933 4281185350672838245429025)
            ·
              refine ⟨3210889013004628684071769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4281185350672838245429025 3210889013004628684071769)
              ·
                refine ⟨2408166759753471513053827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3210889013004628684071769 2408166759753471513053827)
                ·
                  refine ⟨3612250139630207269580741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2408166759753471513053827 3612250139630207269580741)
                  ·
                    refine ⟨677296901180663863046389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3612250139630207269580741 677296901180663863046389)
                    ·
                      rfl

theorem cell23_3957093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 2, 1, 4].length) (baseStart_3957093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3957093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3957093 prefixEnd_3957093 := by exact prefixLift 3957093
  have htrace : WordTrace (prefixWord ++ tailWord_3957093) baseStart_3957093 baseEnd_3957093 := by
    simpa [prefixWord, tailWord_3957093, baseEnd_3957093] using wordTrace_append hprefix tailTrace_3957093
  have hstable : (prefixWord ++ tailWord_3957093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957093).length < 2 ^ (prefixWord ++ tailWord_3957093).sum := by decide
  have hdescent : baseEnd_3957093 < baseStart_3957093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957132 : List Nat := [2, 2, 1, 2, 1, 4, 2, 2, 1, 6]
def baseStart_3957132 : Nat := 118140960795 + 3957132 * 2 ^ 59
def prefixEnd_3957132 : Nat := 4983230072969 + 3 ^ 40 * 3957132 * 2
def baseEnd_3957132 : Nat := 677303576429172312183829

theorem tailTrace_3957132 : CollatzResearch.WordTrace tailWord_3957132 prefixEnd_3957132 677303576429172312183829 := by
  unfold tailWord_3957132
  simp only [CollatzResearch.WordTrace]
  refine ⟨72164230549997031592792825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96218974066662708790390433 72164230549997031592792825)
  ·
    refine ⟨54123172912497773694594619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72164230549997031592792825 54123172912497773694594619)
    ·
      refine ⟨81184759368746660541891929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54123172912497773694594619 81184759368746660541891929)
      ·
        refine ⟨60888569526559995406418947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81184759368746660541891929 60888569526559995406418947)
        ·
          refine ⟨91332854289839993109628421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60888569526559995406418947 91332854289839993109628421)
          ·
            refine ⟨17124910179344998708055329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91332854289839993109628421 17124910179344998708055329)
            ·
              refine ⟨12843682634508749031041497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17124910179344998708055329 12843682634508749031041497)
              ·
                refine ⟨9632761975881561773281123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12843682634508749031041497 9632761975881561773281123)
                ·
                  refine ⟨14449142963822342659921685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9632761975881561773281123 14449142963822342659921685)
                  ·
                    refine ⟨677303576429172312183829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14449142963822342659921685 677303576429172312183829)
                    ·
                      rfl

theorem cell23_3957132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 1, 6].length) (baseStart_3957132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3957132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3957132 prefixEnd_3957132 := by exact prefixLift 3957132
  have htrace : WordTrace (prefixWord ++ tailWord_3957132) baseStart_3957132 baseEnd_3957132 := by
    simpa [prefixWord, tailWord_3957132, baseEnd_3957132] using wordTrace_append hprefix tailTrace_3957132
  have hstable : (prefixWord ++ tailWord_3957132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957132).length < 2 ^ (prefixWord ++ tailWord_3957132).sum := by decide
  have hdescent : baseEnd_3957132 < baseStart_3957132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957145 : List Nat := [1, 2, 1, 2, 1, 4, 12]
def baseStart_3957145 : Nat := 118140960795 + 3957145 * 2 ^ 59
def prefixEnd_3957145 : Nat := 4983230072969 + 3 ^ 40 * 3957145 * 2
def baseEnd_3957145 : Nat := 25085400056000313403567

theorem tailTrace_3957145 : CollatzResearch.WordTrace tailWord_3957145 prefixEnd_3957145 25085400056000313403567 := by
  unfold tailWord_3957145
  simp only [CollatzResearch.WordTrace]
  refine ⟨144328935248946966405808889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96219290165964644270539259 144328935248946966405808889)
  ·
    refine ⟨108246701436710224804356667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144328935248946966405808889 108246701436710224804356667)
    ·
      refine ⟨162370052155065337206535001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108246701436710224804356667 162370052155065337206535001)
      ·
        refine ⟨121777539116299002904901251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162370052155065337206535001 121777539116299002904901251)
        ·
          refine ⟨182666308674448504357351877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121777539116299002904901251 182666308674448504357351877)
          ·
            refine ⟨34249932876459094567003477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182666308674448504357351877 34249932876459094567003477)
            ·
              refine ⟨25085400056000313403567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 34249932876459094567003477 25085400056000313403567)
              ·
                rfl

theorem cell23_3957145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 12].length) (baseStart_3957145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3957145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3957145 prefixEnd_3957145 := by exact prefixLift 3957145
  have htrace : WordTrace (prefixWord ++ tailWord_3957145) baseStart_3957145 baseEnd_3957145 := by
    simpa [prefixWord, tailWord_3957145, baseEnd_3957145] using wordTrace_append hprefix tailTrace_3957145
  have hstable : (prefixWord ++ tailWord_3957145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957145).length < 2 ^ (prefixWord ++ tailWord_3957145).sum := by decide
  have hdescent : baseEnd_3957145 < baseStart_3957145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957150 : List Nat := [4, 3, 1, 2, 1, 1, 2, 4, 1, 1, 3]
def baseStart_3957150 : Nat := 118140960795 + 3957150 * 2 ^ 59
def prefixEnd_3957150 : Nat := 4983230072969 + 3 ^ 40 * 3957150 * 2
def baseEnd_3957150 : Nat := 2031919971939297866126405

theorem tailTrace_3957150 : CollatzResearch.WordTrace tailWord_3957150 prefixEnd_3957150 2031919971939297866126405 := by
  unfold tailWord_3957150
  simp only [CollatzResearch.WordTrace]
  refine ⟨18041139701741106532467613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96219411742619234839827269 18041139701741106532467613)
  ·
    refine ⟨6765427388152914949675355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18041139701741106532467613 6765427388152914949675355)
    ·
      refine ⟨10148141082229372424513033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6765427388152914949675355 10148141082229372424513033)
      ·
        refine ⟨7611105811672029318384775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10148141082229372424513033 7611105811672029318384775)
        ·
          refine ⟨11416658717508043977577163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7611105811672029318384775 11416658717508043977577163)
          ·
            refine ⟨17124988076262065966365745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11416658717508043977577163 17124988076262065966365745)
            ·
              refine ⟨12843741057196549474774309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17124988076262065966365745 12843741057196549474774309)
              ·
                refine ⟨2408201448224353026520183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12843741057196549474774309 2408201448224353026520183)
                ·
                  refine ⟨3612302172336529539780275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2408201448224353026520183 3612302172336529539780275)
                  ·
                    refine ⟨5418453258504794309670413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3612302172336529539780275 5418453258504794309670413)
                    ·
                      refine ⟨2031919971939297866126405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5418453258504794309670413 2031919971939297866126405)
                      ·
                        rfl

theorem cell23_3957150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_3957150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3957150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3957150 prefixEnd_3957150 := by exact prefixLift 3957150
  have htrace : WordTrace (prefixWord ++ tailWord_3957150) baseStart_3957150 baseEnd_3957150 := by
    simpa [prefixWord, tailWord_3957150, baseEnd_3957150] using wordTrace_append hprefix tailTrace_3957150
  have hstable : (prefixWord ++ tailWord_3957150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957150).length < 2 ^ (prefixWord ++ tailWord_3957150).sum := by decide
  have hdescent : baseEnd_3957150 < baseStart_3957150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957156 : List Nat := [2, 3, 1, 2, 1, 1, 3, 3, 3, 2, 2]
def baseStart_3957156 : Nat := 118140960795 + 3957156 * 2 ^ 59
def prefixEnd_3957156 : Nat := 4983230072969 + 3 ^ 40 * 3957156 * 2
def baseEnd_3957156 : Nat := 2031923052823224842651377

theorem tailTrace_3957156 : CollatzResearch.WordTrace tailWord_3957156 prefixEnd_3957156 2031923052823224842651377 := by
  unfold tailWord_3957156
  simp only [CollatzResearch.WordTrace]
  refine ⟨72164668225953557642229661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96219557634604743522972881 72164668225953557642229661)
  ·
    refine ⟨27061750584732584115836123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72164668225953557642229661 27061750584732584115836123)
    ·
      refine ⟨40592625877098876173754185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27061750584732584115836123 40592625877098876173754185)
      ·
        refine ⟨30444469407824157130315639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40592625877098876173754185 30444469407824157130315639)
        ·
          refine ⟨45666704111736235695473459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30444469407824157130315639 45666704111736235695473459)
          ·
            refine ⟨68500056167604353543210189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45666704111736235695473459 68500056167604353543210189)
            ·
              refine ⟨25687521062851632578703821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68500056167604353543210189 25687521062851632578703821)
              ·
                refine ⟨9632820398569362217013933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25687521062851632578703821 9632820398569362217013933)
                ·
                  refine ⟨3612307649463510831380225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9632820398569362217013933 3612307649463510831380225)
                  ·
                    refine ⟨2709230737097633123535169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3612307649463510831380225 2709230737097633123535169)
                    ·
                      refine ⟨2031923052823224842651377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2709230737097633123535169 2031923052823224842651377)
                      ·
                        rfl

theorem cell23_3957156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_3957156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3957156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3957156 prefixEnd_3957156 := by exact prefixLift 3957156
  have htrace : WordTrace (prefixWord ++ tailWord_3957156) baseStart_3957156 baseEnd_3957156 := by
    simpa [prefixWord, tailWord_3957156, baseEnd_3957156] using wordTrace_append hprefix tailTrace_3957156
  have hstable : (prefixWord ++ tailWord_3957156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957156).length < 2 ^ (prefixWord ++ tailWord_3957156).sum := by decide
  have hdescent : baseEnd_3957156 < baseStart_3957156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957159 : List Nat := [1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 5]
def baseStart_3957159 : Nat := 118140960795 + 3957159 * 2 ^ 59
def prefixEnd_3957159 : Nat := 4983230072969 + 3 ^ 40 * 3957159 * 2
def baseEnd_3957159 : Nat := 2031924593265188330913863

theorem tailTrace_3957159 : CollatzResearch.WordTrace tailWord_3957159 prefixEnd_3957159 2031924593265188330913863 := by
  unfold tailWord_3957159
  simp only [CollatzResearch.WordTrace]
  refine ⟨144329445870896246796818531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96219630580597497864545687 144329445870896246796818531)
  ·
    refine ⟨216494168806344370195227797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144329445870896246796818531 216494168806344370195227797)
    ·
      refine ⟨10148164162797392352901303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 216494168806344370195227797 10148164162797392352901303)
      ·
        refine ⟨15222246244196088529351955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10148164162797392352901303 15222246244196088529351955)
        ·
          refine ⟨22833369366294132794027933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15222246244196088529351955 22833369366294132794027933)
          ·
            refine ⟨8562513512360299797760475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22833369366294132794027933 8562513512360299797760475)
            ·
              refine ⟨12843770268540449696640713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8562513512360299797760475 12843770268540449696640713)
              ·
                refine ⟨9632827701405337272480535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12843770268540449696640713 9632827701405337272480535)
                ·
                  refine ⟨14449241552108005908720803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9632827701405337272480535 14449241552108005908720803)
                  ·
                    refine ⟨21673862328162008863081205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14449241552108005908720803 21673862328162008863081205)
                    ·
                      refine ⟨2031924593265188330913863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21673862328162008863081205 2031924593265188330913863)
                      ·
                        rfl

theorem cell23_3957159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_3957159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3957159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3957159 prefixEnd_3957159 := by exact prefixLift 3957159
  have htrace : WordTrace (prefixWord ++ tailWord_3957159) baseStart_3957159 baseEnd_3957159 := by
    simpa [prefixWord, tailWord_3957159, baseEnd_3957159] using wordTrace_append hprefix tailTrace_3957159
  have hstable : (prefixWord ++ tailWord_3957159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957159).length < 2 ^ (prefixWord ++ tailWord_3957159).sum := by decide
  have hdescent : baseEnd_3957159 < baseStart_3957159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957169 : List Nat := [1, 2, 2, 4, 1, 2, 3, 1, 1, 2, 4]
def baseStart_3957169 : Nat := 118140960795 + 3957169 * 2 ^ 59
def prefixEnd_3957169 : Nat := 4983230072969 + 3 ^ 40 * 3957169 * 2
def baseEnd_3957169 : Nat := 2031929728071733291788817

theorem tailTrace_3957169 : CollatzResearch.WordTrace tailWord_3957169 prefixEnd_3957169 2031929728071733291788817 := by
  unfold tailWord_3957169
  simp only [CollatzResearch.WordTrace]
  refine ⟨144329810600860018504682561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96219873733906679003121707 144329810600860018504682561)
  ·
    refine ⟨108247357950645013878511921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144329810600860018504682561 108247357950645013878511921)
    ·
      refine ⟨81185518462983760408883941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108247357950645013878511921 81185518462983760408883941)
      ·
        refine ⟨15222284711809455076665739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81185518462983760408883941 15222284711809455076665739)
        ·
          refine ⟨22833427067714182614998609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15222284711809455076665739 22833427067714182614998609)
          ·
            refine ⟨17125070300785636961248957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22833427067714182614998609 17125070300785636961248957)
            ·
              refine ⟨6421901362794613860468359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17125070300785636961248957 6421901362794613860468359)
              ·
                refine ⟨9632852044191920790702539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6421901362794613860468359 9632852044191920790702539)
                ·
                  refine ⟨14449278066287881186053809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9632852044191920790702539 14449278066287881186053809)
                  ·
                    refine ⟨10836958549715910889540357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14449278066287881186053809 10836958549715910889540357)
                    ·
                      refine ⟨2031929728071733291788817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10836958549715910889540357 2031929728071733291788817)
                      ·
                        rfl

theorem cell23_3957169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_3957169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3957169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3957169 prefixEnd_3957169 := by exact prefixLift 3957169
  have htrace : WordTrace (prefixWord ++ tailWord_3957169) baseStart_3957169 baseEnd_3957169 := by
    simpa [prefixWord, tailWord_3957169, baseEnd_3957169] using wordTrace_append hprefix tailTrace_3957169
  have hstable : (prefixWord ++ tailWord_3957169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957169).length < 2 ^ (prefixWord ++ tailWord_3957169).sum := by decide
  have hdescent : baseEnd_3957169 < baseStart_3957169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957199 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 5, 3, 2]
def baseStart_3957199 : Nat := 118140960795 + 3957199 * 2 ^ 59
def prefixEnd_3957199 : Nat := 4983230072969 + 3 ^ 40 * 3957199 * 2
def baseEnd_3957199 : Nat := 2031945132491368174413679

theorem tailTrace_3957199 : CollatzResearch.WordTrace tailWord_3957199 prefixEnd_3957199 2031945132491368174413679 := by
  unfold tailWord_3957199
  simp only [CollatzResearch.WordTrace]
  refine ⟨144330904790751333628274651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96220603193834222418849767 144330904790751333628274651)
  ·
    refine ⟨216496357186127000442411977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144330904790751333628274651 216496357186127000442411977)
    ·
      refine ⟨162372267889595250331808983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216496357186127000442411977 162372267889595250331808983)
      ·
        refine ⟨243558401834392875497713475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162372267889595250331808983 243558401834392875497713475)
        ·
          refine ⟨365337602751589313246570213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243558401834392875497713475 365337602751589313246570213)
          ·
            refine ⟨68500800515922996233731915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 365337602751589313246570213 68500800515922996233731915)
            ·
              refine ⟨102751200773884494350597873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68500800515922996233731915 102751200773884494350597873)
              ·
                refine ⟨77063400580413370762948405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102751200773884494350597873 77063400580413370762948405)
                ·
                  refine ⟨7224693804413753509026413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77063400580413370762948405 7224693804413753509026413)
                  ·
                    refine ⟨2709260176655157565884905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7224693804413753509026413 2709260176655157565884905)
                    ·
                      refine ⟨2031945132491368174413679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2709260176655157565884905 2031945132491368174413679)
                      ·
                        rfl

theorem cell23_3957199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 3, 2].length) (baseStart_3957199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3957199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3957199 prefixEnd_3957199 := by exact prefixLift 3957199
  have htrace : WordTrace (prefixWord ++ tailWord_3957199) baseStart_3957199 baseEnd_3957199 := by
    simpa [prefixWord, tailWord_3957199, baseEnd_3957199] using wordTrace_append hprefix tailTrace_3957199
  have hstable : (prefixWord ++ tailWord_3957199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957199).length < 2 ^ (prefixWord ++ tailWord_3957199).sum := by decide
  have hdescent : baseEnd_3957199 < baseStart_3957199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957232 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 5]
def baseStart_3957232 : Nat := 118140960795 + 3957232 * 2 ^ 59
def prefixEnd_3957232 : Nat := 4983230072969 + 3 ^ 40 * 3957232 * 2
def baseEnd_3957232 : Nat := 2031962077352966545301027

theorem tailTrace_3957232 : CollatzResearch.WordTrace tailWord_3957232 prefixEnd_3957232 2031962077352966545301027 := by
  unfold tailWord_3957232
  simp only [CollatzResearch.WordTrace]
  refine ⟨72166054199815890132112975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96221405599754520176150633 72166054199815890132112975)
  ·
    refine ⟨108249081299723835198169463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72166054199815890132112975 108249081299723835198169463)
    ·
      refine ⟨162373621949585752797254195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108249081299723835198169463 162373621949585752797254195)
      ·
        refine ⟨243560432924378629195881293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162373621949585752797254195 243560432924378629195881293)
        ·
          refine ⟨91335162346641985948455485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243560432924378629195881293 91335162346641985948455485)
          ·
            refine ⟨34250685879990744730670807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91335162346641985948455485 34250685879990744730670807)
            ·
              refine ⟨51376028819986117096006211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34250685879990744730670807 51376028819986117096006211)
              ·
                refine ⟨77064043229979175644009317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51376028819986117096006211 77064043229979175644009317)
                ·
                  refine ⟨14449508105621095433251747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77064043229979175644009317 14449508105621095433251747)
                  ·
                    refine ⟨21674262158431643149877621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14449508105621095433251747 21674262158431643149877621)
                    ·
                      refine ⟨2031962077352966545301027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21674262158431643149877621 2031962077352966545301027)
                      ·
                        rfl

theorem cell23_3957232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 5].length) (baseStart_3957232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3957232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3957232 prefixEnd_3957232 := by exact prefixLift 3957232
  have htrace : WordTrace (prefixWord ++ tailWord_3957232) baseStart_3957232 baseEnd_3957232 := by
    simpa [prefixWord, tailWord_3957232, baseEnd_3957232] using wordTrace_append hprefix tailTrace_3957232
  have hstable : (prefixWord ++ tailWord_3957232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957232).length < 2 ^ (prefixWord ++ tailWord_3957232).sum := by decide
  have hdescent : baseEnd_3957232 < baseStart_3957232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957242 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 3, 4, 4]
def baseStart_3957242 : Nat := 118140960795 + 3957242 * 2 ^ 59
def prefixEnd_3957242 : Nat := 4983230072969 + 3 ^ 40 * 3957242 * 2
def baseEnd_3957242 : Nat := 2031967212159511506175981

theorem tailTrace_3957242 : CollatzResearch.WordTrace tailWord_3957242 prefixEnd_3957242 2031967212159511506175981 := by
  unfold tailWord_3957242
  simp only [CollatzResearch.WordTrace]
  refine ⟨36083118282398887993022495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96221648753063701314726653 36083118282398887993022495)
  ·
    refine ⟨54124677423598331989533743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36083118282398887993022495 54124677423598331989533743)
    ·
      refine ⟨81187016135397497984300615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54124677423598331989533743 81187016135397497984300615)
      ·
        refine ⟨121780524203096246976450923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81187016135397497984300615 121780524203096246976450923)
        ·
          refine ⟨182670786304644370464676385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121780524203096246976450923 182670786304644370464676385)
          ·
            refine ⟨137003089728483277848507289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182670786304644370464676385 137003089728483277848507289)
            ·
              refine ⟨102752317296362458386380467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137003089728483277848507289 102752317296362458386380467)
              ·
                refine ⟨154128475944543687579570701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102752317296362458386380467 154128475944543687579570701)
                ·
                  refine ⟨57798178479203882842339013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154128475944543687579570701 57798178479203882842339013)
                  ·
                    refine ⟨10837158464850728032938565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57798178479203882842339013 10837158464850728032938565)
                    ·
                      refine ⟨2031967212159511506175981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10837158464850728032938565 2031967212159511506175981)
                      ·
                        rfl

theorem cell23_3957242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 3, 4, 4].length) (baseStart_3957242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3957242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3957242 prefixEnd_3957242 := by exact prefixLift 3957242
  have htrace : WordTrace (prefixWord ++ tailWord_3957242) baseStart_3957242 baseEnd_3957242 := by
    simpa [prefixWord, tailWord_3957242, baseEnd_3957242] using wordTrace_append hprefix tailTrace_3957242
  have hstable : (prefixWord ++ tailWord_3957242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957242).length < 2 ^ (prefixWord ++ tailWord_3957242).sum := by decide
  have hdescent : baseEnd_3957242 < baseStart_3957242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957249 : List Nat := [1, 2, 4, 1, 3, 1, 2, 1, 2, 1, 5]
def baseStart_3957249 : Nat := 118140960795 + 3957249 * 2 ^ 59
def prefixEnd_3957249 : Nat := 4983230072969 + 3 ^ 40 * 3957249 * 2
def baseEnd_3957249 : Nat := 2031970806524092978788449

theorem tailTrace_3957249 : CollatzResearch.WordTrace tailWord_3957249 prefixEnd_3957249 2031970806524092978788449 := by
  unfold tailWord_3957249
  simp only [CollatzResearch.WordTrace]
  refine ⟨144332728440570192167594801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96221818960380128111729867 144332728440570192167594801)
  ·
    refine ⟨108249546330427644125696101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144332728440570192167594801 108249546330427644125696101)
    ·
      refine ⟨20296789936955183273568019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108249546330427644125696101 20296789936955183273568019)
      ·
        refine ⟨30445184905432774910352029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20296789936955183273568019 30445184905432774910352029)
        ·
          refine ⟨11416944339537290591382011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30445184905432774910352029 11416944339537290591382011)
          ·
            refine ⟨17125416509305935887073017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11416944339537290591382011 17125416509305935887073017)
            ·
              refine ⟨12844062381979451915304763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17125416509305935887073017 12844062381979451915304763)
              ·
                refine ⟨19266093572969177872957145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12844062381979451915304763 19266093572969177872957145)
                ·
                  refine ⟨14449570179726883404717859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19266093572969177872957145 14449570179726883404717859)
                  ·
                    refine ⟨21674355269590325107076789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14449570179726883404717859 21674355269590325107076789)
                    ·
                      refine ⟨2031970806524092978788449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21674355269590325107076789 2031970806524092978788449)
                      ·
                        rfl

theorem cell23_3957249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_3957249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3957249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3957249 prefixEnd_3957249 := by exact prefixLift 3957249
  have htrace : WordTrace (prefixWord ++ tailWord_3957249) baseStart_3957249 baseEnd_3957249 := by
    simpa [prefixWord, tailWord_3957249, baseEnd_3957249] using wordTrace_append hprefix tailTrace_3957249
  have hstable : (prefixWord ++ tailWord_3957249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957249).length < 2 ^ (prefixWord ++ tailWord_3957249).sum := by decide
  have hdescent : baseEnd_3957249 < baseStart_3957249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957292 : List Nat := [2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 7]
def baseStart_3957292 : Nat := 118140960795 + 3957292 * 2 ^ 59
def prefixEnd_3957292 : Nat := 4983230072969 + 3 ^ 40 * 3957292 * 2
def baseEnd_3957292 : Nat := 2031992886192236310550751

theorem tailTrace_3957292 : CollatzResearch.WordTrace tailWord_3957292 prefixEnd_3957292 2031992886192236310550751 := by
  unfold tailWord_3957292
  simp only [CollatzResearch.WordTrace]
  refine ⟨72167148389707205255705065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96222864519609607007606753 72167148389707205255705065)
  ·
    refine ⟨54125361292280403941778799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72167148389707205255705065 54125361292280403941778799)
    ·
      refine ⟨81188041938420605912668199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54125361292280403941778799 81188041938420605912668199)
      ·
        refine ⟨121782062907630908869002299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81188041938420605912668199 121782062907630908869002299)
        ·
          refine ⟨182673094361446363303503449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121782062907630908869002299 182673094361446363303503449)
          ·
            refine ⟨137004820771084772477627587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182673094361446363303503449 137004820771084772477627587)
            ·
              refine ⟨205507231156627158716441381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137004820771084772477627587 205507231156627158716441381)
              ·
                refine ⟨38532605841867592259332759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205507231156627158716441381 38532605841867592259332759)
                ·
                  refine ⟨57798908762801388388999139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38532605841867592259332759 57798908762801388388999139)
                  ·
                    refine ⟨86698363144202082583498709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57798908762801388388999139 86698363144202082583498709)
                    ·
                      refine ⟨2031992886192236310550751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 86698363144202082583498709 2031992886192236310550751)
                      ·
                        rfl

theorem cell23_3957292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_3957292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3957292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3957292 prefixEnd_3957292 := by exact prefixLift 3957292
  have htrace : WordTrace (prefixWord ++ tailWord_3957292) baseStart_3957292 baseEnd_3957292 := by
    simpa [prefixWord, tailWord_3957292, baseEnd_3957292] using wordTrace_append hprefix tailTrace_3957292
  have hstable : (prefixWord ++ tailWord_3957292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957292).length < 2 ^ (prefixWord ++ tailWord_3957292).sum := by decide
  have hdescent : baseEnd_3957292 < baseStart_3957292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957336 : List Nat := [2, 1, 2, 2, 1, 2, 4, 1, 2, 4, 2]
def baseStart_3957336 : Nat := 118140960795 + 3957336 * 2 ^ 59
def prefixEnd_3957336 : Nat := 4983230072969 + 3 ^ 40 * 3957336 * 2
def baseEnd_3957336 : Nat := 2032015479341034138400549

theorem tailTrace_3957336 : CollatzResearch.WordTrace tailWord_3957336 prefixEnd_3957336 2032015479341034138400549 := by
  unfold tailWord_3957336
  simp only [CollatzResearch.WordTrace]
  refine ⟨72167950795627503013005931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96223934394170004017341241 72167950795627503013005931)
  ·
    refine ⟨108251926193441254519508897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72167950795627503013005931 108251926193441254519508897)
    ·
      refine ⟨81188944645080940889631673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108251926193441254519508897 81188944645080940889631673)
      ·
        refine ⟨60891708483810705667223755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81188944645080940889631673 60891708483810705667223755)
        ·
          refine ⟨91337562725716058500835633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60891708483810705667223755 91337562725716058500835633)
          ·
            refine ⟨68503172044287043875626725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91337562725716058500835633 68503172044287043875626725)
            ·
              refine ⟨12844344758303820726680011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68503172044287043875626725 12844344758303820726680011)
              ·
                refine ⟨19266517137455731090020017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12844344758303820726680011 19266517137455731090020017)
                ·
                  refine ⟨14449887853091798317515013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19266517137455731090020017 14449887853091798317515013)
                  ·
                    refine ⟨2709353972454712184534065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14449887853091798317515013 2709353972454712184534065)
                    ·
                      refine ⟨2032015479341034138400549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2709353972454712184534065 2032015479341034138400549)
                      ·
                        rfl

theorem cell23_3957336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 2, 4, 2].length) (baseStart_3957336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3957336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3957336 prefixEnd_3957336 := by exact prefixLift 3957336
  have htrace : WordTrace (prefixWord ++ tailWord_3957336) baseStart_3957336 baseEnd_3957336 := by
    simpa [prefixWord, tailWord_3957336, baseEnd_3957336] using wordTrace_append hprefix tailTrace_3957336
  have hstable : (prefixWord ++ tailWord_3957336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957336).length < 2 ^ (prefixWord ++ tailWord_3957336).sum := by decide
  have hdescent : baseEnd_3957336 < baseStart_3957336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957373 : List Nat := [1, 4, 1, 1, 5, 1, 1, 2, 2, 2, 3]
def baseStart_3957373 : Nat := 118140960795 + 3957373 * 2 ^ 59
def prefixEnd_3957373 : Nat := 4983230072969 + 3 ^ 40 * 3957373 * 2
def baseEnd_3957373 : Nat := 2032034478125250493637879

theorem tailTrace_3957373 : CollatzResearch.WordTrace tailWord_3957373 prefixEnd_3957373 2032034478125250493637879 := by
  unfold tailWord_3957373
  simp only [CollatzResearch.WordTrace]
  refine ⟨144337251092120961345108773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96224834061413974230072515 144337251092120961345108773)
  ·
    refine ⟨27063234579772680252207895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144337251092120961345108773 27063234579772680252207895)
    ·
      refine ⟨40594851869659020378311843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27063234579772680252207895 40594851869659020378311843)
      ·
        refine ⟨60892277804488530567467765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40594851869659020378311843 60892277804488530567467765)
        ·
          refine ⟨5708651044170799740700103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60892277804488530567467765 5708651044170799740700103)
          ·
            refine ⟨8562976566256199611050155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5708651044170799740700103 8562976566256199611050155)
            ·
              refine ⟨12844464849384299416575233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8562976566256199611050155 12844464849384299416575233)
              ·
                refine ⟨9633348637038224562431425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12844464849384299416575233 9633348637038224562431425)
                ·
                  refine ⟨7225011477778668421823569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9633348637038224562431425 7225011477778668421823569)
                  ·
                    refine ⟨5418758608334001316367677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7225011477778668421823569 5418758608334001316367677)
                    ·
                      refine ⟨2032034478125250493637879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5418758608334001316367677 2032034478125250493637879)
                      ·
                        rfl

theorem cell23_3957373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 2, 3].length) (baseStart_3957373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3957373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3957373 prefixEnd_3957373 := by exact prefixLift 3957373
  have htrace : WordTrace (prefixWord ++ tailWord_3957373) baseStart_3957373 baseEnd_3957373 := by
    simpa [prefixWord, tailWord_3957373, baseEnd_3957373] using wordTrace_append hprefix tailTrace_3957373
  have hstable : (prefixWord ++ tailWord_3957373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957373).length < 2 ^ (prefixWord ++ tailWord_3957373).sum := by decide
  have hdescent : baseEnd_3957373 < baseStart_3957373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957423 : List Nat := [1, 1, 2, 1, 2, 6, 3, 1, 1, 5]
def baseStart_3957423 : Nat := 118140960795 + 3957423 * 2 ^ 59
def prefixEnd_3957423 : Nat := 4983230072969 + 3 ^ 40 * 3957423 * 2
def baseEnd_3957423 : Nat := 677353384052658432670883

theorem tailTrace_3957423 : CollatzResearch.WordTrace tailWord_3957423 prefixEnd_3957423 677353384052658432670883 := by
  unfold tailWord_3957423
  simp only [CollatzResearch.WordTrace]
  refine ⟨144339074741939819884428923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96226049827959879922952615 144339074741939819884428923)
  ·
    refine ⟨216508612112909729826643385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144339074741939819884428923 216508612112909729826643385)
    ·
      refine ⟨162381459084682297369982539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216508612112909729826643385 162381459084682297369982539)
      ·
        refine ⟨243572188627023446054973809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162381459084682297369982539 243572188627023446054973809)
        ·
          refine ⟨182679141470267584541230357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243572188627023446054973809 182679141470267584541230357)
          ·
            refine ⟨8563084756418793025370173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 182679141470267584541230357 8563084756418793025370173)
            ·
              refine ⟨3211156783657047384513815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8563084756418793025370173 3211156783657047384513815)
              ·
                refine ⟨4816735175485571076770723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3211156783657047384513815 4816735175485571076770723)
                ·
                  refine ⟨7225102763228356615156085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4816735175485571076770723 7225102763228356615156085)
                  ·
                    refine ⟨677353384052658432670883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7225102763228356615156085 677353384052658432670883)
                    ·
                      rfl

theorem cell23_3957423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 1, 5].length) (baseStart_3957423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3957423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3957423 prefixEnd_3957423 := by exact prefixLift 3957423
  have htrace : WordTrace (prefixWord ++ tailWord_3957423) baseStart_3957423 baseEnd_3957423 := by
    simpa [prefixWord, tailWord_3957423, baseEnd_3957423] using wordTrace_append hprefix tailTrace_3957423
  have hstable : (prefixWord ++ tailWord_3957423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957423).length < 2 ^ (prefixWord ++ tailWord_3957423).sum := by decide
  have hdescent : baseEnd_3957423 < baseStart_3957423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957437 : List Nat := [1, 4, 1, 2, 1, 3, 4, 2, 1, 1, 3]
def baseStart_3957437 : Nat := 118140960795 + 3957437 * 2 ^ 59
def prefixEnd_3957437 : Nat := 4983230072969 + 3 ^ 40 * 3957437 * 2
def baseEnd_3957437 : Nat := 2032067340887138243237585

theorem tailTrace_3957437 : CollatzResearch.WordTrace tailWord_3957437 prefixEnd_3957437 2032067340887138243237585 := by
  unfold tailWord_3957437
  simp only [CollatzResearch.WordTrace]
  refine ⟨144339585363889100275438565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96226390242592733516959043 144339585363889100275438565)
  ·
    refine ⟨27063672255729206301644731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144339585363889100275438565 27063672255729206301644731)
    ·
      refine ⟨40595508383593809452467097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27063672255729206301644731 40595508383593809452467097)
      ·
        refine ⟨30446631287695357089350323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40595508383593809452467097 30446631287695357089350323)
        ·
          refine ⟨45669946931543035634025485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30446631287695357089350323 45669946931543035634025485)
          ·
            refine ⟨17126230099328638362759557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45669946931543035634025485 17126230099328638362759557)
            ·
              refine ⟨3211168143624119693017417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17126230099328638362759557 3211168143624119693017417)
              ·
                refine ⟨2408376107718089769763063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3211168143624119693017417 2408376107718089769763063)
                ·
                  refine ⟨3612564161577134654644595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2408376107718089769763063 3612564161577134654644595)
                  ·
                    refine ⟨5418846242365701981966893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3612564161577134654644595 5418846242365701981966893)
                    ·
                      refine ⟨2032067340887138243237585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5418846242365701981966893 2032067340887138243237585)
                      ·
                        rfl

theorem cell23_3957437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 2, 1, 1, 3].length) (baseStart_3957437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3957437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3957437 prefixEnd_3957437 := by exact prefixLift 3957437
  have htrace : WordTrace (prefixWord ++ tailWord_3957437) baseStart_3957437 baseEnd_3957437 := by
    simpa [prefixWord, tailWord_3957437, baseEnd_3957437] using wordTrace_append hprefix tailTrace_3957437
  have hstable : (prefixWord ++ tailWord_3957437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957437).length < 2 ^ (prefixWord ++ tailWord_3957437).sum := by decide
  have hdescent : baseEnd_3957437 < baseStart_3957437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957466 : List Nat := [3, 1, 1, 2, 2, 2, 5, 7]
def baseStart_3957466 : Nat := 118140960795 + 3957466 * 2 ^ 59
def prefixEnd_3957466 : Nat := 4983230072969 + 3 ^ 40 * 3957466 * 2
def baseEnd_3957466 : Nat := 75262304882448838139813

theorem tailTrace_3957466 : CollatzResearch.WordTrace tailWord_3957466 prefixEnd_3957466 75262304882448838139813 := by
  unfold tailWord_3957466
  simp only [CollatzResearch.WordTrace]
  refine ⟨36085160770196009557061063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96227095387189358818829501 36085160770196009557061063)
  ·
    refine ⟨54127741155294014335591595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36085160770196009557061063 54127741155294014335591595)
    ·
      refine ⟨81191611732941021503387393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54127741155294014335591595 81191611732941021503387393)
      ·
        refine ⟨60893708799705766127540545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81191611732941021503387393 60893708799705766127540545)
        ·
          refine ⟨45670281599779324595655409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60893708799705766127540545 45670281599779324595655409)
          ·
            refine ⟨34252711199834493446741557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45670281599779324595655409 34252711199834493446741557)
            ·
              refine ⟨3211191674984483760632021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34252711199834493446741557 3211191674984483760632021)
              ·
                refine ⟨75262304882448838139813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3211191674984483760632021 75262304882448838139813)
                ·
                  rfl

theorem cell23_3957466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 7].length) (baseStart_3957466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3957466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3957466 prefixEnd_3957466 := by exact prefixLift 3957466
  have htrace : WordTrace (prefixWord ++ tailWord_3957466) baseStart_3957466 baseEnd_3957466 := by
    simpa [prefixWord, tailWord_3957466, baseEnd_3957466] using wordTrace_append hprefix tailTrace_3957466
  have hstable : (prefixWord ++ tailWord_3957466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957466).length < 2 ^ (prefixWord ++ tailWord_3957466).sum := by decide
  have hdescent : baseEnd_3957466 < baseStart_3957466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957477 : List Nat := [1, 3, 1, 4, 1, 2, 1, 5, 1, 2, 2]
def baseStart_3957477 : Nat := 118140960795 + 3957477 * 2 ^ 59
def prefixEnd_3957477 : Nat := 4983230072969 + 3 ^ 40 * 3957477 * 2
def baseEnd_3957477 : Nat := 2032087880113318086737401

theorem tailTrace_3957477 : CollatzResearch.WordTrace tailWord_3957477 prefixEnd_3957477 2032087880113318086737401 := by
  unfold tailWord_3957477
  simp only [CollatzResearch.WordTrace]
  refine ⟨144341044283744187106894685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96227362855829458071263123 144341044283744187106894685)
  ·
    refine ⟨54127891606404070165085507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144341044283744187106894685 54127891606404070165085507)
    ·
      refine ⟨81191837409606105247628261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54127891606404070165085507 81191837409606105247628261)
      ·
        refine ⟨15223469514301144733930299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81191837409606105247628261 15223469514301144733930299)
        ·
          refine ⟨22835204271451717100895449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15223469514301144733930299 22835204271451717100895449)
          ·
            refine ⟨17126403203588787825671587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22835204271451717100895449 17126403203588787825671587)
            ·
              refine ⟨25689604805383181738507381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17126403203588787825671587 25689604805383181738507381)
              ·
                refine ⟨2408400450504673287985067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25689604805383181738507381 2408400450504673287985067)
                ·
                  refine ⟨3612600675757009931977601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2408400450504673287985067 3612600675757009931977601)
                  ·
                    refine ⟨2709450506817757448983201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3612600675757009931977601 2709450506817757448983201)
                    ·
                      refine ⟨2032087880113318086737401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2709450506817757448983201 2032087880113318086737401)
                      ·
                        rfl

theorem cell23_3957477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_3957477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3957477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3957477 prefixEnd_3957477 := by exact prefixLift 3957477
  have htrace : WordTrace (prefixWord ++ tailWord_3957477) baseStart_3957477 baseEnd_3957477 := by
    simpa [prefixWord, tailWord_3957477, baseEnd_3957477] using wordTrace_append hprefix tailTrace_3957477
  have hstable : (prefixWord ++ tailWord_3957477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957477).length < 2 ^ (prefixWord ++ tailWord_3957477).sum := by decide
  have hdescent : baseEnd_3957477 < baseStart_3957477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957480 : List Nat := [2, 1, 4, 1, 4, 1, 1, 3, 1, 2, 3]
def baseStart_3957480 : Nat := 118140960795 + 3957480 * 2 ^ 59
def prefixEnd_3957480 : Nat := 4983230072969 + 3 ^ 40 * 3957480 * 2
def baseEnd_3957480 : Nat := 2032089420555281574999887

theorem tailTrace_3957480 : CollatzResearch.WordTrace tailWord_3957480 prefixEnd_3957480 2032089420555281574999887 := by
  unfold tailWord_3957480
  simp only [CollatzResearch.WordTrace]
  refine ⟨72170576851366659309626947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96227435801822212412835929 72170576851366659309626947)
  ·
    refine ⟨108255865277049988964440421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72170576851366659309626947 108255865277049988964440421)
    ·
      refine ⟨20297974739446872930832579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108255865277049988964440421 20297974739446872930832579)
      ·
        refine ⟨30446962109170309396248869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20297974739446872930832579 30446962109170309396248869)
        ·
          refine ⟨5708805395469433011796663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30446962109170309396248869 5708805395469433011796663)
          ·
            refine ⟨8563208093204149517694995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5708805395469433011796663 8563208093204149517694995)
            ·
              refine ⟨12844812139806224276542493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8563208093204149517694995 12844812139806224276542493)
              ·
                refine ⟨4816804552427334103703435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12844812139806224276542493 4816804552427334103703435)
                ·
                  refine ⟨7225206828641001155555153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4816804552427334103703435 7225206828641001155555153)
                  ·
                    refine ⟨5418905121480750866666365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7225206828641001155555153 5418905121480750866666365)
                    ·
                      refine ⟨2032089420555281574999887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5418905121480750866666365 2032089420555281574999887)
                      ·
                        rfl

theorem cell23_3957480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_3957480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3957480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3957480 prefixEnd_3957480 := by exact prefixLift 3957480
  have htrace : WordTrace (prefixWord ++ tailWord_3957480) baseStart_3957480 baseEnd_3957480 := by
    simpa [prefixWord, tailWord_3957480, baseEnd_3957480] using wordTrace_append hprefix tailTrace_3957480
  have hstable : (prefixWord ++ tailWord_3957480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957480).length < 2 ^ (prefixWord ++ tailWord_3957480).sum := by decide
  have hdescent : baseEnd_3957480 < baseStart_3957480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957536 : List Nat := [2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 5]
def baseStart_3957536 : Nat := 118140960795 + 3957536 * 2 ^ 59
def prefixEnd_3957536 : Nat := 4983230072969 + 3 ^ 40 * 3957536 * 2
def baseEnd_3957536 : Nat := 2032118175471933355899629

theorem tailTrace_3957536 : CollatzResearch.WordTrace tailWord_3957536 prefixEnd_3957536 2032118175471933355899629 := by
  unfold tailWord_3957536
  simp only [CollatzResearch.WordTrace]
  refine ⟨72171598095265220091646231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96228797460353626788861641 72171598095265220091646231)
  ·
    refine ⟨108257397142897830137469347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72171598095265220091646231 108257397142897830137469347)
    ·
      refine ⟨162386095714346745206204021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108257397142897830137469347 162386095714346745206204021)
      ·
        refine ⟨15223696473220007363081627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162386095714346745206204021 15223696473220007363081627)
        ·
          refine ⟨22835544709830011044622441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15223696473220007363081627 22835544709830011044622441)
          ·
            refine ⟨17126658532372508283466831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22835544709830011044622441 17126658532372508283466831)
            ·
              refine ⟨25689987798558762425200247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17126658532372508283466831 25689987798558762425200247)
              ·
                refine ⟨38534981697838143637800371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25689987798558762425200247 38534981697838143637800371)
                ·
                  refine ⟨57802472546757215456700557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38534981697838143637800371 57802472546757215456700557)
                  ·
                    refine ⟨21675927205033955796262709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57802472546757215456700557 21675927205033955796262709)
                    ·
                      refine ⟨2032118175471933355899629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21675927205033955796262709 2032118175471933355899629)
                      ·
                        rfl

theorem cell23_3957536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_3957536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3957536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3957536 prefixEnd_3957536 := by exact prefixLift 3957536
  have htrace : WordTrace (prefixWord ++ tailWord_3957536) baseStart_3957536 baseEnd_3957536 := by
    simpa [prefixWord, tailWord_3957536, baseEnd_3957536] using wordTrace_append hprefix tailTrace_3957536
  have hstable : (prefixWord ++ tailWord_3957536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957536).length < 2 ^ (prefixWord ++ tailWord_3957536).sum := by decide
  have hdescent : baseEnd_3957536 < baseStart_3957536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957567 : List Nat := [1, 1, 2, 2, 5, 2, 1, 3, 2, 2, 2]
def baseStart_3957567 : Nat := 118140960795 + 3957567 * 2 ^ 59
def prefixEnd_3957567 : Nat := 4983230072969 + 3 ^ 40 * 3957567 * 2
def baseEnd_3957567 : Nat := 2032134093372222734611987

theorem tailTrace_3957567 : CollatzResearch.WordTrace tailWord_3957567 prefixEnd_3957567 2032134093372222734611987 := by
  unfold tailWord_3957567
  simp only [CollatzResearch.WordTrace]
  refine ⟨144344326853418132477670955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96229551235612088318447303 144344326853418132477670955)
  ·
    refine ⟨216516490280127198716506433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144344326853418132477670955 216516490280127198716506433)
    ·
      refine ⟨162387367710095399037379825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216516490280127198716506433 162387367710095399037379825)
      ·
        refine ⟨121790525782571549278034869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162387367710095399037379825 121790525782571549278034869)
        ·
          refine ⟨11417861792116082744815769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121790525782571549278034869 11417861792116082744815769)
          ·
            refine ⟨8563396344087062058611827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11417861792116082744815769 8563396344087062058611827)
            ·
              refine ⟨12845094516130593087917741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8563396344087062058611827 12845094516130593087917741)
              ·
                refine ⟨4816910443548972407969153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12845094516130593087917741 4816910443548972407969153)
                ·
                  refine ⟨3612682832661729305976865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4816910443548972407969153 3612682832661729305976865)
                  ·
                    refine ⟨2709512124496296979482649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3612682832661729305976865 2709512124496296979482649)
                    ·
                      refine ⟨2032134093372222734611987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2709512124496296979482649 2032134093372222734611987)
                      ·
                        rfl

theorem cell23_3957567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 2, 2, 2].length) (baseStart_3957567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3957567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3957567 prefixEnd_3957567 := by exact prefixLift 3957567
  have htrace : WordTrace (prefixWord ++ tailWord_3957567) baseStart_3957567 baseEnd_3957567 := by
    simpa [prefixWord, tailWord_3957567, baseEnd_3957567] using wordTrace_append hprefix tailTrace_3957567
  have hstable : (prefixWord ++ tailWord_3957567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957567).length < 2 ^ (prefixWord ++ tailWord_3957567).sum := by decide
  have hdescent : baseEnd_3957567 < baseStart_3957567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957603 : List Nat := [1, 1, 1, 5, 3, 1, 2, 2, 2, 5]
def baseStart_3957603 : Nat := 118140960795 + 3957603 * 2 ^ 59
def prefixEnd_3957603 : Nat := 4983230072969 + 3 ^ 40 * 3957603 * 2
def baseEnd_3957603 : Nat := 677384192891928197920607

theorem tailTrace_3957603 : CollatzResearch.WordTrace tailWord_3957603 prefixEnd_3957603 677384192891928197920607 := by
  unfold tailWord_3957603
  simp only [CollatzResearch.WordTrace]
  refine ⟨144345639881287710625981463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96230426587525140417320975 144345639881287710625981463)
  ·
    refine ⟨216518459821931565938972195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144345639881287710625981463 216518459821931565938972195)
    ·
      refine ⟨324777689732897348908458293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216518459821931565938972195 324777689732897348908458293)
      ·
        refine ⟨30447908412459126460167965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 324777689732897348908458293 30447908412459126460167965)
        ·
          refine ⟨11417965654672172422562987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30447908412459126460167965 11417965654672172422562987)
          ·
            refine ⟨17126948482008258633844481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11417965654672172422562987 17126948482008258633844481)
            ·
              refine ⟨12845211361506193975383361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17126948482008258633844481 12845211361506193975383361)
              ·
                refine ⟨9633908521129645481537521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12845211361506193975383361 9633908521129645481537521)
                ·
                  refine ⟨7225431390847234111153141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9633908521129645481537521 7225431390847234111153141)
                  ·
                    refine ⟨677384192891928197920607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7225431390847234111153141 677384192891928197920607)
                    ·
                      rfl

theorem cell23_3957603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 5].length) (baseStart_3957603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3957603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3957603 prefixEnd_3957603 := by exact prefixLift 3957603
  have htrace : WordTrace (prefixWord ++ tailWord_3957603) baseStart_3957603 baseEnd_3957603 := by
    simpa [prefixWord, tailWord_3957603, baseEnd_3957603] using wordTrace_append hprefix tailTrace_3957603
  have hstable : (prefixWord ++ tailWord_3957603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957603).length < 2 ^ (prefixWord ++ tailWord_3957603).sum := by decide
  have hdescent : baseEnd_3957603 < baseStart_3957603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957607 : List Nat := [1, 1, 5, 1, 2, 4, 2, 2, 5]
def baseStart_3957607 : Nat := 118140960795 + 3957607 * 2 ^ 59
def prefixEnd_3957607 : Nat := 4983230072969 + 3 ^ 40 * 3957607 * 2
def baseEnd_3957607 : Nat := 225794959177600286456867

theorem tailTrace_3957607 : CollatzResearch.WordTrace tailWord_3957607 prefixEnd_3957607 225794959177600286456867 := by
  unfold tailWord_3957607
  simp only [CollatzResearch.WordTrace]
  refine ⟨144345785773273219309127075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96230523848848812872751383 144345785773273219309127075)
  ·
    refine ⟨216518678659909828963690613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144345785773273219309127075 216518678659909828963690613)
    ·
      refine ⟨20298626124366546465345995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 216518678659909828963690613 20298626124366546465345995)
      ·
        refine ⟨30447939186549819698018993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20298626124366546465345995 30447939186549819698018993)
        ·
          refine ⟨22835954389912364773514245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30447939186549819698018993 22835954389912364773514245)
          ·
            refine ⟨4281741448108568395033921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22835954389912364773514245 4281741448108568395033921)
            ·
              refine ⟨3211306086081426296275441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4281741448108568395033921 3211306086081426296275441)
              ·
                refine ⟨2408479564561069722206581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3211306086081426296275441 2408479564561069722206581)
                ·
                  refine ⟨225794959177600286456867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2408479564561069722206581 225794959177600286456867)
                  ·
                    rfl

theorem cell23_3957607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 2, 5].length) (baseStart_3957607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3957607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3957607 prefixEnd_3957607 := by exact prefixLift 3957607
  have htrace : WordTrace (prefixWord ++ tailWord_3957607) baseStart_3957607 baseEnd_3957607 := by
    simpa [prefixWord, tailWord_3957607, baseEnd_3957607] using wordTrace_append hprefix tailTrace_3957607
  have hstable : (prefixWord ++ tailWord_3957607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957607).length < 2 ^ (prefixWord ++ tailWord_3957607).sum := by decide
  have hdescent : baseEnd_3957607 < baseStart_3957607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957640 : List Nat := [2, 1, 3, 3, 2, 1, 3, 1, 2, 1, 4]
def baseStart_3957640 : Nat := 118140960795 + 3957640 * 2 ^ 59
def prefixEnd_3957640 : Nat := 4983230072969 + 3 ^ 40 * 3957640 * 2
def baseEnd_3957640 : Nat := 2032171577460000948999151

theorem tailTrace_3957640 : CollatzResearch.WordTrace tailWord_3957640 prefixEnd_3957640 2032171577460000948999151 := by
  unfold tailWord_3957640
  simp only [CollatzResearch.WordTrace]
  refine ⟨72173494691076832972539187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96231326254769110630052249 72173494691076832972539187)
  ·
    refine ⟨108260242036615249458808781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72173494691076832972539187 108260242036615249458808781)
    ·
      refine ⟨40597590763730718547053293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108260242036615249458808781 40597590763730718547053293)
      ·
        refine ⟨15224096536399019455144985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40597590763730718547053293 15224096536399019455144985)
        ·
          refine ⟨11418072402299264591358739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15224096536399019455144985 11418072402299264591358739)
          ·
            refine ⟨17127108603448896887038109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11418072402299264591358739 17127108603448896887038109)
            ·
              refine ⟨6422665726293336332639291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17127108603448896887038109 6422665726293336332639291)
              ·
                refine ⟨9633998589440004498958937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6422665726293336332639291 9633998589440004498958937)
                ·
                  refine ⟨7225498942080003374219203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9633998589440004498958937 7225498942080003374219203)
                  ·
                    refine ⟨10838248413120005061328805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7225498942080003374219203 10838248413120005061328805)
                    ·
                      refine ⟨2032171577460000948999151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10838248413120005061328805 2032171577460000948999151)
                      ·
                        rfl

theorem cell23_3957640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_3957640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3957640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3957640 prefixEnd_3957640 := by exact prefixLift 3957640
  have htrace : WordTrace (prefixWord ++ tailWord_3957640) baseStart_3957640 baseEnd_3957640 := by
    simpa [prefixWord, tailWord_3957640, baseEnd_3957640] using wordTrace_append hprefix tailTrace_3957640
  have hstable : (prefixWord ++ tailWord_3957640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957640).length < 2 ^ (prefixWord ++ tailWord_3957640).sum := by decide
  have hdescent : baseEnd_3957640 < baseStart_3957640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957663 : List Nat := [1, 1, 2, 5, 2, 2, 1, 1, 8]
def baseStart_3957663 : Nat := 118140960795 + 3957663 * 2 ^ 59
def prefixEnd_3957663 : Nat := 4983230072969 + 3 ^ 40 * 3957663 * 2
def baseEnd_3957663 : Nat := 225798154168339373223505

theorem tailTrace_3957663 : CollatzResearch.WordTrace tailWord_3957663 prefixEnd_3957663 225798154168339373223505 := by
  unfold tailWord_3957663
  simp only [CollatzResearch.WordTrace]
  refine ⟨144347828261070340873165643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96231885507380227248777095 144347828261070340873165643)
  ·
    refine ⟨216521742391605511309748465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144347828261070340873165643 216521742391605511309748465)
    ·
      refine ⟨162391306793704133482311349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216521742391605511309748465 162391306793704133482311349)
      ·
        refine ⟨15224185011909762513966689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162391306793704133482311349 15224185011909762513966689)
        ·
          refine ⟨11418138758932321885475017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15224185011909762513966689 11418138758932321885475017)
          ·
            refine ⟨8563604069199241414106263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11418138758932321885475017 8563604069199241414106263)
            ·
              refine ⟨12845406103798862121159395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8563604069199241414106263 12845406103798862121159395)
              ·
                refine ⟨19268109155698293181739093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12845406103798862121159395 19268109155698293181739093)
                ·
                  refine ⟨225798154168339373223505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19268109155698293181739093 225798154168339373223505)
                  ·
                    rfl

theorem cell23_3957663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 8].length) (baseStart_3957663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3957663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3957663 prefixEnd_3957663 := by exact prefixLift 3957663
  have htrace : WordTrace (prefixWord ++ tailWord_3957663) baseStart_3957663 baseEnd_3957663 := by
    simpa [prefixWord, tailWord_3957663, baseEnd_3957663] using wordTrace_append hprefix tailTrace_3957663
  have hstable : (prefixWord ++ tailWord_3957663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957663).length < 2 ^ (prefixWord ++ tailWord_3957663).sum := by decide
  have hdescent : baseEnd_3957663 < baseStart_3957663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957690 : List Nat := [3, 1, 1, 1, 2, 1, 3, 4, 3, 1, 3]
def baseStart_3957690 : Nat := 118140960795 + 3957690 * 2 ^ 59
def prefixEnd_3957690 : Nat := 4983230072969 + 3 ^ 40 * 3957690 * 2
def baseEnd_3957690 : Nat := 2032197251492725753373921

theorem tailTrace_3957690 : CollatzResearch.WordTrace tailWord_3957690 prefixEnd_3957690 2032197251492725753373921 := by
  unfold tailWord_3957690
  simp only [CollatzResearch.WordTrace]
  refine ⟨36087203257993131121099631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96232542021315016322932349 36087203257993131121099631)
  ·
    refine ⟨54130804886989696681649447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36087203257993131121099631 54130804886989696681649447)
    ·
      refine ⟨81196207330484545022474171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54130804886989696681649447 81196207330484545022474171)
      ·
        refine ⟨121794310995726817533711257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81196207330484545022474171 121794310995726817533711257)
        ·
          refine ⟨91345733246795113150283443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121794310995726817533711257 91345733246795113150283443)
          ·
            refine ⟨137018599870192669725425165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91345733246795113150283443 137018599870192669725425165)
            ·
              refine ⟨51381974951322251147034437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137018599870192669725425165 51381974951322251147034437)
              ·
                refine ⟨9634120303372922090068957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51381974951322251147034437 9634120303372922090068957)
                ·
                  refine ⟨3612795113764845783775859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9634120303372922090068957 3612795113764845783775859)
                  ·
                    refine ⟨5419192670647268675663789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3612795113764845783775859 5419192670647268675663789)
                    ·
                      refine ⟨2032197251492725753373921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5419192670647268675663789 2032197251492725753373921)
                      ·
                        rfl

theorem cell23_3957690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 3, 1, 3].length) (baseStart_3957690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3957690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3957690 prefixEnd_3957690 := by exact prefixLift 3957690
  have htrace : WordTrace (prefixWord ++ tailWord_3957690) baseStart_3957690 baseEnd_3957690 := by
    simpa [prefixWord, tailWord_3957690, baseEnd_3957690] using wordTrace_append hprefix tailTrace_3957690
  have hstable : (prefixWord ++ tailWord_3957690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957690).length < 2 ^ (prefixWord ++ tailWord_3957690).sum := by decide
  have hdescent : baseEnd_3957690 < baseStart_3957690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957710 : List Nat := [4, 1, 1, 1, 2, 3, 2, 3, 1, 5]
def baseStart_3957710 : Nat := 118140960795 + 3957710 * 2 ^ 59
def prefixEnd_3957710 : Nat := 4983230072969 + 3 ^ 40 * 3957710 * 2
def baseEnd_3957710 : Nat := 677402507035271891707943

theorem tailTrace_3957710 : CollatzResearch.WordTrace tailWord_3957710 prefixEnd_3957710 677402507035271891707943 := by
  unfold tailWord_3957710
  simp only [CollatzResearch.WordTrace]
  refine ⟨18043692811487508487515823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96233028327933378600084389 18043692811487508487515823)
  ·
    refine ⟨27065539217231262731273735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18043692811487508487515823 27065539217231262731273735)
    ·
      refine ⟨40598308825846894096910603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27065539217231262731273735 40598308825846894096910603)
      ·
        refine ⟨60897463238770341145365905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40598308825846894096910603 60897463238770341145365905)
        ·
          refine ⟨45673097429077755859024429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60897463238770341145365905 45673097429077755859024429)
          ·
            refine ⟨17127411535904158447134161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45673097429077755859024429 17127411535904158447134161)
            ·
              refine ⟨12845558651928118835350621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17127411535904158447134161 12845558651928118835350621)
              ·
                refine ⟨4817084494473044563256483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12845558651928118835350621 4817084494473044563256483)
                ·
                  refine ⟨7225626741709566844884725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4817084494473044563256483 7225626741709566844884725)
                  ·
                    refine ⟨677402507035271891707943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7225626741709566844884725 677402507035271891707943)
                    ·
                      rfl

theorem cell23_3957710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 1, 5].length) (baseStart_3957710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3957710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3957710 prefixEnd_3957710 := by exact prefixLift 3957710
  have htrace : WordTrace (prefixWord ++ tailWord_3957710) baseStart_3957710 baseEnd_3957710 := by
    simpa [prefixWord, tailWord_3957710, baseEnd_3957710] using wordTrace_append hprefix tailTrace_3957710
  have hstable : (prefixWord ++ tailWord_3957710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957710).length < 2 ^ (prefixWord ++ tailWord_3957710).sum := by decide
  have hdescent : baseEnd_3957710 < baseStart_3957710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957743 : List Nat := [1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 6]
def baseStart_3957743 : Nat := 118140960795 + 3957743 * 2 ^ 59
def prefixEnd_3957743 : Nat := 4983230072969 + 3 ^ 40 * 3957743 * 2
def baseEnd_3957743 : Nat := 2032224465967414046011177

theorem tailTrace_3957743 : CollatzResearch.WordTrace tailWord_3957743 prefixEnd_3957743 2032224465967414046011177 := by
  unfold tailWord_3957743
  simp only [CollatzResearch.WordTrace]
  refine ⟨144350746100780514536077883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96233830733853676357385255 144350746100780514536077883)
  ·
    refine ⟨216526119151170771804116825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144350746100780514536077883 216526119151170771804116825)
    ·
      refine ⟨162394589363378078853087619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216526119151170771804116825 162394589363378078853087619)
      ·
        refine ⟨243591884045067118279631429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162394589363378078853087619 243591884045067118279631429)
        ·
          refine ⟨45673478258450084677430893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243591884045067118279631429 45673478258450084677430893)
          ·
            refine ⟨17127554346918781754036585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45673478258450084677430893 17127554346918781754036585)
            ·
              refine ⟨12845665760189086315527439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17127554346918781754036585 12845665760189086315527439)
              ·
                refine ⟨19268498640283629473291159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12845665760189086315527439 19268498640283629473291159)
                ·
                  refine ⟨28902747960425444209936739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19268498640283629473291159 28902747960425444209936739)
                  ·
                    refine ⟨43354121940638166314905109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28902747960425444209936739 43354121940638166314905109)
                    ·
                      refine ⟨2032224465967414046011177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43354121940638166314905109 2032224465967414046011177)
                      ·
                        rfl

theorem cell23_3957743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 6].length) (baseStart_3957743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3957743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3957743 prefixEnd_3957743 := by exact prefixLift 3957743
  have htrace : WordTrace (prefixWord ++ tailWord_3957743) baseStart_3957743 baseEnd_3957743 := by
    simpa [prefixWord, tailWord_3957743, baseEnd_3957743] using wordTrace_append hprefix tailTrace_3957743
  have hstable : (prefixWord ++ tailWord_3957743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957743).length < 2 ^ (prefixWord ++ tailWord_3957743).sum := by decide
  have hdescent : baseEnd_3957743 < baseStart_3957743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957781 : List Nat := [1, 3, 2, 1, 4, 2, 1, 4, 1, 2, 2]
def baseStart_3957781 : Nat := 118140960795 + 3957781 * 2 ^ 59
def prefixEnd_3957781 : Nat := 4983230072969 + 3 ^ 40 * 3957781 * 2
def baseEnd_3957781 : Nat := 2032243978232284897336003

theorem tailTrace_3957781 : CollatzResearch.WordTrace tailWord_3957781 prefixEnd_3957781 2032243978232284897336003 := by
  unfold tailWord_3957781
  simp only [CollatzResearch.WordTrace]
  refine ⟨144352132074642847025961197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96234754716428564683974131 144352132074642847025961197)
  ·
    refine ⟨54132049527991067634735449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144352132074642847025961197 54132049527991067634735449)
    ·
      refine ⟨40599037145993300726051587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54132049527991067634735449 40599037145993300726051587)
      ·
        refine ⟨60898555718989951089077381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40599037145993300726051587 60898555718989951089077381)
        ·
          refine ⟨11418479197310615829202009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60898555718989951089077381 11418479197310615829202009)
          ·
            refine ⟨8563859397982961871901507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11418479197310615829202009 8563859397982961871901507)
            ·
              refine ⟨12845789096974442807852261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8563859397982961871901507 12845789096974442807852261)
              ·
                refine ⟨2408585455682708026472299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12845789096974442807852261 2408585455682708026472299)
                ·
                  refine ⟨3612878183524062039708449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2408585455682708026472299 3612878183524062039708449)
                  ·
                    refine ⟨2709658637643046529781337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3612878183524062039708449 2709658637643046529781337)
                    ·
                      refine ⟨2032243978232284897336003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2709658637643046529781337 2032243978232284897336003)
                      ·
                        rfl

theorem cell23_3957781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 4, 1, 2, 2].length) (baseStart_3957781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3957781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3957781 prefixEnd_3957781 := by exact prefixLift 3957781
  have htrace : WordTrace (prefixWord ++ tailWord_3957781) baseStart_3957781 baseEnd_3957781 := by
    simpa [prefixWord, tailWord_3957781, baseEnd_3957781] using wordTrace_append hprefix tailTrace_3957781
  have hstable : (prefixWord ++ tailWord_3957781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957781).length < 2 ^ (prefixWord ++ tailWord_3957781).sum := by decide
  have hdescent : baseEnd_3957781 < baseStart_3957781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957797 : List Nat := [1, 3, 1, 2, 2, 2, 1, 5, 2, 1, 3]
def baseStart_3957797 : Nat := 118140960795 + 3957797 * 2 ^ 59
def prefixEnd_3957797 : Nat := 4983230072969 + 3 ^ 40 * 3957797 * 2
def baseEnd_3957797 : Nat := 2032252193922756834735929

theorem tailTrace_3957797 : CollatzResearch.WordTrace tailWord_3957797 prefixEnd_3957797 2032252193922756834735929 := by
  unfold tailWord_3957797
  simp only [CollatzResearch.WordTrace]
  refine ⟨144352715642584881758543645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96235143761723254505695763 144352715642584881758543645)
  ·
    refine ⟨54132268365969330659453867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144352715642584881758543645 54132268365969330659453867)
    ·
      refine ⟨81198402548953995989180801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54132268365969330659453867 81198402548953995989180801)
      ·
        refine ⟨60898801911715496991885601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81198402548953995989180801 60898801911715496991885601)
        ·
          refine ⟨45674101433786622743914201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60898801911715496991885601 45674101433786622743914201)
          ·
            refine ⟨34255576075339967057935651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45674101433786622743914201 34255576075339967057935651)
            ·
              refine ⟨51383364113009950586903477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34255576075339967057935651 51383364113009950586903477)
              ·
                refine ⟨4817190385594682867522201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51383364113009950586903477 4817190385594682867522201)
                ·
                  refine ⟨3612892789196012150641651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4817190385594682867522201 3612892789196012150641651)
                  ·
                    refine ⟨5419339183794018225962477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3612892789196012150641651 5419339183794018225962477)
                    ·
                      refine ⟨2032252193922756834735929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5419339183794018225962477 2032252193922756834735929)
                      ·
                        rfl

theorem cell23_3957797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 2, 1, 3].length) (baseStart_3957797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3957797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3957797 prefixEnd_3957797 := by exact prefixLift 3957797
  have htrace : WordTrace (prefixWord ++ tailWord_3957797) baseStart_3957797 baseEnd_3957797 := by
    simpa [prefixWord, tailWord_3957797, baseEnd_3957797] using wordTrace_append hprefix tailTrace_3957797
  have hstable : (prefixWord ++ tailWord_3957797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957797).length < 2 ^ (prefixWord ++ tailWord_3957797).sum := by decide
  have hdescent : baseEnd_3957797 < baseStart_3957797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957803 : List Nat := [1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 4]
def baseStart_3957803 : Nat := 118140960795 + 3957803 * 2 ^ 59
def prefixEnd_3957803 : Nat := 4983230072969 + 3 ^ 40 * 3957803 * 2
def baseEnd_3957803 : Nat := 2032255274806683811260901

theorem tailTrace_3957803 : CollatzResearch.WordTrace tailWord_3957803 prefixEnd_3957803 2032255274806683811260901 := by
  unfold tailWord_3957803
  simp only [CollatzResearch.WordTrace]
  refine ⟨144352934480563144783262063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96235289653708763188841375 144352934480563144783262063)
  ·
    refine ⟨216529401720844717174893095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144352934480563144783262063 216529401720844717174893095)
    ·
      refine ⟨324794102581267075762339643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216529401720844717174893095 324794102581267075762339643)
      ·
        refine ⟨487191153871900613643509465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324794102581267075762339643 487191153871900613643509465)
        ·
          refine ⟨365393365403925460232632099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487191153871900613643509465 365393365403925460232632099)
          ·
            refine ⟨548090048105888190348948149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365393365403925460232632099 548090048105888190348948149)
            ·
              refine ⟨51383442009927017845213889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 548090048105888190348948149 51383442009927017845213889)
              ·
                refine ⟨38537581507445263383910417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51383442009927017845213889 38537581507445263383910417)
                ·
                  refine ⟨28903186130583947537932813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38537581507445263383910417 28903186130583947537932813)
                  ·
                    refine ⟨10838694798968980326724805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28903186130583947537932813 10838694798968980326724805)
                    ·
                      refine ⟨2032255274806683811260901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10838694798968980326724805 2032255274806683811260901)
                      ·
                        rfl

theorem cell23_3957803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 4].length) (baseStart_3957803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3957803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3957803 prefixEnd_3957803 := by exact prefixLift 3957803
  have htrace : WordTrace (prefixWord ++ tailWord_3957803) baseStart_3957803 baseEnd_3957803 := by
    simpa [prefixWord, tailWord_3957803, baseEnd_3957803] using wordTrace_append hprefix tailTrace_3957803
  have hstable : (prefixWord ++ tailWord_3957803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957803).length < 2 ^ (prefixWord ++ tailWord_3957803).sum := by decide
  have hdescent : baseEnd_3957803 < baseStart_3957803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957813 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 3, 8]
def baseStart_3957813 : Nat := 118140960795 + 3957813 * 2 ^ 59
def prefixEnd_3957813 : Nat := 4983230072969 + 3 ^ 40 * 3957813 * 2
def baseEnd_3957813 : Nat := 677420136537742924045285

theorem tailTrace_3957813 : CollatzResearch.WordTrace tailWord_3957813 prefixEnd_3957813 677420136537742924045285 := by
  unfold tailWord_3957813
  simp only [CollatzResearch.WordTrace]
  refine ⟨144353299210526916491126093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96235532807017944327417395 144353299210526916491126093)
  ·
    refine ⟨54132487203947593684172285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144353299210526916491126093 54132487203947593684172285)
    ·
      refine ⟨20299682701480347631564607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54132487203947593684172285 20299682701480347631564607)
      ·
        refine ⟨30449524052220521447346911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20299682701480347631564607 30449524052220521447346911)
        ·
          refine ⟨45674286078330782171020367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30449524052220521447346911 45674286078330782171020367)
          ·
            refine ⟨68511429117496173256530551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45674286078330782171020367 68511429117496173256530551)
            ·
              refine ⟨102767143676244259884795827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68511429117496173256530551 102767143676244259884795827)
              ·
                refine ⟨154150715514366389827193741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102767143676244259884795827 154150715514366389827193741)
                ·
                  refine ⟨57806518317887396185197653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154150715514366389827193741 57806518317887396185197653)
                  ·
                    refine ⟨677420136537742924045285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57806518317887396185197653 677420136537742924045285)
                    ·
                      rfl

theorem cell23_3957813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_3957813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3957813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3957813 prefixEnd_3957813 := by exact prefixLift 3957813
  have htrace : WordTrace (prefixWord ++ tailWord_3957813) baseStart_3957813 baseEnd_3957813 := by
    simpa [prefixWord, tailWord_3957813, baseEnd_3957813] using wordTrace_append hprefix tailTrace_3957813
  have hstable : (prefixWord ++ tailWord_3957813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957813).length < 2 ^ (prefixWord ++ tailWord_3957813).sum := by decide
  have hdescent : baseEnd_3957813 < baseStart_3957813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957823 : List Nat := [1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 5]
def baseStart_3957823 : Nat := 118140960795 + 3957823 * 2 ^ 59
def prefixEnd_3957823 : Nat := 4983230072969 + 3 ^ 40 * 3957823 * 2
def baseEnd_3957823 : Nat := 2032265544419773733010809

theorem tailTrace_3957823 : CollatzResearch.WordTrace tailWord_3957823 prefixEnd_3957823 2032265544419773733010809 := by
  unfold tailWord_3957823
  simp only [CollatzResearch.WordTrace]
  refine ⟨144353663940490688198990123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96235775960327125465993415 144353663940490688198990123)
  ·
    refine ⟨216530495910736032298485185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144353663940490688198990123 216530495910736032298485185)
    ·
      refine ⟨162397871933052024223863889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216530495910736032298485185 162397871933052024223863889)
      ·
        refine ⟨121798403949789018167897917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162397871933052024223863889 121798403949789018167897917)
        ·
          refine ⟨45674401481170881812961719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121798403949789018167897917 45674401481170881812961719)
          ·
            refine ⟨68511602221756322719442579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45674401481170881812961719 68511602221756322719442579)
            ·
              refine ⟨102767403332634484079163869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68511602221756322719442579 102767403332634484079163869)
              ·
                refine ⟨38537776249737931529686451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102767403332634484079163869 38537776249737931529686451)
                ·
                  refine ⟨57806664374606897294529677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38537776249737931529686451 57806664374606897294529677)
                  ·
                    refine ⟨21677499140477586485448629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57806664374606897294529677 21677499140477586485448629)
                    ·
                      refine ⟨2032265544419773733010809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21677499140477586485448629 2032265544419773733010809)
                      ·
                        rfl

theorem cell23_3957823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_3957823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3957823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3957823 prefixEnd_3957823 := by exact prefixLift 3957823
  have htrace : WordTrace (prefixWord ++ tailWord_3957823) baseStart_3957823 baseEnd_3957823 := by
    simpa [prefixWord, tailWord_3957823, baseEnd_3957823] using wordTrace_append hprefix tailTrace_3957823
  have hstable : (prefixWord ++ tailWord_3957823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957823).length < 2 ^ (prefixWord ++ tailWord_3957823).sum := by decide
  have hdescent : baseEnd_3957823 < baseStart_3957823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957843 : List Nat := [1, 1, 1, 2, 1, 1, 2, 7, 7]
def baseStart_3957843 : Nat := 118140960795 + 3957843 * 2 ^ 59
def prefixEnd_3957843 : Nat := 4983230072969 + 3 ^ 40 * 3957843 * 2
def baseEnd_3957843 : Nat := 225808423781429294973413

theorem tailTrace_3957843 : CollatzResearch.WordTrace tailWord_3957843 prefixEnd_3957843 225808423781429294973413 := by
  unfold tailWord_3957843
  simp only [CollatzResearch.WordTrace]
  refine ⟨144354393400418231614718183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96236262266945487743145455 144354393400418231614718183)
  ·
    refine ⟨216531590100627347422077275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144354393400418231614718183 216531590100627347422077275)
    ·
      refine ⟨324797385150941021133115913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216531590100627347422077275 324797385150941021133115913)
      ·
        refine ⟨243598038863205765849836935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324797385150941021133115913 243598038863205765849836935)
        ·
          refine ⟨365397058294808648774755403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243598038863205765849836935 365397058294808648774755403)
          ·
            refine ⟨548095587442212973162133105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365397058294808648774755403 548095587442212973162133105)
            ·
              refine ⟨411071690581659729871599829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 548095587442212973162133105 411071690581659729871599829)
              ·
                refine ⟨9634492748007649918865621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 411071690581659729871599829 9634492748007649918865621)
                ·
                  refine ⟨225808423781429294973413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9634492748007649918865621 225808423781429294973413)
                  ·
                    rfl

theorem cell23_3957843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 7].length) (baseStart_3957843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3957843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3957843 prefixEnd_3957843 := by exact prefixLift 3957843
  have htrace : WordTrace (prefixWord ++ tailWord_3957843) baseStart_3957843 baseEnd_3957843 := by
    simpa [prefixWord, tailWord_3957843, baseEnd_3957843] using wordTrace_append hprefix tailTrace_3957843
  have hstable : (prefixWord ++ tailWord_3957843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957843).length < 2 ^ (prefixWord ++ tailWord_3957843).sum := by decide
  have hdescent : baseEnd_3957843 < baseStart_3957843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957883 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 7]
def baseStart_3957883 : Nat := 118140960795 + 3957883 * 2 ^ 59
def prefixEnd_3957883 : Nat := 4983230072969 + 3 ^ 40 * 3957883 * 2
def baseEnd_3957883 : Nat := 2032296353259043498260533

theorem tailTrace_3957883 : CollatzResearch.WordTrace tailWord_3957883 prefixEnd_3957883 2032296353259043498260533 := by
  unfold tailWord_3957883
  simp only [CollatzResearch.WordTrace]
  refine ⟨144355852320273318446174303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96237234880182212297449535 144355852320273318446174303)
  ·
    refine ⟨216533778480409977669261455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144355852320273318446174303 216533778480409977669261455)
    ·
      refine ⟨324800667720614966503892183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216533778480409977669261455 324800667720614966503892183)
      ·
        refine ⟨487201001580922449755838275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324800667720614966503892183 487201001580922449755838275)
        ·
          refine ⟨730801502371383674633757413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487201001580922449755838275 730801502371383674633757413)
          ·
            refine ⟨137025281694634438993829515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 730801502371383674633757413 137025281694634438993829515)
            ·
              refine ⟨205537922541951658490744273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137025281694634438993829515 205537922541951658490744273)
              ·
                refine ⟨154153441906463743868058205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205537922541951658490744273 154153441906463743868058205)
                ·
                  refine ⟨57807540714923903950521827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154153441906463743868058205 57807540714923903950521827)
                  ·
                    refine ⟨86711311072385855925782741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57807540714923903950521827 86711311072385855925782741)
                    ·
                      refine ⟨2032296353259043498260533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 86711311072385855925782741 2032296353259043498260533)
                      ·
                        rfl

theorem cell23_3957883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 7].length) (baseStart_3957883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3957883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3957883 prefixEnd_3957883 := by exact prefixLift 3957883
  have htrace : WordTrace (prefixWord ++ tailWord_3957883) baseStart_3957883 baseEnd_3957883 := by
    simpa [prefixWord, tailWord_3957883, baseEnd_3957883] using wordTrace_append hprefix tailTrace_3957883
  have hstable : (prefixWord ++ tailWord_3957883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957883).length < 2 ^ (prefixWord ++ tailWord_3957883).sum := by decide
  have hdescent : baseEnd_3957883 < baseStart_3957883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957903 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 3, 10]
def baseStart_3957903 : Nat := 118140960795 + 3957903 * 2 ^ 59
def prefixEnd_3957903 : Nat := 4983230072969 + 3 ^ 40 * 3957903 * 2
def baseEnd_3957903 : Nat := 677435540957377806670147

theorem tailTrace_3957903 : CollatzResearch.WordTrace tailWord_3957903 prefixEnd_3957903 677435540957377806670147 := by
  unfold tailWord_3957903
  simp only [CollatzResearch.WordTrace]
  refine ⟨144356581780200861861902363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96237721186800574574601575 144356581780200861861902363)
  ·
    refine ⟨216534872670301292792853545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144356581780200861861902363 216534872670301292792853545)
    ·
      refine ⟨162401154502725969594640159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216534872670301292792853545 162401154502725969594640159)
      ·
        refine ⟨243601731754088954391960239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162401154502725969594640159 243601731754088954391960239)
        ·
          refine ⟨365402597631133431587940359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243601731754088954391960239 365402597631133431587940359)
          ·
            refine ⟨548103896446700147381910539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365402597631133431587940359 548103896446700147381910539)
            ·
              refine ⟨822155844670050221072865809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548103896446700147381910539 822155844670050221072865809)
              ·
                refine ⟨616616883502537665804649357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 822155844670050221072865809 616616883502537665804649357)
                ·
                  refine ⟨231231331313451624676743509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 616616883502537665804649357 231231331313451624676743509)
                  ·
                    refine ⟨677435540957377806670147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 231231331313451624676743509 677435540957377806670147)
                    ·
                      rfl

theorem cell23_3957903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 10].length) (baseStart_3957903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3957903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3957903 prefixEnd_3957903 := by exact prefixLift 3957903
  have htrace : WordTrace (prefixWord ++ tailWord_3957903) baseStart_3957903 baseEnd_3957903 := by
    simpa [prefixWord, tailWord_3957903, baseEnd_3957903] using wordTrace_append hprefix tailTrace_3957903
  have hstable : (prefixWord ++ tailWord_3957903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957903).length < 2 ^ (prefixWord ++ tailWord_3957903).sum := by decide
  have hdescent : baseEnd_3957903 < baseStart_3957903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958027 : List Nat := [1, 1, 1, 1, 5, 3, 3, 1, 1, 6]
def baseStart_3958027 : Nat := 118140960795 + 3958027 * 2 ^ 59
def prefixEnd_3958027 : Nat := 4983230072969 + 3 ^ 40 * 3958027 * 2
def baseEnd_3958027 : Nat := 677456764824430311619957

theorem tailTrace_3958027 : CollatzResearch.WordTrace tailWord_3958027 prefixEnd_3958027 677456764824430311619957 := by
  unfold tailWord_3958027
  simp only [CollatzResearch.WordTrace]
  refine ⟨144361104431751631039416335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96240736287834420692944223 144361104431751631039416335)
  ·
    refine ⟨216541656647627446559124503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144361104431751631039416335 216541656647627446559124503)
    ·
      refine ⟨324812484971441169838686755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216541656647627446559124503 324812484971441169838686755)
      ·
        refine ⟨487218727457161754758030133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324812484971441169838686755 487218727457161754758030133)
        ·
          refine ⟨45676755699108914508565325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 487218727457161754758030133 45676755699108914508565325)
          ·
            refine ⟨17128783387165842940711997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45676755699108914508565325 17128783387165842940711997)
            ·
              refine ⟨6423293770187191102766999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17128783387165842940711997 6423293770187191102766999)
              ·
                refine ⟨9634940655280786654150499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6423293770187191102766999 9634940655280786654150499)
                ·
                  refine ⟨14452410982921179981225749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9634940655280786654150499 14452410982921179981225749)
                  ·
                    refine ⟨677456764824430311619957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14452410982921179981225749 677456764824430311619957)
                    ·
                      rfl

theorem cell23_3958027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 6].length) (baseStart_3958027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958027 prefixEnd_3958027 := by exact prefixLift 3958027
  have htrace : WordTrace (prefixWord ++ tailWord_3958027) baseStart_3958027 baseEnd_3958027 := by
    simpa [prefixWord, tailWord_3958027, baseEnd_3958027] using wordTrace_append hprefix tailTrace_3958027
  have hstable : (prefixWord ++ tailWord_3958027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958027).length < 2 ^ (prefixWord ++ tailWord_3958027).sum := by decide
  have hdescent : baseEnd_3958027 < baseStart_3958027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958045 : List Nat := [1, 4, 2, 3, 1, 3, 1, 3, 1, 1, 3]
def baseStart_3958045 : Nat := 118140960795 + 3958045 * 2 ^ 59
def prefixEnd_3958045 : Nat := 4983230072969 + 3 ^ 40 * 3958045 * 2
def baseEnd_3958045 : Nat := 2032379537125071864434789

theorem tailTrace_3958045 : CollatzResearch.WordTrace tailWord_3958045 prefixEnd_3958045 2032379537125071864434789 := by
  unfold tailWord_3958045
  simp only [CollatzResearch.WordTrace]
  refine ⟨144361760945686420113571589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96241173963790946742381059 144361760945686420113571589)
  ·
    refine ⟨27067830177316203771294673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144361760945686420113571589 27067830177316203771294673)
    ·
      refine ⟨20300872632987152828471005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27067830177316203771294673 20300872632987152828471005)
      ·
        refine ⟨7612827237370182310676627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20300872632987152828471005 7612827237370182310676627)
        ·
          refine ⟨11419240856055273466014941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7612827237370182310676627 11419240856055273466014941)
          ·
            refine ⟨4282215321020727549755603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11419240856055273466014941 4282215321020727549755603)
            ·
              refine ⟨6423322981531091324633405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4282215321020727549755603 6423322981531091324633405)
              ·
                refine ⟨2408746118074159246737527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6423322981531091324633405 2408746118074159246737527)
                ·
                  refine ⟨3613119177111238870106291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2408746118074159246737527 3613119177111238870106291)
                  ·
                    refine ⟨5419678765666858305159437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3613119177111238870106291 5419678765666858305159437)
                    ·
                      refine ⟨2032379537125071864434789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5419678765666858305159437 2032379537125071864434789)
                      ·
                        rfl

theorem cell23_3958045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_3958045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958045 prefixEnd_3958045 := by exact prefixLift 3958045
  have htrace : WordTrace (prefixWord ++ tailWord_3958045) baseStart_3958045 baseEnd_3958045 := by
    simpa [prefixWord, tailWord_3958045, baseEnd_3958045] using wordTrace_append hprefix tailTrace_3958045
  have hstable : (prefixWord ++ tailWord_3958045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958045).length < 2 ^ (prefixWord ++ tailWord_3958045).sum := by decide
  have hdescent : baseEnd_3958045 < baseStart_3958045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958061 : List Nat := [1, 5, 3, 1, 1, 1, 2, 1, 4, 4]
def baseStart_3958061 : Nat := 118140960795 + 3958061 * 2 ^ 59
def prefixEnd_3958061 : Nat := 4983230072969 + 3 ^ 40 * 3958061 * 2
def baseEnd_3958061 : Nat := 677462584271847933944905

theorem tailTrace_3958061 : CollatzResearch.WordTrace tailWord_3958061 prefixEnd_3958061 677462584271847933944905 := by
  unfold tailWord_3958061
  simp only [CollatzResearch.WordTrace]
  refine ⟨144362344513628454846154037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96241563009085636564102691 144362344513628454846154037)
  ·
    refine ⟨13533969798152667641826941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144362344513628454846154037 13533969798152667641826941)
    ·
      refine ⟨5075238674307250365685103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13533969798152667641826941 5075238674307250365685103)
      ·
        refine ⟨7612858011460875548527655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5075238674307250365685103 7612858011460875548527655)
        ·
          refine ⟨11419287017191313322791483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7612858011460875548527655 11419287017191313322791483)
          ·
            refine ⟨17128930525786969984187225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11419287017191313322791483 17128930525786969984187225)
            ·
              refine ⟨12846697894340227488140419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17128930525786969984187225 12846697894340227488140419)
              ·
                refine ⟨19270046841510341232210629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12846697894340227488140419 19270046841510341232210629)
                ·
                  refine ⟨3613133782783188981039493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19270046841510341232210629 3613133782783188981039493)
                  ·
                    refine ⟨677462584271847933944905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3613133782783188981039493 677462584271847933944905)
                    ·
                      rfl

theorem cell23_3958061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_3958061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958061 prefixEnd_3958061 := by exact prefixLift 3958061
  have htrace : WordTrace (prefixWord ++ tailWord_3958061) baseStart_3958061 baseEnd_3958061 := by
    simpa [prefixWord, tailWord_3958061, baseEnd_3958061] using wordTrace_append hprefix tailTrace_3958061
  have hstable : (prefixWord ++ tailWord_3958061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958061).length < 2 ^ (prefixWord ++ tailWord_3958061).sum := by decide
  have hdescent : baseEnd_3958061 < baseStart_3958061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958117 : List Nat := [1, 3, 1, 3, 1, 2, 2, 2, 2, 6]
def baseStart_3958117 : Nat := 118140960795 + 3958117 * 2 ^ 59
def prefixEnd_3958117 : Nat := 4983230072969 + 3 ^ 40 * 3958117 * 2
def baseEnd_3958117 : Nat := 677472169244065194244819

theorem tailTrace_3958117 : CollatzResearch.WordTrace tailWord_3958117 prefixEnd_3958117 677472169244065194244819 := by
  unfold tailWord_3958117
  simp only [CollatzResearch.WordTrace]
  refine ⟨144364387001425576410192605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96242924667617050940128403 144364387001425576410192605)
  ·
    refine ⟨54136645125534591153822227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144364387001425576410192605 54136645125534591153822227)
    ·
      refine ⟨81204967688301886730733341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54136645125534591153822227 81204967688301886730733341)
      ·
        refine ⟨30451862883113207524025003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81204967688301886730733341 30451862883113207524025003)
        ·
          refine ⟨45677794324669811286037505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30451862883113207524025003 45677794324669811286037505)
          ·
            refine ⟨34258345743502358464528129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45677794324669811286037505 34258345743502358464528129)
            ·
              refine ⟨25693759307626768848396097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34258345743502358464528129 25693759307626768848396097)
              ·
                refine ⟨19270319480720076636297073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25693759307626768848396097 19270319480720076636297073)
                ·
                  refine ⟨14452739610540057477222805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19270319480720076636297073 14452739610540057477222805)
                  ·
                    refine ⟨677472169244065194244819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14452739610540057477222805 677472169244065194244819)
                    ·
                      rfl

theorem cell23_3958117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 6].length) (baseStart_3958117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958117 prefixEnd_3958117 := by exact prefixLift 3958117
  have htrace : WordTrace (prefixWord ++ tailWord_3958117) baseStart_3958117 baseEnd_3958117 := by
    simpa [prefixWord, tailWord_3958117, baseEnd_3958117] using wordTrace_append hprefix tailTrace_3958117
  have hstable : (prefixWord ++ tailWord_3958117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958117).length < 2 ^ (prefixWord ++ tailWord_3958117).sum := by decide
  have hdescent : baseEnd_3958117 < baseStart_3958117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958119 : List Nat := [1, 1, 5, 1, 5, 1, 2, 2, 1, 2, 2]
def baseStart_3958119 : Nat := 118140960795 + 3958119 * 2 ^ 59
def prefixEnd_3958119 : Nat := 4983230072969 + 3 ^ 40 * 3958119 * 2
def baseEnd_3958119 : Nat := 2032417534693504574909449

theorem tailTrace_3958119 : CollatzResearch.WordTrace tailWord_3958119 prefixEnd_3958119 2032417534693504574909449 := by
  unfold tailWord_3958119
  simp only [CollatzResearch.WordTrace]
  refine ⟨144364459947418330751765411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96242973298278887167843607 144364459947418330751765411)
  ·
    refine ⟨216546689921127496127648117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144364459947418330751765411 216546689921127496127648117)
    ·
      refine ⟨20301252180105702761967011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 216546689921127496127648117 20301252180105702761967011)
      ·
        refine ⟨30451878270158554142950517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20301252180105702761967011 30451878270158554142950517)
        ·
          refine ⟨2854863587827364450901611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30451878270158554142950517 2854863587827364450901611)
          ·
            refine ⟨4282295381741046676352417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2854863587827364450901611 4282295381741046676352417)
            ·
              refine ⟨3211721536305785007264313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4282295381741046676352417 3211721536305785007264313)
              ·
                refine ⟨2408791152229338755448235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3211721536305785007264313 2408791152229338755448235)
                ·
                  refine ⟨3613186728344008133172353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2408791152229338755448235 3613186728344008133172353)
                  ·
                    refine ⟨2709890046258006099879265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3613186728344008133172353 2709890046258006099879265)
                    ·
                      refine ⟨2032417534693504574909449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2709890046258006099879265 2032417534693504574909449)
                      ·
                        rfl

theorem cell23_3958119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 2, 1, 2, 2].length) (baseStart_3958119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958119 prefixEnd_3958119 := by exact prefixLift 3958119
  have htrace : WordTrace (prefixWord ++ tailWord_3958119) baseStart_3958119 baseEnd_3958119 := by
    simpa [prefixWord, tailWord_3958119, baseEnd_3958119] using wordTrace_append hprefix tailTrace_3958119
  have hstable : (prefixWord ++ tailWord_3958119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958119).length < 2 ^ (prefixWord ++ tailWord_3958119).sum := by decide
  have hdescent : baseEnd_3958119 < baseStart_3958119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958127 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 1, 6, 3]
def baseStart_3958127 : Nat := 118140960795 + 3958127 * 2 ^ 59
def prefixEnd_3958127 : Nat := 4983230072969 + 3 ^ 40 * 3958127 * 2
def baseEnd_3958127 : Nat := 2032421642538740543609411

theorem tailTrace_3958127 : CollatzResearch.WordTrace tailWord_3958127 prefixEnd_3958127 2032421642538740543609411 := by
  unfold tailWord_3958127
  simp only [CollatzResearch.WordTrace]
  refine ⟨144364751731389348118056635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96243167820926232078704423 144364751731389348118056635)
  ·
    refine ⟨216547127597084022177084953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144364751731389348118056635 216547127597084022177084953)
    ·
      refine ⟨162410345697813016632813715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216547127597084022177084953 162410345697813016632813715)
      ·
        refine ⟨243615518546719524949220573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162410345697813016632813715 243615518546719524949220573)
        ·
          refine ⟨91355819455019821855957715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243615518546719524949220573 91355819455019821855957715)
          ·
            refine ⟨137033729182529732783936573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91355819455019821855957715 137033729182529732783936573)
            ·
              refine ⟨51387648443448649793976215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137033729182529732783936573 51387648443448649793976215)
              ·
                refine ⟨77081472665172974690964323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51387648443448649793976215 77081472665172974690964323)
                ·
                  refine ⟨115622208997759462036446485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77081472665172974690964323 115622208997759462036446485)
                  ·
                    refine ⟨5419791046769974782958429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 115622208997759462036446485 5419791046769974782958429)
                    ·
                      refine ⟨2032421642538740543609411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5419791046769974782958429 2032421642538740543609411)
                      ·
                        rfl

theorem cell23_3958127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 6, 3].length) (baseStart_3958127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958127 prefixEnd_3958127 := by exact prefixLift 3958127
  have htrace : WordTrace (prefixWord ++ tailWord_3958127) baseStart_3958127 baseEnd_3958127 := by
    simpa [prefixWord, tailWord_3958127, baseEnd_3958127] using wordTrace_append hprefix tailTrace_3958127
  have hstable : (prefixWord ++ tailWord_3958127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958127).length < 2 ^ (prefixWord ++ tailWord_3958127).sum := by decide
  have hdescent : baseEnd_3958127 < baseStart_3958127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958137 : List Nat := [1, 2, 1, 3, 2, 1, 3, 1, 1, 4, 4]
def baseStart_3958137 : Nat := 118140960795 + 3958137 * 2 ^ 59
def prefixEnd_3958137 : Nat := 4983230072969 + 3 ^ 40 * 3958137 * 2
def baseEnd_3958137 : Nat := 2032426777345285504484365

theorem tailTrace_3958137 : CollatzResearch.WordTrace tailWord_3958137 prefixEnd_3958137 2032426777345285504484365 := by
  unfold tailWord_3958137
  simp only [CollatzResearch.WordTrace]
  refine ⟨144365116461353119825920665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96243410974235413217280443 144365116461353119825920665)
  ·
    refine ⟨108273837346014839869440499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144365116461353119825920665 108273837346014839869440499)
    ·
      refine ⟨162410756019022259804160749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108273837346014839869440499 162410756019022259804160749)
      ·
        refine ⟨60904033507133347426560281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162410756019022259804160749 60904033507133347426560281)
        ·
          refine ⟨45678025130350010569920211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60904033507133347426560281 45678025130350010569920211)
          ·
            refine ⟨68517037695525015854880317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45678025130350010569920211 68517037695525015854880317)
            ·
              refine ⟨25693889135821880945580119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68517037695525015854880317 25693889135821880945580119)
              ·
                refine ⟨38540833703732821418370179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25693889135821880945580119 38540833703732821418370179)
                ·
                  refine ⟨57811250555599232127555269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38540833703732821418370179 57811250555599232127555269)
                  ·
                    refine ⟨10839609479174856023916613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57811250555599232127555269 10839609479174856023916613)
                    ·
                      refine ⟨2032426777345285504484365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10839609479174856023916613 2032426777345285504484365)
                      ·
                        rfl

theorem cell23_3958137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_3958137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958137 prefixEnd_3958137 := by exact prefixLift 3958137
  have htrace : WordTrace (prefixWord ++ tailWord_3958137) baseStart_3958137 baseEnd_3958137 := by
    simpa [prefixWord, tailWord_3958137, baseEnd_3958137] using wordTrace_append hprefix tailTrace_3958137
  have hstable : (prefixWord ++ tailWord_3958137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958137).length < 2 ^ (prefixWord ++ tailWord_3958137).sum := by decide
  have hdescent : baseEnd_3958137 < baseStart_3958137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958141 : List Nat := [1, 4, 1, 1, 2, 2, 4, 1, 1, 4, 2]
def baseStart_3958141 : Nat := 118140960795 + 3958141 * 2 ^ 59
def prefixEnd_3958141 : Nat := 4983230072969 + 3 ^ 40 * 3958141 * 2
def baseEnd_3958141 : Nat := 2032428831267903488834347

theorem tailTrace_3958141 : CollatzResearch.WordTrace tailWord_3958141 prefixEnd_3958141 2032428831267903488834347 := by
  unfold tailWord_3958141
  simp only [CollatzResearch.WordTrace]
  refine ⟨144365262353338628509066277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96243508235559085672710851 144365262353338628509066277)
  ·
    refine ⟨27068486691250992845449927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144365262353338628509066277 27068486691250992845449927)
    ·
      refine ⟨40602730036876489268174891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27068486691250992845449927 40602730036876489268174891)
      ·
        refine ⟨60904095055314733902262337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40602730036876489268174891 60904095055314733902262337)
        ·
          refine ⟨45678071291486050426696753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60904095055314733902262337 45678071291486050426696753)
          ·
            refine ⟨34258553468614537820022565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45678071291486050426696753 34258553468614537820022565)
            ·
              refine ⟨6423478775365225841254231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34258553468614537820022565 6423478775365225841254231)
              ·
                refine ⟨9635218163047838761881347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6423478775365225841254231 9635218163047838761881347)
                ·
                  refine ⟨14452827244571758142822021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9635218163047838761881347 14452827244571758142822021)
                  ·
                    refine ⟨2709905108357204651779129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14452827244571758142822021 2709905108357204651779129)
                    ·
                      refine ⟨2032428831267903488834347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2709905108357204651779129 2032428831267903488834347)
                      ·
                        rfl

theorem cell23_3958141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 4, 2].length) (baseStart_3958141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958141 prefixEnd_3958141 := by exact prefixLift 3958141
  have htrace : WordTrace (prefixWord ++ tailWord_3958141) baseStart_3958141 baseEnd_3958141 := by
    simpa [prefixWord, tailWord_3958141, baseEnd_3958141] using wordTrace_append hprefix tailTrace_3958141
  have hstable : (prefixWord ++ tailWord_3958141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958141).length < 2 ^ (prefixWord ++ tailWord_3958141).sum := by decide
  have hdescent : baseEnd_3958141 < baseStart_3958141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958147 : List Nat := [1, 1, 1, 3, 5, 1, 1, 1, 9]
def baseStart_3958147 : Nat := 118140960795 + 3958147 * 2 ^ 59
def prefixEnd_3958147 : Nat := 4983230072969 + 3 ^ 40 * 3958147 * 2
def baseEnd_3958147 : Nat := 225825768016870051706591

theorem tailTrace_3958147 : CollatzResearch.WordTrace tailWord_3958147 prefixEnd_3958147 225825768016870051706591 := by
  unfold tailWord_3958147
  simp only [CollatzResearch.WordTrace]
  refine ⟨144365481191316891533784695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96243654127544594355856463 144365481191316891533784695)
  ·
    refine ⟨216548221786975337300677043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144365481191316891533784695 216548221786975337300677043)
    ·
      refine ⟨324822332680463005951015565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216548221786975337300677043 324822332680463005951015565)
      ·
        refine ⟨121808374755173627231630837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324822332680463005951015565 121808374755173627231630837)
        ·
          refine ⟨11419535133297527552965391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121808374755173627231630837 11419535133297527552965391)
          ·
            refine ⟨17129302699946291329448087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11419535133297527552965391 17129302699946291329448087)
            ·
              refine ⟨25693954049919436994172131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17129302699946291329448087 25693954049919436994172131)
              ·
                refine ⟨38540931074879155491258197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25693954049919436994172131 38540931074879155491258197)
                ·
                  refine ⟨225825768016870051706591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 38540931074879155491258197 225825768016870051706591)
                  ·
                    rfl

theorem cell23_3958147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 9].length) (baseStart_3958147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958147 prefixEnd_3958147 := by exact prefixLift 3958147
  have htrace : WordTrace (prefixWord ++ tailWord_3958147) baseStart_3958147 baseEnd_3958147 := by
    simpa [prefixWord, tailWord_3958147, baseEnd_3958147] using wordTrace_append hprefix tailTrace_3958147
  have hstable : (prefixWord ++ tailWord_3958147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958147).length < 2 ^ (prefixWord ++ tailWord_3958147).sum := by decide
  have hdescent : baseEnd_3958147 < baseStart_3958147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958175 : List Nat := [1, 1, 2, 5, 1, 4, 1, 2, 2, 2, 2]
def baseStart_3958175 : Nat := 118140960795 + 3958175 * 2 ^ 59
def prefixEnd_3958175 : Nat := 4983230072969 + 3 ^ 40 * 3958175 * 2
def baseEnd_3958175 : Nat := 2032446289610156355809191

theorem tailTrace_3958175 : CollatzResearch.WordTrace tailWord_3958175 prefixEnd_3958175 2032446289610156355809191 := by
  unfold tailWord_3958175
  simp only [CollatzResearch.WordTrace]
  refine ⟨144366502435215452315803979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96244334956810301543869319 144366502435215452315803979)
  ·
    refine ⟨216549753652823178473705969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144366502435215452315803979 216549753652823178473705969)
    ·
      refine ⟨162412315239617383855279477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216549753652823178473705969 162412315239617383855279477)
      ·
        refine ⟨15226154553714129736432451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162412315239617383855279477 15226154553714129736432451)
        ·
          refine ⟨22839231830571194604648677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15226154553714129736432451 22839231830571194604648677)
          ·
            refine ⟨4282355968232098988371627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22839231830571194604648677 4282355968232098988371627)
            ·
              refine ⟨6423533952348148482557441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4282355968232098988371627 6423533952348148482557441)
              ·
                refine ⟨4817650464261111361918081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6423533952348148482557441 4817650464261111361918081)
                ·
                  refine ⟨3613237848195833521438561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4817650464261111361918081 3613237848195833521438561)
                  ·
                    refine ⟨2709928386146875141078921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3613237848195833521438561 2709928386146875141078921)
                    ·
                      refine ⟨2032446289610156355809191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2709928386146875141078921 2032446289610156355809191)
                      ·
                        rfl

theorem cell23_3958175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_3958175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958175 prefixEnd_3958175 := by exact prefixLift 3958175
  have htrace : WordTrace (prefixWord ++ tailWord_3958175) baseStart_3958175 baseEnd_3958175 := by
    simpa [prefixWord, tailWord_3958175, baseEnd_3958175] using wordTrace_append hprefix tailTrace_3958175
  have hstable : (prefixWord ++ tailWord_3958175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958175).length < 2 ^ (prefixWord ++ tailWord_3958175).sum := by decide
  have hdescent : baseEnd_3958175 < baseStart_3958175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958217 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 2, 3, 5]
def baseStart_3958217 : Nat := 118140960795 + 3958217 * 2 ^ 59
def prefixEnd_3958217 : Nat := 4983230072969 + 3 ^ 40 * 3958217 * 2
def baseEnd_3958217 : Nat := 2032467855797645191483997

theorem tailTrace_3958217 : CollatzResearch.WordTrace tailWord_3958217 prefixEnd_3958217 2032467855797645191483997 := by
  unfold tailWord_3958217
  simp only [CollatzResearch.WordTrace]
  refine ⟨144368034301063293488832905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96245356200708862325888603 144368034301063293488832905)
  ·
    refine ⟨108276025725797470116624679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144368034301063293488832905 108276025725797470116624679)
    ·
      refine ⟨162414038588696205174937019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108276025725797470116624679 162414038588696205174937019)
      ·
        refine ⟨243621057883044307762405529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162414038588696205174937019 243621057883044307762405529)
        ·
          refine ⟨182715793412283230821804147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243621057883044307762405529 182715793412283230821804147)
          ·
            refine ⟨274073690118424846232706221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182715793412283230821804147 274073690118424846232706221)
            ·
              refine ⟨102777633794409317337264833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 274073690118424846232706221 102777633794409317337264833)
              ·
                refine ⟨77083225345806988002948625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102777633794409317337264833 77083225345806988002948625)
                ·
                  refine ⟨57812419009355241002211469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77083225345806988002948625 57812419009355241002211469)
                  ·
                    refine ⟨21679657128508215375829301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57812419009355241002211469 21679657128508215375829301)
                    ·
                      refine ⟨2032467855797645191483997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21679657128508215375829301 2032467855797645191483997)
                      ·
                        rfl

theorem cell23_3958217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 3, 5].length) (baseStart_3958217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958217 prefixEnd_3958217 := by exact prefixLift 3958217
  have htrace : WordTrace (prefixWord ++ tailWord_3958217) baseStart_3958217 baseEnd_3958217 := by
    simpa [prefixWord, tailWord_3958217, baseEnd_3958217] using wordTrace_append hprefix tailTrace_3958217
  have hstable : (prefixWord ++ tailWord_3958217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958217).length < 2 ^ (prefixWord ++ tailWord_3958217).sum := by decide
  have hdescent : baseEnd_3958217 < baseStart_3958217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958241 : List Nat := [1, 2, 3, 1, 2, 3, 3, 1, 3, 4]
def baseStart_3958241 : Nat := 118140960795 + 3958241 * 2 ^ 59
def prefixEnd_3958241 : Nat := 4983230072969 + 3 ^ 40 * 3958241 * 2
def baseEnd_3958241 : Nat := 677493393111117699194629

theorem tailTrace_3958241 : CollatzResearch.WordTrace tailWord_3958241 prefixEnd_3958241 677493393111117699194629 := by
  unfold tailWord_3958241
  simp only [CollatzResearch.WordTrace]
  refine ⟨144368909652976345587706577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96245939768650897058471051 144368909652976345587706577)
  ·
    refine ⟨108276682239732259190779933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144368909652976345587706577 108276682239732259190779933)
    ·
      refine ⟨40603755839899597196542475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108276682239732259190779933 40603755839899597196542475)
      ·
        refine ⟨60905633759849395794813713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40603755839899597196542475 60905633759849395794813713)
        ·
          refine ⟨45679225319887046846110285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60905633759849395794813713 45679225319887046846110285)
          ·
            refine ⟨17129709494957642567291357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45679225319887046846110285 17129709494957642567291357)
            ·
              refine ⟨6423641060609115962734259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17129709494957642567291357 6423641060609115962734259)
              ·
                refine ⟨9635461590913673944101389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6423641060609115962734259 9635461590913673944101389)
                ·
                  refine ⟨3613298096592627729038021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9635461590913673944101389 3613298096592627729038021)
                  ·
                    refine ⟨677493393111117699194629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3613298096592627729038021 677493393111117699194629)
                    ·
                      rfl

theorem cell23_3958241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 3, 4].length) (baseStart_3958241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958241 prefixEnd_3958241 := by exact prefixLift 3958241
  have htrace : WordTrace (prefixWord ++ tailWord_3958241) baseStart_3958241 baseEnd_3958241 := by
    simpa [prefixWord, tailWord_3958241, baseEnd_3958241] using wordTrace_append hprefix tailTrace_3958241
  have hstable : (prefixWord ++ tailWord_3958241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958241).length < 2 ^ (prefixWord ++ tailWord_3958241).sum := by decide
  have hdescent : baseEnd_3958241 < baseStart_3958241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958267 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 2, 9]
def baseStart_3958267 : Nat := 118140960795 + 3958267 * 2 ^ 59
def prefixEnd_3958267 : Nat := 4983230072969 + 3 ^ 40 * 3958267 * 2
def baseEnd_3958267 : Nat := 677497843276789998619589

theorem tailTrace_3958267 : CollatzResearch.WordTrace tailWord_3958267 prefixEnd_3958267 677497843276789998619589 := by
  unfold tailWord_3958267
  simp only [CollatzResearch.WordTrace]
  refine ⟨144369857950882152028153055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96246571967254768018768703 144369857950882152028153055)
  ·
    refine ⟨216554786926323228042229583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144369857950882152028153055 216554786926323228042229583)
    ·
      refine ⟨324832180389484842063344375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216554786926323228042229583 324832180389484842063344375)
      ·
        refine ⟨487248270584227263095016563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324832180389484842063344375 487248270584227263095016563)
        ·
          refine ⟨730872405876340894642524845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487248270584227263095016563 730872405876340894642524845)
          ·
            refine ⟨274077152203627835490946817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 730872405876340894642524845 274077152203627835490946817)
            ·
              refine ⟨205557864152720876618210113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274077152203627835490946817 205557864152720876618210113)
              ·
                refine ⟨154168398114540657463657585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205557864152720876618210113 154168398114540657463657585)
                ·
                  refine ⟨115626298585905493097743189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154168398114540657463657585 115626298585905493097743189)
                  ·
                    refine ⟨677497843276789998619589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 115626298585905493097743189 677497843276789998619589)
                    ·
                      rfl

theorem cell23_3958267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 9].length) (baseStart_3958267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958267 prefixEnd_3958267 := by exact prefixLift 3958267
  have htrace : WordTrace (prefixWord ++ tailWord_3958267) baseStart_3958267 baseEnd_3958267 := by
    simpa [prefixWord, tailWord_3958267, baseEnd_3958267] using wordTrace_append hprefix tailTrace_3958267
  have hstable : (prefixWord ++ tailWord_3958267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958267).length < 2 ^ (prefixWord ++ tailWord_3958267).sum := by decide
  have hdescent : baseEnd_3958267 < baseStart_3958267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958292 : List Nat := [2, 4, 3, 1, 2, 1, 1, 4, 1, 4]
def baseStart_3958292 : Nat := 118140960795 + 3958292 * 2 ^ 59
def prefixEnd_3958292 : Nat := 4983230072969 + 3 ^ 40 * 3958292 * 2
def baseEnd_3958292 : Nat := 677502122282244132682051

theorem tailTrace_3958292 : CollatzResearch.WordTrace tailWord_3958292 prefixEnd_3958292 677502122282244132682051 := by
  unfold tailWord_3958292
  simp only [CollatzResearch.WordTrace]
  refine ⟨72185384887895790648906565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96247179850527720865208753 72185384887895790648906565)
  ·
    refine ⟨13534759666480460746669981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72185384887895790648906565 13534759666480460746669981)
    ·
      refine ⟨5075534874930172780001243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13534759666480460746669981 5075534874930172780001243)
      ·
        refine ⟨7613302312395259170001865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5075534874930172780001243 7613302312395259170001865)
        ·
          refine ⟨5709976734296444377501399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7613302312395259170001865 5709976734296444377501399)
          ·
            refine ⟨8564965101444666566252099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5709976734296444377501399 8564965101444666566252099)
            ·
              refine ⟨12847447652166999849378149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8564965101444666566252099 12847447652166999849378149)
              ·
                refine ⟨2408896434781312471758403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12847447652166999849378149 2408896434781312471758403)
                ·
                  refine ⟨3613344652171968707637605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2408896434781312471758403 3613344652171968707637605)
                  ·
                    refine ⟨677502122282244132682051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3613344652171968707637605 677502122282244132682051)
                    ·
                      rfl

theorem cell23_3958292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_3958292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958292 prefixEnd_3958292 := by exact prefixLift 3958292
  have htrace : WordTrace (prefixWord ++ tailWord_3958292) baseStart_3958292 baseEnd_3958292 := by
    simpa [prefixWord, tailWord_3958292, baseEnd_3958292] using wordTrace_append hprefix tailTrace_3958292
  have hstable : (prefixWord ++ tailWord_3958292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958292).length < 2 ^ (prefixWord ++ tailWord_3958292).sum := by decide
  have hdescent : baseEnd_3958292 < baseStart_3958292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958321 : List Nat := [1, 2, 2, 3, 1, 1, 1, 6, 1, 1, 4]
def baseStart_3958321 : Nat := 118140960795 + 3958321 * 2 ^ 59
def prefixEnd_3958321 : Nat := 4983230072969 + 3 ^ 40 * 3958321 * 2
def baseEnd_3958321 : Nat := 2032521257785712784583519

theorem tailTrace_3958321 : CollatzResearch.WordTrace tailWord_3958321 prefixEnd_3958321 2032521257785712784583519 := by
  unfold tailWord_3958321
  simp only [CollatzResearch.WordTrace]
  refine ⟨144371827492686519250618817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96247884995124346167079211 144371827492686519250618817)
  ·
    refine ⟨108278870619514889437964113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144371827492686519250618817 108278870619514889437964113)
    ·
      refine ⟨81209152964636167078473085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108278870619514889437964113 81209152964636167078473085)
      ·
        refine ⟨30453432361738562654427407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81209152964636167078473085 30453432361738562654427407)
        ·
          refine ⟨45680148542607843981641111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30453432361738562654427407 45680148542607843981641111)
          ·
            refine ⟨68520222813911765972461667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45680148542607843981641111 68520222813911765972461667)
            ·
              refine ⟨102780334220867648958692501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68520222813911765972461667 102780334220867648958692501)
              ·
                refine ⟨4817828166603171044938711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102780334220867648958692501 4817828166603171044938711)
                ·
                  refine ⟨7226742249904756567408067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4817828166603171044938711 7226742249904756567408067)
                  ·
                    refine ⟨10840113374857134851112101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7226742249904756567408067 10840113374857134851112101)
                    ·
                      refine ⟨2032521257785712784583519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10840113374857134851112101 2032521257785712784583519)
                      ·
                        rfl

theorem cell23_3958321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_3958321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958321 prefixEnd_3958321 := by exact prefixLift 3958321
  have htrace : WordTrace (prefixWord ++ tailWord_3958321) baseStart_3958321 baseEnd_3958321 := by
    simpa [prefixWord, tailWord_3958321, baseEnd_3958321] using wordTrace_append hprefix tailTrace_3958321
  have hstable : (prefixWord ++ tailWord_3958321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958321).length < 2 ^ (prefixWord ++ tailWord_3958321).sum := by decide
  have hdescent : baseEnd_3958321 < baseStart_3958321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958325 : List Nat := [1, 3, 3, 1, 1, 5, 1, 1, 2, 3, 2]
def baseStart_3958325 : Nat := 118140960795 + 3958325 * 2 ^ 59
def prefixEnd_3958325 : Nat := 4983230072969 + 3 ^ 40 * 3958325 * 2
def baseEnd_3958325 : Nat := 2032523311708330768933501

theorem tailTrace_3958325 : CollatzResearch.WordTrace tailWord_3958325 prefixEnd_3958325 2032523311708330768933501 := by
  unfold tailWord_3958325
  simp only [CollatzResearch.WordTrace]
  refine ⟨144371973384672027933764429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96247982256448018622509619 144371973384672027933764429)
  ·
    refine ⟨54139490019252010475161661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144371973384672027933764429 54139490019252010475161661)
    ·
      refine ⟨20302308757219503928185623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54139490019252010475161661 20302308757219503928185623)
      ·
        refine ⟨30453463135829255892278435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20302308757219503928185623 30453463135829255892278435)
        ·
          refine ⟨45680194703743883838417653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30453463135829255892278435 45680194703743883838417653)
          ·
            refine ⟨4282518253475989109851655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45680194703743883838417653 4282518253475989109851655)
            ·
              refine ⟨6423777380213983664777483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4282518253475989109851655 6423777380213983664777483)
              ·
                refine ⟨9635666070320975497166225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6423777380213983664777483 9635666070320975497166225)
                ·
                  refine ⟨7226749552740731622874669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9635666070320975497166225 7226749552740731622874669)
                  ·
                    refine ⟨2710031082277774358578001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7226749552740731622874669 2710031082277774358578001)
                    ·
                      refine ⟨2032523311708330768933501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2710031082277774358578001 2032523311708330768933501)
                      ·
                        rfl

theorem cell23_3958325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_3958325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958325 prefixEnd_3958325 := by exact prefixLift 3958325
  have htrace : WordTrace (prefixWord ++ tailWord_3958325) baseStart_3958325 baseEnd_3958325 := by
    simpa [prefixWord, tailWord_3958325, baseEnd_3958325] using wordTrace_append hprefix tailTrace_3958325
  have hstable : (prefixWord ++ tailWord_3958325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958325).length < 2 ^ (prefixWord ++ tailWord_3958325).sum := by decide
  have hdescent : baseEnd_3958325 < baseStart_3958325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958332 : List Nat := [2, 2, 2, 2, 4, 1, 2, 3, 1, 1, 3]
def baseStart_3958332 : Nat := 118140960795 + 3958332 * 2 ^ 59
def prefixEnd_3958332 : Nat := 4983230072969 + 3 ^ 40 * 3958332 * 2
def baseEnd_3958332 : Nat := 2032526906072912241545969

theorem tailTrace_3958332 : CollatzResearch.WordTrace tailWord_3958332 prefixEnd_3958332 2032526906072912241545969 := by
  unfold tailWord_3958332
  simp only [CollatzResearch.WordTrace]
  refine ⟨72186114347823334064634625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96248152463764445419512833 72186114347823334064634625)
  ·
    refine ⟨54139585760867500548475969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72186114347823334064634625 54139585760867500548475969)
    ·
      refine ⟨40604689320650625411356977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54139585760867500548475969 40604689320650625411356977)
      ·
        refine ⟨30453516990487969058517733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40604689320650625411356977 30453516990487969058517733)
        ·
          refine ⟨5710034435716494198472075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30453516990487969058517733 5710034435716494198472075)
          ·
            refine ⟨8565051653574741297708113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5710034435716494198472075 8565051653574741297708113)
            ·
              refine ⟨6423788740181055973281085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8565051653574741297708113 6423788740181055973281085)
              ·
                refine ⟨2408920777567895989980407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6423788740181055973281085 2408920777567895989980407)
                ·
                  refine ⟨3613381166351843984970611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2408920777567895989980407 3613381166351843984970611)
                  ·
                    refine ⟨5420071749527765977455917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3613381166351843984970611 5420071749527765977455917)
                    ·
                      refine ⟨2032526906072912241545969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5420071749527765977455917 2032526906072912241545969)
                      ·
                        rfl

theorem cell23_3958332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 3, 1, 1, 3].length) (baseStart_3958332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958332 prefixEnd_3958332 := by exact prefixLift 3958332
  have htrace : WordTrace (prefixWord ++ tailWord_3958332) baseStart_3958332 baseEnd_3958332 := by
    simpa [prefixWord, tailWord_3958332, baseEnd_3958332] using wordTrace_append hprefix tailTrace_3958332
  have hstable : (prefixWord ++ tailWord_3958332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958332).length < 2 ^ (prefixWord ++ tailWord_3958332).sum := by decide
  have hdescent : baseEnd_3958332 < baseStart_3958332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958348 : List Nat := [2, 2, 1, 3, 1, 3, 3, 2, 2, 4]
def baseStart_3958348 : Nat := 118140960795 + 3958348 * 2 ^ 59
def prefixEnd_3958348 : Nat := 4983230072969 + 3 ^ 40 * 3958348 * 2
def baseEnd_3958348 : Nat := 677511707254461392981965

theorem tailTrace_3958348 : CollatzResearch.WordTrace tailWord_3958348 prefixEnd_3958348 677511707254461392981965 := by
  unfold tailWord_3958348
  simp only [CollatzResearch.WordTrace]
  refine ⟨72186406131794351430925849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96248541509059135241234465 72186406131794351430925849)
  ·
    refine ⟨54139804598845763573194387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72186406131794351430925849 54139804598845763573194387)
    ·
      refine ⟨81209706898268645359791581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54139804598845763573194387 81209706898268645359791581)
      ·
        refine ⟨30453640086850742009921843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81209706898268645359791581 30453640086850742009921843)
        ·
          refine ⟨45680460130276113014882765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30453640086850742009921843 45680460130276113014882765)
          ·
            refine ⟨17130172548853542380581037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45680460130276113014882765 17130172548853542380581037)
            ·
              refine ⟨6423814705820078392717889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17130172548853542380581037 6423814705820078392717889)
              ·
                refine ⟨4817861029365058794538417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6423814705820078392717889 4817861029365058794538417)
                ·
                  refine ⟨3613395772023794095903813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4817861029365058794538417 3613395772023794095903813)
                  ·
                    refine ⟨677511707254461392981965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3613395772023794095903813 677511707254461392981965)
                    ·
                      rfl

theorem cell23_3958348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 2, 4].length) (baseStart_3958348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958348 prefixEnd_3958348 := by exact prefixLift 3958348
  have htrace : WordTrace (prefixWord ++ tailWord_3958348) baseStart_3958348 baseEnd_3958348 := by
    simpa [prefixWord, tailWord_3958348, baseEnd_3958348] using wordTrace_append hprefix tailTrace_3958348
  have hstable : (prefixWord ++ tailWord_3958348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958348).length < 2 ^ (prefixWord ++ tailWord_3958348).sum := by decide
  have hdescent : baseEnd_3958348 < baseStart_3958348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958378 : List Nat := [3, 1, 3, 2, 1, 4, 2, 7]
def baseStart_3958378 : Nat := 118140960795 + 3958378 * 2 ^ 59
def prefixEnd_3958378 : Nat := 4983230072969 + 3 ^ 40 * 3958378 * 2
def baseEnd_3958378 : Nat := 75279649117889594872991

theorem tailTrace_3958378 : CollatzResearch.WordTrace tailWord_3958378 prefixEnd_3958378 75279649117889594872991 := by
  unfold tailWord_3958378
  simp only [CollatzResearch.WordTrace]
  refine ⟨36093476613370004496360947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96249270968986678656962525 36093476613370004496360947)
  ·
    refine ⟨54140214920055006744541421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36093476613370004496360947 54140214920055006744541421)
    ·
      refine ⟨20302580595020627529203033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54140214920055006744541421 20302580595020627529203033)
      ·
        refine ⟨15226935446265470646902275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20302580595020627529203033 15226935446265470646902275)
        ·
          refine ⟨22840403169398205970353413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15226935446265470646902275 22840403169398205970353413)
          ·
            refine ⟨4282575594262163619441265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22840403169398205970353413 4282575594262163619441265)
            ·
              refine ⟨3211931695696622714580949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4282575594262163619441265 3211931695696622714580949)
              ·
                refine ⟨75279649117889594872991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3211931695696622714580949 75279649117889594872991)
                ·
                  rfl

theorem cell23_3958378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 7].length) (baseStart_3958378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958378 prefixEnd_3958378 := by exact prefixLift 3958378
  have htrace : WordTrace (prefixWord ++ tailWord_3958378) baseStart_3958378 baseEnd_3958378 := by
    simpa [prefixWord, tailWord_3958378, baseEnd_3958378] using wordTrace_append hprefix tailTrace_3958378
  have hstable : (prefixWord ++ tailWord_3958378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958378).length < 2 ^ (prefixWord ++ tailWord_3958378).sum := by decide
  have hdescent : baseEnd_3958378 < baseStart_3958378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958389 : List Nat := [1, 3, 4, 2, 1, 1, 3, 3, 1, 2, 2]
def baseStart_3958389 : Nat := 118140960795 + 3958389 * 2 ^ 59
def prefixEnd_3958389 : Nat := 4983230072969 + 3 ^ 40 * 3958389 * 2
def baseEnd_3958389 : Nat := 2032556174470218518533207

theorem tailTrace_3958389 : CollatzResearch.WordTrace tailWord_3958389 prefixEnd_3958389 2032556174470218518533207 := by
  unfold tailWord_3958389
  simp only [CollatzResearch.WordTrace]
  refine ⟨144374307656440166864094221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96249538437626777909396147 144374307656440166864094221)
  ·
    refine ⟨54140365371165062574035333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144374307656440166864094221 54140365371165062574035333)
    ·
      refine ⟨10151318507093449232631625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54140365371165062574035333 10151318507093449232631625)
      ·
        refine ⟨7613488880320086924473719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10151318507093449232631625 7613488880320086924473719)
        ·
          refine ⟨11420233320480130386710579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7613488880320086924473719 11420233320480130386710579)
          ·
            refine ⟨17130349980720195580065869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11420233320480130386710579 17130349980720195580065869)
            ·
              refine ⟨6423881242770073342524701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17130349980720195580065869 6423881242770073342524701)
              ·
                refine ⟨2408955466038777503446763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6423881242770073342524701 2408955466038777503446763)
                ·
                  refine ⟨3613433199058166255170145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2408955466038777503446763 3613433199058166255170145)
                  ·
                    refine ⟨2710074899293624691377609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3613433199058166255170145 2710074899293624691377609)
                    ·
                      refine ⟨2032556174470218518533207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2710074899293624691377609 2032556174470218518533207)
                      ·
                        rfl

theorem cell23_3958389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_3958389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958389 prefixEnd_3958389 := by exact prefixLift 3958389
  have htrace : WordTrace (prefixWord ++ tailWord_3958389) baseStart_3958389 baseEnd_3958389 := by
    simpa [prefixWord, tailWord_3958389, baseEnd_3958389] using wordTrace_append hprefix tailTrace_3958389
  have hstable : (prefixWord ++ tailWord_3958389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958389).length < 2 ^ (prefixWord ++ tailWord_3958389).sum := by decide
  have hdescent : baseEnd_3958389 < baseStart_3958389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958432 : List Nat := [2, 1, 1, 4, 3, 3, 1, 2, 1, 3, 2]
def baseStart_3958432 : Nat := 118140960795 + 3958432 * 2 ^ 59
def prefixEnd_3958432 : Nat := 4983230072969 + 3 ^ 40 * 3958432 * 2
def baseEnd_3958432 : Nat := 2032578254138361850295509

theorem tailTrace_3958432 : CollatzResearch.WordTrace tailWord_3958432 prefixEnd_3958432 2032578254138361850295509 := by
  unfold tailWord_3958432
  simp only [CollatzResearch.WordTrace]
  refine ⟨72187937997642192603954775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96250583996856256805273033 72187937997642192603954775)
  ·
    refine ⟨108281906996463288905932163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72187937997642192603954775 108281906996463288905932163)
    ·
      refine ⟨162422860494694933358898245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108281906996463288905932163 162422860494694933358898245)
      ·
        refine ⟨30454286342755300004793421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162422860494694933358898245 30454286342755300004793421)
        ·
          refine ⟨11420357378533237501797533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30454286342755300004793421 11420357378533237501797533)
          ·
            refine ⟨4282634016949964063174075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11420357378533237501797533 4282634016949964063174075)
            ·
              refine ⟨6423951025424946094761113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4282634016949964063174075 6423951025424946094761113)
              ·
                refine ⟨4817963269068709571070835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6423951025424946094761113 4817963269068709571070835)
                ·
                  refine ⟨7226944903603064356606253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4817963269068709571070835 7226944903603064356606253)
                  ·
                    refine ⟨2710104338851149133727345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7226944903603064356606253 2710104338851149133727345)
                    ·
                      refine ⟨2032578254138361850295509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2710104338851149133727345 2032578254138361850295509)
                      ·
                        rfl

theorem cell23_3958432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_3958432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958432 prefixEnd_3958432 := by exact prefixLift 3958432
  have htrace : WordTrace (prefixWord ++ tailWord_3958432) baseStart_3958432 baseEnd_3958432 := by
    simpa [prefixWord, tailWord_3958432, baseEnd_3958432] using wordTrace_append hprefix tailTrace_3958432
  have hstable : (prefixWord ++ tailWord_3958432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958432).length < 2 ^ (prefixWord ++ tailWord_3958432).sum := by decide
  have hdescent : baseEnd_3958432 < baseStart_3958432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958445 : List Nat := [1, 5, 2, 1, 1, 1, 3, 2, 1, 4, 2]
def baseStart_3958445 : Nat := 118140960795 + 3958445 * 2 ^ 59
def prefixEnd_3958445 : Nat := 4983230072969 + 3 ^ 40 * 3958445 * 2
def baseEnd_3958445 : Nat := 2032584929386870299432949

theorem tailTrace_3958445 : CollatzResearch.WordTrace tailWord_3958445 prefixEnd_3958445 2032584929386870299432949 := by
  unfold tailWord_3958445
  simp only [CollatzResearch.WordTrace]
  refine ⟨144376350144237288428132789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96250900096158192285421859 144376350144237288428132789)
  ·
    refine ⟨13535282826022245790137449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144376350144237288428132789 13535282826022245790137449)
    ·
      refine ⟨10151462119516684342603087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13535282826022245790137449 10151462119516684342603087)
      ·
        refine ⟨15227193179275026513904631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10151462119516684342603087 15227193179275026513904631)
        ·
          refine ⟨22840789768912539770856947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15227193179275026513904631 22840789768912539770856947)
          ·
            refine ⟨34261184653368809656285421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22840789768912539770856947 34261184653368809656285421)
            ·
              refine ⟨12847944245013303621107033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34261184653368809656285421 12847944245013303621107033)
              ·
                refine ⟨9635958183759977715830275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12847944245013303621107033 9635958183759977715830275)
                ·
                  refine ⟨14453937275639966573745413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9635958183759977715830275 14453937275639966573745413)
                  ·
                    refine ⟨2710113239182493732577265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14453937275639966573745413 2710113239182493732577265)
                    ·
                      refine ⟨2032584929386870299432949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2710113239182493732577265 2032584929386870299432949)
                      ·
                        rfl

theorem cell23_3958445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_3958445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958445 prefixEnd_3958445 := by exact prefixLift 3958445
  have htrace : WordTrace (prefixWord ++ tailWord_3958445) baseStart_3958445 baseEnd_3958445 := by
    simpa [prefixWord, tailWord_3958445, baseEnd_3958445] using wordTrace_append hprefix tailTrace_3958445
  have hstable : (prefixWord ++ tailWord_3958445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958445).length < 2 ^ (prefixWord ++ tailWord_3958445).sum := by decide
  have hdescent : baseEnd_3958445 < baseStart_3958445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958462 : List Nat := [4, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2]
def baseStart_3958462 : Nat := 118140960795 + 3958462 * 2 ^ 59
def prefixEnd_3958462 : Nat := 4983230072969 + 3 ^ 40 * 3958462 * 2
def baseEnd_3958462 : Nat := 2032593658557996732920371

theorem tailTrace_3958462 : CollatzResearch.WordTrace tailWord_3958462 prefixEnd_3958462 2032593658557996732920371 := by
  unfold tailWord_3958462
  simp only [CollatzResearch.WordTrace]
  refine ⟨18047121273146962541437705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96251313456783800221001093 18047121273146962541437705)
  ·
    refine ⟨13535340954860221906078279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18047121273146962541437705 13535340954860221906078279)
    ·
      refine ⟨20303011432290332859117419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13535340954860221906078279 20303011432290332859117419)
      ·
        refine ⟨30454517148435499288676129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20303011432290332859117419 30454517148435499288676129)
        ·
          refine ⟨22840887861326624466507097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30454517148435499288676129 22840887861326624466507097)
          ·
            refine ⟨17130665895994968349880323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22840887861326624466507097 17130665895994968349880323)
            ·
              refine ⟨25695998843992452524820485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17130665895994968349880323 25695998843992452524820485)
              ·
                refine ⟨4817999783248584848403841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25695998843992452524820485 4817999783248584848403841)
                ·
                  refine ⟨3613499837436438636302881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4817999783248584848403841 3613499837436438636302881)
                  ·
                    refine ⟨2710124878077328977227161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3613499837436438636302881 2710124878077328977227161)
                    ·
                      refine ⟨2032593658557996732920371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2710124878077328977227161 2032593658557996732920371)
                      ·
                        rfl

theorem cell23_3958462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_3958462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958462 prefixEnd_3958462 := by exact prefixLift 3958462
  have htrace : WordTrace (prefixWord ++ tailWord_3958462) baseStart_3958462 baseEnd_3958462 := by
    simpa [prefixWord, tailWord_3958462, baseEnd_3958462] using wordTrace_append hprefix tailTrace_3958462
  have hstable : (prefixWord ++ tailWord_3958462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958462).length < 2 ^ (prefixWord ++ tailWord_3958462).sum := by decide
  have hdescent : baseEnd_3958462 < baseStart_3958462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958478 : List Nat := [4, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3]
def baseStart_3958478 : Nat := 118140960795 + 3958478 * 2 ^ 59
def prefixEnd_3958478 : Nat := 4983230072969 + 3 ^ 40 * 3958478 * 2
def baseEnd_3958478 : Nat := 2032601874248468670320297

theorem tailTrace_3958478 : CollatzResearch.WordTrace tailWord_3958478 prefixEnd_3958478 2032601874248468670320297 := by
  unfold tailWord_3958478
  simp only [CollatzResearch.WordTrace]
  refine ⟨18047194219139716883010511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96251702502078490042722725 18047194219139716883010511)
  ·
    refine ⟨27070791328709575324515767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18047194219139716883010511 27070791328709575324515767)
    ·
      refine ⟨40606186993064362986773651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27070791328709575324515767 40606186993064362986773651)
      ·
        refine ⟨60909280489596544480160477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40606186993064362986773651 60909280489596544480160477)
        ·
          refine ⟨22840980183598704180060179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60909280489596544480160477 22840980183598704180060179)
          ·
            refine ⟨34261470275398056270090269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22840980183598704180060179 34261470275398056270090269)
            ·
              refine ⟨12848051353274271101283851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34261470275398056270090269 12848051353274271101283851)
              ·
                refine ⟨19272077029911406651925777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12848051353274271101283851 19272077029911406651925777)
                ·
                  refine ⟨14454057772433554988944333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19272077029911406651925777 14454057772433554988944333)
                  ·
                    refine ⟨5420271664662583120854125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14454057772433554988944333 5420271664662583120854125)
                    ·
                      refine ⟨2032601874248468670320297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5420271664662583120854125 2032601874248468670320297)
                      ·
                        rfl

theorem cell23_3958478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3].length) (baseStart_3958478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958478 prefixEnd_3958478 := by exact prefixLift 3958478
  have htrace : WordTrace (prefixWord ++ tailWord_3958478) baseStart_3958478 baseEnd_3958478 := by
    simpa [prefixWord, tailWord_3958478, baseEnd_3958478] using wordTrace_append hprefix tailTrace_3958478
  have hstable : (prefixWord ++ tailWord_3958478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958478).length < 2 ^ (prefixWord ++ tailWord_3958478).sum := by decide
  have hdescent : baseEnd_3958478 < baseStart_3958478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958488 : List Nat := [2, 1, 2, 2, 3, 1, 1, 2, 2, 5, 2]
def baseStart_3958488 : Nat := 118140960795 + 3958488 * 2 ^ 59
def prefixEnd_3958488 : Nat := 4983230072969 + 3 ^ 40 * 3958488 * 2
def baseEnd_3958488 : Nat := 2032607009055013631195251

theorem tailTrace_3958488 : CollatzResearch.WordTrace tailWord_3958488 prefixEnd_3958488 2032607009055013631195251 := by
  unfold tailWord_3958488
  simp only [CollatzResearch.WordTrace]
  refine ⟨72188959241540753385974059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96251945655387671181298745 72188959241540753385974059)
  ·
    refine ⟨108283438862311130078961089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72188959241540753385974059 108283438862311130078961089)
    ·
      refine ⟨81212579146733347559220817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108283438862311130078961089 81212579146733347559220817)
      ·
        refine ⟨60909434360050010669415613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81212579146733347559220817 60909434360050010669415613)
        ·
          refine ⟨22841037885018754001030855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60909434360050010669415613 22841037885018754001030855)
          ·
            refine ⟨34261556827528131001546283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22841037885018754001030855 34261556827528131001546283)
            ·
              refine ⟨51392335241292196502319425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34261556827528131001546283 51392335241292196502319425)
              ·
                refine ⟨38544251430969147376739569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51392335241292196502319425 38544251430969147376739569)
                ·
                  refine ⟨28908188573226860532554677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38544251430969147376739569 28908188573226860532554677)
                  ·
                    refine ⟨2710142678740018174927001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28908188573226860532554677 2710142678740018174927001)
                    ·
                      refine ⟨2032607009055013631195251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2710142678740018174927001 2032607009055013631195251)
                      ·
                        rfl

theorem cell23_3958488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 2, 5, 2].length) (baseStart_3958488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958488 prefixEnd_3958488 := by exact prefixLift 3958488
  have htrace : WordTrace (prefixWord ++ tailWord_3958488) baseStart_3958488 baseEnd_3958488 := by
    simpa [prefixWord, tailWord_3958488, baseEnd_3958488] using wordTrace_append hprefix tailTrace_3958488
  have hstable : (prefixWord ++ tailWord_3958488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958488).length < 2 ^ (prefixWord ++ tailWord_3958488).sum := by decide
  have hdescent : baseEnd_3958488 < baseStart_3958488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958538 : List Nat := [3, 1, 2, 2, 1, 3, 1, 2, 1, 4, 3]
def baseStart_3958538 : Nat := 118140960795 + 3958538 * 2 ^ 59
def prefixEnd_3958538 : Nat := 4983230072969 + 3 ^ 40 * 3958538 * 2
def baseEnd_3958538 : Nat := 2032632683087738435570021

theorem tailTrace_3958538 : CollatzResearch.WordTrace tailWord_3958538 prefixEnd_3958538 2032632683087738435570021 := by
  unfold tailWord_3958538
  simp only [CollatzResearch.WordTrace]
  refine ⟨36094935533225091327817067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96253161421933576874178845 36094935533225091327817067)
  ·
    refine ⟨54142403299837636991725601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36094935533225091327817067 54142403299837636991725601)
    ·
      refine ⟨40606802474878227743794201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54142403299837636991725601 40606802474878227743794201)
      ·
        refine ⟨30455101856158670807845651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40606802474878227743794201 30455101856158670807845651)
        ·
          refine ⟨45682652784238006211768477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30455101856158670807845651 45682652784238006211768477)
          ·
            refine ⟨17130994794089252329413179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45682652784238006211768477 17130994794089252329413179)
            ·
              refine ⟨25696492191133878494119769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17130994794089252329413179 25696492191133878494119769)
              ·
                refine ⟨19272369143350408870589827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25696492191133878494119769 19272369143350408870589827)
                ·
                  refine ⟨28908553715025613305884741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19272369143350408870589827 28908553715025613305884741)
                  ·
                    refine ⟨5420353821567302494853389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28908553715025613305884741 5420353821567302494853389)
                    ·
                      refine ⟨2032632683087738435570021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5420353821567302494853389 2032632683087738435570021)
                      ·
                        rfl

theorem cell23_3958538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_3958538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958538 prefixEnd_3958538 := by exact prefixLift 3958538
  have htrace : WordTrace (prefixWord ++ tailWord_3958538) baseStart_3958538 baseEnd_3958538 := by
    simpa [prefixWord, tailWord_3958538, baseEnd_3958538] using wordTrace_append hprefix tailTrace_3958538
  have hstable : (prefixWord ++ tailWord_3958538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958538).length < 2 ^ (prefixWord ++ tailWord_3958538).sum := by decide
  have hdescent : baseEnd_3958538 < baseStart_3958538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958579 : List Nat := [1, 1, 1, 2, 7, 1, 3, 2, 1, 4]
def baseStart_3958579 : Nat := 118140960795 + 3958579 * 2 ^ 59
def prefixEnd_3958579 : Nat := 4983230072969 + 3 ^ 40 * 3958579 * 2
def baseEnd_3958579 : Nat := 677551245264857591719111

theorem tailTrace_3958579 : CollatzResearch.WordTrace tailWord_3958579 prefixEnd_3958579 677551245264857591719111 := by
  unfold tailWord_3958579
  simp only [CollatzResearch.WordTrace]
  refine ⟨144381237525751829313510791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96254158350501219542340527 144381237525751829313510791)
  ·
    refine ⟨216571856288627743970266187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144381237525751829313510791 216571856288627743970266187)
    ·
      refine ⟨324857784432941615955399281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216571856288627743970266187 324857784432941615955399281)
      ·
        refine ⟨243643338324706211966549461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324857784432941615955399281 243643338324706211966549461)
        ·
          refine ⟨5710390741985301842966003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 243643338324706211966549461 5710390741985301842966003)
          ·
            refine ⟨8565586112977952764449005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5710390741985301842966003 8565586112977952764449005)
            ·
              refine ⟨3212094792366732286668377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8565586112977952764449005 3212094792366732286668377)
              ·
                refine ⟨2409071094275049215001283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3212094792366732286668377 2409071094275049215001283)
                ·
                  refine ⟨3613606641412573822501925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2409071094275049215001283 3613606641412573822501925)
                  ·
                    refine ⟨677551245264857591719111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3613606641412573822501925 677551245264857591719111)
                    ·
                      rfl

theorem cell23_3958579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 2, 1, 4].length) (baseStart_3958579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958579 prefixEnd_3958579 := by exact prefixLift 3958579
  have htrace : WordTrace (prefixWord ++ tailWord_3958579) baseStart_3958579 baseEnd_3958579 := by
    simpa [prefixWord, tailWord_3958579, baseEnd_3958579] using wordTrace_append hprefix tailTrace_3958579
  have hstable : (prefixWord ++ tailWord_3958579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958579).length < 2 ^ (prefixWord ++ tailWord_3958579).sum := by decide
  have hdescent : baseEnd_3958579 < baseStart_3958579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958611 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 5]
def baseStart_3958611 : Nat := 118140960795 + 3958611 * 2 ^ 59
def prefixEnd_3958611 : Nat := 4983230072969 + 3 ^ 40 * 3958611 * 2
def baseEnd_3958611 : Nat := 2032670167175516649957185

theorem tailTrace_3958611 : CollatzResearch.WordTrace tailWord_3958611 prefixEnd_3958611 2032670167175516649957185 := by
  unfold tailWord_3958611
  simp only [CollatzResearch.WordTrace]
  refine ⟨144382404661635898778675687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96254936441090599185783791 144382404661635898778675687)
  ·
    refine ⟨216573606992453848168013531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144382404661635898778675687 216573606992453848168013531)
    ·
      refine ⟨324860410488680772252020297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216573606992453848168013531 324860410488680772252020297)
      ·
        refine ⟨243645307866510579189015223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324860410488680772252020297 243645307866510579189015223)
        ·
          refine ⟨365467961799765868783522835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243645307866510579189015223 365467961799765868783522835)
          ·
            refine ⟨548201942699648803175284253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365467961799765868783522835 548201942699648803175284253)
            ·
              refine ⟨205575728512368301190731595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 548201942699648803175284253 205575728512368301190731595)
              ·
                refine ⟨308363592768552451786097393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205575728512368301190731595 308363592768552451786097393)
                ·
                  refine ⟨231272694576414338839573045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 308363592768552451786097393 231272694576414338839573045)
                  ·
                    refine ⟨21681815116538844266209973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 231272694576414338839573045 21681815116538844266209973)
                    ·
                      refine ⟨2032670167175516649957185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21681815116538844266209973 2032670167175516649957185)
                      ·
                        rfl

theorem cell23_3958611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 5].length) (baseStart_3958611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958611 prefixEnd_3958611 := by exact prefixLift 3958611
  have htrace : WordTrace (prefixWord ++ tailWord_3958611) baseStart_3958611 baseEnd_3958611 := by
    simpa [prefixWord, tailWord_3958611, baseEnd_3958611] using wordTrace_append hprefix tailTrace_3958611
  have hstable : (prefixWord ++ tailWord_3958611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958611).length < 2 ^ (prefixWord ++ tailWord_3958611).sum := by decide
  have hdescent : baseEnd_3958611 < baseStart_3958611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958612 : List Nat := [2, 4, 1, 1, 3, 1, 1, 3, 2, 3, 2]
def baseStart_3958612 : Nat := 118140960795 + 3958612 * 2 ^ 59
def prefixEnd_3958612 : Nat := 4983230072969 + 3 ^ 40 * 3958612 * 2
def baseEnd_3958612 : Nat := 2032670680656171146044681

theorem tailTrace_3958612 : CollatzResearch.WordTrace tailWord_3958612 prefixEnd_3958612 2032670680656171146044681 := by
  unfold tailWord_3958612
  simp only [CollatzResearch.WordTrace]
  refine ⟨72191220567316137974731045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96254960756421517299641393 72191220567316137974731045)
  ·
    refine ⟨13535853856371775870262071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72191220567316137974731045 13535853856371775870262071)
    ·
      refine ⟨20303780784557663805393107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13535853856371775870262071 20303780784557663805393107)
      ·
        refine ⟨30455671176836495708089661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20303780784557663805393107 30455671176836495708089661)
        ·
          refine ⟨11420876691313685890533623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30455671176836495708089661 11420876691313685890533623)
          ·
            refine ⟨17131315036970528835800435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11420876691313685890533623 17131315036970528835800435)
            ·
              refine ⟨25696972555455793253700653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17131315036970528835800435 25696972555455793253700653)
              ·
                refine ⟨9636364708295922470137745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25696972555455793253700653 9636364708295922470137745)
                ·
                  refine ⟨7227273531221941852603309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9636364708295922470137745 7227273531221941852603309)
                  ·
                    refine ⟨2710227574208228194726241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7227273531221941852603309 2710227574208228194726241)
                    ·
                      refine ⟨2032670680656171146044681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2710227574208228194726241 2032670680656171146044681)
                      ·
                        rfl

theorem cell23_3958612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_3958612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958612 prefixEnd_3958612 := by exact prefixLift 3958612
  have htrace : WordTrace (prefixWord ++ tailWord_3958612) baseStart_3958612 baseEnd_3958612 := by
    simpa [prefixWord, tailWord_3958612, baseEnd_3958612] using wordTrace_append hprefix tailTrace_3958612
  have hstable : (prefixWord ++ tailWord_3958612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958612).length < 2 ^ (prefixWord ++ tailWord_3958612).sum := by decide
  have hdescent : baseEnd_3958612 < baseStart_3958612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958618 : List Nat := [3, 1, 1, 2, 1, 3, 3, 2, 1, 6]
def baseStart_3958618 : Nat := 118140960795 + 3958618 * 2 ^ 59
def prefixEnd_3958618 : Nat := 4983230072969 + 3 ^ 40 * 3958618 * 2
def baseEnd_3958618 : Nat := 677557920513366040856551

theorem tailTrace_3958618 : CollatzResearch.WordTrace tailWord_3958618 prefixEnd_3958618 677557920513366040856551 := by
  unfold tailWord_3958618
  simp only [CollatzResearch.WordTrace]
  refine ⟨36095664993152634743545127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96255106648407025982787005 36095664993152634743545127)
  ·
    refine ⟨54143497489728952115317691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36095664993152634743545127 54143497489728952115317691)
    ·
      refine ⟨81215246234593428172976537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54143497489728952115317691 81215246234593428172976537)
      ·
        refine ⟨60911434675945071129732403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81215246234593428172976537 60911434675945071129732403)
        ·
          refine ⟨91367152013917606694598605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60911434675945071129732403 91367152013917606694598605)
          ·
            refine ⟨34262682005219102510474477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91367152013917606694598605 34262682005219102510474477)
            ·
              refine ⟨12848505751957163441427929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34262682005219102510474477 12848505751957163441427929)
              ·
                refine ⟨9636379313967872581070947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12848505751957163441427929 9636379313967872581070947)
                ·
                  refine ⟨14454568970951808871606421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9636379313967872581070947 14454568970951808871606421)
                  ·
                    refine ⟨677557920513366040856551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14454568970951808871606421 677557920513366040856551)
                    ·
                      rfl

theorem cell23_3958618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 1, 6].length) (baseStart_3958618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958618 prefixEnd_3958618 := by exact prefixLift 3958618
  have htrace : WordTrace (prefixWord ++ tailWord_3958618) baseStart_3958618 baseEnd_3958618 := by
    simpa [prefixWord, tailWord_3958618, baseEnd_3958618] using wordTrace_append hprefix tailTrace_3958618
  have hstable : (prefixWord ++ tailWord_3958618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958618).length < 2 ^ (prefixWord ++ tailWord_3958618).sum := by decide
  have hdescent : baseEnd_3958618 < baseStart_3958618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958636 : List Nat := [2, 2, 1, 1, 4, 4, 2, 2, 1, 1, 3]
def baseStart_3958636 : Nat := 118140960795 + 3958636 * 2 ^ 59
def prefixEnd_3958636 : Nat := 4983230072969 + 3 ^ 40 * 3958636 * 2
def baseEnd_3958636 : Nat := 2032683004191879052144571

theorem tailTrace_3958636 : CollatzResearch.WordTrace tailWord_3958636 prefixEnd_3958636 2032683004191879052144571 := by
  unfold tailWord_3958636
  simp only [CollatzResearch.WordTrace]
  refine ⟨72191658243272664024167881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96255544324363552032223841 72191658243272664024167881)
  ·
    refine ⟨54143743682454498018125911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72191658243272664024167881 54143743682454498018125911)
    ·
      refine ⟨81215615523681747027188867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54143743682454498018125911 81215615523681747027188867)
      ·
        refine ⟨121823423285522620540783301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81215615523681747027188867 121823423285522620540783301)
        ·
          refine ⟨22841891866035491351396869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121823423285522620540783301 22841891866035491351396869)
          ·
            refine ⟨4282854724881654628386913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22841891866035491351396869 4282854724881654628386913)
            ·
              refine ⟨3212141043661240971290185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4282854724881654628386913 3212141043661240971290185)
              ·
                refine ⟨2409105782745930728467639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3212141043661240971290185 2409105782745930728467639)
                ·
                  refine ⟨3613658674118896092701459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2409105782745930728467639 3613658674118896092701459)
                  ·
                    refine ⟨5420488011178344139052189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3613658674118896092701459 5420488011178344139052189)
                    ·
                      refine ⟨2032683004191879052144571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5420488011178344139052189 2032683004191879052144571)
                      ·
                        rfl

theorem cell23_3958636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 2, 1, 1, 3].length) (baseStart_3958636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958636 prefixEnd_3958636 := by exact prefixLift 3958636
  have htrace : WordTrace (prefixWord ++ tailWord_3958636) baseStart_3958636 baseEnd_3958636 := by
    simpa [prefixWord, tailWord_3958636, baseEnd_3958636] using wordTrace_append hprefix tailTrace_3958636
  have hstable : (prefixWord ++ tailWord_3958636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958636).length < 2 ^ (prefixWord ++ tailWord_3958636).sum := by decide
  have hdescent : baseEnd_3958636 < baseStart_3958636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958642 : List Nat := [3, 2, 1, 2, 1, 1, 1, 5, 3, 2, 2]
def baseStart_3958642 : Nat := 118140960795 + 3958642 * 2 ^ 59
def prefixEnd_3958642 : Nat := 4983230072969 + 3 ^ 40 * 3958642 * 2
def baseEnd_3958642 : Nat := 2032686085075806028669543

theorem tailTrace_3958642 : CollatzResearch.WordTrace tailWord_3958642 prefixEnd_3958642 2032686085075806028669543 := by
  unfold tailWord_3958642
  simp only [CollatzResearch.WordTrace]
  refine ⟨36095883831130897768263545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96255690216349060715369453 36095883831130897768263545)
  ·
    refine ⟨27071912873348173326197659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36095883831130897768263545 27071912873348173326197659)
    ·
      refine ⟨40607869310022259989296489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27071912873348173326197659 40607869310022259989296489)
      ·
        refine ⟨30455901982516694991972367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40607869310022259989296489 30455901982516694991972367)
        ·
          refine ⟨45683852973775042487958551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30455901982516694991972367 45683852973775042487958551)
          ·
            refine ⟨68525779460662563731937827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45683852973775042487958551 68525779460662563731937827)
            ·
              refine ⟨102788669190993845597906741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68525779460662563731937827 102788669190993845597906741)
              ·
                refine ⟨9636437736655673024803757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102788669190993845597906741 9636437736655673024803757)
                ·
                  refine ⟨3613664151245877384301409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9636437736655673024803757 3613664151245877384301409)
                  ·
                    refine ⟨2710248113434408038226057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3613664151245877384301409 2710248113434408038226057)
                    ·
                      refine ⟨2032686085075806028669543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2710248113434408038226057 2032686085075806028669543)
                      ·
                        rfl

theorem cell23_3958642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_3958642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958642 prefixEnd_3958642 := by exact prefixLift 3958642
  have htrace : WordTrace (prefixWord ++ tailWord_3958642) baseStart_3958642 baseEnd_3958642 := by
    simpa [prefixWord, tailWord_3958642, baseEnd_3958642] using wordTrace_append hprefix tailTrace_3958642
  have hstable : (prefixWord ++ tailWord_3958642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958642).length < 2 ^ (prefixWord ++ tailWord_3958642).sum := by decide
  have hdescent : baseEnd_3958642 < baseStart_3958642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958645 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 5, 2, 3]
def baseStart_3958645 : Nat := 118140960795 + 3958645 * 2 ^ 59
def prefixEnd_3958645 : Nat := 4983230072969 + 3 ^ 40 * 3958645 * 2
def baseEnd_3958645 : Nat := 2032687625517769516932029

theorem tailTrace_3958645 : CollatzResearch.WordTrace tailWord_3958645 prefixEnd_3958645 2032687625517769516932029 := by
  unfold tailWord_3958645
  simp only [CollatzResearch.WordTrace]
  refine ⟨144383644743512722585413389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96255763162341815056942259 144383644743512722585413389)
  ·
    refine ⟨54143866778817270969530021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144383644743512722585413389 54143866778817270969530021)
    ·
      refine ⟨10151975021028238306786879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54143866778817270969530021 10151975021028238306786879)
      ·
        refine ⟨15227962531542357460180319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10151975021028238306786879 15227962531542357460180319)
        ·
          refine ⟨22841943797313536190270479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15227962531542357460180319 22841943797313536190270479)
          ·
            refine ⟨34262915695970304285405719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22841943797313536190270479 34262915695970304285405719)
            ·
              refine ⟨51394373543955456428108579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34262915695970304285405719 51394373543955456428108579)
              ·
                refine ⟨77091560315933184642162869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51394373543955456428108579 77091560315933184642162869)
                ·
                  refine ⟨7227333779618736060202769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77091560315933184642162869 7227333779618736060202769)
                  ·
                    refine ⟨5420500334714052045152077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7227333779618736060202769 5420500334714052045152077)
                    ·
                      refine ⟨2032687625517769516932029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5420500334714052045152077 2032687625517769516932029)
                      ·
                        rfl

theorem cell23_3958645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_3958645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958645 prefixEnd_3958645 := by exact prefixLift 3958645
  have htrace : WordTrace (prefixWord ++ tailWord_3958645) baseStart_3958645 baseEnd_3958645 := by
    simpa [prefixWord, tailWord_3958645, baseEnd_3958645] using wordTrace_append hprefix tailTrace_3958645
  have hstable : (prefixWord ++ tailWord_3958645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958645).length < 2 ^ (prefixWord ++ tailWord_3958645).sum := by decide
  have hdescent : baseEnd_3958645 < baseStart_3958645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958676 : List Nat := [2, 4, 2, 1, 1, 2, 1, 5, 1, 2, 2]
def baseStart_3958676 : Nat := 118140960795 + 3958676 * 2 ^ 59
def prefixEnd_3958676 : Nat := 4983230072969 + 3 ^ 40 * 3958676 * 2
def baseEnd_3958676 : Nat := 2032703543418058895644387

theorem tailTrace_3958676 : CollatzResearch.WordTrace tailWord_3958676 prefixEnd_3958676 2032703543418058895644387 := by
  unfold tailWord_3958676
  simp only [CollatzResearch.WordTrace]
  refine ⟨72192387703200207439895941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96256516937600276586527921 72192387703200207439895941)
  ·
    refine ⟨13536072694350038894980489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72192387703200207439895941 13536072694350038894980489)
    ·
      refine ⟨10152054520762529171235367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13536072694350038894980489 10152054520762529171235367)
      ·
        refine ⟨15228081781143793756853051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10152054520762529171235367 15228081781143793756853051)
        ·
          refine ⟨22842122671715690635279577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15228081781143793756853051 22842122671715690635279577)
          ·
            refine ⟨17131592003786767976459683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22842122671715690635279577 17131592003786767976459683)
            ·
              refine ⟨25697388005680151964689525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17131592003786767976459683 25697388005680151964689525)
              ·
                refine ⟨2409130125532514246689643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25697388005680151964689525 2409130125532514246689643)
                ·
                  refine ⟨3613695188298771370034465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2409130125532514246689643 3613695188298771370034465)
                  ·
                    refine ⟨2710271391224078527525849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3613695188298771370034465 2710271391224078527525849)
                    ·
                      refine ⟨2032703543418058895644387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2710271391224078527525849 2032703543418058895644387)
                      ·
                        rfl

theorem cell23_3958676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_3958676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958676 prefixEnd_3958676 := by exact prefixLift 3958676
  have htrace : WordTrace (prefixWord ++ tailWord_3958676) baseStart_3958676 baseEnd_3958676 := by
    simpa [prefixWord, tailWord_3958676, baseEnd_3958676] using wordTrace_append hprefix tailTrace_3958676
  have hstable : (prefixWord ++ tailWord_3958676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958676).length < 2 ^ (prefixWord ++ tailWord_3958676).sum := by decide
  have hdescent : baseEnd_3958676 < baseStart_3958676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958679 : List Nat := [1, 1, 3, 3, 1, 5, 2, 1, 1, 2, 3]
def baseStart_3958679 : Nat := 118140960795 + 3958679 * 2 ^ 59
def prefixEnd_3958679 : Nat := 4983230072969 + 3 ^ 40 * 3958679 * 2
def baseEnd_3958679 : Nat := 2032705083860022383906873

theorem tailTrace_3958679 : CollatzResearch.WordTrace tailWord_3958679 prefixEnd_3958679 2032705083860022383906873 := by
  unfold tailWord_3958679
  simp only [CollatzResearch.WordTrace]
  refine ⟨144384884825389546392151091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96256589883593030928100727 144384884825389546392151091)
  ·
    refine ⟨216577327238084319588226637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144384884825389546392151091 216577327238084319588226637)
    ·
      refine ⟨81216497714281619845584989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216577327238084319588226637 81216497714281619845584989)
      ·
        refine ⟨30456186642855607442094371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81216497714281619845584989 30456186642855607442094371)
        ·
          refine ⟨45684279964283411163141557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30456186642855607442094371 45684279964283411163141557)
          ·
            refine ⟨4282901246651569796544521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45684279964283411163141557 4282901246651569796544521)
            ·
              refine ⟨3212175934988677347408391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4282901246651569796544521 3212175934988677347408391)
              ·
                refine ⟨4818263902483016021112587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3212175934988677347408391 4818263902483016021112587)
                ·
                  refine ⟨7227395853724524031668881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4818263902483016021112587 7227395853724524031668881)
                  ·
                    refine ⟨5420546890293393023751661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7227395853724524031668881 5420546890293393023751661)
                    ·
                      refine ⟨2032705083860022383906873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5420546890293393023751661 2032705083860022383906873)
                      ·
                        rfl

theorem cell23_3958679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_3958679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958679 prefixEnd_3958679 := by exact prefixLift 3958679
  have htrace : WordTrace (prefixWord ++ tailWord_3958679) baseStart_3958679 baseEnd_3958679 := by
    simpa [prefixWord, tailWord_3958679, baseEnd_3958679] using wordTrace_append hprefix tailTrace_3958679
  have hstable : (prefixWord ++ tailWord_3958679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958679).length < 2 ^ (prefixWord ++ tailWord_3958679).sum := by decide
  have hdescent : baseEnd_3958679 < baseStart_3958679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958692 : List Nat := [2, 3, 1, 2, 1, 4, 1, 1, 4, 1, 3]
def baseStart_3958692 : Nat := 118140960795 + 3958692 * 2 ^ 59
def prefixEnd_3958692 : Nat := 4983230072969 + 3 ^ 40 * 3958692 * 2
def baseEnd_3958692 : Nat := 2032711759108530833044313

theorem tailTrace_3958692 : CollatzResearch.WordTrace tailWord_3958692 prefixEnd_3958692 2032711759108530833044313 := by
  unfold tailWord_3958692
  simp only [CollatzResearch.WordTrace]
  refine ⟨72192679487171224806187165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96256905982894966408249553 72192679487171224806187165)
  ·
    refine ⟨27072254807689209302320187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72192679487171224806187165 27072254807689209302320187)
    ·
      refine ⟨40608382211533813953480281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27072254807689209302320187 40608382211533813953480281)
      ·
        refine ⟨30456286658650360465110211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40608382211533813953480281 30456286658650360465110211)
        ·
          refine ⟨45684429987975540697665317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30456286658650360465110211 45684429987975540697665317)
          ·
            refine ⟨8565830622745413880812247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45684429987975540697665317 8565830622745413880812247)
            ·
              refine ⟨12848745934118120821218371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8565830622745413880812247 12848745934118120821218371)
              ·
                refine ⟨19273118901177181231827557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12848745934118120821218371 19273118901177181231827557)
                ·
                  refine ⟨3613709793970721480967667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19273118901177181231827557 3613709793970721480967667)
                  ·
                    refine ⟨5420564690956082221451501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3613709793970721480967667 5420564690956082221451501)
                    ·
                      refine ⟨2032711759108530833044313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5420564690956082221451501 2032711759108530833044313)
                      ·
                        rfl

theorem cell23_3958692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_3958692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958692 prefixEnd_3958692 := by exact prefixLift 3958692
  have htrace : WordTrace (prefixWord ++ tailWord_3958692) baseStart_3958692 baseEnd_3958692 := by
    simpa [prefixWord, tailWord_3958692, baseEnd_3958692] using wordTrace_append hprefix tailTrace_3958692
  have hstable : (prefixWord ++ tailWord_3958692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958692).length < 2 ^ (prefixWord ++ tailWord_3958692).sum := by decide
  have hdescent : baseEnd_3958692 < baseStart_3958692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958755 : List Nat := [1, 1, 1, 6, 1, 2, 3, 1, 7]
def baseStart_3958755 : Nat := 118140960795 + 3958755 * 2 ^ 59
def prefixEnd_3958755 : Nat := 4983230072969 + 3 ^ 40 * 3958755 * 2
def baseEnd_3958755 : Nat := 225860456487751565172947

theorem tailTrace_3958755 : CollatzResearch.WordTrace tailWord_3958755 prefixEnd_3958755 225860456487751565172947 := by
  unfold tailWord_3958755
  simp only [CollatzResearch.WordTrace]
  refine ⟨144387656773114211371917719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96258437848742807581278479 144387656773114211371917719)
  ·
    refine ⟨216581485159671317057876579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144387656773114211371917719 216581485159671317057876579)
    ·
      refine ⟨324872227739506975586814869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216581485159671317057876579 324872227739506975586814869)
      ·
        refine ⟨15228385675289389480631947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 324872227739506975586814869 15228385675289389480631947)
        ·
          refine ⟨22842578512934084220947921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15228385675289389480631947 22842578512934084220947921)
          ·
            refine ⟨17131933884700563165710941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22842578512934084220947921 17131933884700563165710941)
            ·
              refine ⟨6424475206762711187141603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17131933884700563165710941 6424475206762711187141603)
              ·
                refine ⟨9636712810144066780712405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6424475206762711187141603 9636712810144066780712405)
                ·
                  refine ⟨225860456487751565172947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9636712810144066780712405 225860456487751565172947)
                  ·
                    rfl

theorem cell23_3958755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 7].length) (baseStart_3958755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958755 prefixEnd_3958755 := by exact prefixLift 3958755
  have htrace : WordTrace (prefixWord ++ tailWord_3958755) baseStart_3958755 baseEnd_3958755 := by
    simpa [prefixWord, tailWord_3958755, baseEnd_3958755] using wordTrace_append hprefix tailTrace_3958755
  have hstable : (prefixWord ++ tailWord_3958755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958755).length < 2 ^ (prefixWord ++ tailWord_3958755).sum := by decide
  have hdescent : baseEnd_3958755 < baseStart_3958755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958766 : List Nat := [4, 1, 2, 1, 3, 2, 1, 3, 2, 2, 2]
def baseStart_3958766 : Nat := 118140960795 + 3958766 * 2 ^ 59
def prefixEnd_3958766 : Nat := 4983230072969 + 3 ^ 40 * 3958766 * 2
def baseEnd_3958766 : Nat := 2032749756676963543518973

theorem tailTrace_3958766 : CollatzResearch.WordTrace tailWord_3958766 prefixEnd_3958766 2032749756676963543518973 := by
  unfold tailWord_3958766
  simp only [CollatzResearch.WordTrace]
  refine ⟨18048507247009295031321019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96258705317382906833712101 18048507247009295031321019)
  ·
    refine ⟨27072760870513942546981529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18048507247009295031321019 27072760870513942546981529)
    ·
      refine ⟨20304570652885456910236147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27072760870513942546981529 20304570652885456910236147)
      ·
        refine ⟨30456855979328185365354221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20304570652885456910236147 30456855979328185365354221)
        ·
          refine ⟨11421320992248069512007833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30456855979328185365354221 11421320992248069512007833)
          ·
            refine ⟨8565990744186052134005875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11421320992248069512007833 8565990744186052134005875)
            ·
              refine ⟨12848986116279078201008813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8565990744186052134005875 12848986116279078201008813)
              ·
                refine ⟨4818369793604654325378305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12848986116279078201008813 4818369793604654325378305)
                ·
                  refine ⟨3613777345203490744033729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4818369793604654325378305 3613777345203490744033729)
                  ·
                    refine ⟨2710333008902618058025297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3613777345203490744033729 2710333008902618058025297)
                    ·
                      refine ⟨2032749756676963543518973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2710333008902618058025297 2032749756676963543518973)
                      ·
                        rfl

theorem cell23_3958766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_3958766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958766 prefixEnd_3958766 := by exact prefixLift 3958766
  have htrace : WordTrace (prefixWord ++ tailWord_3958766) baseStart_3958766 baseEnd_3958766 := by
    simpa [prefixWord, tailWord_3958766, baseEnd_3958766] using wordTrace_append hprefix tailTrace_3958766
  have hstable : (prefixWord ++ tailWord_3958766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958766).length < 2 ^ (prefixWord ++ tailWord_3958766).sum := by decide
  have hdescent : baseEnd_3958766 < baseStart_3958766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958768 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 3, 7]
def baseStart_3958768 : Nat := 118140960795 + 3958768 * 2 ^ 59
def prefixEnd_3958768 : Nat := 4983230072969 + 3 ^ 40 * 3958768 * 2
def baseEnd_3958768 : Nat := 677583594546090845231321

theorem tailTrace_3958768 : CollatzResearch.WordTrace tailWord_3958768 prefixEnd_3958768 677583594546090845231321 := by
  unfold tailWord_3958768
  simp only [CollatzResearch.WordTrace]
  refine ⟨72194065461033557296070479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96258753948044743061427305 72194065461033557296070479)
  ·
    refine ⟨108291098191550335944105719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72194065461033557296070479 108291098191550335944105719)
    ·
      refine ⟨162436647287325503916158579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108291098191550335944105719 162436647287325503916158579)
      ·
        refine ⟨243654970930988255874237869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162436647287325503916158579 243654970930988255874237869)
        ·
          refine ⟨91370614099120595952839201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243654970930988255874237869 91370614099120595952839201)
          ·
            refine ⟨68527960574340446964629401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91370614099120595952839201 68527960574340446964629401)
            ·
              refine ⟨51395970430755335223472051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68527960574340446964629401 51395970430755335223472051)
              ·
                refine ⟨77093955646133002835208077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51395970430755335223472051 77093955646133002835208077)
                ·
                  refine ⟨28910233367299876063203029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77093955646133002835208077 28910233367299876063203029)
                  ·
                    refine ⟨677583594546090845231321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28910233367299876063203029 677583594546090845231321)
                    ·
                      rfl

theorem cell23_3958768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 3, 7].length) (baseStart_3958768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958768 prefixEnd_3958768 := by exact prefixLift 3958768
  have htrace : WordTrace (prefixWord ++ tailWord_3958768) baseStart_3958768 baseEnd_3958768 := by
    simpa [prefixWord, tailWord_3958768, baseEnd_3958768] using wordTrace_append hprefix tailTrace_3958768
  have hstable : (prefixWord ++ tailWord_3958768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958768).length < 2 ^ (prefixWord ++ tailWord_3958768).sum := by decide
  have hdescent : baseEnd_3958768 < baseStart_3958768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958832 : List Nat := [2, 1, 1, 1, 2, 6, 1, 2, 3, 4]
def baseStart_3958832 : Nat := 118140960795 + 3958832 * 2 ^ 59
def prefixEnd_3958832 : Nat := 4983230072969 + 3 ^ 40 * 3958832 * 2
def baseEnd_3958832 : Nat := 677594548800053428431223

theorem tailTrace_3958832 : CollatzResearch.WordTrace tailWord_3958832 prefixEnd_3958832 677594548800053428431223 := by
  unfold tailWord_3958832
  simp only [CollatzResearch.WordTrace]
  refine ⟨72195232596917626761235375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96260310129223502348313833 72195232596917626761235375)
  ·
    refine ⟨108292848895376440141853063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72195232596917626761235375 108292848895376440141853063)
    ·
      refine ⟨162439273343064660212779595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108292848895376440141853063 162439273343064660212779595)
      ·
        refine ⟨243658910014596990319169393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162439273343064660212779595 243658910014596990319169393)
        ·
          refine ⟨182744182510947742739377045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243658910014596990319169393 182744182510947742739377045)
          ·
            refine ⟨8566133555200675440908299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 182744182510947742739377045 8566133555200675440908299)
            ·
              refine ⟨12849200332801013161362449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8566133555200675440908299 12849200332801013161362449)
              ·
                refine ⟨9636900249600759871021837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12849200332801013161362449 9636900249600759871021837)
                ·
                  refine ⟨3613837593600284951633189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9636900249600759871021837 3613837593600284951633189)
                  ·
                    refine ⟨677594548800053428431223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3613837593600284951633189 677594548800053428431223)
                    ·
                      rfl

theorem cell23_3958832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 3, 4].length) (baseStart_3958832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958832 prefixEnd_3958832 := by exact prefixLift 3958832
  have htrace : WordTrace (prefixWord ++ tailWord_3958832) baseStart_3958832 baseEnd_3958832 := by
    simpa [prefixWord, tailWord_3958832, baseEnd_3958832] using wordTrace_append hprefix tailTrace_3958832
  have hstable : (prefixWord ++ tailWord_3958832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958832).length < 2 ^ (prefixWord ++ tailWord_3958832).sum := by decide
  have hdescent : baseEnd_3958832 < baseStart_3958832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958836 : List Nat := [2, 5, 1, 2, 2, 2, 1, 1, 2, 5]
def baseStart_3958836 : Nat := 118140960795 + 3958836 * 2 ^ 59
def prefixEnd_3958836 : Nat := 4983230072969 + 3 ^ 40 * 3958836 * 2
def baseEnd_3958836 : Nat := 677595233440926089881217

theorem tailTrace_3958836 : CollatzResearch.WordTrace tailWord_3958836 prefixEnd_3958836 677595233440926089881217 := by
  unfold tailWord_3958836
  simp only [CollatzResearch.WordTrace]
  refine ⟨72195305542910381102808181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96260407390547174803744241 72195305542910381102808181)
  ·
    refine ⟨6768309894647848228388267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72195305542910381102808181 6768309894647848228388267)
    ·
      refine ⟨10152464841971772342582401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6768309894647848228388267 10152464841971772342582401)
      ·
        refine ⟨7614348631478829256936801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10152464841971772342582401 7614348631478829256936801)
        ·
          refine ⟨5710761473609121942702601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7614348631478829256936801 5710761473609121942702601)
          ·
            refine ⟨4283071105206841457026951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5710761473609121942702601 4283071105206841457026951)
            ·
              refine ⟨6424606657810262185540427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4283071105206841457026951 6424606657810262185540427)
              ·
                refine ⟨9636909986715393278310641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6424606657810262185540427 9636909986715393278310641)
                ·
                  refine ⟨7227682490036544958732981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9636909986715393278310641 7227682490036544958732981)
                  ·
                    refine ⟨677595233440926089881217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7227682490036544958732981 677595233440926089881217)
                    ·
                      rfl

theorem cell23_3958836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_3958836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958836 prefixEnd_3958836 := by exact prefixLift 3958836
  have htrace : WordTrace (prefixWord ++ tailWord_3958836) baseStart_3958836 baseEnd_3958836 := by
    simpa [prefixWord, tailWord_3958836, baseEnd_3958836] using wordTrace_append hprefix tailTrace_3958836
  have hstable : (prefixWord ++ tailWord_3958836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958836).length < 2 ^ (prefixWord ++ tailWord_3958836).sum := by decide
  have hdescent : baseEnd_3958836 < baseStart_3958836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958845 : List Nat := [1, 4, 1, 3, 1, 1, 2, 2, 8]
def baseStart_3958845 : Nat := 118140960795 + 3958845 * 2 ^ 59
def prefixEnd_3958845 : Nat := 4983230072969 + 3 ^ 40 * 3958845 * 2
def baseEnd_3958845 : Nat := 225865591294296526047901

theorem tailTrace_3958845 : CollatzResearch.WordTrace tailWord_3958845 prefixEnd_3958845 225865591294296526047901 := by
  unfold tailWord_3958845
  simp only [CollatzResearch.WordTrace]
  refine ⟨144390939342788156742693989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96260626228525437828462659 144390939342788156742693989)
  ·
    refine ⟨27073301126772779389255123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144390939342788156742693989 27073301126772779389255123)
    ·
      refine ⟨40609951690159169083882685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27073301126772779389255123 40609951690159169083882685)
      ·
        refine ⟨15228731883809688406456007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40609951690159169083882685 15228731883809688406456007)
        ·
          refine ⟨22843097825714532609684011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15228731883809688406456007 22843097825714532609684011)
          ·
            refine ⟨34264646738571798914526017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22843097825714532609684011 34264646738571798914526017)
            ·
              refine ⟨25698485053928849185894513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34264646738571798914526017 25698485053928849185894513)
              ·
                refine ⟨19273863790446636889420885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25698485053928849185894513 19273863790446636889420885)
                ·
                  refine ⟨225865591294296526047901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19273863790446636889420885 225865591294296526047901)
                  ·
                    rfl

theorem cell23_3958845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 8].length) (baseStart_3958845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958845 prefixEnd_3958845 := by exact prefixLift 3958845
  have htrace : WordTrace (prefixWord ++ tailWord_3958845) baseStart_3958845 baseEnd_3958845 := by
    simpa [prefixWord, tailWord_3958845, baseEnd_3958845] using wordTrace_append hprefix tailTrace_3958845
  have hstable : (prefixWord ++ tailWord_3958845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958845).length < 2 ^ (prefixWord ++ tailWord_3958845).sum := by decide
  have hdescent : baseEnd_3958845 < baseStart_3958845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958862 : List Nat := [4, 1, 1, 1, 1, 4, 3, 2, 6]
def baseStart_3958862 : Nat := 118140960795 + 3958862 * 2 ^ 59
def prefixEnd_3958862 : Nat := 4983230072969 + 3 ^ 40 * 3958862 * 2
def baseEnd_3958862 : Nat := 225866561202199463102059

theorem tailTrace_3958862 : CollatzResearch.WordTrace tailWord_3958862 prefixEnd_3958862 225866561202199463102059 := by
  unfold tailWord_3958862
  simp only [CollatzResearch.WordTrace]
  refine ⟨18048944922965821080757855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96261039589151045764041893 18048944922965821080757855)
  ·
    refine ⟨27073417384448731621136783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18048944922965821080757855 27073417384448731621136783)
    ·
      refine ⟨40610126076673097431705175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27073417384448731621136783 40610126076673097431705175)
      ·
        refine ⟨60915189115009646147557763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40610126076673097431705175 60915189115009646147557763)
        ·
          refine ⟨91372783672514469221336645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60915189115009646147557763 91372783672514469221336645)
          ·
            refine ⟨17132396938596462979000621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91372783672514469221336645 17132396938596462979000621)
            ·
              refine ⟨6424648851973673617125233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17132396938596462979000621 6424648851973673617125233)
              ·
                refine ⟨4818486638980255212843925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6424648851973673617125233 4818486638980255212843925)
                ·
                  refine ⟨225866561202199463102059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4818486638980255212843925 225866561202199463102059)
                  ·
                    rfl

theorem cell23_3958862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 6].length) (baseStart_3958862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958862 prefixEnd_3958862 := by exact prefixLift 3958862
  have htrace : WordTrace (prefixWord ++ tailWord_3958862) baseStart_3958862 baseEnd_3958862 := by
    simpa [prefixWord, tailWord_3958862, baseEnd_3958862] using wordTrace_append hprefix tailTrace_3958862
  have hstable : (prefixWord ++ tailWord_3958862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958862).length < 2 ^ (prefixWord ++ tailWord_3958862).sum := by decide
  have hdescent : baseEnd_3958862 < baseStart_3958862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958892 : List Nat := [2, 2, 1, 1, 3, 3, 1, 4, 1, 5]
def baseStart_3958892 : Nat := 118140960795 + 3958892 * 2 ^ 59
def prefixEnd_3958892 : Nat := 4983230072969 + 3 ^ 40 * 3958892 * 2
def baseEnd_3958892 : Nat := 677604818413143350181131

theorem tailTrace_3958892 : CollatzResearch.WordTrace tailWord_3958892 prefixEnd_3958892 677604818413143350181131 := by
  unfold tailWord_3958892
  simp only [CollatzResearch.WordTrace]
  refine ⟨72196326786808941884827465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96261769049078589179769953 72196326786808941884827465)
  ·
    refine ⟨54147245090106706413620599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72196326786808941884827465 54147245090106706413620599)
    ·
      refine ⟨81220867635160059620430899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54147245090106706413620599 81220867635160059620430899)
      ·
        refine ⟨121831301452740089430646349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81220867635160059620430899 121831301452740089430646349)
        ·
          refine ⟨45686738044777533536492381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121831301452740089430646349 45686738044777533536492381)
          ·
            refine ⟨17132526766791575076184643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45686738044777533536492381 17132526766791575076184643)
            ·
              refine ⟨25698790150187362614276965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17132526766791575076184643 25698790150187362614276965)
              ·
                refine ⟨4818523153160130490176931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25698790150187362614276965 4818523153160130490176931)
                ·
                  refine ⟨7227784729740195735265397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4818523153160130490176931 7227784729740195735265397)
                  ·
                    refine ⟨677604818413143350181131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7227784729740195735265397 677604818413143350181131)
                    ·
                      rfl

theorem cell23_3958892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 5].length) (baseStart_3958892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958892 prefixEnd_3958892 := by exact prefixLift 3958892
  have htrace : WordTrace (prefixWord ++ tailWord_3958892) baseStart_3958892 baseEnd_3958892 := by
    simpa [prefixWord, tailWord_3958892, baseEnd_3958892] using wordTrace_append hprefix tailTrace_3958892
  have hstable : (prefixWord ++ tailWord_3958892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958892).length < 2 ^ (prefixWord ++ tailWord_3958892).sum := by decide
  have hdescent : baseEnd_3958892 < baseStart_3958892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958946 : List Nat := [3, 3, 1, 3, 1, 1, 3, 2, 1, 1, 4]
def baseStart_3958946 : Nat := 118140960795 + 3958946 * 2 ^ 59
def prefixEnd_3958946 : Nat := 4983230072969 + 3 ^ 40 * 3958946 * 2
def baseEnd_3958946 : Nat := 2032842183194772839268145

theorem tailTrace_3958946 : CollatzResearch.WordTrace tailWord_3958946 prefixEnd_3958946 2032842183194772839268145 := by
  unfold tailWord_3958946
  simp only [CollatzResearch.WordTrace]
  refine ⟨36098655778855562748030173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96263082076948167328080461 36098655778855562748030173)
  ·
    refine ⟨13536995917070836030511315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36098655778855562748030173 13536995917070836030511315)
    ·
      refine ⟨20305493875606254045766973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13536995917070836030511315 20305493875606254045766973)
      ·
        refine ⟨7614560203352345267162615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20305493875606254045766973 7614560203352345267162615)
        ·
          refine ⟨11421840305028517900743923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7614560203352345267162615 11421840305028517900743923)
          ·
            refine ⟨17132760457542776851115885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11421840305028517900743923 17132760457542776851115885)
            ·
              refine ⟨6424785171578541319168457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17132760457542776851115885 6424785171578541319168457)
              ·
                refine ⟨4818588878683905989376343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6424785171578541319168457 4818588878683905989376343)
                ·
                  refine ⟨7227883318025858984064515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4818588878683905989376343 7227883318025858984064515)
                  ·
                    refine ⟨10841824977038788476096773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7227883318025858984064515 10841824977038788476096773)
                    ·
                      refine ⟨2032842183194772839268145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10841824977038788476096773 2032842183194772839268145)
                      ·
                        rfl

theorem cell23_3958946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_3958946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958946 prefixEnd_3958946 := by exact prefixLift 3958946
  have htrace : WordTrace (prefixWord ++ tailWord_3958946) baseStart_3958946 baseEnd_3958946 := by
    simpa [prefixWord, tailWord_3958946, baseEnd_3958946] using wordTrace_append hprefix tailTrace_3958946
  have hstable : (prefixWord ++ tailWord_3958946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958946).length < 2 ^ (prefixWord ++ tailWord_3958946).sum := by decide
  have hdescent : baseEnd_3958946 < baseStart_3958946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958980 : List Nat := [2, 3, 3, 1, 2, 2, 1, 4, 1, 2, 2]
def baseStart_3958980 : Nat := 118140960795 + 3958980 * 2 ^ 59
def prefixEnd_3958980 : Nat := 4983230072969 + 3 ^ 40 * 3958980 * 2
def baseEnd_3958980 : Nat := 2032859641537025706242989

theorem tailTrace_3958980 : CollatzResearch.WordTrace tailWord_3958980 prefixEnd_3958980 2032859641537025706242989 := by
  unfold tailWord_3958980
  simp only [CollatzResearch.WordTrace]
  refine ⟨72197931598649537399429197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96263908798199383199238929 72197931598649537399429197)
  ·
    refine ⟨27074224349493576524785949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72197931598649537399429197 27074224349493576524785949)
    ·
      refine ⟨10152834131060091196794731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27074224349493576524785949 10152834131060091196794731)
      ·
        refine ⟨15229251196590136795192097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10152834131060091196794731 15229251196590136795192097)
        ·
          refine ⟨11421938397442602596394073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15229251196590136795192097 11421938397442602596394073)
          ·
            refine ⟨8566453798081951947295555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11421938397442602596394073 8566453798081951947295555)
            ·
              refine ⟨12849680697122927920943333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8566453798081951947295555 12849680697122927920943333)
              ·
                refine ⟨2409315130710548985176875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12849680697122927920943333 2409315130710548985176875)
                ·
                  refine ⟨3613972696065823477765313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2409315130710548985176875 3613972696065823477765313)
                  ·
                    refine ⟨2710479522049367608323985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3613972696065823477765313 2710479522049367608323985)
                    ·
                      refine ⟨2032859641537025706242989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2710479522049367608323985 2032859641537025706242989)
                      ·
                        rfl

theorem cell23_3958980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_3958980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3958980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3958980 prefixEnd_3958980 := by exact prefixLift 3958980
  have htrace : WordTrace (prefixWord ++ tailWord_3958980) baseStart_3958980 baseEnd_3958980 := by
    simpa [prefixWord, tailWord_3958980, baseEnd_3958980] using wordTrace_append hprefix tailTrace_3958980
  have hstable : (prefixWord ++ tailWord_3958980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958980).length < 2 ^ (prefixWord ++ tailWord_3958980).sum := by decide
  have hdescent : baseEnd_3958980 < baseStart_3958980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959019 : List Nat := [1, 1, 1, 1, 2, 5, 1, 4, 1, 4, 2]
def baseStart_3959019 : Nat := 118140960795 + 3959019 * 2 ^ 59
def prefixEnd_3959019 : Nat := 4983230072969 + 3 ^ 40 * 3959019 * 2
def baseEnd_3959019 : Nat := 2032879667282551053655309

theorem tailTrace_3959019 : CollatzResearch.WordTrace tailWord_3959019 prefixEnd_3959019 2032879667282551053655309 := by
  unfold tailWord_3959019
  simp only [CollatzResearch.WordTrace]
  refine ⟨144397285644157784459528111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96264857096105189639685407 144397285644157784459528111)
  ·
    refine ⟨216595928466236676689292167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144397285644157784459528111 216595928466236676689292167)
    ·
      refine ⟨324893892699355015033938251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216595928466236676689292167 324893892699355015033938251)
      ·
        refine ⟨487340839049032522550907377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324893892699355015033938251 487340839049032522550907377)
        ·
          refine ⟨365505629286774391913180533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487340839049032522550907377 365505629286774391913180533)
          ·
            refine ⟨34266152745635099241860675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 365505629286774391913180533 34266152745635099241860675)
            ·
              refine ⟨51399229118452648862791013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34266152745635099241860675 51399229118452648862791013)
              ·
                refine ⟨9637355459709871661773315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51399229118452648862791013 9637355459709871661773315)
                ·
                  refine ⟨14456033189564807492659973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9637355459709871661773315 14456033189564807492659973)
                  ·
                    refine ⟨2710506223043401404873745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14456033189564807492659973 2710506223043401404873745)
                    ·
                      refine ⟨2032879667282551053655309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2710506223043401404873745 2032879667282551053655309)
                      ·
                        rfl

theorem cell23_3959019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 4, 2].length) (baseStart_3959019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959019 prefixEnd_3959019 := by exact prefixLift 3959019
  have htrace : WordTrace (prefixWord ++ tailWord_3959019) baseStart_3959019 baseEnd_3959019 := by
    simpa [prefixWord, tailWord_3959019, baseEnd_3959019] using wordTrace_append hprefix tailTrace_3959019
  have hstable : (prefixWord ++ tailWord_3959019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959019).length < 2 ^ (prefixWord ++ tailWord_3959019).sum := by decide
  have hdescent : baseEnd_3959019 < baseStart_3959019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959022 : List Nat := [4, 1, 2, 1, 1, 1, 1, 3, 1, 3, 5]
def baseStart_3959022 : Nat := 118140960795 + 3959022 * 2 ^ 59
def prefixEnd_3959022 : Nat := 4983230072969 + 3 ^ 40 * 3959022 * 2
def baseEnd_3959022 : Nat := 2032881207724514541917795

theorem tailTrace_3959022 : CollatzResearch.WordTrace tailWord_3959022 prefixEnd_3959022 2032881207724514541917795 := by
  unfold tailWord_3959022
  simp only [CollatzResearch.WordTrace]
  refine ⟨18049674382893364496485915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96264930042097943981258213 18049674382893364496485915)
  ·
    refine ⟨27074511574340046744728873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18049674382893364496485915 27074511574340046744728873)
    ·
      refine ⟨20305883680755035058546655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27074511574340046744728873 20305883680755035058546655)
      ·
        refine ⟨30458825521132552587819983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20305883680755035058546655 30458825521132552587819983)
        ·
          refine ⟨45688238281698828881729975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30458825521132552587819983 45688238281698828881729975)
          ·
            refine ⟨68532357422548243322594963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45688238281698828881729975 68532357422548243322594963)
            ·
              refine ⟨102798536133822364983892445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68532357422548243322594963 102798536133822364983892445)
              ·
                refine ⟨38549451050183386868959667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102798536133822364983892445 38549451050183386868959667)
                ·
                  refine ⟨57824176575275080303439501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38549451050183386868959667 57824176575275080303439501)
                  ·
                    refine ⟨21684066215728155113789813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57824176575275080303439501 21684066215728155113789813)
                    ·
                      refine ⟨2032881207724514541917795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21684066215728155113789813 2032881207724514541917795)
                      ·
                        rfl

theorem cell23_3959022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_3959022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959022 prefixEnd_3959022 := by exact prefixLift 3959022
  have htrace : WordTrace (prefixWord ++ tailWord_3959022) baseStart_3959022 baseEnd_3959022 := by
    simpa [prefixWord, tailWord_3959022, baseEnd_3959022] using wordTrace_append hprefix tailTrace_3959022
  have hstable : (prefixWord ++ tailWord_3959022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959022).length < 2 ^ (prefixWord ++ tailWord_3959022).sum := by decide
  have hdescent : baseEnd_3959022 < baseStart_3959022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959023 : List Nat := [1, 1, 2, 1, 6, 1, 4, 1, 1, 3, 2]
def baseStart_3959023 : Nat := 118140960795 + 3959023 * 2 ^ 59
def prefixEnd_3959023 : Nat := 4983230072969 + 3 ^ 40 * 3959023 * 2
def baseEnd_3959023 : Nat := 2032881721205169038005291

theorem tailTrace_3959023 : CollatzResearch.WordTrace tailWord_3959023 prefixEnd_3959023 2032881721205169038005291 := by
  unfold tailWord_3959023
  simp only [CollatzResearch.WordTrace]
  refine ⟨144397431536143293142673723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96264954357428862095115815 144397431536143293142673723)
  ·
    refine ⟨216596147304214939714010585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144397431536143293142673723 216596147304214939714010585)
    ·
      refine ⟨162447110478161204785507939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216596147304214939714010585 162447110478161204785507939)
      ·
        refine ⟨243670665717241807178261909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162447110478161204785507939 243670665717241807178261909)
        ·
          refine ⟨11422062455495709711481027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 243670665717241807178261909 11422062455495709711481027)
          ·
            refine ⟨17133093683243564567221541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11422062455495709711481027 17133093683243564567221541)
            ·
              refine ⟨3212455065608168356354039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17133093683243564567221541 3212455065608168356354039)
              ·
                refine ⟨4818682598412252534531059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3212455065608168356354039 4818682598412252534531059)
                ·
                  refine ⟨7228023897618378801796589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4818682598412252534531059 7228023897618378801796589)
                  ·
                    refine ⟨2710508961606892050673721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7228023897618378801796589 2710508961606892050673721)
                    ·
                      refine ⟨2032881721205169038005291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2710508961606892050673721 2032881721205169038005291)
                      ·
                        rfl

theorem cell23_3959023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 1, 3, 2].length) (baseStart_3959023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959023 prefixEnd_3959023 := by exact prefixLift 3959023
  have htrace : WordTrace (prefixWord ++ tailWord_3959023) baseStart_3959023 baseEnd_3959023 := by
    simpa [prefixWord, tailWord_3959023, baseEnd_3959023] using wordTrace_append hprefix tailTrace_3959023
  have hstable : (prefixWord ++ tailWord_3959023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959023).length < 2 ^ (prefixWord ++ tailWord_3959023).sum := by decide
  have hdescent : baseEnd_3959023 < baseStart_3959023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959070 : List Nat := [4, 3, 2, 1, 1, 1, 1, 2, 4, 2, 2]
def baseStart_3959070 : Nat := 118140960795 + 3959070 * 2 ^ 59
def prefixEnd_3959070 : Nat := 4983230072969 + 3 ^ 40 * 3959070 * 2
def baseEnd_3959070 : Nat := 2032905854795930354117575

theorem tailTrace_3959070 : CollatzResearch.WordTrace tailWord_3959070 prefixEnd_3959070 2032905854795930354117575 := by
  unfold tailWord_3959070
  simp only [CollatzResearch.WordTrace]
  refine ⟨18049893220871627521204333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96266097177982013446423109 18049893220871627521204333)
  ·
    refine ⟨6768709957826860320451625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18049893220871627521204333 6768709957826860320451625)
    ·
      refine ⟨5076532468370145240338719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6768709957826860320451625 5076532468370145240338719)
      ·
        refine ⟨7614798702555217860508079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5076532468370145240338719 7614798702555217860508079)
        ·
          refine ⟨11422198053832826790762119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7614798702555217860508079 11422198053832826790762119)
          ·
            refine ⟨17133297080749240186143179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11422198053832826790762119 17133297080749240186143179)
            ·
              refine ⟨25699945621123860279214769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17133297080749240186143179 25699945621123860279214769)
              ·
                refine ⟨19274959215842895209411077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25699945621123860279214769 19274959215842895209411077)
                ·
                  refine ⟨3614054852970542851764577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19274959215842895209411077 3614054852970542851764577)
                  ·
                    refine ⟨2710541139727907138823433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3614054852970542851764577 2710541139727907138823433)
                    ·
                      refine ⟨2032905854795930354117575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2710541139727907138823433 2032905854795930354117575)
                      ·
                        rfl

theorem cell23_3959070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_3959070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959070 prefixEnd_3959070 := by exact prefixLift 3959070
  have htrace : WordTrace (prefixWord ++ tailWord_3959070) baseStart_3959070 baseEnd_3959070 := by
    simpa [prefixWord, tailWord_3959070, baseEnd_3959070] using wordTrace_append hprefix tailTrace_3959070
  have hstable : (prefixWord ++ tailWord_3959070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959070).length < 2 ^ (prefixWord ++ tailWord_3959070).sum := by decide
  have hdescent : baseEnd_3959070 < baseStart_3959070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959076 : List Nat := [2, 3, 1, 3, 1, 2, 3, 3, 5]
def baseStart_3959076 : Nat := 118140960795 + 3959076 * 2 ^ 59
def prefixEnd_3959076 : Nat := 4983230072969 + 3 ^ 40 * 3959076 * 2
def baseEnd_3959076 : Nat := 225878770631095258960283

theorem tailTrace_3959076 : CollatzResearch.WordTrace tailWord_3959076 prefixEnd_3959076 225878770631095258960283 := by
  unfold tailWord_3959076
  simp only [CollatzResearch.WordTrace]
  refine ⟨72199682302475641597176541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96266243069967522129568721 72199682302475641597176541)
  ·
    refine ⟨27074880863428365598941203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72199682302475641597176541 27074880863428365598941203)
    ·
      refine ⟨40612321295142548398411805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27074880863428365598941203 40612321295142548398411805)
      ·
        refine ⟨15229620485678455649404427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40612321295142548398411805 15229620485678455649404427)
        ·
          refine ⟨22844430728517683474106641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15229620485678455649404427 22844430728517683474106641)
          ·
            refine ⟨17133323046388262605579981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22844430728517683474106641 17133323046388262605579981)
            ·
              refine ⟨6424996142395598477092493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17133323046388262605579981 6424996142395598477092493)
              ·
                refine ⟨2409373553398349428909685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6424996142395598477092493 2409373553398349428909685)
                ·
                  refine ⟨225878770631095258960283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2409373553398349428909685 225878770631095258960283)
                  ·
                    rfl

theorem cell23_3959076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 3, 5].length) (baseStart_3959076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959076 prefixEnd_3959076 := by exact prefixLift 3959076
  have htrace : WordTrace (prefixWord ++ tailWord_3959076) baseStart_3959076 baseEnd_3959076 := by
    simpa [prefixWord, tailWord_3959076, baseEnd_3959076] using wordTrace_append hprefix tailTrace_3959076
  have hstable : (prefixWord ++ tailWord_3959076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959076).length < 2 ^ (prefixWord ++ tailWord_3959076).sum := by decide
  have hdescent : baseEnd_3959076 < baseStart_3959076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959162 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 1, 11]
def baseStart_3959162 : Nat := 118140960795 + 3959162 * 2 ^ 59
def prefixEnd_3959162 : Nat := 4983230072969 + 3 ^ 40 * 3959162 * 2
def baseEnd_3959162 : Nat := 677651031672047998055717

theorem tailTrace_3959162 : CollatzResearch.WordTrace tailWord_3959162 prefixEnd_3959162 677651031672047998055717 := by
  unfold tailWord_3959162
  simp only [CollatzResearch.WordTrace]
  refine ⟨36100625320659929970495935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96268334188426479921322493 36100625320659929970495935)
  ·
    refine ⟨54150937980989894955743903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36100625320659929970495935 54150937980989894955743903)
    ·
      refine ⟨81226406971484842433615855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54150937980989894955743903 81226406971484842433615855)
      ·
        refine ⟨121839610457227263650423783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81226406971484842433615855 121839610457227263650423783)
        ·
          refine ⟨182759415685840895475635675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121839610457227263650423783 182759415685840895475635675)
          ·
            refine ⟨274139123528761343213453513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182759415685840895475635675 274139123528761343213453513)
            ·
              refine ⟨205604342646571007410090135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274139123528761343213453513 205604342646571007410090135)
              ·
                refine ⟨308406513969856511115135203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205604342646571007410090135 308406513969856511115135203)
                ·
                  refine ⟨462609770954784766672702805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 308406513969856511115135203 462609770954784766672702805)
                  ·
                    refine ⟨677651031672047998055717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 462609770954784766672702805 677651031672047998055717)
                    ·
                      rfl

theorem cell23_3959162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 1, 11].length) (baseStart_3959162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959162 prefixEnd_3959162 := by exact prefixLift 3959162
  have htrace : WordTrace (prefixWord ++ tailWord_3959162) baseStart_3959162 baseEnd_3959162 := by
    simpa [prefixWord, tailWord_3959162, baseEnd_3959162] using wordTrace_append hprefix tailTrace_3959162
  have hstable : (prefixWord ++ tailWord_3959162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959162).length < 2 ^ (prefixWord ++ tailWord_3959162).sum := by decide
  have hdescent : baseEnd_3959162 < baseStart_3959162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959170 : List Nat := [3, 4, 2, 1, 2, 1, 1, 2, 3, 4]
def baseStart_3959170 : Nat := 118140960795 + 3959170 * 2 ^ 59
def prefixEnd_3959170 : Nat := 4983230072969 + 3 ^ 40 * 3959170 * 2
def baseEnd_3959170 : Nat := 677652400953793320955705

theorem tailTrace_3959170 : CollatzResearch.WordTrace tailWord_3959170 prefixEnd_3959170 677652400953793320955705 := by
  unfold tailWord_3959170
  simp only [CollatzResearch.WordTrace]
  refine ⟨36100698266652684312068741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96268528711073824832183309 36100698266652684312068741)
  ·
    refine ⟨6768880924997378308512889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36100698266652684312068741 6768880924997378308512889)
    ·
      refine ⟨5076660693748033731384667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6768880924997378308512889 5076660693748033731384667)
      ·
        refine ⟨7614991040622050597077001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5076660693748033731384667 7614991040622050597077001)
        ·
          refine ⟨5711243280466537947807751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7614991040622050597077001 5711243280466537947807751)
          ·
            refine ⟨8566864920699806921711627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5711243280466537947807751 8566864920699806921711627)
            ·
              refine ⟨12850297381049710382567441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8566864920699806921711627 12850297381049710382567441)
              ·
                refine ⟨9637723035787282786925581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12850297381049710382567441 9637723035787282786925581)
                ·
                  refine ⟨3614146138420231045097093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9637723035787282786925581 3614146138420231045097093)
                  ·
                    refine ⟨677652400953793320955705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3614146138420231045097093 677652400953793320955705)
                    ·
                      rfl

theorem cell23_3959170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_3959170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959170 prefixEnd_3959170 := by exact prefixLift 3959170
  have htrace : WordTrace (prefixWord ++ tailWord_3959170) baseStart_3959170 baseEnd_3959170 := by
    simpa [prefixWord, tailWord_3959170, baseEnd_3959170] using wordTrace_append hprefix tailTrace_3959170
  have hstable : (prefixWord ++ tailWord_3959170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959170).length < 2 ^ (prefixWord ++ tailWord_3959170).sum := by decide
  have hdescent : baseEnd_3959170 < baseStart_3959170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959179 : List Nat := [1, 1, 1, 1, 4, 4, 2, 1, 3, 5]
def baseStart_3959179 : Nat := 118140960795 + 3959179 * 2 ^ 59
def prefixEnd_3959179 : Nat := 4983230072969 + 3 ^ 40 * 3959179 * 2
def baseEnd_3959179 : Nat := 677653941395756809218191

theorem tailTrace_3959179 : CollatzResearch.WordTrace tailWord_3959179 prefixEnd_3959179 677653941395756809218191 := by
  unfold tailWord_3959179
  simp only [CollatzResearch.WordTrace]
  refine ⟨144403121323578131785352591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96268747549052087856901727 144403121323578131785352591)
  ·
    refine ⟨216604681985367197678028887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144403121323578131785352591 216604681985367197678028887)
    ·
      refine ⟨324907022978050796517043331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216604681985367197678028887 324907022978050796517043331)
      ·
        refine ⟨487360534467076194775564997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324907022978050796517043331 487360534467076194775564997)
        ·
          refine ⟨91380100212576786520418437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 487360534467076194775564997 91380100212576786520418437)
          ·
            refine ⟨17133768789858147472578457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91380100212576786520418437 17133768789858147472578457)
            ·
              refine ⟨12850326592393610604433843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17133768789858147472578457 12850326592393610604433843)
              ·
                refine ⟨19275489888590415906650765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12850326592393610604433843 19275489888590415906650765)
                ·
                  refine ⟨7228308708221405964994037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19275489888590415906650765 7228308708221405964994037)
                  ·
                    refine ⟨677653941395756809218191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7228308708221405964994037 677653941395756809218191)
                    ·
                      rfl

theorem cell23_3959179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 5].length) (baseStart_3959179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959179 prefixEnd_3959179 := by exact prefixLift 3959179
  have htrace : WordTrace (prefixWord ++ tailWord_3959179) baseStart_3959179 baseEnd_3959179 := by
    simpa [prefixWord, tailWord_3959179, baseEnd_3959179] using wordTrace_append hprefix tailTrace_3959179
  have hstable : (prefixWord ++ tailWord_3959179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959179).length < 2 ^ (prefixWord ++ tailWord_3959179).sum := by decide
  have hdescent : baseEnd_3959179 < baseStart_3959179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959226 : List Nat := [3, 1, 1, 1, 2, 1, 1, 7, 2, 4]
def baseStart_3959226 : Nat := 118140960795 + 3959226 * 2 ^ 59
def prefixEnd_3959226 : Nat := 4983230072969 + 3 ^ 40 * 3959226 * 2
def baseEnd_3959226 : Nat := 677661985926010581255619

theorem tailTrace_3959226 : CollatzResearch.WordTrace tailWord_3959226 prefixEnd_3959226 677661985926010581255619 := by
  unfold tailWord_3959226
  simp only [CollatzResearch.WordTrace]
  refine ⟨36101208888601964703078383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96269890369605239208209021 36101208888601964703078383)
  ·
    refine ⟨54151813332902947054617575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36101208888601964703078383 54151813332902947054617575)
    ·
      refine ⟨81227719999354420581926363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54151813332902947054617575 81227719999354420581926363)
      ·
        refine ⟨121841579999031630872889545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81227719999354420581926363 121841579999031630872889545)
        ·
          refine ⟨91381184999273723154667159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121841579999031630872889545 91381184999273723154667159)
          ·
            refine ⟨137071777498910584732000739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91381184999273723154667159 137071777498910584732000739)
            ·
              refine ⟨205607666248365877098001109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137071777498910584732000739 205607666248365877098001109)
              ·
                refine ⟨4818929677696075244484401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 205607666248365877098001109 4818929677696075244484401)
                ·
                  refine ⟨3614197258272056433363301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4818929677696075244484401 3614197258272056433363301)
                  ·
                    refine ⟨677661985926010581255619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3614197258272056433363301 677661985926010581255619)
                    ·
                      rfl

theorem cell23_3959226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 2, 4].length) (baseStart_3959226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959226 prefixEnd_3959226 := by exact prefixLift 3959226
  have htrace : WordTrace (prefixWord ++ tailWord_3959226) baseStart_3959226 baseEnd_3959226 := by
    simpa [prefixWord, tailWord_3959226, baseEnd_3959226] using wordTrace_append hprefix tailTrace_3959226
  have hstable : (prefixWord ++ tailWord_3959226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959226).length < 2 ^ (prefixWord ++ tailWord_3959226).sum := by decide
  have hdescent : baseEnd_3959226 < baseStart_3959226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959239 : List Nat := [1, 1, 4, 1, 1, 5, 1, 9]
def baseStart_3959239 : Nat := 118140960795 + 3959239 * 2 ^ 59
def prefixEnd_3959239 : Nat := 4983230072969 + 3 ^ 40 * 3959239 * 2
def baseEnd_3959239 : Nat := 75296023445427414552011

theorem tailTrace_3959239 : CollatzResearch.WordTrace tailWord_3959239 prefixEnd_3959239 75296023445427414552011 := by
  unfold tailWord_3959239
  simp only [CollatzResearch.WordTrace]
  refine ⟨144405309703360762032536771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96270206468907174688357847 144405309703360762032536771)
  ·
    refine ⟨216607964555041143048805157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144405309703360762032536771 216607964555041143048805157)
    ·
      refine ⟨40613993354070214321650967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216607964555041143048805157 40613993354070214321650967)
      ·
        refine ⟨60920990031105321482476451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40613993354070214321650967 60920990031105321482476451)
        ·
          refine ⟨91381485046657982223714677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60920990031105321482476451 91381485046657982223714677)
          ·
            refine ⟨8567014223124185833473251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91381485046657982223714677 8567014223124185833473251)
            ·
              refine ⟨12850521334686278750209877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8567014223124185833473251 12850521334686278750209877)
              ·
                refine ⟨75296023445427414552011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12850521334686278750209877 75296023445427414552011)
                ·
                  rfl

theorem cell23_3959239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 9].length) (baseStart_3959239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959239 prefixEnd_3959239 := by exact prefixLift 3959239
  have htrace : WordTrace (prefixWord ++ tailWord_3959239) baseStart_3959239 baseEnd_3959239 := by
    simpa [prefixWord, tailWord_3959239, baseEnd_3959239] using wordTrace_append hprefix tailTrace_3959239
  have hstable : (prefixWord ++ tailWord_3959239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959239).length < 2 ^ (prefixWord ++ tailWord_3959239).sum := by decide
  have hdescent : baseEnd_3959239 < baseStart_3959239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959244 : List Nat := [2, 2, 1, 4, 4, 1, 1, 3, 1, 1, 3]
def baseStart_3959244 : Nat := 118140960795 + 3959244 * 2 ^ 59
def prefixEnd_3959244 : Nat := 4983230072969 + 3 ^ 40 * 3959244 * 2
def baseEnd_3959244 : Nat := 2032995200429812673341775

theorem tailTrace_3959244 : CollatzResearch.WordTrace tailWord_3959244 prefixEnd_3959244 2032995200429812673341775 := by
  unfold tailWord_3959244
  simp only [CollatzResearch.WordTrace]
  refine ⟨72202746034171323943234393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96270328045561765257645857 72202746034171323943234393)
  ·
    refine ⟨54152059525628492957425795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72202746034171323943234393 54152059525628492957425795)
    ·
      refine ⟨81228089288442739436138693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54152059525628492957425795 81228089288442739436138693)
      ·
        refine ⟨15230266741583013644276005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81228089288442739436138693 15230266741583013644276005)
        ·
          refine ⟨2855675014046815058301751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15230266741583013644276005 2855675014046815058301751)
          ·
            refine ⟨4283512521070222587452627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2855675014046815058301751 4283512521070222587452627)
            ·
              refine ⟨6425268781605333881178941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4283512521070222587452627 6425268781605333881178941)
              ·
                refine ⟨2409475793102000205442103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6425268781605333881178941 2409475793102000205442103)
                ·
                  refine ⟨3614213689653000308163155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2409475793102000205442103 3614213689653000308163155)
                  ·
                    refine ⟨5421320534479500462244733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3614213689653000308163155 5421320534479500462244733)
                    ·
                      refine ⟨2032995200429812673341775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5421320534479500462244733 2032995200429812673341775)
                      ·
                        rfl

theorem cell23_3959244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_3959244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959244 prefixEnd_3959244 := by exact prefixLift 3959244
  have htrace : WordTrace (prefixWord ++ tailWord_3959244) baseStart_3959244 baseEnd_3959244 := by
    simpa [prefixWord, tailWord_3959244, baseEnd_3959244] using wordTrace_append hprefix tailTrace_3959244
  have hstable : (prefixWord ++ tailWord_3959244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959244).length < 2 ^ (prefixWord ++ tailWord_3959244).sum := by decide
  have hdescent : baseEnd_3959244 < baseStart_3959244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959253 : List Nat := [1, 3, 2, 3, 1, 2, 2, 3, 1, 2, 3]
def baseStart_3959253 : Nat := 118140960795 + 3959253 * 2 ^ 59
def prefixEnd_3959253 : Nat := 4983230072969 + 3 ^ 40 * 3959253 * 2
def baseEnd_3959253 : Nat := 2032999821755703138129233

theorem tailTrace_3959253 : CollatzResearch.WordTrace tailWord_3959253 prefixEnd_3959253 2032999821755703138129233 := by
  unfold tailWord_3959253
  simp only [CollatzResearch.WordTrace]
  refine ⟨144405820325310042423546413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96270546883540028282364275 144405820325310042423546413)
  ·
    refine ⟨54152182621991265908829905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144405820325310042423546413 54152182621991265908829905)
    ·
      refine ⟨40614136966493449431622429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54152182621991265908829905 40614136966493449431622429)
      ·
        refine ⟨15230301362435043536858411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40614136966493449431622429 15230301362435043536858411)
        ·
          refine ⟨22845452043652565305287617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15230301362435043536858411 22845452043652565305287617)
          ·
            refine ⟨17134089032739423978965713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22845452043652565305287617 17134089032739423978965713)
            ·
              refine ⟨12850566774554567984224285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17134089032739423978965713 12850566774554567984224285)
              ·
                refine ⟨4818962540457962994084107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12850566774554567984224285 4818962540457962994084107)
                ·
                  refine ⟨7228443810686944491126161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4818962540457962994084107 7228443810686944491126161)
                  ·
                    refine ⟨5421332858015208368344621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7228443810686944491126161 5421332858015208368344621)
                    ·
                      refine ⟨2032999821755703138129233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5421332858015208368344621 2032999821755703138129233)
                      ·
                        rfl

theorem cell23_3959253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_3959253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959253 prefixEnd_3959253 := by exact prefixLift 3959253
  have htrace : WordTrace (prefixWord ++ tailWord_3959253) baseStart_3959253 baseEnd_3959253 := by
    simpa [prefixWord, tailWord_3959253, baseEnd_3959253] using wordTrace_append hprefix tailTrace_3959253
  have hstable : (prefixWord ++ tailWord_3959253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959253).length < 2 ^ (prefixWord ++ tailWord_3959253).sum := by decide
  have hdescent : baseEnd_3959253 < baseStart_3959253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959267 : List Nat := [1, 1, 1, 6, 3, 2, 1, 1, 3, 2, 2]
def baseStart_3959267 : Nat := 118140960795 + 3959267 * 2 ^ 59
def prefixEnd_3959267 : Nat := 4983230072969 + 3 ^ 40 * 3959267 * 2
def baseEnd_3959267 : Nat := 2033007010484866083354169

theorem tailTrace_3959267 : CollatzResearch.WordTrace tailWord_3959267 prefixEnd_3959267 2033007010484866083354169 := by
  unfold tailWord_3959267
  simp only [CollatzResearch.WordTrace]
  refine ⟨144406330947259322814556055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96270887298172881876370703 144406330947259322814556055)
  ·
    refine ⟨216609496420888984221834083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144406330947259322814556055 216609496420888984221834083)
    ·
      refine ⟨324914244631333476332751125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216609496420888984221834083 324914244631333476332751125)
      ·
        refine ⟨15230355217093756703097709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 324914244631333476332751125 15230355217093756703097709)
        ·
          refine ⟨5711383206410158763661641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15230355217093756703097709 5711383206410158763661641)
          ·
            refine ⟨4283537404807619072746231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5711383206410158763661641 4283537404807619072746231)
            ·
              refine ⟨6425306107211428609119347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4283537404807619072746231 6425306107211428609119347)
              ·
                refine ⟨9637959160817142913679021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6425306107211428609119347 9637959160817142913679021)
                ·
                  refine ⟨3614234685306428592629633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9637959160817142913679021 3614234685306428592629633)
                  ·
                    refine ⟨2710676013979821444472225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3614234685306428592629633 2710676013979821444472225)
                    ·
                      refine ⟨2033007010484866083354169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2710676013979821444472225 2033007010484866083354169)
                      ·
                        rfl

theorem cell23_3959267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_3959267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959267 prefixEnd_3959267 := by exact prefixLift 3959267
  have htrace : WordTrace (prefixWord ++ tailWord_3959267) baseStart_3959267 baseEnd_3959267 := by
    simpa [prefixWord, tailWord_3959267, baseEnd_3959267] using wordTrace_append hprefix tailTrace_3959267
  have hstable : (prefixWord ++ tailWord_3959267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959267).length < 2 ^ (prefixWord ++ tailWord_3959267).sum := by decide
  have hdescent : baseEnd_3959267 < baseStart_3959267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959277 : List Nat := [1, 5, 1, 3, 1, 3, 2, 1, 2, 4]
def baseStart_3959277 : Nat := 118140960795 + 3959277 * 2 ^ 59
def prefixEnd_3959277 : Nat := 4983230072969 + 3 ^ 40 * 3959277 * 2
def baseEnd_3959277 : Nat := 677670715097137014743041

theorem tailTrace_3959277 : CollatzResearch.WordTrace tailWord_3959277 prefixEnd_3959277 677670715097137014743041 := by
  unfold tailWord_3959277
  simp only [CollatzResearch.WordTrace]
  refine ⟨144406695677223094522420085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96271130451482063014946723 144406695677223094522420085)
  ·
    refine ⟨13538127719739665111476883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144406695677223094522420085 13538127719739665111476883)
    ·
      refine ⟨20307191579609497667215325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13538127719739665111476883 20307191579609497667215325)
      ·
        refine ⟨7615196842353561625205747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20307191579609497667215325 7615196842353561625205747)
        ·
          refine ⟨11422795263530342437808621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7615196842353561625205747 11422795263530342437808621)
          ·
            refine ⟨4283548223823878414178233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11422795263530342437808621 4283548223823878414178233)
            ·
              refine ⟨3212661167867908810633675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4283548223823878414178233 3212661167867908810633675)
              ·
                refine ⟨4818991751801863215950513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3212661167867908810633675 4818991751801863215950513)
                ·
                  refine ⟨3614243813851397411962885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4818991751801863215950513 3614243813851397411962885)
                  ·
                    refine ⟨677670715097137014743041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3614243813851397411962885 677670715097137014743041)
                    ·
                      rfl

theorem cell23_3959277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_3959277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959277 prefixEnd_3959277 := by exact prefixLift 3959277
  have htrace : WordTrace (prefixWord ++ tailWord_3959277) baseStart_3959277 baseEnd_3959277 := by
    simpa [prefixWord, tailWord_3959277, baseEnd_3959277] using wordTrace_append hprefix tailTrace_3959277
  have hstable : (prefixWord ++ tailWord_3959277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959277).length < 2 ^ (prefixWord ++ tailWord_3959277).sum := by decide
  have hdescent : baseEnd_3959277 < baseStart_3959277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959283 : List Nat := [1, 1, 1, 2, 2, 2, 5, 3, 2, 1, 3]
def baseStart_3959283 : Nat := 118140960795 + 3959283 * 2 ^ 59
def prefixEnd_3959283 : Nat := 4983230072969 + 3 ^ 40 * 3959283 * 2
def baseEnd_3959283 : Nat := 2033015226175338020754095

theorem tailTrace_3959283 : CollatzResearch.WordTrace tailWord_3959283 prefixEnd_3959283 2033015226175338020754095 := by
  unfold tailWord_3959283
  simp only [CollatzResearch.WordTrace]
  refine ⟨144406914515201357547138503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96271276343467571698092335 144406914515201357547138503)
  ·
    refine ⟨216610371772802036320707755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144406914515201357547138503 216610371772802036320707755)
    ·
      refine ⟨324915557659203054481061633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216610371772802036320707755 324915557659203054481061633)
      ·
        refine ⟨243686668244402290860796225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324915557659203054481061633 243686668244402290860796225)
        ·
          refine ⟨182765001183301718145597169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243686668244402290860796225 182765001183301718145597169)
          ·
            refine ⟨137073750887476288609197877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182765001183301718145597169 137073750887476288609197877)
            ·
              refine ⟨12850664145700902057112301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137073750887476288609197877 12850664145700902057112301)
              ·
                refine ⟨4818999054637838271417113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12850664145700902057112301 4818999054637838271417113)
                ·
                  refine ⟨3614249290978378703562835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4818999054637838271417113 3614249290978378703562835)
                  ·
                    refine ⟨5421373936467568055344253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3614249290978378703562835 5421373936467568055344253)
                    ·
                      refine ⟨2033015226175338020754095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5421373936467568055344253 2033015226175338020754095)
                      ·
                        rfl

theorem cell23_3959283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 2, 1, 3].length) (baseStart_3959283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959283 prefixEnd_3959283 := by exact prefixLift 3959283
  have htrace : WordTrace (prefixWord ++ tailWord_3959283) baseStart_3959283 baseEnd_3959283 := by
    simpa [prefixWord, tailWord_3959283, baseEnd_3959283] using wordTrace_append hprefix tailTrace_3959283
  have hstable : (prefixWord ++ tailWord_3959283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959283).length < 2 ^ (prefixWord ++ tailWord_3959283).sum := by decide
  have hdescent : baseEnd_3959283 < baseStart_3959283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959293 : List Nat := [1, 4, 1, 1, 1, 3, 3, 1, 3, 3, 2]
def baseStart_3959293 : Nat := 118140960795 + 3959293 * 2 ^ 59
def prefixEnd_3959293 : Nat := 4983230072969 + 3 ^ 40 * 3959293 * 2
def baseEnd_3959293 : Nat := 2033020360981882981629049

theorem tailTrace_3959293 : CollatzResearch.WordTrace tailWord_3959293 prefixEnd_3959293 2033020360981882981629049 := by
  unfold tailWord_3959293
  simp only [CollatzResearch.WordTrace]
  refine ⟨144407279245165129255002533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96271519496776752836668355 144407279245165129255002533)
  ·
    refine ⟨27076364858468461735312975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144407279245165129255002533 27076364858468461735312975)
    ·
      refine ⟨40614547287702692602969463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27076364858468461735312975 40614547287702692602969463)
      ·
        refine ⟨60921820931554038904454195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40614547287702692602969463 60921820931554038904454195)
        ·
          refine ⟨91382731397331058356681293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60921820931554038904454195 91382731397331058356681293)
          ·
            refine ⟨34268524273999146883755485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91382731397331058356681293 34268524273999146883755485)
            ·
              refine ⟨12850696602749680081408307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34268524273999146883755485 12850696602749680081408307)
              ·
                refine ⟨19276044904124520122112461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12850696602749680081408307 19276044904124520122112461)
                ·
                  refine ⟨7228516839046695045792173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19276044904124520122112461 7228516839046695045792173)
                  ·
                    refine ⟨2710693814642510642172065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7228516839046695045792173 2710693814642510642172065)
                    ·
                      refine ⟨2033020360981882981629049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2710693814642510642172065 2033020360981882981629049)
                      ·
                        rfl

theorem cell23_3959293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 3, 2].length) (baseStart_3959293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959293 prefixEnd_3959293 := by exact prefixLift 3959293
  have htrace : WordTrace (prefixWord ++ tailWord_3959293) baseStart_3959293 baseEnd_3959293 := by
    simpa [prefixWord, tailWord_3959293, baseEnd_3959293] using wordTrace_append hprefix tailTrace_3959293
  have hstable : (prefixWord ++ tailWord_3959293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959293).length < 2 ^ (prefixWord ++ tailWord_3959293).sum := by decide
  have hdescent : baseEnd_3959293 < baseStart_3959293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959379 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 8]
def baseStart_3959379 : Nat := 118140960795 + 3959379 * 2 ^ 59
def prefixEnd_3959379 : Nat := 4983230072969 + 3 ^ 40 * 3959379 * 2
def baseEnd_3959379 : Nat := 2033064520318169645153653

theorem tailTrace_3959379 : CollatzResearch.WordTrace tailWord_3959379 prefixEnd_3959379 2033064520318169645153653 := by
  unfold tailWord_3959379
  simp only [CollatzResearch.WordTrace]
  refine ⟨144410415922853565942633191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96273610615235710628422127 144410415922853565942633191)
  ·
    refine ⟨216615623884280348913949787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144410415922853565942633191 216615623884280348913949787)
    ·
      refine ⟨324923435826420523370924681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216615623884280348913949787 324923435826420523370924681)
      ·
        refine ⟨243692576869815392528193511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324923435826420523370924681 243692576869815392528193511)
        ·
          refine ⟨365538865304723088792290267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243692576869815392528193511 365538865304723088792290267)
          ·
            refine ⟨548308297957084633188435401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365538865304723088792290267 548308297957084633188435401)
            ·
              refine ⟨411231223467813474891326551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 548308297957084633188435401 411231223467813474891326551)
              ·
                refine ⟨616846835201720212336989827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 411231223467813474891326551 616846835201720212336989827)
                ·
                  refine ⟨925270252802580318505484741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 616846835201720212336989827 925270252802580318505484741)
                  ·
                    refine ⟨173488172400483809719778389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 925270252802580318505484741 173488172400483809719778389)
                    ·
                      refine ⟨2033064520318169645153653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 173488172400483809719778389 2033064520318169645153653)
                      ·
                        rfl

theorem cell23_3959379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 8].length) (baseStart_3959379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959379 prefixEnd_3959379 := by exact prefixLift 3959379
  have htrace : WordTrace (prefixWord ++ tailWord_3959379) baseStart_3959379 baseEnd_3959379 := by
    simpa [prefixWord, tailWord_3959379, baseEnd_3959379] using wordTrace_append hprefix tailTrace_3959379
  have hstable : (prefixWord ++ tailWord_3959379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959379).length < 2 ^ (prefixWord ++ tailWord_3959379).sum := by decide
  have hdescent : baseEnd_3959379 < baseStart_3959379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959396 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4]
def baseStart_3959396 : Nat := 118140960795 + 3959396 * 2 ^ 59
def prefixEnd_3959396 : Nat := 4983230072969 + 3 ^ 40 * 3959396 * 2
def baseEnd_3959396 : Nat := 2033073249489296078641075

theorem tailTrace_3959396 : CollatzResearch.WordTrace tailWord_3959396 prefixEnd_3959396 2033073249489296078641075 := by
  unfold tailWord_3959396
  simp only [CollatzResearch.WordTrace]
  refine ⟨72205517981895988923001021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96274023975861318564001361 72205517981895988923001021)
  ·
    refine ⟨27077069243210995846125383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72205517981895988923001021 27077069243210995846125383)
    ·
      refine ⟨40615603864816493769188075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27077069243210995846125383 40615603864816493769188075)
      ·
        refine ⟨60923405797224740653782113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40615603864816493769188075 60923405797224740653782113)
        ·
          refine ⟨45692554347918555490336585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60923405797224740653782113 45692554347918555490336585)
          ·
            refine ⟨34269415760938916617752439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45692554347918555490336585 34269415760938916617752439)
            ·
              refine ⟨51404123641408374926628659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34269415760938916617752439 51404123641408374926628659)
              ·
                refine ⟨77106185462112562389942989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51404123641408374926628659 77106185462112562389942989)
                ·
                  refine ⟨28914819548292210896228621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77106185462112562389942989 28914819548292210896228621)
                  ·
                    refine ⟨10843057330609579086085733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28914819548292210896228621 10843057330609579086085733)
                    ·
                      refine ⟨2033073249489296078641075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10843057330609579086085733 2033073249489296078641075)
                      ·
                        rfl

theorem cell23_3959396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_3959396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959396 prefixEnd_3959396 := by exact prefixLift 3959396
  have htrace : WordTrace (prefixWord ++ tailWord_3959396) baseStart_3959396 baseEnd_3959396 := by
    simpa [prefixWord, tailWord_3959396, baseEnd_3959396] using wordTrace_append hprefix tailTrace_3959396
  have hstable : (prefixWord ++ tailWord_3959396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959396).length < 2 ^ (prefixWord ++ tailWord_3959396).sum := by decide
  have hdescent : baseEnd_3959396 < baseStart_3959396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959414 : List Nat := [5, 1, 1, 2, 4, 1, 1, 3, 5]
def baseStart_3959414 : Nat := 118140960795 + 3959414 * 2 ^ 59
def prefixEnd_3959414 : Nat := 4983230072969 + 3 ^ 40 * 3959414 * 2
def baseEnd_3959414 : Nat := 225898054682341889801777

theorem tailTrace_3959414 : CollatzResearch.WordTrace tailWord_3959414 prefixEnd_3959414 225898054682341889801777 := by
  unfold tailWord_3959414
  simp only [CollatzResearch.WordTrace]
  refine ⟨9025730779857922932509831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96274461651817844613438197 9025730779857922932509831)
  ·
    refine ⟨13538596169786884398764747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9025730779857922932509831 13538596169786884398764747)
    ·
      refine ⟨20307894254680326598147121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13538596169786884398764747 20307894254680326598147121)
      ·
        refine ⟨15230920691010244948610341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20307894254680326598147121 15230920691010244948610341)
        ·
          refine ⟨2855797629564420927864439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15230920691010244948610341 2855797629564420927864439)
          ·
            refine ⟨4283696444346631391796659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2855797629564420927864439 4283696444346631391796659)
            ·
              refine ⟨6425544666519947087694989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4283696444346631391796659 6425544666519947087694989)
              ·
                refine ⟨2409579249944980157885621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6425544666519947087694989 2409579249944980157885621)
                ·
                  refine ⟨225898054682341889801777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2409579249944980157885621 225898054682341889801777)
                  ·
                    rfl

theorem cell23_3959414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_3959414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959414 prefixEnd_3959414 := by exact prefixLift 3959414
  have htrace : WordTrace (prefixWord ++ tailWord_3959414) baseStart_3959414 baseEnd_3959414 := by
    simpa [prefixWord, tailWord_3959414, baseEnd_3959414] using wordTrace_append hprefix tailTrace_3959414
  have hstable : (prefixWord ++ tailWord_3959414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959414).length < 2 ^ (prefixWord ++ tailWord_3959414).sum := by decide
  have hdescent : baseEnd_3959414 < baseStart_3959414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959503 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 4, 6, 2]
def baseStart_3959503 : Nat := 118140960795 + 3959503 * 2 ^ 59
def prefixEnd_3959503 : Nat := 4983230072969 + 3 ^ 40 * 3959503 * 2
def baseEnd_3959503 : Nat := 2033128191919327160003083

theorem tailTrace_3959503 : CollatzResearch.WordTrace tailWord_3959503 prefixEnd_3959503 2033128191919327160003083 := by
  unfold tailWord_3959503
  simp only [CollatzResearch.WordTrace]
  refine ⟨144414938574404335120147163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96276625716269556746764775 144414938574404335120147163)
  ·
    refine ⟨216622407861606502680220745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144414938574404335120147163 216622407861606502680220745)
    ·
      refine ⟨162466805896204877010165559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216622407861606502680220745 162466805896204877010165559)
      ·
        refine ⟨243700208844307315515248339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162466805896204877010165559 243700208844307315515248339)
        ·
          refine ⟨365550313266460973272872509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243700208844307315515248339 365550313266460973272872509)
          ·
            refine ⟨137081367474922864977327191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 365550313266460973272872509 137081367474922864977327191)
            ·
              refine ⟨205622051212384297465990787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137081367474922864977327191 205622051212384297465990787)
              ·
                refine ⟨308433076818576446198986181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205622051212384297465990787 308433076818576446198986181)
                ·
                  refine ⟨57831201903483083662309909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 308433076818576446198986181 57831201903483083662309909)
                  ·
                    refine ⟨2710837589225769546670777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 57831201903483083662309909 2710837589225769546670777)
                    ·
                      refine ⟨2033128191919327160003083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2710837589225769546670777 2033128191919327160003083)
                      ·
                        rfl

theorem cell23_3959503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 6, 2].length) (baseStart_3959503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959503 prefixEnd_3959503 := by exact prefixLift 3959503
  have htrace : WordTrace (prefixWord ++ tailWord_3959503) baseStart_3959503 baseEnd_3959503 := by
    simpa [prefixWord, tailWord_3959503, baseEnd_3959503] using wordTrace_append hprefix tailTrace_3959503
  have hstable : (prefixWord ++ tailWord_3959503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959503).length < 2 ^ (prefixWord ++ tailWord_3959503).sum := by decide
  have hdescent : baseEnd_3959503 < baseStart_3959503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959513 : List Nat := [1, 2, 1, 2, 3, 2, 4, 1, 1, 6]
def baseStart_3959513 : Nat := 118140960795 + 3959513 * 2 ^ 59
def prefixEnd_3959513 : Nat := 4983230072969 + 3 ^ 40 * 3959513 * 2
def baseEnd_3959513 : Nat := 677711108908624040292679

theorem tailTrace_3959513 : CollatzResearch.WordTrace tailWord_3959513 prefixEnd_3959513 677711108908624040292679 := by
  unfold tailWord_3959513
  simp only [CollatzResearch.WordTrace]
  refine ⟨144415303304368106828011193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96276868869578737885340795 144415303304368106828011193)
  ·
    refine ⟨108311477478276080121008395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144415303304368106828011193 108311477478276080121008395)
    ·
      refine ⟨162467216217414120181512593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108311477478276080121008395 162467216217414120181512593)
      ·
        refine ⟨121850412163060590136134445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162467216217414120181512593 121850412163060590136134445)
        ·
          refine ⟨45693904561147721301050417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121850412163060590136134445 45693904561147721301050417)
          ·
            refine ⟨34270428420860790975787813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45693904561147721301050417 34270428420860790975787813)
            ·
              refine ⟨6425705328911398307960215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34270428420860790975787813 6425705328911398307960215)
              ·
                refine ⟨9638557993367097461940323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6425705328911398307960215 9638557993367097461940323)
                ·
                  refine ⟨14457836990050646192910485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9638557993367097461940323 14457836990050646192910485)
                  ·
                    refine ⟨677711108908624040292679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14457836990050646192910485 677711108908624040292679)
                    ·
                      rfl

theorem cell23_3959513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 6].length) (baseStart_3959513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959513 prefixEnd_3959513 := by exact prefixLift 3959513
  have htrace : WordTrace (prefixWord ++ tailWord_3959513) baseStart_3959513 baseEnd_3959513 := by
    simpa [prefixWord, tailWord_3959513, baseEnd_3959513] using wordTrace_append hprefix tailTrace_3959513
  have hstable : (prefixWord ++ tailWord_3959513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959513).length < 2 ^ (prefixWord ++ tailWord_3959513).sum := by decide
  have hdescent : baseEnd_3959513 < baseStart_3959513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959554 : List Nat := [3, 4, 1, 1, 1, 2, 1, 3, 3, 2, 2]
def baseStart_3959554 : Nat := 118140960795 + 3959554 * 2 ^ 59
def prefixEnd_3959554 : Nat := 4983230072969 + 3 ^ 40 * 3959554 * 2
def baseEnd_3959554 : Nat := 2033154379432706460465349

theorem tailTrace_3959554 : CollatzResearch.WordTrace tailWord_3959554 prefixEnd_3959554 2033154379432706460465349 := by
  unfold tailWord_3959554
  simp only [CollatzResearch.WordTrace]
  refine ⟨36104199674304892707563429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96277865798146380553502477 36104199674304892707563429)
  ·
    refine ⟨6769537438932167382668143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36104199674304892707563429 6769537438932167382668143)
    ·
      refine ⟨10154306158398251074002215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6769537438932167382668143 10154306158398251074002215)
      ·
        refine ⟨15231459237597376611003323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10154306158398251074002215 15231459237597376611003323)
        ·
          refine ⟨22847188856396064916504985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15231459237597376611003323 22847188856396064916504985)
          ·
            refine ⟨17135391642297048687378739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22847188856396064916504985 17135391642297048687378739)
            ·
              refine ⟨25703087463445573031068109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17135391642297048687378739 25703087463445573031068109)
              ·
                refine ⟨9638657798792089886650541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25703087463445573031068109 9638657798792089886650541)
                ·
                  refine ⟨3614496674547033707493953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9638657798792089886650541 3614496674547033707493953)
                  ·
                    refine ⟨2710872505910275280620465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3614496674547033707493953 2710872505910275280620465)
                    ·
                      refine ⟨2033154379432706460465349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2710872505910275280620465 2033154379432706460465349)
                      ·
                        rfl

theorem cell23_3959554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_3959554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959554 prefixEnd_3959554 := by exact prefixLift 3959554
  have htrace : WordTrace (prefixWord ++ tailWord_3959554) baseStart_3959554 baseEnd_3959554 := by
    simpa [prefixWord, tailWord_3959554, baseEnd_3959554] using wordTrace_append hprefix tailTrace_3959554
  have hstable : (prefixWord ++ tailWord_3959554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959554).length < 2 ^ (prefixWord ++ tailWord_3959554).sum := by decide
  have hdescent : baseEnd_3959554 < baseStart_3959554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959583 : List Nat := [1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 5]
def baseStart_3959583 : Nat := 118140960795 + 3959583 * 2 ^ 59
def prefixEnd_3959583 : Nat := 4983230072969 + 3 ^ 40 * 3959583 * 2
def baseEnd_3959583 : Nat := 2033169270371686847002715

theorem tailTrace_3959583 : CollatzResearch.WordTrace tailWord_3959583 prefixEnd_3959583 2033169270371686847002715 := by
  unfold tailWord_3959583
  simp only [CollatzResearch.WordTrace]
  refine ⟨144417856414114508783059403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96278570942743005855372935 144417856414114508783059403)
  ·
    refine ⟨216626784621171763174589105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144417856414114508783059403 216626784621171763174589105)
    ·
      refine ⟨162470088465878822380941829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216626784621171763174589105 162470088465878822380941829)
      ·
        refine ⟨30463141587352279196426593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162470088465878822380941829 30463141587352279196426593)
        ·
          refine ⟨22847356190514209397319945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30463141587352279196426593 22847356190514209397319945)
          ·
            refine ⟨17135517142885657047989959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22847356190514209397319945 17135517142885657047989959)
            ·
              refine ⟨25703275714328485571984939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17135517142885657047989959 25703275714328485571984939)
              ·
                refine ⟨38554913571492728357977409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25703275714328485571984939 38554913571492728357977409)
                ·
                  refine ⟨28916185178619546268483057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38554913571492728357977409 28916185178619546268483057)
                  ·
                    refine ⟨21687138883964659701362293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28916185178619546268483057 21687138883964659701362293)
                    ·
                      refine ⟨2033169270371686847002715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21687138883964659701362293 2033169270371686847002715)
                      ·
                        rfl

theorem cell23_3959583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_3959583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959583 prefixEnd_3959583 := by exact prefixLift 3959583
  have htrace : WordTrace (prefixWord ++ tailWord_3959583) baseStart_3959583 baseEnd_3959583 := by
    simpa [prefixWord, tailWord_3959583, baseEnd_3959583] using wordTrace_append hprefix tailTrace_3959583
  have hstable : (prefixWord ++ tailWord_3959583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959583).length < 2 ^ (prefixWord ++ tailWord_3959583).sum := by decide
  have hdescent : baseEnd_3959583 < baseStart_3959583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959588 : List Nat := [2, 3, 1, 3, 3, 2, 1, 3, 1, 2, 2]
def baseStart_3959588 : Nat := 118140960795 + 3959588 * 2 ^ 59
def prefixEnd_3959588 : Nat := 4983230072969 + 3 ^ 40 * 3959588 * 2
def baseEnd_3959588 : Nat := 2033171837774959327440193

theorem tailTrace_3959588 : CollatzResearch.WordTrace tailWord_3959588 prefixEnd_3959588 2033171837774959327440193 := by
  unfold tailWord_3959588
  simp only [CollatzResearch.WordTrace]
  refine ⟨72209019389548197318495709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96278692519397596424660945 72209019389548197318495709)
  ·
    refine ⟨27078382271080573994435891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72209019389548197318495709 27078382271080573994435891)
    ·
      refine ⟨40617573406620860991653837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27078382271080573994435891 40617573406620860991653837)
      ·
        refine ⟨15231590027482822871870189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40617573406620860991653837 15231590027482822871870189)
        ·
          refine ⟨5711846260306058576951321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15231590027482822871870189 5711846260306058576951321)
          ·
            refine ⟨4283884695229543932713491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5711846260306058576951321 4283884695229543932713491)
            ·
              refine ⟨6425827042844315899070237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4283884695229543932713491 6425827042844315899070237)
              ·
                refine ⟨2409685141066618462151339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6425827042844315899070237 2409685141066618462151339)
                ·
                  refine ⟨3614527711599927693227009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2409685141066618462151339 3614527711599927693227009)
                  ·
                    refine ⟨2710895783699945769920257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3614527711599927693227009 2710895783699945769920257)
                    ·
                      refine ⟨2033171837774959327440193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2710895783699945769920257 2033171837774959327440193)
                      ·
                        rfl

theorem cell23_3959588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_3959588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959588 prefixEnd_3959588 := by exact prefixLift 3959588
  have htrace : WordTrace (prefixWord ++ tailWord_3959588) baseStart_3959588 baseEnd_3959588 := by
    simpa [prefixWord, tailWord_3959588, baseEnd_3959588] using wordTrace_append hprefix tailTrace_3959588
  have hstable : (prefixWord ++ tailWord_3959588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959588).length < 2 ^ (prefixWord ++ tailWord_3959588).sum := by decide
  have hdescent : baseEnd_3959588 < baseStart_3959588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959623 : List Nat := [1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 4]
def baseStart_3959623 : Nat := 118140960795 + 3959623 * 2 ^ 59
def prefixEnd_3959623 : Nat := 4983230072969 + 3 ^ 40 * 3959623 * 2
def baseEnd_3959623 : Nat := 2033189809597866690502531

theorem tailTrace_3959623 : CollatzResearch.WordTrace tailWord_3959623 prefixEnd_3959623 2033189809597866690502531 := by
  unfold tailWord_3959623
  simp only [CollatzResearch.WordTrace]
  refine ⟨144419315333969595614515523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96279543555979730409677015 144419315333969595614515523)
  ·
    refine ⟨216628973000954393421773285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144419315333969595614515523 216628973000954393421773285)
    ·
      refine ⟨40617932437678948766582491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216628973000954393421773285 40617932437678948766582491)
      ·
        refine ⟨60926898656518423149873737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40617932437678948766582491 60926898656518423149873737)
        ·
          refine ⟨45695173992388817362405303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60926898656518423149873737 45695173992388817362405303)
          ·
            refine ⟨68542760988583226043607955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45695173992388817362405303 68542760988583226043607955)
            ·
              refine ⟨102814141482874839065411933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68542760988583226043607955 102814141482874839065411933)
              ·
                refine ⟨38555303056078064649529475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102814141482874839065411933 38555303056078064649529475)
                ·
                  refine ⟨57832954584117096974294213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38555303056078064649529475 57832954584117096974294213)
                  ·
                    refine ⟨10843678984521955682680165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57832954584117096974294213 10843678984521955682680165)
                    ·
                      refine ⟨2033189809597866690502531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10843678984521955682680165 2033189809597866690502531)
                      ·
                        rfl

theorem cell23_3959623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_3959623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959623 prefixEnd_3959623 := by exact prefixLift 3959623
  have htrace : WordTrace (prefixWord ++ tailWord_3959623) baseStart_3959623 baseEnd_3959623 := by
    simpa [prefixWord, tailWord_3959623, baseEnd_3959623] using wordTrace_append hprefix tailTrace_3959623
  have hstable : (prefixWord ++ tailWord_3959623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959623).length < 2 ^ (prefixWord ++ tailWord_3959623).sum := by decide
  have hdescent : baseEnd_3959623 < baseStart_3959623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959644 : List Nat := [2, 2, 4, 2, 1, 2, 1, 2, 1, 4, 2]
def baseStart_3959644 : Nat := 118140960795 + 3959644 * 2 ^ 59
def prefixEnd_3959644 : Nat := 4983230072969 + 3 ^ 40 * 3959644 * 2
def baseEnd_3959644 : Nat := 2033200592691611108339935

theorem tailTrace_3959644 : CollatzResearch.WordTrace tailWord_3959644 prefixEnd_3959644 2033200592691611108339935 := by
  unfold tailWord_3959644
  simp only [CollatzResearch.WordTrace]
  refine ⟨72210040633446758100514993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96280054177929010800686657 72210040633446758100514993)
  ·
    refine ⟨54157530475085068575386245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72210040633446758100514993 54157530475085068575386245)
    ·
      refine ⟨10154536964078450357884921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54157530475085068575386245 10154536964078450357884921)
      ·
        refine ⟨7615902723058837768413691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10154536964078450357884921 7615902723058837768413691)
        ·
          refine ⟨11423854084588256652620537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7615902723058837768413691 11423854084588256652620537)
          ·
            refine ⟨8567890563441192489465403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11423854084588256652620537 8567890563441192489465403)
            ·
              refine ⟨12851835845161788734198105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8567890563441192489465403 12851835845161788734198105)
              ·
                refine ⟨9638876883871341550648579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12851835845161788734198105 9638876883871341550648579)
                ·
                  refine ⟨14458315325807012325972869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9638876883871341550648579 14458315325807012325972869)
                  ·
                    refine ⟨2710934123588814811119913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14458315325807012325972869 2710934123588814811119913)
                    ·
                      refine ⟨2033200592691611108339935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2710934123588814811119913 2033200592691611108339935)
                      ·
                        rfl

theorem cell23_3959644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_3959644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959644 prefixEnd_3959644 := by exact prefixLift 3959644
  have htrace : WordTrace (prefixWord ++ tailWord_3959644) baseStart_3959644 baseEnd_3959644 := by
    simpa [prefixWord, tailWord_3959644, baseEnd_3959644] using wordTrace_append hprefix tailTrace_3959644
  have hstable : (prefixWord ++ tailWord_3959644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959644).length < 2 ^ (prefixWord ++ tailWord_3959644).sum := by decide
  have hdescent : baseEnd_3959644 < baseStart_3959644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959660 : List Nat := [2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 3]
def baseStart_3959660 : Nat := 118140960795 + 3959660 * 2 ^ 59
def prefixEnd_3959660 : Nat := 4983230072969 + 3 ^ 40 * 3959660 * 2
def baseEnd_3959660 : Nat := 2033208808382083045739861

theorem tailTrace_3959660 : CollatzResearch.WordTrace tailWord_3959660 prefixEnd_3959660 2033208808382083045739861 := by
  unfold tailWord_3959660
  simp only [CollatzResearch.WordTrace]
  refine ⟨72210332417417775466806217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96280443223223700622408289 72210332417417775466806217)
  ·
    refine ⟨54157749313063331600104663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72210332417417775466806217 54157749313063331600104663)
    ·
      refine ⟨81236623969594997400156995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54157749313063331600104663 81236623969594997400156995)
      ·
        refine ⟨121854935954392496100235493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81236623969594997400156995 121854935954392496100235493)
        ·
          refine ⟨22847800491448593018794155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121854935954392496100235493 22847800491448593018794155)
          ·
            refine ⟨34271700737172889528191233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22847800491448593018794155 34271700737172889528191233)
            ·
              refine ⟨25703775552879667146143425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34271700737172889528191233 25703775552879667146143425)
              ·
                refine ⟨19277831664659750359607569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25703775552879667146143425 19277831664659750359607569)
                ·
                  refine ⟨14458373748494812769705677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19277831664659750359607569 14458373748494812769705677)
                  ·
                    refine ⟨5421890155685554788639629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14458373748494812769705677 5421890155685554788639629)
                    ·
                      refine ⟨2033208808382083045739861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5421890155685554788639629 2033208808382083045739861)
                      ·
                        rfl

theorem cell23_3959660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 3].length) (baseStart_3959660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959660 prefixEnd_3959660 := by exact prefixLift 3959660
  have htrace : WordTrace (prefixWord ++ tailWord_3959660) baseStart_3959660 baseEnd_3959660 := by
    simpa [prefixWord, tailWord_3959660, baseEnd_3959660] using wordTrace_append hprefix tailTrace_3959660
  have hstable : (prefixWord ++ tailWord_3959660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959660).length < 2 ^ (prefixWord ++ tailWord_3959660).sum := by decide
  have hdescent : baseEnd_3959660 < baseStart_3959660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959667 : List Nat := [1, 1, 1, 2, 2, 1, 8, 2, 5]
def baseStart_3959667 : Nat := 118140960795 + 3959667 * 2 ^ 59
def prefixEnd_3959667 : Nat := 4983230072969 + 3 ^ 40 * 3959667 * 2
def baseEnd_3959667 : Nat := 225912489194073835372481

theorem tailTrace_3959667 : CollatzResearch.WordTrace tailWord_3959667 prefixEnd_3959667 225912489194073835372481 := by
  unfold tailWord_3959667
  simp only [CollatzResearch.WordTrace]
  refine ⟨144420920145810191129117255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96280613430540127419411503 144420920145810191129117255)
  ·
    refine ⟨216631380218715286693675883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144420920145810191129117255 216631380218715286693675883)
    ·
      refine ⟨324947070328072930040513825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216631380218715286693675883 324947070328072930040513825)
      ·
        refine ⟨243710302746054697530385369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324947070328072930040513825 243710302746054697530385369)
        ·
          refine ⟨182782727059541023147789027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243710302746054697530385369 182782727059541023147789027)
          ·
            refine ⟨274174090589311534721683541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182782727059541023147789027 274174090589311534721683541)
            ·
              refine ⟨3212977624093494547519729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 274174090589311534721683541 3212977624093494547519729)
              ·
                refine ⟨2409733218070120910639797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3212977624093494547519729 2409733218070120910639797)
                ·
                  refine ⟨225912489194073835372481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2409733218070120910639797 225912489194073835372481)
                  ·
                    rfl

theorem cell23_3959667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 2, 5].length) (baseStart_3959667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959667 prefixEnd_3959667 := by exact prefixLift 3959667
  have htrace : WordTrace (prefixWord ++ tailWord_3959667) baseStart_3959667 baseEnd_3959667 := by
    simpa [prefixWord, tailWord_3959667, baseEnd_3959667] using wordTrace_append hprefix tailTrace_3959667
  have hstable : (prefixWord ++ tailWord_3959667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959667).length < 2 ^ (prefixWord ++ tailWord_3959667).sum := by decide
  have hdescent : baseEnd_3959667 < baseStart_3959667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959723 : List Nat := [1, 1, 1, 1, 2, 1, 1, 7, 8]
def baseStart_3959723 : Nat := 118140960795 + 3959723 * 2 ^ 59
def prefixEnd_3959723 : Nat := 4983230072969 + 3 ^ 40 * 3959723 * 2
def baseEnd_3959723 : Nat := 225915684184812922139119

theorem tailTrace_3959723 : CollatzResearch.WordTrace tailWord_3959723 prefixEnd_3959723 225915684184812922139119 := by
  unfold tailWord_3959723
  simp only [CollatzResearch.WordTrace]
  refine ⟨144422962633607312693155823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96281975089071541795437215 144422962633607312693155823)
  ·
    refine ⟨216634443950410969039733735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144422962633607312693155823 216634443950410969039733735)
    ·
      refine ⟨324951665925616453559600603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216634443950410969039733735 324951665925616453559600603)
      ·
        refine ⟨487427498888424680339400905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324951665925616453559600603 487427498888424680339400905)
        ·
          refine ⟨365570624166318510254550679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487427498888424680339400905 365570624166318510254550679)
          ·
            refine ⟨548355936249477765381826019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365570624166318510254550679 548355936249477765381826019)
            ·
              refine ⟨822533904374216648072739029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548355936249477765381826019 822533904374216648072739029)
              ·
                refine ⟨19278138383770702689204821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 822533904374216648072739029 19278138383770702689204821)
                ·
                  refine ⟨225915684184812922139119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19278138383770702689204821 225915684184812922139119)
                  ·
                    rfl

theorem cell23_3959723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 8].length) (baseStart_3959723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959723 prefixEnd_3959723 := by exact prefixLift 3959723
  have htrace : WordTrace (prefixWord ++ tailWord_3959723) baseStart_3959723 baseEnd_3959723 := by
    simpa [prefixWord, tailWord_3959723, baseEnd_3959723] using wordTrace_append hprefix tailTrace_3959723
  have hstable : (prefixWord ++ tailWord_3959723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959723).length < 2 ^ (prefixWord ++ tailWord_3959723).sum := by decide
  have hdescent : baseEnd_3959723 < baseStart_3959723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959784 : List Nat := [2, 1, 4, 1, 1, 1, 5, 1, 3, 1, 3]
def baseStart_3959784 : Nat := 118140960795 + 3959784 * 2 ^ 59
def prefixEnd_3959784 : Nat := 4983230072969 + 3 ^ 40 * 3959784 * 2
def baseEnd_3959784 : Nat := 2033272479983240560589291

theorem tailTrace_3959784 : CollatzResearch.WordTrace tailWord_3959784 prefixEnd_3959784 2033272479983240560589291 := by
  unfold tailWord_3959784
  simp only [CollatzResearch.WordTrace]
  refine ⟨72212593743193160055563203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96283458324257546740750937 72212593743193160055563203)
  ·
    refine ⟨108318890614789740083344805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72212593743193160055563203 108318890614789740083344805)
    ·
      refine ⟨20309791990273076265627151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108318890614789740083344805 20309791990273076265627151)
      ·
        refine ⟨30464687985409614398440727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20309791990273076265627151 30464687985409614398440727)
        ·
          refine ⟨45697031978114421597661091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30464687985409614398440727 45697031978114421597661091)
          ·
            refine ⟨68545547967171632396491637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45697031978114421597661091 68545547967171632396491637)
            ·
              refine ⟨6426145121922340537171091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68545547967171632396491637 6426145121922340537171091)
              ·
                refine ⟨9639217682883510805756637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6426145121922340537171091 9639217682883510805756637)
                ·
                  refine ⟨3614706631081316552158739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9639217682883510805756637 3614706631081316552158739)
                  ·
                    refine ⟨5422059946621974828238109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3614706631081316552158739 5422059946621974828238109)
                    ·
                      refine ⟨2033272479983240560589291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5422059946621974828238109 2033272479983240560589291)
                      ·
                        rfl

theorem cell23_3959784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_3959784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959784 prefixEnd_3959784 := by exact prefixLift 3959784
  have htrace : WordTrace (prefixWord ++ tailWord_3959784) baseStart_3959784 baseEnd_3959784 := by
    simpa [prefixWord, tailWord_3959784, baseEnd_3959784] using wordTrace_append hprefix tailTrace_3959784
  have hstable : (prefixWord ++ tailWord_3959784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959784).length < 2 ^ (prefixWord ++ tailWord_3959784).sum := by decide
  have hdescent : baseEnd_3959784 < baseStart_3959784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959800 : List Nat := [2, 1, 2, 1, 1, 3, 1, 5, 1, 6]
def baseStart_3959800 : Nat := 118140960795 + 3959800 * 2 ^ 59
def prefixEnd_3959800 : Nat := 4983230072969 + 3 ^ 40 * 3959800 * 2
def baseEnd_3959800 : Nat := 677760231891237499329739

theorem tailTrace_3959800 : CollatzResearch.WordTrace tailWord_3959800 prefixEnd_3959800 677760231891237499329739 := by
  unfold tailWord_3959800
  simp only [CollatzResearch.WordTrace]
  refine ⟨72212885527164177421854427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96283847369552236562472569 72212885527164177421854427)
  ·
    refine ⟨108319328290746266132781641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72212885527164177421854427 108319328290746266132781641)
    ·
      refine ⟨81239496218059699599586231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108319328290746266132781641 81239496218059699599586231)
      ·
        refine ⟨121859244327089549399379347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81239496218059699599586231 121859244327089549399379347)
        ·
          refine ⟨182788866490634324099069021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121859244327089549399379347 182788866490634324099069021)
          ·
            refine ⟨68545824933987871537150883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182788866490634324099069021 68545824933987871537150883)
            ·
              refine ⟨102818737400981807305726325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68545824933987871537150883 102818737400981807305726325)
              ·
                refine ⟨9639256631342044434911843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102818737400981807305726325 9639256631342044434911843)
                ·
                  refine ⟨14458884947013066652367765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9639256631342044434911843 14458884947013066652367765)
                  ·
                    refine ⟨677760231891237499329739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14458884947013066652367765 677760231891237499329739)
                    ·
                      rfl

theorem cell23_3959800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 1, 6].length) (baseStart_3959800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959800 prefixEnd_3959800 := by exact prefixLift 3959800
  have htrace : WordTrace (prefixWord ++ tailWord_3959800) baseStart_3959800 baseEnd_3959800 := by
    simpa [prefixWord, tailWord_3959800, baseEnd_3959800] using wordTrace_append hprefix tailTrace_3959800
  have hstable : (prefixWord ++ tailWord_3959800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959800).length < 2 ^ (prefixWord ++ tailWord_3959800).sum := by decide
  have hdescent : baseEnd_3959800 < baseStart_3959800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959804 : List Nat := [2, 2, 2, 1, 2, 5, 1, 2, 1, 5]
def baseStart_3959804 : Nat := 118140960795 + 3959804 * 2 ^ 59
def prefixEnd_3959804 : Nat := 4983230072969 + 3 ^ 40 * 3959804 * 2
def baseEnd_3959804 : Nat := 677760916532110160779733

theorem tailTrace_3959804 : CollatzResearch.WordTrace tailWord_3959804 prefixEnd_3959804 677760916532110160779733 := by
  unfold tailWord_3959804
  simp only [CollatzResearch.WordTrace]
  refine ⟨72212958473156931763427233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96283944630875909017902977 72212958473156931763427233)
  ·
    refine ⟨54159718854867698822570425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72212958473156931763427233 54159718854867698822570425)
    ·
      refine ⟨40619789141150774116927819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54159718854867698822570425 40619789141150774116927819)
      ·
        refine ⟨60929683711726161175391729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40619789141150774116927819 60929683711726161175391729)
        ·
          refine ⟨45697262783794620881543797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60929683711726161175391729 45697262783794620881543797)
          ·
            refine ⟨4284118385980745707644731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45697262783794620881543797 4284118385980745707644731)
            ·
              refine ⟨6426177578971118561467097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4284118385980745707644731 6426177578971118561467097)
              ·
                refine ⟨4819633184228338921100323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6426177578971118561467097 4819633184228338921100323)
                ·
                  refine ⟨7229449776342508381650485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4819633184228338921100323 7229449776342508381650485)
                  ·
                    refine ⟨677760916532110160779733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7229449776342508381650485 677760916532110160779733)
                    ·
                      rfl

theorem cell23_3959804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 1, 5].length) (baseStart_3959804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959804 prefixEnd_3959804 := by exact prefixLift 3959804
  have htrace : WordTrace (prefixWord ++ tailWord_3959804) baseStart_3959804 baseEnd_3959804 := by
    simpa [prefixWord, tailWord_3959804, baseEnd_3959804] using wordTrace_append hprefix tailTrace_3959804
  have hstable : (prefixWord ++ tailWord_3959804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959804).length < 2 ^ (prefixWord ++ tailWord_3959804).sum := by decide
  have hdescent : baseEnd_3959804 < baseStart_3959804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959834 : List Nat := [3, 1, 1, 3, 1, 2, 4, 2, 2, 4]
def baseStart_3959834 : Nat := 118140960795 + 3959834 * 2 ^ 59
def prefixEnd_3959834 : Nat := 4983230072969 + 3 ^ 40 * 3959834 * 2
def baseEnd_3959834 : Nat := 677766051338655121654687

theorem tailTrace_3959834 : CollatzResearch.WordTrace tailWord_3959834 prefixEnd_3959834 677766051338655121654687 := by
  unfold tailWord_3959834
  simp only [CollatzResearch.WordTrace]
  refine ⟨36106752784051294662611639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96284674090803452433631037 36106752784051294662611639)
  ·
    refine ⟨54160129176076941993917459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36106752784051294662611639 54160129176076941993917459)
    ·
      refine ⟨81240193764115412990876189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54160129176076941993917459 81240193764115412990876189)
      ·
        refine ⟨30465072661543279871578571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81240193764115412990876189 30465072661543279871578571)
        ·
          refine ⟨45697608992314919807367857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30465072661543279871578571 45697608992314919807367857)
          ·
            refine ⟨34273206744236189855525893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45697608992314919807367857 34273206744236189855525893)
            ·
              refine ⟨6426226264544285597911105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34273206744236189855525893 6426226264544285597911105)
              ·
                refine ⟨4819669698408214198433329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6426226264544285597911105 4819669698408214198433329)
                ·
                  refine ⟨3614752273806160648824997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4819669698408214198433329 3614752273806160648824997)
                  ·
                    refine ⟨677766051338655121654687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3614752273806160648824997 677766051338655121654687)
                    ·
                      rfl

theorem cell23_3959834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 2, 4].length) (baseStart_3959834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959834 prefixEnd_3959834 := by exact prefixLift 3959834
  have htrace : WordTrace (prefixWord ++ tailWord_3959834) baseStart_3959834 baseEnd_3959834 := by
    simpa [prefixWord, tailWord_3959834, baseEnd_3959834] using wordTrace_append hprefix tailTrace_3959834
  have hstable : (prefixWord ++ tailWord_3959834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959834).length < 2 ^ (prefixWord ++ tailWord_3959834).sum := by decide
  have hdescent : baseEnd_3959834 < baseStart_3959834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959844 : List Nat := [2, 3, 1, 4, 1, 1, 1, 2, 3, 2, 3]
def baseStart_3959844 : Nat := 118140960795 + 3959844 * 2 ^ 59
def prefixEnd_3959844 : Nat := 4983230072969 + 3 ^ 40 * 3959844 * 2
def baseEnd_3959844 : Nat := 2033303288822510325839015

theorem tailTrace_3959844 : CollatzResearch.WordTrace tailWord_3959844 prefixEnd_3959844 2033303288822510325839015 := by
  unfold tailWord_3959844
  simp only [CollatzResearch.WordTrace]
  refine ⟨72213687933084475179155293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96284917244112633572207057 72213687933084475179155293)
  ·
    refine ⟨27080132974906678192183235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72213687933084475179155293 27080132974906678192183235)
    ·
      refine ⟨40620199462360017288274853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27080132974906678192183235 40620199462360017288274853)
      ·
        refine ⟨7616287399192503241551535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40620199462360017288274853 7616287399192503241551535)
        ·
          refine ⟨11424431098788754862327303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7616287399192503241551535 11424431098788754862327303)
          ·
            refine ⟨17136646648183132293490955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11424431098788754862327303 17136646648183132293490955)
            ·
              refine ⟨25704969972274698440236433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17136646648183132293490955 25704969972274698440236433)
              ·
                refine ⟨19278727479206023830177325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25704969972274698440236433 19278727479206023830177325)
                ·
                  refine ⟨7229522804702258936316497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19278727479206023830177325 7229522804702258936316497)
                  ·
                    refine ⟨5422142103526694202237373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7229522804702258936316497 5422142103526694202237373)
                    ·
                      refine ⟨2033303288822510325839015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5422142103526694202237373 2033303288822510325839015)
                      ·
                        rfl

theorem cell23_3959844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_3959844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959844 prefixEnd_3959844 := by exact prefixLift 3959844
  have htrace : WordTrace (prefixWord ++ tailWord_3959844) baseStart_3959844 baseEnd_3959844 := by
    simpa [prefixWord, tailWord_3959844, baseEnd_3959844] using wordTrace_append hprefix tailTrace_3959844
  have hstable : (prefixWord ++ tailWord_3959844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959844).length < 2 ^ (prefixWord ++ tailWord_3959844).sum := by decide
  have hdescent : baseEnd_3959844 < baseStart_3959844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959854 : List Nat := [4, 1, 3, 1, 1, 1, 4, 1, 1, 2, 4]
def baseStart_3959854 : Nat := 118140960795 + 3959854 * 2 ^ 59
def prefixEnd_3959854 : Nat := 4983230072969 + 3 ^ 40 * 3959854 * 2
def baseEnd_3959854 : Nat := 2033308423629055286713969

theorem tailTrace_3959854 : CollatzResearch.WordTrace tailWord_3959854 prefixEnd_3959854 2033308423629055286713969 := by
  unfold tailWord_3959854
  simp only [CollatzResearch.WordTrace]
  refine ⟨18053467574516590258271827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96285160397421814710783077 18053467574516590258271827)
  ·
    refine ⟨27080201361774885387407741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18053467574516590258271827 27080201361774885387407741)
    ·
      refine ⟨10155075510665582020277903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27080201361774885387407741 10155075510665582020277903)
      ·
        refine ⟨15232613265998373030416855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10155075510665582020277903 15232613265998373030416855)
        ·
          refine ⟨22848919898997559545625283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15232613265998373030416855 22848919898997559545625283)
          ·
            refine ⟨34273379848496339318437925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22848919898997559545625283 34273379848496339318437925)
            ·
              refine ⟨6426258721593063622207111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34273379848496339318437925 6426258721593063622207111)
              ·
                refine ⟨9639388082389595433310667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6426258721593063622207111 9639388082389595433310667)
                ·
                  refine ⟨14459082123584393149966001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9639388082389595433310667 14459082123584393149966001)
                  ·
                    refine ⟨10844311592688294862474501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14459082123584393149966001 10844311592688294862474501)
                    ·
                      refine ⟨2033308423629055286713969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10844311592688294862474501 2033308423629055286713969)
                      ·
                        rfl

theorem cell23_3959854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_3959854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959854 prefixEnd_3959854 := by exact prefixLift 3959854
  have htrace : WordTrace (prefixWord ++ tailWord_3959854) baseStart_3959854 baseEnd_3959854 := by
    simpa [prefixWord, tailWord_3959854, baseEnd_3959854] using wordTrace_append hprefix tailTrace_3959854
  have hstable : (prefixWord ++ tailWord_3959854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959854).length < 2 ^ (prefixWord ++ tailWord_3959854).sum := by decide
  have hdescent : baseEnd_3959854 < baseStart_3959854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959878 : List Nat := [6, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3]
def baseStart_3959878 : Nat := 118140960795 + 3959878 * 2 ^ 59
def prefixEnd_3959878 : Nat := 4983230072969 + 3 ^ 40 * 3959878 * 2
def baseEnd_3959878 : Nat := 2033320747164763192813859

theorem tailTrace_3959878 : CollatzResearch.WordTrace tailWord_3959878 prefixEnd_3959878 2033320747164763192813859 := by
  unfold tailWord_3959878
  simp only [CollatzResearch.WordTrace]
  refine ⟨4513394248376430442657759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 96285743965363849443365525 4513394248376430442657759)
  ·
    refine ⟨6770091372564645663986639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4513394248376430442657759 6770091372564645663986639)
    ·
      refine ⟨10155137058846968495979959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6770091372564645663986639 10155137058846968495979959)
      ·
        refine ⟨15232705588270452743969939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10155137058846968495979959 15232705588270452743969939)
        ·
          refine ⟨22849058382405679115954909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15232705588270452743969939 22849058382405679115954909)
          ·
            refine ⟨8568396893402129668483091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22849058382405679115954909 8568396893402129668483091)
            ·
              refine ⟨12852595340103194502724637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8568396893402129668483091 12852595340103194502724637)
              ·
                refine ⟨4819723252538697938521739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12852595340103194502724637 4819723252538697938521739)
                ·
                  refine ⟨7229584878808046907782609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4819723252538697938521739 7229584878808046907782609)
                  ·
                    refine ⟨5422188659106035180836957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7229584878808046907782609 5422188659106035180836957)
                    ·
                      refine ⟨2033320747164763192813859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5422188659106035180836957 2033320747164763192813859)
                      ·
                        rfl

theorem cell23_3959878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_3959878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959878 prefixEnd_3959878 := by exact prefixLift 3959878
  have htrace : WordTrace (prefixWord ++ tailWord_3959878) baseStart_3959878 baseEnd_3959878 := by
    simpa [prefixWord, tailWord_3959878, baseEnd_3959878] using wordTrace_append hprefix tailTrace_3959878
  have hstable : (prefixWord ++ tailWord_3959878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959878).length < 2 ^ (prefixWord ++ tailWord_3959878).sum := by decide
  have hdescent : baseEnd_3959878 < baseStart_3959878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959918 : List Nat := [4, 1, 2, 2, 1, 3, 2, 2, 1, 3, 2]
def baseStart_3959918 : Nat := 118140960795 + 3959918 * 2 ^ 59
def prefixEnd_3959918 : Nat := 4983230072969 + 3 ^ 40 * 3959918 * 2
def baseEnd_3959918 : Nat := 2033341286390943036313675

theorem tailTrace_3959918 : CollatzResearch.WordTrace tailWord_3959918 prefixEnd_3959918 2033341286390943036313675 := by
  unfold tailWord_3959918
  simp only [CollatzResearch.WordTrace]
  refine ⟨18053759358487607624563051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96286716578600573997669605 18053759358487607624563051)
  ·
    refine ⟨27080639037731411436844577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18053759358487607624563051 27080639037731411436844577)
    ·
      refine ⟨20310479278298558577633433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27080639037731411436844577 20310479278298558577633433)
      ·
        refine ⟨15232859458723918933225075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20310479278298558577633433 15232859458723918933225075)
        ·
          refine ⟨22849289188085878399837613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15232859458723918933225075 22849289188085878399837613)
          ·
            refine ⟨8568483445532204399939105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22849289188085878399837613 8568483445532204399939105)
            ·
              refine ⟨6426362584149153299954329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8568483445532204399939105 6426362584149153299954329)
              ·
                refine ⟨4819771938111864974965747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6426362584149153299954329 4819771938111864974965747)
                ·
                  refine ⟨7229657907167797462448621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4819771938111864974965747 7229657907167797462448621)
                  ·
                    refine ⟨2711121715187924048418233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7229657907167797462448621 2711121715187924048418233)
                    ·
                      refine ⟨2033341286390943036313675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2711121715187924048418233 2033341286390943036313675)
                      ·
                        rfl

theorem cell23_3959918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_3959918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959918 prefixEnd_3959918 := by exact prefixLift 3959918
  have htrace : WordTrace (prefixWord ++ tailWord_3959918) baseStart_3959918 baseEnd_3959918 := by
    simpa [prefixWord, tailWord_3959918, baseEnd_3959918] using wordTrace_append hprefix tailTrace_3959918
  have hstable : (prefixWord ++ tailWord_3959918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959918).length < 2 ^ (prefixWord ++ tailWord_3959918).sum := by decide
  have hdescent : baseEnd_3959918 < baseStart_3959918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959947 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 4, 3, 3]
def baseStart_3959947 : Nat := 118140960795 + 3959947 * 2 ^ 59
def prefixEnd_3959947 : Nat := 4983230072969 + 3 ^ 40 * 3959947 * 2
def baseEnd_3959947 : Nat := 2033356177329923422851041

theorem tailTrace_3959947 : CollatzResearch.WordTrace tailWord_3959947 prefixEnd_3959947 2033356177329923422851041 := by
  unfold tailWord_3959947
  simp only [CollatzResearch.WordTrace]
  refine ⟨144431132584795798949310095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96287421723197199299540063 144431132584795798949310095)
  ·
    refine ⟨216646698877193698423965143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144431132584795798949310095 216646698877193698423965143)
    ·
      refine ⟨324970048315790547635947715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216646698877193698423965143 324970048315790547635947715)
      ·
        refine ⟨487455072473685821453921573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324970048315790547635947715 487455072473685821453921573)
        ·
          refine ⟨91397826088816091522610295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 487455072473685821453921573 91397826088816091522610295)
          ·
            refine ⟨137096739133224137283915443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91397826088816091522610295 137096739133224137283915443)
            ·
              refine ⟨205645108699836205925873165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137096739133224137283915443 205645108699836205925873165)
              ·
                refine ⟨77116915762438577222202437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205645108699836205925873165 77116915762438577222202437)
                ·
                  refine ⟨14459421705457233229162957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77116915762438577222202437 14459421705457233229162957)
                  ·
                    refine ⟨5422283139546462460936109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14459421705457233229162957 5422283139546462460936109)
                    ·
                      refine ⟨2033356177329923422851041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5422283139546462460936109 2033356177329923422851041)
                      ·
                        rfl

theorem cell23_3959947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 3, 3].length) (baseStart_3959947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959947 prefixEnd_3959947 := by exact prefixLift 3959947
  have htrace : WordTrace (prefixWord ++ tailWord_3959947) baseStart_3959947 baseEnd_3959947 := by
    simpa [prefixWord, tailWord_3959947, baseEnd_3959947] using wordTrace_append hprefix tailTrace_3959947
  have hstable : (prefixWord ++ tailWord_3959947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959947).length < 2 ^ (prefixWord ++ tailWord_3959947).sum := by decide
  have hdescent : baseEnd_3959947 < baseStart_3959947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959954 : List Nat := [3, 2, 3, 1, 1, 2, 3, 1, 7]
def baseStart_3959954 : Nat := 118140960795 + 3959954 * 2 ^ 59
def prefixEnd_3959954 : Nat := 4983230072969 + 3 ^ 40 * 3959954 * 2
def baseEnd_3959954 : Nat := 225928863521611655051501

theorem tailTrace_3959954 : CollatzResearch.WordTrace tailWord_3959954 prefixEnd_3959954 225928863521611655051501 := by
  unfold tailWord_3959954
  simp only [CollatzResearch.WordTrace]
  refine ⟨36107846973942609786203729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96287591930513626096543277 36107846973942609786203729)
  ·
    refine ⟨27080885230456957339652797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36107846973942609786203729 27080885230456957339652797)
    ·
      refine ⟨10155331961421359002369799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27080885230456957339652797 10155331961421359002369799)
      ·
        refine ⟨15232997942132038503554699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10155331961421359002369799 15232997942132038503554699)
        ·
          refine ⟨22849496913198057755332049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15232997942132038503554699 22849496913198057755332049)
          ·
            refine ⟨17137122684898543316499037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22849496913198057755332049 17137122684898543316499037)
            ·
              refine ⟨6426421006836953743687139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17137122684898543316499037 6426421006836953743687139)
              ·
                refine ⟨9639631510255430615530709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6426421006836953743687139 9639631510255430615530709)
                ·
                  refine ⟨225928863521611655051501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9639631510255430615530709 225928863521611655051501)
                  ·
                    rfl

theorem cell23_3959954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 7].length) (baseStart_3959954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959954 prefixEnd_3959954 := by exact prefixLift 3959954
  have htrace : WordTrace (prefixWord ++ tailWord_3959954) baseStart_3959954 baseEnd_3959954 := by
    simpa [prefixWord, tailWord_3959954, baseEnd_3959954] using wordTrace_append hprefix tailTrace_3959954
  have hstable : (prefixWord ++ tailWord_3959954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959954).length < 2 ^ (prefixWord ++ tailWord_3959954).sum := by decide
  have hdescent : baseEnd_3959954 < baseStart_3959954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959987 : List Nat := [1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 4]
def baseStart_3959987 : Nat := 118140960795 + 3959987 * 2 ^ 59
def prefixEnd_3959987 : Nat := 4983230072969 + 3 ^ 40 * 3959987 * 2
def baseEnd_3959987 : Nat := 2033376716556103266350857

theorem tailTrace_3959987 : CollatzResearch.WordTrace tailWord_3959987 prefixEnd_3959987 2033376716556103266350857 := by
  unfold tailWord_3959987
  simp only [CollatzResearch.WordTrace]
  refine ⟨144432591504650885780766215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96288394336433923853844143 144432591504650885780766215)
  ·
    refine ⟨216648887256976328671149323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144432591504650885780766215 216648887256976328671149323)
    ·
      refine ⟨324973330885464493006723985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216648887256976328671149323 324973330885464493006723985)
      ·
        refine ⟨243729998164098369755042989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324973330885464493006723985 243729998164098369755042989)
        ·
          refine ⟨91398749311536888658141121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243729998164098369755042989 91398749311536888658141121)
          ·
            refine ⟨68549061983652666493605841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91398749311536888658141121 68549061983652666493605841)
            ·
              refine ⟨51411796487739499870204381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68549061983652666493605841 51411796487739499870204381)
              ·
                refine ⟨19279423682902312451326643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51411796487739499870204381 19279423682902312451326643)
                ·
                  refine ⟨28919135524353468676989965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19279423682902312451326643 28919135524353468676989965)
                  ·
                    refine ⟨10844675821632550753871237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28919135524353468676989965 10844675821632550753871237)
                    ·
                      refine ⟨2033376716556103266350857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10844675821632550753871237 2033376716556103266350857)
                      ·
                        rfl

theorem cell23_3959987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 4].length) (baseStart_3959987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3959987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3959987 prefixEnd_3959987 := by exact prefixLift 3959987
  have htrace : WordTrace (prefixWord ++ tailWord_3959987) baseStart_3959987 baseEnd_3959987 := by
    simpa [prefixWord, tailWord_3959987, baseEnd_3959987] using wordTrace_append hprefix tailTrace_3959987
  have hstable : (prefixWord ++ tailWord_3959987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959987).length < 2 ^ (prefixWord ++ tailWord_3959987).sum := by decide
  have hdescent : baseEnd_3959987 < baseStart_3959987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960001 : List Nat := [1, 2, 6, 1, 1, 1, 2, 2, 2, 5]
def baseStart_3960001 : Nat := 118140960795 + 3960001 * 2 ^ 59
def prefixEnd_3960001 : Nat := 4983230072969 + 3 ^ 40 * 3960001 * 2
def baseEnd_3960001 : Nat := 677794635095088737191931

theorem tailTrace_3960001 : CollatzResearch.WordTrace tailWord_3960001 prefixEnd_3960001 677794635095088737191931 := by
  unfold tailWord_3960001
  simp only [CollatzResearch.WordTrace]
  refine ⟨144433102126600166171775857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96288734751066777447850571 144433102126600166171775857)
  ·
    refine ⟨108324826594950124628831893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144433102126600166171775857 108324826594950124628831893)
    ·
      refine ⟨5077726246638287091976495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 108324826594950124628831893 5077726246638287091976495)
      ·
        refine ⟨7616589369957430637964743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5077726246638287091976495 7616589369957430637964743)
        ·
          refine ⟨11424884054936145956947115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7616589369957430637964743 11424884054936145956947115)
          ·
            refine ⟨17137326082404218935420673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11424884054936145956947115 17137326082404218935420673)
            ·
              refine ⟨12852994561803164201565505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17137326082404218935420673 12852994561803164201565505)
              ·
                refine ⟨9639745921352373151174129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12852994561803164201565505 9639745921352373151174129)
                ·
                  refine ⟨7229809441014279863380597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9639745921352373151174129 7229809441014279863380597)
                  ·
                    refine ⟨677794635095088737191931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7229809441014279863380597 677794635095088737191931)
                    ·
                      rfl

theorem cell23_3960001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_3960001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960001 prefixEnd_3960001 := by exact prefixLift 3960001
  have htrace : WordTrace (prefixWord ++ tailWord_3960001) baseStart_3960001 baseEnd_3960001 := by
    simpa [prefixWord, tailWord_3960001, baseEnd_3960001] using wordTrace_append hprefix tailTrace_3960001
  have hstable : (prefixWord ++ tailWord_3960001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960001).length < 2 ^ (prefixWord ++ tailWord_3960001).sum := by decide
  have hdescent : baseEnd_3960001 < baseStart_3960001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960017 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 2, 4, 4]
def baseStart_3960017 : Nat := 118140960795 + 3960017 * 2 ^ 59
def prefixEnd_3960017 : Nat := 4983230072969 + 3 ^ 40 * 3960017 * 2
def baseEnd_3960017 : Nat := 2033392120975738148975719

theorem tailTrace_3960017 : CollatzResearch.WordTrace tailWord_3960017 prefixEnd_3960017 2033392120975738148975719 := by
  unfold tailWord_3960017
  simp only [CollatzResearch.WordTrace]
  refine ⟨144433685694542200904358305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96289123796361467269572203 144433685694542200904358305)
  ·
    refine ⟨108325264270906650678268729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144433685694542200904358305 108325264270906650678268729)
    ·
      refine ⟨81243948203179988008701547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108325264270906650678268729 81243948203179988008701547)
      ·
        refine ⟨121865922304769982013052321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81243948203179988008701547 121865922304769982013052321)
        ·
          refine ⟨91399441728577486509789241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121865922304769982013052321 91399441728577486509789241)
          ·
            refine ⟨68549581296433114882341931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91399441728577486509789241 68549581296433114882341931)
            ·
              refine ⟨102824371944649672323512897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68549581296433114882341931 102824371944649672323512897)
              ·
                refine ⟨77118278958487254242634673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102824371944649672323512897 77118278958487254242634673)
                ·
                  refine ⟨57838709218865440681976005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77118278958487254242634673 57838709218865440681976005)
                  ·
                    refine ⟨10844757978537270127870501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57838709218865440681976005 10844757978537270127870501)
                    ·
                      refine ⟨2033392120975738148975719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10844757978537270127870501 2033392120975738148975719)
                      ·
                        rfl

theorem cell23_3960017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 4, 4].length) (baseStart_3960017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960017 prefixEnd_3960017 := by exact prefixLift 3960017
  have htrace : WordTrace (prefixWord ++ tailWord_3960017) baseStart_3960017 baseEnd_3960017 := by
    simpa [prefixWord, tailWord_3960017, baseEnd_3960017] using wordTrace_append hprefix tailTrace_3960017
  have hstable : (prefixWord ++ tailWord_3960017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960017).length < 2 ^ (prefixWord ++ tailWord_3960017).sum := by decide
  have hdescent : baseEnd_3960017 < baseStart_3960017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960021 : List Nat := [1, 3, 2, 4, 1, 1, 1, 1, 1, 6, 2]
def baseStart_3960021 : Nat := 118140960795 + 3960021 * 2 ^ 59
def prefixEnd_3960021 : Nat := 4983230072969 + 3 ^ 40 * 3960021 * 2
def baseEnd_3960021 : Nat := 2033394174898356133325701

theorem tailTrace_3960021 : CollatzResearch.WordTrace tailWord_3960021 prefixEnd_3960021 2033394174898356133325701 := by
  unfold tailWord_3960021
  simp only [CollatzResearch.WordTrace]
  refine ⟨144433831586527709587503917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96289221057685139725002611 144433831586527709587503917)
  ·
    refine ⟨54162686844947891095313969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144433831586527709587503917 54162686844947891095313969)
    ·
      refine ⟨40622015133710918321485477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54162686844947891095313969 40622015133710918321485477)
      ·
        refine ⟨7616627837570797185278527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40622015133710918321485477 7616627837570797185278527)
        ·
          refine ⟨11424941756356195777917791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7616627837570797185278527 11424941756356195777917791)
          ·
            refine ⟨17137412634534293666876687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11424941756356195777917791 17137412634534293666876687)
            ·
              refine ⟨25706118951801440500315031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17137412634534293666876687 25706118951801440500315031)
              ·
                refine ⟨38559178427702160750472547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25706118951801440500315031 38559178427702160750472547)
                ·
                  refine ⟨57838767641553241125708821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38559178427702160750472547 57838767641553241125708821)
                  ·
                    refine ⟨2711192233197808177767601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 57838767641553241125708821 2711192233197808177767601)
                    ·
                      refine ⟨2033394174898356133325701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2711192233197808177767601 2033394174898356133325701)
                      ·
                        rfl

theorem cell23_3960021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_3960021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960021 prefixEnd_3960021 := by exact prefixLift 3960021
  have htrace : WordTrace (prefixWord ++ tailWord_3960021) baseStart_3960021 baseEnd_3960021 := by
    simpa [prefixWord, tailWord_3960021, baseEnd_3960021] using wordTrace_append hprefix tailTrace_3960021
  have hstable : (prefixWord ++ tailWord_3960021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960021).length < 2 ^ (prefixWord ++ tailWord_3960021).sum := by decide
  have hdescent : baseEnd_3960021 < baseStart_3960021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960107 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 6]
def baseStart_3960107 : Nat := 118140960795 + 3960107 * 2 ^ 59
def prefixEnd_3960107 : Nat := 4983230072969 + 3 ^ 40 * 3960107 * 2
def baseEnd_3960107 : Nat := 2033438334234642796850305

theorem tailTrace_3960107 : CollatzResearch.WordTrace tailWord_3960107 prefixEnd_3960107 2033438334234642796850305 := by
  unfold tailWord_3960107
  simp only [CollatzResearch.WordTrace]
  refine ⟨144436968264216146275134575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96291312176144097516756383 144436968264216146275134575)
  ·
    refine ⟨216655452396324219412701863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144436968264216146275134575 216655452396324219412701863)
    ·
      refine ⟨324983178594486329119052795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216655452396324219412701863 324983178594486329119052795)
      ·
        refine ⟨487474767891729493678579193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324983178594486329119052795 487474767891729493678579193)
        ·
          refine ⟨365606075918797120258934395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487474767891729493678579193 365606075918797120258934395)
          ·
            refine ⟨548409113878195680388401593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365606075918797120258934395 548409113878195680388401593)
            ·
              refine ⟨411306835408646760291301195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 548409113878195680388401593 411306835408646760291301195)
              ·
                refine ⟨616960253112970140436951793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 411306835408646760291301195 616960253112970140436951793)
                ·
                  refine ⟨462720189834727605327713845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 616960253112970140436951793 462720189834727605327713845)
                  ·
                    refine ⟨43380017797005712999473173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 462720189834727605327713845 43380017797005712999473173)
                    ·
                      refine ⟨2033438334234642796850305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43380017797005712999473173 2033438334234642796850305)
                      ·
                        rfl

theorem cell23_3960107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 6].length) (baseStart_3960107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960107 prefixEnd_3960107 := by exact prefixLift 3960107
  have htrace : WordTrace (prefixWord ++ tailWord_3960107) baseStart_3960107 baseEnd_3960107 := by
    simpa [prefixWord, tailWord_3960107, baseEnd_3960107] using wordTrace_append hprefix tailTrace_3960107
  have hstable : (prefixWord ++ tailWord_3960107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960107).length < 2 ^ (prefixWord ++ tailWord_3960107).sum := by decide
  have hdescent : baseEnd_3960107 < baseStart_3960107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960124 : List Nat := [2, 2, 2, 2, 1, 3, 1, 2, 1, 1, 6]
def baseStart_3960124 : Nat := 118140960795 + 3960124 * 2 ^ 59
def prefixEnd_3960124 : Nat := 4983230072969 + 3 ^ 40 * 3960124 * 2
def baseEnd_3960124 : Nat := 2033447063405769230337727

theorem tailTrace_3960124 : CollatzResearch.WordTrace tailWord_3960124 prefixEnd_3960124 2033447063405769230337727 := by
  unfold tailWord_3960124
  simp only [CollatzResearch.WordTrace]
  refine ⟨72218794152577279089251713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96291725536769705452335617 72218794152577279089251713)
  ·
    refine ⟨54164095614432959316938785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72218794152577279089251713 54164095614432959316938785)
    ·
      refine ⟨40623071710824719487704089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54164095614432959316938785 40623071710824719487704089)
      ·
        refine ⟨30467303783118539615778067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40623071710824719487704089 30467303783118539615778067)
        ·
          refine ⟨45700955674677809423667101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30467303783118539615778067 45700955674677809423667101)
          ·
            refine ⟨17137858378004178533875163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45700955674677809423667101 17137858378004178533875163)
            ·
              refine ⟨25706787567006267800812745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17137858378004178533875163 25706787567006267800812745)
              ·
                refine ⟨19280090675254700850609559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25706787567006267800812745 19280090675254700850609559)
                ·
                  refine ⟨28920136012882051275914339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19280090675254700850609559 28920136012882051275914339)
                  ·
                    refine ⟨43380204019323076913871509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28920136012882051275914339 43380204019323076913871509)
                    ·
                      refine ⟨2033447063405769230337727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43380204019323076913871509 2033447063405769230337727)
                      ·
                        rfl

theorem cell23_3960124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_3960124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960124 prefixEnd_3960124 := by exact prefixLift 3960124
  have htrace : WordTrace (prefixWord ++ tailWord_3960124) baseStart_3960124 baseEnd_3960124 := by
    simpa [prefixWord, tailWord_3960124, baseEnd_3960124] using wordTrace_append hprefix tailTrace_3960124
  have hstable : (prefixWord ++ tailWord_3960124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960124).length < 2 ^ (prefixWord ++ tailWord_3960124).sum := by decide
  have hdescent : baseEnd_3960124 < baseStart_3960124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960161 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 6, 1, 3]
def baseStart_3960161 : Nat := 118140960795 + 3960161 * 2 ^ 59
def prefixEnd_3960161 : Nat := 4983230072969 + 3 ^ 40 * 3960161 * 2
def baseEnd_3960161 : Nat := 2033466062189985585575057

theorem tailTrace_3960161 : CollatzResearch.WordTrace tailWord_3960161 prefixEnd_3960161 2033466062189985585575057 := by
  unfold tailWord_3960161
  simp only [CollatzResearch.WordTrace]
  refine ⟨144438937806020513497600337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96292625204013675665066891 144438937806020513497600337)
  ·
    refine ⟨108329203354515385123200253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144438937806020513497600337 108329203354515385123200253)
    ·
      refine ⟨40623451257943269421200095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108329203354515385123200253 40623451257943269421200095)
      ·
        refine ⟨60935176886914904131800143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40623451257943269421200095 60935176886914904131800143)
        ·
          refine ⟨91402765330372356197700215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60935176886914904131800143 91402765330372356197700215)
          ·
            refine ⟨137104147995558534296550323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91402765330372356197700215 137104147995558534296550323)
            ·
              refine ⟨205656221993337801444825485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137104147995558534296550323 205656221993337801444825485)
              ·
                refine ⟨77121083247501675541809557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205656221993337801444825485 77121083247501675541809557)
                ·
                  refine ⟨3615050777226641041022323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 77121083247501675541809557 3615050777226641041022323)
                  ·
                    refine ⟨5422576165839961561533485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3615050777226641041022323 5422576165839961561533485)
                    ·
                      refine ⟨2033466062189985585575057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5422576165839961561533485 2033466062189985585575057)
                      ·
                        rfl

theorem cell23_3960161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 6, 1, 3].length) (baseStart_3960161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960161 prefixEnd_3960161 := by exact prefixLift 3960161
  have htrace : WordTrace (prefixWord ++ tailWord_3960161) baseStart_3960161 baseEnd_3960161 := by
    simpa [prefixWord, tailWord_3960161, baseEnd_3960161] using wordTrace_append hprefix tailTrace_3960161
  have hstable : (prefixWord ++ tailWord_3960161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960161).length < 2 ^ (prefixWord ++ tailWord_3960161).sum := by decide
  have hdescent : baseEnd_3960161 < baseStart_3960161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960162 : List Nat := [3, 3, 2, 1, 1, 1, 2, 5, 1, 2, 2]
def baseStart_3960162 : Nat := 118140960795 + 3960162 * 2 ^ 59
def prefixEnd_3960162 : Nat := 4983230072969 + 3 ^ 40 * 3960162 * 2
def baseEnd_3960162 : Nat := 2033466575670640081662553

theorem tailTrace_3960162 : CollatzResearch.WordTrace tailWord_3960162 prefixEnd_3960162 2033466575670640081662553 := by
  unfold tailWord_3960162
  simp only [CollatzResearch.WordTrace]
  refine ⟨36109743569754222667096685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96292649519344593778924493 36109743569754222667096685)
  ·
    refine ⟨13541153838657833500161257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36109743569754222667096685 13541153838657833500161257)
    ·
      refine ⟨10155865378993375125120943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13541153838657833500161257 10155865378993375125120943)
      ·
        refine ⟨15233798068490062687681415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10155865378993375125120943 15233798068490062687681415)
        ·
          refine ⟨22850697102735094031522123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15233798068490062687681415 22850697102735094031522123)
          ·
            refine ⟨34276045654102641047283185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22850697102735094031522123 34276045654102641047283185)
            ·
              refine ⟨25707034240576980785462389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34276045654102641047283185 25707034240576980785462389)
              ·
                refine ⟨2410034460054091948637099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25707034240576980785462389 2410034460054091948637099)
                ·
                  refine ⟨3615051690081137922955649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2410034460054091948637099 3615051690081137922955649)
                  ·
                    refine ⟨2711288767560853442216737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3615051690081137922955649 2711288767560853442216737)
                    ·
                      refine ⟨2033466575670640081662553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2711288767560853442216737 2033466575670640081662553)
                      ·
                        rfl

theorem cell23_3960162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_3960162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960162 prefixEnd_3960162 := by exact prefixLift 3960162
  have htrace : WordTrace (prefixWord ++ tailWord_3960162) baseStart_3960162 baseEnd_3960162 := by
    simpa [prefixWord, tailWord_3960162, baseEnd_3960162] using wordTrace_append hprefix tailTrace_3960162
  have hstable : (prefixWord ++ tailWord_3960162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960162).length < 2 ^ (prefixWord ++ tailWord_3960162).sum := by decide
  have hdescent : baseEnd_3960162 < baseStart_3960162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960171 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 7, 3, 2]
def baseStart_3960171 : Nat := 118140960795 + 3960171 * 2 ^ 59
def prefixEnd_3960171 : Nat := 4983230072969 + 3 ^ 40 * 3960171 * 2
def baseEnd_3960171 : Nat := 2033471196996530546450011

theorem tailTrace_3960171 : CollatzResearch.WordTrace tailWord_3960171 prefixEnd_3960171 2033471196996530546450011 := by
  unfold tailWord_3960171
  simp only [CollatzResearch.WordTrace]
  refine ⟨144439302535984285205464367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96292868357322856803642911 144439302535984285205464367)
  ·
    refine ⟨216658953803976427808196551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144439302535984285205464367 216658953803976427808196551)
    ·
      refine ⟨324988430705964641712294827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216658953803976427808196551 324988430705964641712294827)
      ·
        refine ⟨487482646058946962568442241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324988430705964641712294827 487482646058946962568442241)
        ·
          refine ⟨365611984544210221926331681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487482646058946962568442241 365611984544210221926331681)
          ·
            refine ⟨274208988408157666444748761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365611984544210221926331681 274208988408157666444748761)
            ·
              refine ⟨205656741306118249833561571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274208988408157666444748761 205656741306118249833561571)
              ·
                refine ⟨308485111959177374750342357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205656741306118249833561571 308485111959177374750342357)
                ·
                  refine ⟨7230119811543219720711149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 308485111959177374750342357 7230119811543219720711149)
                  ·
                    refine ⟨2711294929328707395266681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7230119811543219720711149 2711294929328707395266681)
                    ·
                      refine ⟨2033471196996530546450011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2711294929328707395266681 2033471196996530546450011)
                      ·
                        rfl

theorem cell23_3960171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 3, 2].length) (baseStart_3960171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960171 prefixEnd_3960171 := by exact prefixLift 3960171
  have htrace : WordTrace (prefixWord ++ tailWord_3960171) baseStart_3960171 baseEnd_3960171 := by
    simpa [prefixWord, tailWord_3960171, baseEnd_3960171] using wordTrace_append hprefix tailTrace_3960171
  have hstable : (prefixWord ++ tailWord_3960171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960171).length < 2 ^ (prefixWord ++ tailWord_3960171).sum := by decide
  have hdescent : baseEnd_3960171 < baseStart_3960171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960218 : List Nat := [3, 1, 1, 4, 1, 1, 1, 4, 1, 4, 2]
def baseStart_3960218 : Nat := 118140960795 + 3960218 * 2 ^ 59
def prefixEnd_3960218 : Nat := 4983230072969 + 3 ^ 40 * 3960218 * 2
def baseEnd_3960218 : Nat := 2033495330587291862562295

theorem tailTrace_3960218 : CollatzResearch.WordTrace tailWord_3960218 prefixEnd_3960218 2033495330587291862562295 := by
  unfold tailWord_3960218
  simp only [CollatzResearch.WordTrace]
  refine ⟨36110254191703503058106327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96294011177876008154950205 36110254191703503058106327)
  ·
    refine ⟨54165381287555254587159491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36110254191703503058106327 54165381287555254587159491)
    ·
      refine ⟨81248071931332881880739237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54165381287555254587159491 81248071931332881880739237)
      ·
        refine ⟨15234013487124915352638607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81248071931332881880739237 15234013487124915352638607)
        ·
          refine ⟨22851020230687373028957911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15234013487124915352638607 22851020230687373028957911)
          ·
            refine ⟨34276530346031059543436867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22851020230687373028957911 34276530346031059543436867)
            ·
              refine ⟨51414795519046589315155301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34276530346031059543436867 51414795519046589315155301)
              ·
                refine ⟨9640274159821235496591619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51414795519046589315155301 9640274159821235496591619)
                ·
                  refine ⟨14460411239731853244887429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9640274159821235496591619 14460411239731853244887429)
                  ·
                    refine ⟨2711327107449722483416393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14460411239731853244887429 2711327107449722483416393)
                    ·
                      refine ⟨2033495330587291862562295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2711327107449722483416393 2033495330587291862562295)
                      ·
                        rfl

theorem cell23_3960218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_3960218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960218 prefixEnd_3960218 := by exact prefixLift 3960218
  have htrace : WordTrace (prefixWord ++ tailWord_3960218) baseStart_3960218 baseEnd_3960218 := by
    simpa [prefixWord, tailWord_3960218, baseEnd_3960218] using wordTrace_append hprefix tailTrace_3960218
  have hstable : (prefixWord ++ tailWord_3960218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960218).length < 2 ^ (prefixWord ++ tailWord_3960218).sum := by decide
  have hdescent : baseEnd_3960218 < baseStart_3960218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960224 : List Nat := [2, 1, 1, 4, 1, 2, 1, 2, 9]
def baseStart_3960224 : Nat := 118140960795 + 3960224 * 2 ^ 59
def prefixEnd_3960224 : Nat := 4983230072969 + 3 ^ 40 * 3960224 * 2
def baseEnd_3960224 : Nat := 225944267941246537676363

theorem tailTrace_3960224 : CollatzResearch.WordTrace tailWord_3960224 prefixEnd_3960224 225944267941246537676363 := by
  unfold tailWord_3960224
  simp only [CollatzResearch.WordTrace]
  refine ⟨72220617802396137628571863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96294157069861516838095817 72220617802396137628571863)
  ·
    refine ⟨108330926703594206442857795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72220617802396137628571863 108330926703594206442857795)
    ·
      refine ⟨162496390055391309664286693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108330926703594206442857795 162496390055391309664286693)
      ·
        refine ⟨30468073135385870562053755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162496390055391309664286693 30468073135385870562053755)
        ·
          refine ⟨45702109703078805843080633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30468073135385870562053755 45702109703078805843080633)
          ·
            refine ⟨34276582277309104382310475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45702109703078805843080633 34276582277309104382310475)
            ·
              refine ⟨51414873415963656573465713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34276582277309104382310475 51414873415963656573465713)
              ·
                refine ⟨38561155061972742430099285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51414873415963656573465713 38561155061972742430099285)
                ·
                  refine ⟨225944267941246537676363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 38561155061972742430099285 225944267941246537676363)
                  ·
                    rfl

theorem cell23_3960224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 9].length) (baseStart_3960224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960224 prefixEnd_3960224 := by exact prefixLift 3960224
  have htrace : WordTrace (prefixWord ++ tailWord_3960224) baseStart_3960224 baseEnd_3960224 := by
    simpa [prefixWord, tailWord_3960224, baseEnd_3960224] using wordTrace_append hprefix tailTrace_3960224
  have hstable : (prefixWord ++ tailWord_3960224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960224).length < 2 ^ (prefixWord ++ tailWord_3960224).sum := by decide
  have hdescent : baseEnd_3960224 < baseStart_3960224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960231 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 4]
def baseStart_3960231 : Nat := 118140960795 + 3960231 * 2 ^ 59
def prefixEnd_3960231 : Nat := 4983230072969 + 3 ^ 40 * 3960231 * 2
def baseEnd_3960231 : Nat := 2033502005835800311699735

theorem tailTrace_3960231 : CollatzResearch.WordTrace tailWord_3960231 prefixEnd_3960231 2033502005835800311699735 := by
  unfold tailWord_3960231
  simp only [CollatzResearch.WordTrace]
  refine ⟨144441490915766915452648547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96294327277177943635099031 144441490915766915452648547)
  ·
    refine ⟨216662236373650373178972821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144441490915766915452648547 216662236373650373178972821)
    ·
      refine ⟨10156042330014861242764351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 216662236373650373178972821 10156042330014861242764351)
      ·
        refine ⟨15234063495022291864146527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10156042330014861242764351 15234063495022291864146527)
        ·
          refine ⟨22851095242533437796219791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15234063495022291864146527 22851095242533437796219791)
          ·
            refine ⟨34276642863800156694329687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22851095242533437796219791 34276642863800156694329687)
            ·
              refine ⟨51414964295700235041494531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34276642863800156694329687 51414964295700235041494531)
              ·
                refine ⟨77122446443550352562241797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51414964295700235041494531 77122446443550352562241797)
                ·
                  refine ⟨14460458708165691105420337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77122446443550352562241797 14460458708165691105420337)
                  ·
                    refine ⟨10845344031124268329065253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14460458708165691105420337 10845344031124268329065253)
                    ·
                      refine ⟨2033502005835800311699735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10845344031124268329065253 2033502005835800311699735)
                      ·
                        rfl

theorem cell23_3960231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_3960231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960231 prefixEnd_3960231 := by exact prefixLift 3960231
  have htrace : WordTrace (prefixWord ++ tailWord_3960231) baseStart_3960231 baseEnd_3960231 := by
    simpa [prefixWord, tailWord_3960231, baseEnd_3960231] using wordTrace_append hprefix tailTrace_3960231
  have hstable : (prefixWord ++ tailWord_3960231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960231).length < 2 ^ (prefixWord ++ tailWord_3960231).sum := by decide
  have hdescent : baseEnd_3960231 < baseStart_3960231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960241 : List Nat := [1, 2, 2, 4, 1, 1, 4, 1, 7]
def baseStart_3960241 : Nat := 118140960795 + 3960241 * 2 ^ 59
def prefixEnd_3960241 : Nat := 4983230072969 + 3 ^ 40 * 3960241 * 2
def baseEnd_3960241 : Nat := 225945237849149474730521

theorem tailTrace_3960241 : CollatzResearch.WordTrace tailWord_3960241 prefixEnd_3960241 225945237849149474730521 := by
  unfold tailWord_3960241
  simp only [CollatzResearch.WordTrace]
  refine ⟨144441855645730687160512577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96294570430487124773675051 144441855645730687160512577)
  ·
    refine ⟨108331391734298015370384433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144441855645730687160512577 108331391734298015370384433)
    ·
      refine ⟨81248543800723511527788325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108331391734298015370384433 81248543800723511527788325)
      ·
        refine ⟨15234101962635658411460311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81248543800723511527788325 15234101962635658411460311)
        ·
          refine ⟨22851152943953487617190467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15234101962635658411460311 22851152943953487617190467)
          ·
            refine ⟨34276729415930231425785701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22851152943953487617190467 34276729415930231425785701)
            ·
              refine ⟨6426886765486918392334819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34276729415930231425785701 6426886765486918392334819)
              ·
                refine ⟨9640330148230377588502229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6426886765486918392334819 9640330148230377588502229)
                ·
                  refine ⟨225945237849149474730521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9640330148230377588502229 225945237849149474730521)
                  ·
                    rfl

theorem cell23_3960241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 7].length) (baseStart_3960241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960241 prefixEnd_3960241 := by exact prefixLift 3960241
  have htrace : WordTrace (prefixWord ++ tailWord_3960241) baseStart_3960241 baseEnd_3960241 := by
    simpa [prefixWord, tailWord_3960241, baseEnd_3960241] using wordTrace_append hprefix tailTrace_3960241
  have hstable : (prefixWord ++ tailWord_3960241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960241).length < 2 ^ (prefixWord ++ tailWord_3960241).sum := by decide
  have hdescent : baseEnd_3960241 < baseStart_3960241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960252 : List Nat := [2, 2, 2, 4, 2, 2, 1, 1, 1, 4, 2]
def baseStart_3960252 : Nat := 118140960795 + 3960252 * 2 ^ 59
def prefixEnd_3960252 : Nat := 4983230072969 + 3 ^ 40 * 3960252 * 2
def baseEnd_3960252 : Nat := 2033512788929544729537139

theorem tailTrace_3960252 : CollatzResearch.WordTrace tailWord_3960252 prefixEnd_3960252 2033512788929544729537139 := by
  unfold tailWord_3960252
  simp only [CollatzResearch.WordTrace]
  refine ⟨72221128424345418019581505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96294837899127224026108673 72221128424345418019581505)
  ·
    refine ⟨54165846318259063514686129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72221128424345418019581505 54165846318259063514686129)
    ·
      refine ⟨40624384738694297636014597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54165846318259063514686129 40624384738694297636014597)
      ·
        refine ⟨7617072138505180806752737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40624384738694297636014597 7617072138505180806752737)
        ·
          refine ⟨5712804103878885605064553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7617072138505180806752737 5712804103878885605064553)
          ·
            refine ⟨4284603077909164203798415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5712804103878885605064553 4284603077909164203798415)
            ·
              refine ⟨6426904616863746305697623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4284603077909164203798415 6426904616863746305697623)
              ·
                refine ⟨9640356925295619458546435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6426904616863746305697623 9640356925295619458546435)
                ·
                  refine ⟨14460535387943429187819653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9640356925295619458546435 14460535387943429187819653)
                  ·
                    refine ⟨2711350385239392972716185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14460535387943429187819653 2711350385239392972716185)
                    ·
                      refine ⟨2033512788929544729537139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2711350385239392972716185 2033512788929544729537139)
                      ·
                        rfl

theorem cell23_3960252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_3960252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960252 prefixEnd_3960252 := by exact prefixLift 3960252
  have htrace : WordTrace (prefixWord ++ tailWord_3960252) baseStart_3960252 baseEnd_3960252 := by
    simpa [prefixWord, tailWord_3960252, baseEnd_3960252] using wordTrace_append hprefix tailTrace_3960252
  have hstable : (prefixWord ++ tailWord_3960252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960252).length < 2 ^ (prefixWord ++ tailWord_3960252).sum := by decide
  have hdescent : baseEnd_3960252 < baseStart_3960252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960298 : List Nat := [3, 1, 3, 1, 4, 1, 1, 1, 1, 2, 5]
def baseStart_3960298 : Nat := 118140960795 + 3960298 * 2 ^ 59
def prefixEnd_3960298 : Nat := 4983230072969 + 3 ^ 40 * 3960298 * 2
def baseEnd_3960298 : Nat := 2033536409039651549561927

theorem tailTrace_3960298 : CollatzResearch.WordTrace tailWord_3960298 prefixEnd_3960298 2033536409039651549561927 := by
  unfold tailWord_3960298
  simp only [CollatzResearch.WordTrace]
  refine ⟨36110983651631046473834387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96295956404349457263558365 36110983651631046473834387)
  ·
    refine ⟨54166475477446569710751581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36110983651631046473834387 54166475477446569710751581)
    ·
      refine ⟨20312428304042463641531843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54166475477446569710751581 20312428304042463641531843)
      ·
        refine ⟨30468642456063695462297765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20312428304042463641531843 30468642456063695462297765)
        ·
          refine ⟨5712870460511942899180831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30468642456063695462297765 5712870460511942899180831)
          ·
            refine ⟨8569305690767914348771247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5712870460511942899180831 8569305690767914348771247)
            ·
              refine ⟨12853958536151871523156871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8569305690767914348771247 12853958536151871523156871)
              ·
                refine ⟨19280937804227807284735307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12853958536151871523156871 19280937804227807284735307)
                ·
                  refine ⟨28921406706341710927102961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19280937804227807284735307 28921406706341710927102961)
                  ·
                    refine ⟨21691055029756283195327221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28921406706341710927102961 21691055029756283195327221)
                    ·
                      refine ⟨2033536409039651549561927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21691055029756283195327221 2033536409039651549561927)
                      ·
                        rfl

theorem cell23_3960298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_3960298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960298 prefixEnd_3960298 := by exact prefixLift 3960298
  have htrace : WordTrace (prefixWord ++ tailWord_3960298) baseStart_3960298 baseEnd_3960298 := by
    simpa [prefixWord, tailWord_3960298, baseEnd_3960298] using wordTrace_append hprefix tailTrace_3960298
  have hstable : (prefixWord ++ tailWord_3960298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960298).length < 2 ^ (prefixWord ++ tailWord_3960298).sum := by decide
  have hdescent : baseEnd_3960298 < baseStart_3960298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960311 : List Nat := [1, 1, 3, 1, 1, 1, 1, 6, 1, 4, 3]
def baseStart_3960311 : Nat := 118140960795 + 3960311 * 2 ^ 59
def prefixEnd_3960311 : Nat := 4983230072969 + 3 ^ 40 * 3960311 * 2
def baseEnd_3960311 : Nat := 2033543084288159998699367

theorem tailTrace_3960311 : CollatzResearch.WordTrace tailWord_3960311 prefixEnd_3960311 2033543084288159998699367 := by
  unfold tailWord_3960311
  simp only [CollatzResearch.WordTrace]
  refine ⟨144444408755477089115560787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96296272503651392743707191 144444408755477089115560787)
  ·
    refine ⟨216666613133215633673341181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144444408755477089115560787 216666613133215633673341181)
    ·
      refine ⟨81249979924955862627502943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216666613133215633673341181 81249979924955862627502943)
      ·
        refine ⟨121874969887433793941254415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81249979924955862627502943 121874969887433793941254415)
        ·
          refine ⟨182812454831150690911881623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121874969887433793941254415 182812454831150690911881623)
          ·
            refine ⟨274218682246726036367822435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182812454831150690911881623 274218682246726036367822435)
            ·
              refine ⟨411328023370089054551733653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274218682246726036367822435 411328023370089054551733653)
              ·
                refine ⟨19281001095472924432112515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 411328023370089054551733653 19281001095472924432112515)
                ·
                  refine ⟨28921501643209386648168773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19281001095472924432112515 28921501643209386648168773)
                  ·
                    refine ⟨5422781558101759996531645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28921501643209386648168773 5422781558101759996531645)
                    ·
                      refine ⟨2033543084288159998699367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5422781558101759996531645 2033543084288159998699367)
                      ·
                        rfl

theorem cell23_3960311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 4, 3].length) (baseStart_3960311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960311 prefixEnd_3960311 := by exact prefixLift 3960311
  have htrace : WordTrace (prefixWord ++ tailWord_3960311) baseStart_3960311 baseEnd_3960311 := by
    simpa [prefixWord, tailWord_3960311, baseEnd_3960311] using wordTrace_append hprefix tailTrace_3960311
  have hstable : (prefixWord ++ tailWord_3960311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960311).length < 2 ^ (prefixWord ++ tailWord_3960311).sum := by decide
  have hdescent : baseEnd_3960311 < baseStart_3960311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960328 : List Nat := [2, 1, 3, 2, 1, 1, 3, 3, 2, 2, 3]
def baseStart_3960328 : Nat := 118140960795 + 3960328 * 2 ^ 59
def prefixEnd_3960328 : Nat := 4983230072969 + 3 ^ 40 * 3960328 * 2
def baseEnd_3960328 : Nat := 2033551813459286432186789

theorem tailTrace_3960328 : CollatzResearch.WordTrace tailWord_3960328 prefixEnd_3960328 2033551813459286432186789 := by
  unfold tailWord_3960328
  simp only [CollatzResearch.WordTrace]
  refine ⟨72222514398207750509464819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96296685864277000679286425 72222514398207750509464819)
  ·
    refine ⟨108333771597311625764197229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72222514398207750509464819 108333771597311625764197229)
    ·
      refine ⟨40625164348991859661573961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108333771597311625764197229 40625164348991859661573961)
      ·
        refine ⟨30468873261743894746180471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40625164348991859661573961 30468873261743894746180471)
        ·
          refine ⟨45703309892615842119270707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30468873261743894746180471 45703309892615842119270707)
          ·
            refine ⟨68554964838923763178906061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45703309892615842119270707 68554964838923763178906061)
            ·
              refine ⟨25708111814596411192089773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68554964838923763178906061 25708111814596411192089773)
              ·
                refine ⟨9640541930473654197033665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25708111814596411192089773 9640541930473654197033665)
                ·
                  refine ⟨7230406447855240647775249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9640541930473654197033665 7230406447855240647775249)
                  ·
                    refine ⟨5422804835891430485831437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7230406447855240647775249 5422804835891430485831437)
                    ·
                      refine ⟨2033551813459286432186789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5422804835891430485831437 2033551813459286432186789)
                      ·
                        rfl

theorem cell23_3960328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_3960328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960328 prefixEnd_3960328 := by exact prefixLift 3960328
  have htrace : WordTrace (prefixWord ++ tailWord_3960328) baseStart_3960328 baseEnd_3960328 := by
    simpa [prefixWord, tailWord_3960328, baseEnd_3960328] using wordTrace_append hprefix tailTrace_3960328
  have hstable : (prefixWord ++ tailWord_3960328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960328).length < 2 ^ (prefixWord ++ tailWord_3960328).sum := by decide
  have hdescent : baseEnd_3960328 < baseStart_3960328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960348 : List Nat := [2, 2, 3, 1, 2, 1, 4, 2, 6]
def baseStart_3960348 : Nat := 118140960795 + 3960348 * 2 ^ 59
def prefixEnd_3960348 : Nat := 4983230072969 + 3 ^ 40 * 3960348 * 2
def baseEnd_3960348 : Nat := 225951342563597372659633

theorem tailTrace_3960348 : CollatzResearch.WordTrace tailWord_3960348 prefixEnd_3960348 225951342563597372659633 := by
  unfold tailWord_3960348
  simp only [CollatzResearch.WordTrace]
  refine ⟨72222879128171522217328849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96297172170895362956438465 72222879128171522217328849)
  ·
    refine ⟨54167159346128641662996637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72222879128171522217328849 54167159346128641662996637)
    ·
      refine ⟨20312684754798240623623739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54167159346128641662996637 20312684754798240623623739)
      ·
        refine ⟨30469027132197360935435609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20312684754798240623623739 30469027132197360935435609)
        ·
          refine ⟨22851770349148020701576707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30469027132197360935435609 22851770349148020701576707)
          ·
            refine ⟨34277655523722031052365061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22851770349148020701576707 34277655523722031052365061)
            ·
              refine ⟨6427060410697880822318449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34277655523722031052365061 6427060410697880822318449)
              ·
                refine ⟨4820295308023410616738837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6427060410697880822318449 4820295308023410616738837)
                ·
                  refine ⟨225951342563597372659633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4820295308023410616738837 225951342563597372659633)
                  ·
                    rfl

theorem cell23_3960348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 6].length) (baseStart_3960348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960348 prefixEnd_3960348 := by exact prefixLift 3960348
  have htrace : WordTrace (prefixWord ++ tailWord_3960348) baseStart_3960348 baseEnd_3960348 := by
    simpa [prefixWord, tailWord_3960348, baseEnd_3960348] using wordTrace_append hprefix tailTrace_3960348
  have hstable : (prefixWord ++ tailWord_3960348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960348).length < 2 ^ (prefixWord ++ tailWord_3960348).sum := by decide
  have hdescent : baseEnd_3960348 < baseStart_3960348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960352 : List Nat := [2, 1, 1, 6, 1, 2, 1, 4, 1, 4]
def baseStart_3960352 : Nat := 118140960795 + 3960352 * 2 ^ 59
def prefixEnd_3960352 : Nat := 4983230072969 + 3 ^ 40 * 3960352 * 2
def baseEnd_3960352 : Nat := 677854712331664779428893

theorem tailTrace_3960352 : CollatzResearch.WordTrace tailWord_3960352 prefixEnd_3960352 677854712331664779428893 := by
  unfold tailWord_3960352
  simp only [CollatzResearch.WordTrace]
  refine ⟨72222952074164276558901655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96297269432219035411868873 72222952074164276558901655)
  ·
    refine ⟨108334428111246414838352483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72222952074164276558901655 108334428111246414838352483)
    ·
      refine ⟨162501642166869622257528725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108334428111246414838352483 162501642166869622257528725)
      ·
        refine ⟨7617264476572013543321659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 162501642166869622257528725 7617264476572013543321659)
        ·
          refine ⟨11425896714858020314982489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7617264476572013543321659 11425896714858020314982489)
          ·
            refine ⟨8569422536143515236236867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11425896714858020314982489 8569422536143515236236867)
            ·
              refine ⟨12854133804215272854355301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8569422536143515236236867 12854133804215272854355301)
              ·
                refine ⟨2410150088290363660191619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12854133804215272854355301 2410150088290363660191619)
                ·
                  refine ⟨3615225132435545490287429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2410150088290363660191619 3615225132435545490287429)
                  ·
                    refine ⟨677854712331664779428893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3615225132435545490287429 677854712331664779428893)
                    ·
                      rfl

theorem cell23_3960352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 4, 1, 4].length) (baseStart_3960352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960352 prefixEnd_3960352 := by exact prefixLift 3960352
  have htrace : WordTrace (prefixWord ++ tailWord_3960352) baseStart_3960352 baseEnd_3960352 := by
    simpa [prefixWord, tailWord_3960352, baseEnd_3960352] using wordTrace_append hprefix tailTrace_3960352
  have hstable : (prefixWord ++ tailWord_3960352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960352).length < 2 ^ (prefixWord ++ tailWord_3960352).sum := by decide
  have hdescent : baseEnd_3960352 < baseStart_3960352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960368 : List Nat := [2, 1, 1, 1, 2, 3, 1, 4, 1, 5, 2]
def baseStart_3960368 : Nat := 118140960795 + 3960368 * 2 ^ 59
def prefixEnd_3960368 : Nat := 4983230072969 + 3 ^ 40 * 3960368 * 2
def baseEnd_3960368 : Nat := 2033572352685466275686605

theorem tailTrace_3960368 : CollatzResearch.WordTrace tailWord_3960368 prefixEnd_3960368 2033572352685466275686605 := by
  unfold tailWord_3960368
  simp only [CollatzResearch.WordTrace]
  refine ⟨72223243858135293925192879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96297658477513725233590505 72223243858135293925192879)
  ·
    refine ⟨108334865787202940887789319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72223243858135293925192879 108334865787202940887789319)
    ·
      refine ⟨162502298680804411331683979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108334865787202940887789319 162502298680804411331683979)
      ·
        refine ⟨243753448021206616997525969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162502298680804411331683979 243753448021206616997525969)
        ·
          refine ⟨182815086015904962748144477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243753448021206616997525969 182815086015904962748144477)
          ·
            refine ⟨68555657255964361030554179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182815086015904962748144477 68555657255964361030554179)
            ·
              refine ⟨102833485883946541545831269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68555657255964361030554179 102833485883946541545831269)
              ·
                refine ⟨19281278603239976539843363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102833485883946541545831269 19281278603239976539843363)
                ·
                  refine ⟨28921917904859964809765045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19281278603239976539843363 28921917904859964809765045)
                  ·
                    refine ⟨2711429803580621700915473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28921917904859964809765045 2711429803580621700915473)
                    ·
                      refine ⟨2033572352685466275686605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2711429803580621700915473 2033572352685466275686605)
                      ·
                        rfl

theorem cell23_3960368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 1, 5, 2].length) (baseStart_3960368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960368 prefixEnd_3960368 := by exact prefixLift 3960368
  have htrace : WordTrace (prefixWord ++ tailWord_3960368) baseStart_3960368 baseEnd_3960368 := by
    simpa [prefixWord, tailWord_3960368, baseEnd_3960368] using wordTrace_append hprefix tailTrace_3960368
  have hstable : (prefixWord ++ tailWord_3960368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960368).length < 2 ^ (prefixWord ++ tailWord_3960368).sum := by decide
  have hdescent : baseEnd_3960368 < baseStart_3960368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960375 : List Nat := [1, 1, 3, 1, 2, 5, 1, 2, 3, 1, 3]
def baseStart_3960375 : Nat := 118140960795 + 3960375 * 2 ^ 59
def prefixEnd_3960375 : Nat := 4983230072969 + 3 ^ 40 * 3960375 * 2
def baseEnd_3960375 : Nat := 2033575947050047748299073

theorem tailTrace_3960375 : CollatzResearch.WordTrace tailWord_3960375 prefixEnd_3960375 2033575947050047748299073 := by
  unfold tailWord_3960375
  simp only [CollatzResearch.WordTrace]
  refine ⟨144446743027245228045890579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96297828684830152030593719 144446743027245228045890579)
  ·
    refine ⟨216670114540867842068835869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144446743027245228045890579 216670114540867842068835869)
    ·
      refine ⟨81251292952825440775813451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216670114540867842068835869 81251292952825440775813451)
      ·
        refine ⟨121876939429238161163720177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81251292952825440775813451 121876939429238161163720177)
        ·
          refine ⟨91407704571928620872790133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121876939429238161163720177 91407704571928620872790133)
          ·
            refine ⟨8569472303618308206824075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91407704571928620872790133 8569472303618308206824075)
            ·
              refine ⟨12854208455427462310236113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8569472303618308206824075 12854208455427462310236113)
              ·
                refine ⟨9640656341570596732677085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12854208455427462310236113 9640656341570596732677085)
                ·
                  refine ⟨3615246128088973774753907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9640656341570596732677085 3615246128088973774753907)
                  ·
                    refine ⟨5422869192133460662130861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3615246128088973774753907 5422869192133460662130861)
                    ·
                      refine ⟨2033575947050047748299073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5422869192133460662130861 2033575947050047748299073)
                      ·
                        rfl

theorem cell23_3960375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 3, 1, 3].length) (baseStart_3960375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960375 prefixEnd_3960375 := by exact prefixLift 3960375
  have htrace : WordTrace (prefixWord ++ tailWord_3960375) baseStart_3960375 baseEnd_3960375 := by
    simpa [prefixWord, tailWord_3960375, baseEnd_3960375] using wordTrace_append hprefix tailTrace_3960375
  have hstable : (prefixWord ++ tailWord_3960375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960375).length < 2 ^ (prefixWord ++ tailWord_3960375).sum := by decide
  have hdescent : baseEnd_3960375 < baseStart_3960375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960378 : List Nat := [3, 1, 1, 1, 3, 2, 2, 4, 1, 5]
def baseStart_3960378 : Nat := 118140960795 + 3960378 * 2 ^ 59
def prefixEnd_3960378 : Nat := 4983230072969 + 3 ^ 40 * 3960378 * 2
def baseEnd_3960378 : Nat := 677859162497337078853853

theorem tailTrace_3960378 : CollatzResearch.WordTrace tailWord_3960378 prefixEnd_3960378 677859162497337078853853 := by
  unfold tailWord_3960378
  simp only [CollatzResearch.WordTrace]
  refine ⟨36111713111558589889562447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96297901630822906372166525 36111713111558589889562447)
  ·
    refine ⟨54167569667337884834343671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36111713111558589889562447 54167569667337884834343671)
    ·
      refine ⟨81251354501006827251515507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54167569667337884834343671 81251354501006827251515507)
      ·
        refine ⟨121877031751510240877273261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81251354501006827251515507 121877031751510240877273261)
        ·
          refine ⟨45703886906816340328977473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121877031751510240877273261 45703886906816340328977473)
          ·
            refine ⟨34277915180112255246733105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45703886906816340328977473 34277915180112255246733105)
            ·
              refine ⟨25708436385084191435049829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34277915180112255246733105 25708436385084191435049829)
              ·
                refine ⟨4820331822203285894071843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25708436385084191435049829 4820331822203285894071843)
                ·
                  refine ⟨7230497733304928841107765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4820331822203285894071843 7230497733304928841107765)
                  ·
                    refine ⟨677859162497337078853853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7230497733304928841107765 677859162497337078853853)
                    ·
                      rfl

theorem cell23_3960378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 1, 5].length) (baseStart_3960378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960378 prefixEnd_3960378 := by exact prefixLift 3960378
  have htrace : WordTrace (prefixWord ++ tailWord_3960378) baseStart_3960378 baseEnd_3960378 := by
    simpa [prefixWord, tailWord_3960378, baseEnd_3960378] using wordTrace_append hprefix tailTrace_3960378
  have hstable : (prefixWord ++ tailWord_3960378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960378).length < 2 ^ (prefixWord ++ tailWord_3960378).sum := by decide
  have hdescent : baseEnd_3960378 < baseStart_3960378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960385 : List Nat := [1, 2, 5, 1, 1, 1, 3, 1, 1, 5, 2]
def baseStart_3960385 : Nat := 118140960795 + 3960385 * 2 ^ 59
def prefixEnd_3960385 : Nat := 4983230072969 + 3 ^ 40 * 3960385 * 2
def baseEnd_3960385 : Nat := 2033581081856592709174027

theorem tailTrace_3960385 : CollatzResearch.WordTrace tailWord_3960385 prefixEnd_3960385 2033581081856592709174027 := by
  unfold tailWord_3960385
  simp only [CollatzResearch.WordTrace]
  refine ⟨144447107757208999753754609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96298071838139333169169739 144447107757208999753754609)
  ·
    refine ⟨108335330817906749815315957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144447107757208999753754609 108335330817906749815315957)
    ·
      refine ⟨10156437264178757795185871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108335330817906749815315957 10156437264178757795185871)
      ·
        refine ⟨15234655896268136692778807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10156437264178757795185871 15234655896268136692778807)
        ·
          refine ⟨22851983844402205039168211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15234655896268136692778807 22851983844402205039168211)
          ·
            refine ⟨34277975766603307558752317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22851983844402205039168211 34277975766603307558752317)
            ·
              refine ⟨12854240912476240334532119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34277975766603307558752317 12854240912476240334532119)
              ·
                refine ⟨19281361368714360501798179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12854240912476240334532119 19281361368714360501798179)
                ·
                  refine ⟨28922042053071540752697269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19281361368714360501798179 28922042053071540752697269)
                  ·
                    refine ⟨2711441442475456945565369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28922042053071540752697269 2711441442475456945565369)
                    ·
                      refine ⟨2033581081856592709174027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2711441442475456945565369 2033581081856592709174027)
                      ·
                        rfl

theorem cell23_3960385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_3960385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960385 prefixEnd_3960385 := by exact prefixLift 3960385
  have htrace : WordTrace (prefixWord ++ tailWord_3960385) baseStart_3960385 baseEnd_3960385 := by
    simpa [prefixWord, tailWord_3960385, baseEnd_3960385] using wordTrace_append hprefix tailTrace_3960385
  have hstable : (prefixWord ++ tailWord_3960385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960385).length < 2 ^ (prefixWord ++ tailWord_3960385).sum := by decide
  have hdescent : baseEnd_3960385 < baseStart_3960385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960432 : List Nat := [2, 1, 1, 1, 6, 1, 2, 2, 3, 2, 2]
def baseStart_3960432 : Nat := 118140960795 + 3960432 * 2 ^ 59
def prefixEnd_3960432 : Nat := 4983230072969 + 3 ^ 40 * 3960432 * 2
def baseEnd_3960432 : Nat := 2033605215447354025286311

theorem tailTrace_3960432 : CollatzResearch.WordTrace tailWord_3960432 prefixEnd_3960432 2033605215447354025286311 := by
  unfold tailWord_3960432
  simp only [CollatzResearch.WordTrace]
  refine ⟨72224410994019363390357775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96299214658692484520477033 72224410994019363390357775)
  ·
    refine ⟨108336616491029045085536663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72224410994019363390357775 108336616491029045085536663)
    ·
      refine ⟨162504924736543567628304995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108336616491029045085536663 162504924736543567628304995)
      ·
        refine ⟨243757387104815351442457493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162504924736543567628304995 243757387104815351442457493)
        ·
          refine ⟨11426127520538219598865195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 243757387104815351442457493 11426127520538219598865195)
          ·
            refine ⟨17139191280807329398297793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11426127520538219598865195 17139191280807329398297793)
            ·
              refine ⟨12854393460605497048723345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17139191280807329398297793 12854393460605497048723345)
              ·
                refine ⟨9640795095454122786542509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12854393460605497048723345 9640795095454122786542509)
                ·
                  refine ⟨3615298160795296044953441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9640795095454122786542509 3615298160795296044953441)
                  ·
                    refine ⟨2711473620596472033715081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3615298160795296044953441 2711473620596472033715081)
                    ·
                      refine ⟨2033605215447354025286311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2711473620596472033715081 2033605215447354025286311)
                      ·
                        rfl

theorem cell23_3960432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 3, 2, 2].length) (baseStart_3960432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960432 prefixEnd_3960432 := by exact prefixLift 3960432
  have htrace : WordTrace (prefixWord ++ tailWord_3960432) baseStart_3960432 baseEnd_3960432 := by
    simpa [prefixWord, tailWord_3960432, baseEnd_3960432] using wordTrace_append hprefix tailTrace_3960432
  have hstable : (prefixWord ++ tailWord_3960432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960432).length < 2 ^ (prefixWord ++ tailWord_3960432).sum := by decide
  have hdescent : baseEnd_3960432 < baseStart_3960432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960448 : List Nat := [2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 3]
def baseStart_3960448 : Nat := 118140960795 + 3960448 * 2 ^ 59
def prefixEnd_3960448 : Nat := 4983230072969 + 3 ^ 40 * 3960448 * 2
def baseEnd_3960448 : Nat := 2033613431137825962686237

theorem tailTrace_3960448 : CollatzResearch.WordTrace tailWord_3960448 prefixEnd_3960448 2033613431137825962686237 := by
  unfold tailWord_3960448
  simp only [CollatzResearch.WordTrace]
  refine ⟨72224702777990380756648999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96299603703987174342198665 72224702777990380756648999)
  ·
    refine ⟨108337054166985571134973499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72224702777990380756648999 108337054166985571134973499)
    ·
      refine ⟨162505581250478356702460249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108337054166985571134973499 162505581250478356702460249)
      ·
        refine ⟨121879185937858767526845187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162505581250478356702460249 121879185937858767526845187)
        ·
          refine ⟨182818778906788151290267781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121879185937858767526845187 182818778906788151290267781)
          ·
            refine ⟨34278521045022778366925209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182818778906788151290267781 34278521045022778366925209)
            ·
              refine ⟨25708890783767083775193907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34278521045022778366925209 25708890783767083775193907)
              ·
                refine ⟨38563336175650625662790861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25708890783767083775193907 38563336175650625662790861)
                ·
                  refine ⟨14461251065868984623546573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38563336175650625662790861 14461251065868984623546573)
                  ·
                    refine ⟨5422969149700869233829965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14461251065868984623546573 5422969149700869233829965)
                    ·
                      refine ⟨2033613431137825962686237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5422969149700869233829965 2033613431137825962686237)
                      ·
                        rfl

theorem cell23_3960448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 3].length) (baseStart_3960448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960448 prefixEnd_3960448 := by exact prefixLift 3960448
  have htrace : WordTrace (prefixWord ++ tailWord_3960448) baseStart_3960448 baseEnd_3960448 := by
    simpa [prefixWord, tailWord_3960448, baseEnd_3960448] using wordTrace_append hprefix tailTrace_3960448
  have hstable : (prefixWord ++ tailWord_3960448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960448).length < 2 ^ (prefixWord ++ tailWord_3960448).sum := by decide
  have hdescent : baseEnd_3960448 < baseStart_3960448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960451 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 1, 9]
def baseStart_3960451 : Nat := 118140960795 + 3960451 * 2 ^ 59
def prefixEnd_3960451 : Nat := 4983230072969 + 3 ^ 40 * 3960451 * 2
def baseEnd_3960451 : Nat := 677871657193263150316241

theorem tailTrace_3960451 : CollatzResearch.WordTrace tailWord_3960451 prefixEnd_3960451 677871657193263150316241 := by
  unfold tailWord_3960451
  simp only [CollatzResearch.WordTrace]
  refine ⟨144449514974969893025657207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96299676649979928683771471 144449514974969893025657207)
  ·
    refine ⟨216674272462454839538485811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144449514974969893025657207 216674272462454839538485811)
    ·
      refine ⟨325011408693682259307728717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216674272462454839538485811 325011408693682259307728717)
      ·
        refine ⟨121879278260130847240398269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325011408693682259307728717 121879278260130847240398269)
        ·
          refine ⟨45704729347549067715149351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121879278260130847240398269 45704729347549067715149351)
          ·
            refine ⟨68557094021323601572724027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45704729347549067715149351 68557094021323601572724027)
            ·
              refine ⟨102835641031985402359086041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68557094021323601572724027 102835641031985402359086041)
              ·
                refine ⟨77126730773989051769314531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102835641031985402359086041 77126730773989051769314531)
                ·
                  refine ⟨115690096160983577653971797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77126730773989051769314531 115690096160983577653971797)
                  ·
                    refine ⟨677871657193263150316241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 115690096160983577653971797 677871657193263150316241)
                    ·
                      rfl

theorem cell23_3960451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 9].length) (baseStart_3960451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960451 prefixEnd_3960451 := by exact prefixLift 3960451
  have htrace : WordTrace (prefixWord ++ tailWord_3960451) baseStart_3960451 baseEnd_3960451 := by
    simpa [prefixWord, tailWord_3960451, baseEnd_3960451] using wordTrace_append hprefix tailTrace_3960451
  have hstable : (prefixWord ++ tailWord_3960451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960451).length < 2 ^ (prefixWord ++ tailWord_3960451).sum := by decide
  have hdescent : baseEnd_3960451 < baseStart_3960451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960466 : List Nat := [3, 2, 3, 1, 3, 2, 1, 1, 3, 2, 2]
def baseStart_3960466 : Nat := 118140960795 + 3960466 * 2 ^ 59
def prefixEnd_3960466 : Nat := 4983230072969 + 3 ^ 40 * 3960466 * 2
def baseEnd_3960466 : Nat := 2033622673789606892261155

theorem tailTrace_3960466 : CollatzResearch.WordTrace tailWord_3960466 prefixEnd_3960466 2033622673789606892261155 := by
  unfold tailWord_3960466
  simp only [CollatzResearch.WordTrace]
  refine ⟨36112515517478887646863313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96300041379943700391635501 36112515517478887646863313)
  ·
    refine ⟨27084386638109165735147485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36112515517478887646863313 27084386638109165735147485)
    ·
      refine ⟨10156644989290937150680307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27084386638109165735147485 10156644989290937150680307)
      ·
        refine ⟨15234967483936405726020461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10156644989290937150680307 15234967483936405726020461)
        ·
          refine ⟨5713112806476152147257673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15234967483936405726020461 5713112806476152147257673)
          ·
            refine ⟨4284834604857114110443255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5713112806476152147257673 4284834604857114110443255)
            ·
              refine ⟨6427251907285671165664883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4284834604857114110443255 6427251907285671165664883)
              ·
                refine ⟨9640877860928506748497325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6427251907285671165664883 9640877860928506748497325)
                ·
                  refine ⟨3615329197848190030686497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9640877860928506748497325 3615329197848190030686497)
                  ·
                    refine ⟨2711496898386142523014873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3615329197848190030686497 2711496898386142523014873)
                    ·
                      refine ⟨2033622673789606892261155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2711496898386142523014873 2033622673789606892261155)
                      ·
                        rfl

theorem cell23_3960466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_3960466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960466 prefixEnd_3960466 := by exact prefixLift 3960466
  have htrace : WordTrace (prefixWord ++ tailWord_3960466) baseStart_3960466 baseEnd_3960466 := by
    simpa [prefixWord, tailWord_3960466, baseEnd_3960466] using wordTrace_append hprefix tailTrace_3960466
  have hstable : (prefixWord ++ tailWord_3960466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960466).length < 2 ^ (prefixWord ++ tailWord_3960466).sum := by decide
  have hdescent : baseEnd_3960466 < baseStart_3960466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960476 : List Nat := [2, 2, 3, 2, 4, 1, 2, 1, 2, 4]
def baseStart_3960476 : Nat := 118140960795 + 3960476 * 2 ^ 59
def prefixEnd_3960476 : Nat := 4983230072969 + 3 ^ 40 * 3960476 * 2
def baseEnd_3960476 : Nat := 677875936198717284378703

theorem tailTrace_3960476 : CollatzResearch.WordTrace tailWord_3960476 prefixEnd_3960476 677875936198717284378703 := by
  unfold tailWord_3960476
  simp only [CollatzResearch.WordTrace]
  refine ⟨72225213399939661147658641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96300284533252881530211521 72225213399939661147658641)
  ·
    refine ⟨54168910049954745860743981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72225213399939661147658641 54168910049954745860743981)
    ·
      refine ⟨20313341268733029697778993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54168910049954745860743981 20313341268733029697778993)
      ·
        refine ⟨15235005951549772273334245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20313341268733029697778993 15235005951549772273334245)
        ·
          refine ⟨2856563615915582301250171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15235005951549772273334245 2856563615915582301250171)
          ·
            refine ⟨4284845423873373451875257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2856563615915582301250171 4284845423873373451875257)
            ·
              refine ⟨3213634067905030088906443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4284845423873373451875257 3213634067905030088906443)
              ·
                refine ⟨4820451101857545133359665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3213634067905030088906443 4820451101857545133359665)
                ·
                  refine ⟨3615338326393158850019749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4820451101857545133359665 3615338326393158850019749)
                  ·
                    refine ⟨677875936198717284378703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3615338326393158850019749 677875936198717284378703)
                    ·
                      rfl

theorem cell23_3960476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_3960476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960476 prefixEnd_3960476 := by exact prefixLift 3960476
  have htrace : WordTrace (prefixWord ++ tailWord_3960476) baseStart_3960476 baseEnd_3960476 := by
    simpa [prefixWord, tailWord_3960476, baseEnd_3960476] using wordTrace_append hprefix tailTrace_3960476
  have hstable : (prefixWord ++ tailWord_3960476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960476).length < 2 ^ (prefixWord ++ tailWord_3960476).sum := by decide
  have hdescent : baseEnd_3960476 < baseStart_3960476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960491 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 9]
def baseStart_3960491 : Nat := 118140960795 + 3960491 * 2 ^ 59
def prefixEnd_3960491 : Nat := 4983230072969 + 3 ^ 40 * 3960491 * 2
def baseEnd_3960491 : Nat := 2033635510805969294448539

theorem tailTrace_3960491 : CollatzResearch.WordTrace tailWord_3960491 prefixEnd_3960491 2033635510805969294448539 := by
  unfold tailWord_3960491
  simp only [CollatzResearch.WordTrace]
  refine ⟨144450973894824979857113327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96300649263216653238075551 144450973894824979857113327)
  ·
    refine ⟨216676460842237469785669991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144450973894824979857113327 216676460842237469785669991)
    ·
      refine ⟨325014691263356204678504987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216676460842237469785669991 325014691263356204678504987)
      ·
        refine ⟨487522036895034307017757481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325014691263356204678504987 487522036895034307017757481)
        ·
          refine ⟨365641527671275730263318111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487522036895034307017757481 365641527671275730263318111)
          ·
            refine ⟨548462291506913595394977167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365641527671275730263318111 548462291506913595394977167)
            ·
              refine ⟨822693437260370393092465751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548462291506913595394977167 822693437260370393092465751)
              ·
                refine ⟨1234040155890555589638698627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 822693437260370393092465751 1234040155890555589638698627)
                ·
                  refine ⟨1851060233835833384458047941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1234040155890555589638698627 1851060233835833384458047941)
                  ·
                    refine ⟨347073793844218759585883989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1851060233835833384458047941 347073793844218759585883989)
                    ·
                      refine ⟨2033635510805969294448539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 347073793844218759585883989 2033635510805969294448539)
                      ·
                        rfl

theorem cell23_3960491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 9].length) (baseStart_3960491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960491 prefixEnd_3960491 := by exact prefixLift 3960491
  have htrace : WordTrace (prefixWord ++ tailWord_3960491) baseStart_3960491 baseEnd_3960491 := by
    simpa [prefixWord, tailWord_3960491, baseEnd_3960491] using wordTrace_append hprefix tailTrace_3960491
  have hstable : (prefixWord ++ tailWord_3960491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960491).length < 2 ^ (prefixWord ++ tailWord_3960491).sum := by decide
  have hdescent : baseEnd_3960491 < baseStart_3960491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960505 : List Nat := [1, 2, 1, 4, 1, 1, 3, 1, 3, 4, 2]
def baseStart_3960505 : Nat := 118140960795 + 3960505 * 2 ^ 59
def prefixEnd_3960505 : Nat := 4983230072969 + 3 ^ 40 * 3960505 * 2
def baseEnd_3960505 : Nat := 2033642699535132239673475

theorem tailTrace_3960505 : CollatzResearch.WordTrace tailWord_3960505 prefixEnd_3960505 2033642699535132239673475 := by
  unfold tailWord_3960505
  simp only [CollatzResearch.WordTrace]
  refine ⟨144451484516774260248122969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96300989677849506832081979 144451484516774260248122969)
  ·
    refine ⟨108338613387580695186092227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144451484516774260248122969 108338613387580695186092227)
    ·
      refine ⟨162507920081371042779138341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108338613387580695186092227 162507920081371042779138341)
      ·
        refine ⟨30470235015257070521088439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162507920081371042779138341 30470235015257070521088439)
        ·
          refine ⟨45705352522885605781632659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30470235015257070521088439 45705352522885605781632659)
          ·
            refine ⟨68558028784328408672448989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45705352522885605781632659 68558028784328408672448989)
            ·
              refine ⟨25709260794123153252168371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68558028784328408672448989 25709260794123153252168371)
              ·
                refine ⟨38563891191184729878252557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25709260794123153252168371 38563891191184729878252557)
                ·
                  refine ⟨14461459196694273704344709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38563891191184729878252557 14461459196694273704344709)
                  ·
                    refine ⟨2711523599380176319564633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14461459196694273704344709 2711523599380176319564633)
                    ·
                      refine ⟨2033642699535132239673475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2711523599380176319564633 2033642699535132239673475)
                      ·
                        rfl

theorem cell23_3960505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_3960505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960505 prefixEnd_3960505 := by exact prefixLift 3960505
  have htrace : WordTrace (prefixWord ++ tailWord_3960505) baseStart_3960505 baseEnd_3960505 := by
    simpa [prefixWord, tailWord_3960505, baseEnd_3960505] using wordTrace_append hprefix tailTrace_3960505
  have hstable : (prefixWord ++ tailWord_3960505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960505).length < 2 ^ (prefixWord ++ tailWord_3960505).sum := by decide
  have hdescent : baseEnd_3960505 < baseStart_3960505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960509 : List Nat := [1, 4, 1, 2, 1, 2, 5, 1, 1, 3, 2]
def baseStart_3960509 : Nat := 118140960795 + 3960509 * 2 ^ 59
def prefixEnd_3960509 : Nat := 4983230072969 + 3 ^ 40 * 3960509 * 2
def baseEnd_3960509 : Nat := 2033644753457750224023457

theorem tailTrace_3960509 : CollatzResearch.WordTrace tailWord_3960509 prefixEnd_3960509 2033644753457750224023457 := by
  unfold tailWord_3960509
  simp only [CollatzResearch.WordTrace]
  refine ⟨144451630408759768931268581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96301086939173179287512387 144451630408759768931268581)
  ·
    refine ⟨27084680701642456674612859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144451630408759768931268581 27084680701642456674612859)
    ·
      refine ⟨40627021052463685011919289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27084680701642456674612859 40627021052463685011919289)
      ·
        refine ⟨30470265789347763758939467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40627021052463685011919289 30470265789347763758939467)
        ·
          refine ⟨45705398684021645638409201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30470265789347763758939467 45705398684021645638409201)
          ·
            refine ⟨34279049013016234228806901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45705398684021645638409201 34279049013016234228806901)
            ·
              refine ⟨3213660844970271958950647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34279049013016234228806901 3213660844970271958950647)
              ·
                refine ⟨4820491267455407938425971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3213660844970271958950647 4820491267455407938425971)
                ·
                  refine ⟨7230736901183111907638957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4820491267455407938425971 7230736901183111907638957)
                  ·
                    refine ⟨2711526337943666965364609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7230736901183111907638957 2711526337943666965364609)
                    ·
                      refine ⟨2033644753457750224023457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2711526337943666965364609 2033644753457750224023457)
                      ·
                        rfl

theorem cell23_3960509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_3960509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960509 prefixEnd_3960509 := by exact prefixLift 3960509
  have htrace : WordTrace (prefixWord ++ tailWord_3960509) baseStart_3960509 baseEnd_3960509 := by
    simpa [prefixWord, tailWord_3960509, baseEnd_3960509] using wordTrace_append hprefix tailTrace_3960509
  have hstable : (prefixWord ++ tailWord_3960509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960509).length < 2 ^ (prefixWord ++ tailWord_3960509).sum := by decide
  have hdescent : baseEnd_3960509 < baseStart_3960509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960545 : List Nat := [1, 2, 3, 1, 5, 1, 1, 2, 7]
def baseStart_3960545 : Nat := 118140960795 + 3960545 * 2 ^ 59
def prefixEnd_3960545 : Nat := 4983230072969 + 3 ^ 40 * 3960545 * 2
def baseEnd_3960545 : Nat := 225962582084590231463699

theorem tailTrace_3960545 : CollatzResearch.WordTrace tailWord_3960545 prefixEnd_3960545 225962582084590231463699 := by
  unfold tailWord_3960545
  simp only [CollatzResearch.WordTrace]
  refine ⟨144452943436629347079579089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96301962291086231386386059 144452943436629347079579089)
  ·
    refine ⟨108339707577472010309684317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144452943436629347079579089 108339707577472010309684317)
    ·
      refine ⟨40627390341552003866131619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108339707577472010309684317 40627390341552003866131619)
      ·
        refine ⟨60941085512328005799197429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40627390341552003866131619 60941085512328005799197429)
        ·
          refine ⟨5713226766780750543674759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60941085512328005799197429 5713226766780750543674759)
          ·
            refine ⟨8569840150171125815512139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5713226766780750543674759 8569840150171125815512139)
            ·
              refine ⟨12854760225256688723268209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8569840150171125815512139 12854760225256688723268209)
              ·
                refine ⟨9641070168942516542451157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12854760225256688723268209 9641070168942516542451157)
                ·
                  refine ⟨225962582084590231463699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9641070168942516542451157 225962582084590231463699)
                  ·
                    rfl

theorem cell23_3960545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 7].length) (baseStart_3960545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960545 prefixEnd_3960545 := by exact prefixLift 3960545
  have htrace : WordTrace (prefixWord ++ tailWord_3960545) baseStart_3960545 baseEnd_3960545 := by
    simpa [prefixWord, tailWord_3960545, baseEnd_3960545] using wordTrace_append hprefix tailTrace_3960545
  have hstable : (prefixWord ++ tailWord_3960545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960545).length < 2 ^ (prefixWord ++ tailWord_3960545).sum := by decide
  have hdescent : baseEnd_3960545 < baseStart_3960545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960562 : List Nat := [3, 2, 1, 3, 1, 1, 4, 3, 5]
def baseStart_3960562 : Nat := 118140960795 + 3960562 * 2 ^ 59
def prefixEnd_3960562 : Nat := 4983230072969 + 3 ^ 40 * 3960562 * 2
def baseEnd_3960562 : Nat := 225963551992493168517857

theorem tailTrace_3960562 : CollatzResearch.WordTrace tailWord_3960562 prefixEnd_3960562 225963551992493168517857 := by
  unfold tailWord_3960562
  simp only [CollatzResearch.WordTrace]
  refine ⟨36113390869391939745736985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96302375651711839321965293 36113390869391939745736985)
  ·
    refine ⟨27085043152043954809302739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36113390869391939745736985 27085043152043954809302739)
    ·
      refine ⟨40627564728065932213954109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27085043152043954809302739 40627564728065932213954109)
      ·
        refine ⟨15235336773024724580232791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40627564728065932213954109 15235336773024724580232791)
        ·
          refine ⟨22853005159537086870349187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15235336773024724580232791 22853005159537086870349187)
          ·
            refine ⟨34279507739305630305523781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22853005159537086870349187 34279507739305630305523781)
            ·
              refine ⟨6427407701119805682285709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34279507739305630305523781 6427407701119805682285709)
              ·
                refine ⟨2410277887919927130857141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6427407701119805682285709 2410277887919927130857141)
                ·
                  refine ⟨225963551992493168517857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2410277887919927130857141 225963551992493168517857)
                  ·
                    rfl

theorem cell23_3960562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 3, 5].length) (baseStart_3960562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960562 prefixEnd_3960562 := by exact prefixLift 3960562
  have htrace : WordTrace (prefixWord ++ tailWord_3960562) baseStart_3960562 baseEnd_3960562 := by
    simpa [prefixWord, tailWord_3960562, baseEnd_3960562] using wordTrace_append hprefix tailTrace_3960562
  have hstable : (prefixWord ++ tailWord_3960562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960562).length < 2 ^ (prefixWord ++ tailWord_3960562).sum := by decide
  have hdescent : baseEnd_3960562 < baseStart_3960562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960568 : List Nat := [2, 1, 2, 1, 1, 2, 2, 4, 1, 2, 5]
def baseStart_3960568 : Nat := 118140960795 + 3960568 * 2 ^ 59
def prefixEnd_3960568 : Nat := 4983230072969 + 3 ^ 40 * 3960568 * 2
def baseEnd_3960568 : Nat := 2033675048816365493185685

theorem tailTrace_3960568 : CollatzResearch.WordTrace tailWord_3960568 prefixEnd_3960568 2033675048816365493185685 := by
  unfold tailWord_3960568
  simp only [CollatzResearch.WordTrace]
  refine ⟨72226891157773011003833179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96302521543697348005110905 72226891157773011003833179)
  ·
    refine ⟨108340336736659516505749769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72226891157773011003833179 108340336736659516505749769)
    ·
      refine ⟨81255252552494637379312327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108340336736659516505749769 81255252552494637379312327)
      ·
        refine ⟨121882878828741956068968491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81255252552494637379312327 121882878828741956068968491)
        ·
          refine ⟨182824318243112934103452737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121882878828741956068968491 182824318243112934103452737)
          ·
            refine ⟨137118238682334700577589553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182824318243112934103452737 137118238682334700577589553)
            ·
              refine ⟨102838679011751025433192165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137118238682334700577589553 102838679011751025433192165)
              ·
                refine ⟨19282252314703317268723531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102838679011751025433192165 19282252314703317268723531)
                ·
                  refine ⟨28923378472054975903085297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19282252314703317268723531 28923378472054975903085297)
                  ·
                    refine ⟨21692533854041231927313973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28923378472054975903085297 21692533854041231927313973)
                    ·
                      refine ⟨2033675048816365493185685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21692533854041231927313973 2033675048816365493185685)
                      ·
                        rfl

theorem cell23_3960568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 1, 2, 5].length) (baseStart_3960568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960568 prefixEnd_3960568 := by exact prefixLift 3960568
  have htrace : WordTrace (prefixWord ++ tailWord_3960568) baseStart_3960568 baseEnd_3960568 := by
    simpa [prefixWord, tailWord_3960568, baseEnd_3960568] using wordTrace_append hprefix tailTrace_3960568
  have hstable : (prefixWord ++ tailWord_3960568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960568).length < 2 ^ (prefixWord ++ tailWord_3960568).sum := by decide
  have hdescent : baseEnd_3960568 < baseStart_3960568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960595 : List Nat := [1, 1, 1, 2, 1, 3, 2, 3, 1, 6, 2]
def baseStart_3960595 : Nat := 118140960795 + 3960595 * 2 ^ 59
def prefixEnd_3960595 : Nat := 4983230072969 + 3 ^ 40 * 3960595 * 2
def baseEnd_3960595 : Nat := 2033688912794036887548061

theorem tailTrace_3960595 : CollatzResearch.WordTrace tailWord_3960595 prefixEnd_3960595 2033688912794036887548061 := by
  unfold tailWord_3960595
  simp only [CollatzResearch.WordTrace]
  refine ⟨144454767086448205618899239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96303178057632137079266159 144454767086448205618899239)
  ·
    refine ⟨216682150629672308428348859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144454767086448205618899239 216682150629672308428348859)
    ·
      refine ⟨325023225944508462642523289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216682150629672308428348859 325023225944508462642523289)
      ·
        refine ⟨243767419458381346981892467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325023225944508462642523289 243767419458381346981892467)
        ·
          refine ⟨365651129187572020472838701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243767419458381346981892467 365651129187572020472838701)
          ·
            refine ⟨137119173445339507677314513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 365651129187572020472838701 137119173445339507677314513)
            ·
              refine ⟨102839380084004630757985885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137119173445339507677314513 102839380084004630757985885)
              ·
                refine ⟨38564767531501736534244707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102839380084004630757985885 38564767531501736534244707)
                ·
                  refine ⟨57847151297252604801367061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38564767531501736534244707 57847151297252604801367061)
                  ·
                    refine ⟨2711585217058715850064081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 57847151297252604801367061 2711585217058715850064081)
                    ·
                      refine ⟨2033688912794036887548061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2711585217058715850064081 2033688912794036887548061)
                      ·
                        rfl

theorem cell23_3960595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 6, 2].length) (baseStart_3960595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960595 prefixEnd_3960595 := by exact prefixLift 3960595
  have htrace : WordTrace (prefixWord ++ tailWord_3960595) baseStart_3960595 baseEnd_3960595 := by
    simpa [prefixWord, tailWord_3960595, baseEnd_3960595] using wordTrace_append hprefix tailTrace_3960595
  have hstable : (prefixWord ++ tailWord_3960595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960595).length < 2 ^ (prefixWord ++ tailWord_3960595).sum := by decide
  have hdescent : baseEnd_3960595 < baseStart_3960595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960632 : List Nat := [2, 1, 2, 1, 3, 4, 1, 2, 2, 2, 3]
def baseStart_3960632 : Nat := 118140960795 + 3960632 * 2 ^ 59
def prefixEnd_3960632 : Nat := 4983230072969 + 3 ^ 40 * 3960632 * 2
def baseEnd_3960632 : Nat := 2033707911578253242785391

theorem tailTrace_3960632 : CollatzResearch.WordTrace tailWord_3960632 prefixEnd_3960632 2033707911578253242785391 := by
  unfold tailWord_3960632
  simp only [CollatzResearch.WordTrace]
  refine ⟨72228058293657080468998075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96304077724876107291997433 72228058293657080468998075)
  ·
    refine ⟨108342087440485620703497113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72228058293657080468998075 108342087440485620703497113)
    ·
      refine ⟨81256565580364215527622835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108342087440485620703497113 81256565580364215527622835)
      ·
        refine ⟨121884848370546323291434253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81256565580364215527622835 121884848370546323291434253)
        ·
          refine ⟨45706818138954871234287845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121884848370546323291434253 45706818138954871234287845)
          ·
            refine ⟨8570028401054038356428971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45706818138954871234287845 8570028401054038356428971)
            ·
              refine ⟨12855042601581057534643457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8570028401054038356428971 12855042601581057534643457)
              ·
                refine ⟨9641281951185793150982593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12855042601581057534643457 9641281951185793150982593)
                ·
                  refine ⟨7230961463389344863236945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9641281951185793150982593 7230961463389344863236945)
                  ·
                    refine ⟨5423221097542008647427709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7230961463389344863236945 5423221097542008647427709)
                    ·
                      refine ⟨2033707911578253242785391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5423221097542008647427709 2033707911578253242785391)
                      ·
                        rfl

theorem cell23_3960632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 2, 2, 3].length) (baseStart_3960632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960632 prefixEnd_3960632 := by exact prefixLift 3960632
  have htrace : WordTrace (prefixWord ++ tailWord_3960632) baseStart_3960632 baseEnd_3960632 := by
    simpa [prefixWord, tailWord_3960632, baseEnd_3960632] using wordTrace_append hprefix tailTrace_3960632
  have hstable : (prefixWord ++ tailWord_3960632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960632).length < 2 ^ (prefixWord ++ tailWord_3960632).sum := by decide
  have hdescent : baseEnd_3960632 < baseStart_3960632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960639 : List Nat := [1, 1, 2, 2, 6, 2, 1, 1, 3, 4]
def baseStart_3960639 : Nat := 118140960795 + 3960639 * 2 ^ 59
def prefixEnd_3960639 : Nat := 4983230072969 + 3 ^ 40 * 3960639 * 2
def baseEnd_3960639 : Nat := 677903835314278238465953

theorem tailTrace_3960639 : CollatzResearch.WordTrace tailWord_3960639 prefixEnd_3960639 677903835314278238465953 := by
  unfold tailWord_3960639
  simp only [CollatzResearch.WordTrace]
  refine ⟨144456371898288801133500971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96304247932192534089000647 144456371898288801133500971)
  ·
    refine ⟨216684557847433201700251457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144456371898288801133500971 216684557847433201700251457)
    ·
      refine ⟨162513418385574901275188593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216684557847433201700251457 162513418385574901275188593)
      ·
        refine ⟨121885063789181175956391445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162513418385574901275188593 121885063789181175956391445)
        ·
          refine ⟨5713362365117867622955849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 121885063789181175956391445 5713362365117867622955849)
          ·
            refine ⟨4285021773838400717216887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5713362365117867622955849 4285021773838400717216887)
            ·
              refine ⟨6427532660757601075825331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4285021773838400717216887 6427532660757601075825331)
              ·
                refine ⟨9641298991136401613737997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6427532660757601075825331 9641298991136401613737997)
                ·
                  refine ⟨3615487121676150605151749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9641298991136401613737997 3615487121676150605151749)
                  ·
                    refine ⟨677903835314278238465953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3615487121676150605151749 677903835314278238465953)
                    ·
                      rfl

theorem cell23_3960639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 3, 4].length) (baseStart_3960639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960639 prefixEnd_3960639 := by exact prefixLift 3960639
  have htrace : WordTrace (prefixWord ++ tailWord_3960639) baseStart_3960639 baseEnd_3960639 := by
    simpa [prefixWord, tailWord_3960639, baseEnd_3960639] using wordTrace_append hprefix tailTrace_3960639
  have hstable : (prefixWord ++ tailWord_3960639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960639).length < 2 ^ (prefixWord ++ tailWord_3960639).sum := by decide
  have hdescent : baseEnd_3960639 < baseStart_3960639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960652 : List Nat := [2, 2, 1, 3, 4, 1, 1, 3, 6]
def baseStart_3960652 : Nat := 118140960795 + 3960652 * 2 ^ 59
def prefixEnd_3960652 : Nat := 4983230072969 + 3 ^ 40 * 3960652 * 2
def baseEnd_3960652 : Nat := 225968686799038129392811

theorem tailTrace_3960652 : CollatzResearch.WordTrace tailWord_3960652 prefixEnd_3960652 225968686799038129392811 := by
  unfold tailWord_3960652
  simp only [CollatzResearch.WordTrace]
  refine ⟨72228423023620852176862105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96304564031494469569149473 72228423023620852176862105)
  ·
    refine ⟨54171317267715639132646579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72228423023620852176862105 54171317267715639132646579)
    ·
      refine ⟨81256975901573458698969869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54171317267715639132646579 81256975901573458698969869)
      ·
        refine ⟨30471365963090047012113701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81256975901573458698969869 30471365963090047012113701)
        ·
          refine ⟨5713381118079383814771319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30471365963090047012113701 5713381118079383814771319)
          ·
            refine ⟨8570071677119075722156979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5713381118079383814771319 8570071677119075722156979)
            ·
              refine ⟨12855107515678613583235469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8570071677119075722156979 12855107515678613583235469)
              ·
                refine ⟨4820665318379480093713301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12855107515678613583235469 4820665318379480093713301)
                ·
                  refine ⟨225968686799038129392811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4820665318379480093713301 225968686799038129392811)
                  ·
                    rfl

theorem cell23_3960652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 6].length) (baseStart_3960652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960652 prefixEnd_3960652 := by exact prefixLift 3960652
  have htrace : WordTrace (prefixWord ++ tailWord_3960652) baseStart_3960652 baseEnd_3960652 := by
    simpa [prefixWord, tailWord_3960652, baseEnd_3960652] using wordTrace_append hprefix tailTrace_3960652
  have hstable : (prefixWord ++ tailWord_3960652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960652).length < 2 ^ (prefixWord ++ tailWord_3960652).sum := by decide
  have hdescent : baseEnd_3960652 < baseStart_3960652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960665 : List Nat := [1, 2, 1, 2, 2, 3, 3, 1, 3, 5]
def baseStart_3960665 : Nat := 118140960795 + 3960665 * 2 ^ 59
def prefixEnd_3960665 : Nat := 4983230072969 + 3 ^ 40 * 3960665 * 2
def baseEnd_3960665 : Nat := 677908285479950537890913

theorem tailTrace_3960665 : CollatzResearch.WordTrace tailWord_3960665 prefixEnd_3960665 677908285479950537890913 := by
  unfold tailWord_3960665
  simp only [CollatzResearch.WordTrace]
  refine ⟨144457320196194607573947449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96304880130796405049298299 144457320196194607573947449)
  ·
    refine ⟨108342990147145955680460587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144457320196194607573947449 108342990147145955680460587)
    ·
      refine ⟨162514485220718933520690881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108342990147145955680460587 162514485220718933520690881)
      ·
        refine ⟨121885863915539200140518161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162514485220718933520690881 121885863915539200140518161)
        ·
          refine ⟨91414397936654400105388621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121885863915539200140518161 91414397936654400105388621)
          ·
            refine ⟨34280399226245400039520733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91414397936654400105388621 34280399226245400039520733)
            ·
              refine ⟨12855149709842025014820275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34280399226245400039520733 12855149709842025014820275)
              ·
                refine ⟨19282724564763037522230413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12855149709842025014820275 19282724564763037522230413)
                ·
                  refine ⟨7231021711786139070836405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19282724564763037522230413 7231021711786139070836405)
                  ·
                    refine ⟨677908285479950537890913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7231021711786139070836405 677908285479950537890913)
                    ·
                      rfl

theorem cell23_3960665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 5].length) (baseStart_3960665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960665 prefixEnd_3960665 := by exact prefixLift 3960665
  have htrace : WordTrace (prefixWord ++ tailWord_3960665) baseStart_3960665 baseEnd_3960665 := by
    simpa [prefixWord, tailWord_3960665, baseEnd_3960665] using wordTrace_append hprefix tailTrace_3960665
  have hstable : (prefixWord ++ tailWord_3960665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960665).length < 2 ^ (prefixWord ++ tailWord_3960665).sum := by decide
  have hdescent : baseEnd_3960665 < baseStart_3960665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960753 : List Nat := [1, 2, 2, 4, 2, 1, 2, 4, 1, 2, 2]
def baseStart_3960753 : Nat := 118140960795 + 3960753 * 2 ^ 59
def prefixEnd_3960753 : Nat := 4983230072969 + 3 ^ 40 * 3960753 * 2
def baseEnd_3960753 : Nat := 2033770042737447269372335

theorem tailTrace_3960753 : CollatzResearch.WordTrace tailWord_3960753 prefixEnd_3960753 2033770042737447269372335 := by
  unfold tailWord_3960753
  simp only [CollatzResearch.WordTrace]
  refine ⟨144460529819875798603150913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96307019879917199068767275 144460529819875798603150913)
  ·
    refine ⟨108345397364906848952363185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144460529819875798603150913 108345397364906848952363185)
    ·
      refine ⟨81259048023680136714272389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108345397364906848952363185 81259048023680136714272389)
      ·
        refine ⟨15236071504440025633926073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81259048023680136714272389 15236071504440025633926073)
        ·
          refine ⟨11427053628330019225444555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15236071504440025633926073 11427053628330019225444555)
          ·
            refine ⟨17140580442495028838166833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11427053628330019225444555 17140580442495028838166833)
            ·
              refine ⟨12855435331871271628625125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17140580442495028838166833 12855435331871271628625125)
              ·
                refine ⟨2410394124725863430367211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12855435331871271628625125 2410394124725863430367211)
                ·
                  refine ⟨3615591187088795145550817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2410394124725863430367211 3615591187088795145550817)
                  ·
                    refine ⟨2711693390316596359163113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3615591187088795145550817 2711693390316596359163113)
                    ·
                      refine ⟨2033770042737447269372335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2711693390316596359163113 2033770042737447269372335)
                      ·
                        rfl

theorem cell23_3960753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_3960753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960753 prefixEnd_3960753 := by exact prefixLift 3960753
  have htrace : WordTrace (prefixWord ++ tailWord_3960753) baseStart_3960753 baseEnd_3960753 := by
    simpa [prefixWord, tailWord_3960753, baseEnd_3960753] using wordTrace_append hprefix tailTrace_3960753
  have hstable : (prefixWord ++ tailWord_3960753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960753).length < 2 ^ (prefixWord ++ tailWord_3960753).sum := by decide
  have hdescent : baseEnd_3960753 < baseStart_3960753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960756 : List Nat := [2, 5, 2, 1, 2, 1, 1, 2, 1, 1, 5]
def baseStart_3960756 : Nat := 118140960795 + 3960756 * 2 ^ 59
def prefixEnd_3960756 : Nat := 4983230072969 + 3 ^ 40 * 3960756 * 2
def baseEnd_3960756 : Nat := 2033771583179410757634821

theorem tailTrace_3960756 : CollatzResearch.WordTrace tailWord_3960756 prefixEnd_3960756 2033771583179410757634821 := by
  unfold tailWord_3960756
  simp only [CollatzResearch.WordTrace]
  refine ⟨72230319619432465057755061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96307092825909953410340081 72230319619432465057755061)
  ·
    refine ⟨6771592464321793599164537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72230319619432465057755061 6771592464321793599164537)
    ·
      refine ⟨5078694348241345199373403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6771592464321793599164537 5078694348241345199373403)
      ·
        refine ⟨7618041522362017799060105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5078694348241345199373403 7618041522362017799060105)
        ·
          refine ⟨5713531141771513349295079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7618041522362017799060105 5713531141771513349295079)
          ·
            refine ⟨8570296712657270023942619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5713531141771513349295079 8570296712657270023942619)
            ·
              refine ⟨12855445068985905035913929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8570296712657270023942619 12855445068985905035913929)
              ·
                refine ⟨9641583801739428776935447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12855445068985905035913929 9641583801739428776935447)
                ·
                  refine ⟨14462375702609143165403171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9641583801739428776935447 14462375702609143165403171)
                  ·
                    refine ⟨21693563553913714748104757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14462375702609143165403171 21693563553913714748104757)
                    ·
                      refine ⟨2033771583179410757634821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21693563553913714748104757 2033771583179410757634821)
                      ·
                        rfl

theorem cell23_3960756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_3960756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960756 prefixEnd_3960756 := by exact prefixLift 3960756
  have htrace : WordTrace (prefixWord ++ tailWord_3960756) baseStart_3960756 baseEnd_3960756 := by
    simpa [prefixWord, tailWord_3960756, baseEnd_3960756] using wordTrace_append hprefix tailTrace_3960756
  have hstable : (prefixWord ++ tailWord_3960756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960756).length < 2 ^ (prefixWord ++ tailWord_3960756).sum := by decide
  have hdescent : baseEnd_3960756 < baseStart_3960756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960762 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 2, 7, 2]
def baseStart_3960762 : Nat := 118140960795 + 3960762 * 2 ^ 59
def prefixEnd_3960762 : Nat := 4983230072969 + 3 ^ 40 * 3960762 * 2
def baseEnd_3960762 : Nat := 2033774664063337734159793

theorem tailTrace_3960762 : CollatzResearch.WordTrace tailWord_3960762 prefixEnd_3960762 2033774664063337734159793 := by
  unfold tailWord_3960762
  simp only [CollatzResearch.WordTrace]
  refine ⟨36115214519210798285057135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96307238717895462093485693 36115214519210798285057135)
  ·
    refine ⟨54172821778816197427585703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36115214519210798285057135 54172821778816197427585703)
    ·
      refine ⟨81259232668224296141378555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54172821778816197427585703 81259232668224296141378555)
      ·
        refine ⟨121888849002336444212067833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81259232668224296141378555 121888849002336444212067833)
        ·
          refine ⟨91416636751752333159050875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121888849002336444212067833 91416636751752333159050875)
          ·
            refine ⟨137124955127628499738576313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91416636751752333159050875 137124955127628499738576313)
            ·
              refine ⟨102843716345721374803932235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137124955127628499738576313 102843716345721374803932235)
              ·
                refine ⟨154265574518582062205898353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102843716345721374803932235 154265574518582062205898353)
                ·
                  refine ⟨115699180888936546654423765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154265574518582062205898353 115699180888936546654423765)
                  ·
                    refine ⟨2711699552084450312213057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 115699180888936546654423765 2711699552084450312213057)
                    ·
                      refine ⟨2033774664063337734159793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2711699552084450312213057 2033774664063337734159793)
                      ·
                        rfl

theorem cell23_3960762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 2, 7, 2].length) (baseStart_3960762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960762 prefixEnd_3960762 := by exact prefixLift 3960762
  have htrace : WordTrace (prefixWord ++ tailWord_3960762) baseStart_3960762 baseEnd_3960762 := by
    simpa [prefixWord, tailWord_3960762, baseEnd_3960762] using wordTrace_append hprefix tailTrace_3960762
  have hstable : (prefixWord ++ tailWord_3960762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960762).length < 2 ^ (prefixWord ++ tailWord_3960762).sum := by decide
  have hdescent : baseEnd_3960762 < baseStart_3960762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960785 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 4, 6]
def baseStart_3960785 : Nat := 118140960795 + 3960785 * 2 ^ 59
def prefixEnd_3960785 : Nat := 4983230072969 + 3 ^ 40 * 3960785 * 2
def baseEnd_3960785 : Nat := 677928824706130381390729

theorem tailTrace_3960785 : CollatzResearch.WordTrace tailWord_3960785 prefixEnd_3960785 677928824706130381390729 := by
  unfold tailWord_3960785
  simp only [CollatzResearch.WordTrace]
  refine ⟨144461696955759868068315809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96307797970506578712210539 144461696955759868068315809)
  ·
    refine ⟨108346272716819901051236857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144461696955759868068315809 108346272716819901051236857)
    ·
      refine ⟨81259704537614925788427643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108346272716819901051236857 81259704537614925788427643)
      ·
        refine ⟨121889556806422388682641465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81259704537614925788427643 121889556806422388682641465)
        ·
          refine ⟨91417167604816791511981099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121889556806422388682641465 91417167604816791511981099)
          ·
            refine ⟨137125751407225187267971649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91417167604816791511981099 137125751407225187267971649)
            ·
              refine ⟨102844313555418890450978737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137125751407225187267971649 102844313555418890450978737)
              ·
                refine ⟨77133235166564167838234053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102844313555418890450978737 77133235166564167838234053)
                ·
                  refine ⟨14462481593730781469668885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77133235166564167838234053 14462481593730781469668885)
                  ·
                    refine ⟨677928824706130381390729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14462481593730781469668885 677928824706130381390729)
                    ·
                      rfl

theorem cell23_3960785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 6].length) (baseStart_3960785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960785 prefixEnd_3960785 := by exact prefixLift 3960785
  have htrace : WordTrace (prefixWord ++ tailWord_3960785) baseStart_3960785 baseEnd_3960785 := by
    simpa [prefixWord, tailWord_3960785, baseEnd_3960785] using wordTrace_append hprefix tailTrace_3960785
  have hstable : (prefixWord ++ tailWord_3960785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960785).length < 2 ^ (prefixWord ++ tailWord_3960785).sum := by decide
  have hdescent : baseEnd_3960785 < baseStart_3960785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960830 : List Nat := [4, 2, 2, 2, 1, 3, 1, 2, 1, 3, 2]
def baseStart_3960830 : Nat := 118140960795 + 3960830 * 2 ^ 59
def prefixEnd_3960830 : Nat := 4983230072969 + 3 ^ 40 * 3960830 * 2
def baseEnd_3960830 : Nat := 2033809580747843468109481

theorem tailTrace_3960830 : CollatzResearch.WordTrace tailWord_3960830 prefixEnd_3960830 2033809580747843468109481 := by
  unfold tailWord_3960830
  simp only [CollatzResearch.WordTrace]
  refine ⟨18057917280074605094212993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96308892160397893835802629 18057917280074605094212993)
  ·
    refine ⟨13543437960055953820659745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18057917280074605094212993 13543437960055953820659745)
    ·
      refine ⟨10157578470041965365494809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13543437960055953820659745 10157578470041965365494809)
      ·
        refine ⟨7618183852531474024121107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10157578470041965365494809 7618183852531474024121107)
        ·
          refine ⟨11427275778797211036181661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7618183852531474024121107 11427275778797211036181661)
          ·
            refine ⟨4285228417048954138568123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11427275778797211036181661 4285228417048954138568123)
            ·
              refine ⟨6427842625573431207852185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4285228417048954138568123 6427842625573431207852185)
              ·
                refine ⟨4820881969180073405889139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6427842625573431207852185 4820881969180073405889139)
                ·
                  refine ⟨7231322953770110108833709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4820881969180073405889139 7231322953770110108833709)
                  ·
                    refine ⟨2711746107663791290812641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7231322953770110108833709 2711746107663791290812641)
                    ·
                      refine ⟨2033809580747843468109481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2711746107663791290812641 2033809580747843468109481)
                      ·
                        rfl

theorem cell23_3960830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_3960830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960830 prefixEnd_3960830 := by exact prefixLift 3960830
  have htrace : WordTrace (prefixWord ++ tailWord_3960830) baseStart_3960830 baseEnd_3960830 := by
    simpa [prefixWord, tailWord_3960830, baseEnd_3960830] using wordTrace_append hprefix tailTrace_3960830
  have hstable : (prefixWord ++ tailWord_3960830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960830).length < 2 ^ (prefixWord ++ tailWord_3960830).sum := by decide
  have hdescent : baseEnd_3960830 < baseStart_3960830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960835 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 8]
def baseStart_3960835 : Nat := 118140960795 + 3960835 * 2 ^ 59
def prefixEnd_3960835 : Nat := 4983230072969 + 3 ^ 40 * 3960835 * 2
def baseEnd_3960835 : Nat := 2033812148151115948546957

theorem tailTrace_3960835 : CollatzResearch.WordTrace tailWord_3960835 prefixEnd_3960835 2033812148151115948546957 := by
  unfold tailWord_3960835
  simp only [CollatzResearch.WordTrace]
  refine ⟨144463520605578726607635959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96309013737052484405090639 144463520605578726607635959)
  ·
    refine ⟨216695280908368089911453939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144463520605578726607635959 216695280908368089911453939)
    ·
      refine ⟨325042921362552134867180909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216695280908368089911453939 325042921362552134867180909)
      ·
        refine ⟨121891095510957050575192841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325042921362552134867180909 121891095510957050575192841)
        ·
          refine ⟨91418321633217787931394631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121891095510957050575192841 91418321633217787931394631)
          ·
            refine ⟨137127482449826681897091947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91418321633217787931394631 137127482449826681897091947)
            ·
              refine ⟨205691223674740022845637921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137127482449826681897091947 205691223674740022845637921)
              ·
                refine ⟨154268417756055017134228441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205691223674740022845637921 154268417756055017134228441)
                ·
                  refine ⟨115701313317041262850671331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154268417756055017134228441 115701313317041262850671331)
                  ·
                    refine ⟨173551969975561894276006997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 115701313317041262850671331 173551969975561894276006997)
                    ·
                      refine ⟨2033812148151115948546957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 173551969975561894276006997 2033812148151115948546957)
                      ·
                        rfl

theorem cell23_3960835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_3960835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960835 prefixEnd_3960835 := by exact prefixLift 3960835
  have htrace : WordTrace (prefixWord ++ tailWord_3960835) baseStart_3960835 baseEnd_3960835 := by
    simpa [prefixWord, tailWord_3960835, baseEnd_3960835] using wordTrace_append hprefix tailTrace_3960835
  have hstable : (prefixWord ++ tailWord_3960835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960835).length < 2 ^ (prefixWord ++ tailWord_3960835).sum := by decide
  have hdescent : baseEnd_3960835 < baseStart_3960835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960869 : List Nat := [1, 3, 1, 2, 2, 3, 1, 1, 2, 5, 2]
def baseStart_3960869 : Nat := 118140960795 + 3960869 * 2 ^ 59
def prefixEnd_3960869 : Nat := 4983230072969 + 3 ^ 40 * 3960869 * 2
def baseEnd_3960869 : Nat := 2033829606493368815521801

theorem tailTrace_3960869 : CollatzResearch.WordTrace tailWord_3960869 prefixEnd_3960869 2033829606493368815521801 := by
  unfold tailWord_3960869
  simp only [CollatzResearch.WordTrace]
  refine ⟨144464760687455550414373661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96309840458303700276249107 144464760687455550414373661)
  ·
    refine ⟨54174285257795831405390123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144464760687455550414373661 54174285257795831405390123)
    ·
      refine ⟨81261427886693747108085185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54174285257795831405390123 81261427886693747108085185)
      ·
        refine ⟨60946070915020310331063889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81261427886693747108085185 60946070915020310331063889)
        ·
          refine ⟨45709553186265232748297917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60946070915020310331063889 45709553186265232748297917)
          ·
            refine ⟨17141082444849462280611719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45709553186265232748297917 17141082444849462280611719)
            ·
              refine ⟨25711623667274193420917579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17141082444849462280611719 25711623667274193420917579)
              ·
                refine ⟨38567435500911290131376369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25711623667274193420917579 38567435500911290131376369)
                ·
                  refine ⟨28925576625683467598532277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38567435500911290131376369 28925576625683467598532277)
                  ·
                    refine ⟨2711772808657825087362401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28925576625683467598532277 2711772808657825087362401)
                    ·
                      refine ⟨2033829606493368815521801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2711772808657825087362401 2033829606493368815521801)
                      ·
                        rfl

theorem cell23_3960869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 5, 2].length) (baseStart_3960869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960869 prefixEnd_3960869 := by exact prefixLift 3960869
  have htrace : WordTrace (prefixWord ++ tailWord_3960869) baseStart_3960869 baseEnd_3960869 := by
    simpa [prefixWord, tailWord_3960869, baseEnd_3960869] using wordTrace_append hprefix tailTrace_3960869
  have hstable : (prefixWord ++ tailWord_3960869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960869).length < 2 ^ (prefixWord ++ tailWord_3960869).sum := by decide
  have hdescent : baseEnd_3960869 < baseStart_3960869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960886 : List Nat := [5, 1, 2, 1, 1, 1, 1, 2, 2, 5, 2]
def baseStart_3960886 : Nat := 118140960795 + 3960886 * 2 ^ 59
def prefixEnd_3960886 : Nat := 4983230072969 + 3 ^ 40 * 3960886 * 2
def baseEnd_3960886 : Nat := 2033838335664495249009223

theorem tailTrace_3960886 : CollatzResearch.WordTrace tailWord_3960886 prefixEnd_3960886 2033838335664495249009223 := by
  unfold tailWord_3960886
  simp only [CollatzResearch.WordTrace]
  refine ⟨9029086295524622644858907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96310253818929308211828341 9029086295524622644858907)
  ·
    refine ⟨13543629443286933967288361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9029086295524622644858907 13543629443286933967288361)
    ·
      refine ⟨10157722082465200475466271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13543629443286933967288361 10157722082465200475466271)
      ·
        refine ⟨15236583123697800713199407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10157722082465200475466271 15236583123697800713199407)
        ·
          refine ⟨22854874685546701069799111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15236583123697800713199407 22854874685546701069799111)
          ·
            refine ⟨34282312028320051604698667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22854874685546701069799111 34282312028320051604698667)
            ·
              refine ⟨51423468042480077407048001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34282312028320051604698667 51423468042480077407048001)
              ·
                refine ⟨38567601031860058055286001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51423468042480077407048001 38567601031860058055286001)
                ·
                  refine ⟨28925700773895043541464501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38567601031860058055286001 28925700773895043541464501)
                  ·
                    refine ⟨2711784447552660332012297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28925700773895043541464501 2711784447552660332012297)
                    ·
                      refine ⟨2033838335664495249009223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2711784447552660332012297 2033838335664495249009223)
                      ·
                        rfl

theorem cell23_3960886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_3960886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960886 prefixEnd_3960886 := by exact prefixLift 3960886
  have htrace : WordTrace (prefixWord ++ tailWord_3960886) baseStart_3960886 baseEnd_3960886 := by
    simpa [prefixWord, tailWord_3960886, baseEnd_3960886] using wordTrace_append hprefix tailTrace_3960886
  have hstable : (prefixWord ++ tailWord_3960886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960886).length < 2 ^ (prefixWord ++ tailWord_3960886).sum := by decide
  have hdescent : baseEnd_3960886 < baseStart_3960886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960919 : List Nat := [1, 1, 3, 2, 2, 1, 2, 4, 2, 2, 3]
def baseStart_3960919 : Nat := 118140960795 + 3960919 * 2 ^ 59
def prefixEnd_3960919 : Nat := 4983230072969 + 3 ^ 40 * 3960919 * 2
def baseEnd_3960919 : Nat := 2033855280526093619896571

theorem tailTrace_3960919 : CollatzResearch.WordTrace tailWord_3960919 prefixEnd_3960919 2033855280526093619896571 := by
  unfold tailWord_3960919
  simp only [CollatzResearch.WordTrace]
  refine ⟨144466584337274408953693811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96311056224849605969129207 144466584337274408953693811)
  ·
    refine ⟨216699876505911613430540717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144466584337274408953693811 216699876505911613430540717)
    ·
      refine ⟨81262453689716855036452769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216699876505911613430540717 81262453689716855036452769)
      ·
        refine ⟨60946840267287641277339577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81262453689716855036452769 60946840267287641277339577)
        ·
          refine ⟨45710130200465730958004683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60946840267287641277339577 45710130200465730958004683)
          ·
            refine ⟨68565195300698596437007025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45710130200465730958004683 68565195300698596437007025)
            ·
              refine ⟨51423896475523947327755269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68565195300698596437007025 51423896475523947327755269)
              ·
                refine ⟨9641980589160740123954113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51423896475523947327755269 9641980589160740123954113)
                ·
                  refine ⟨7231485441870555092965585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9641980589160740123954113 7231485441870555092965585)
                  ·
                    refine ⟨5423614081402916319724189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7231485441870555092965585 5423614081402916319724189)
                    ·
                      refine ⟨2033855280526093619896571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5423614081402916319724189 2033855280526093619896571)
                      ·
                        rfl

theorem cell23_3960919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 2, 3].length) (baseStart_3960919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960919 prefixEnd_3960919 := by exact prefixLift 3960919
  have htrace : WordTrace (prefixWord ++ tailWord_3960919) baseStart_3960919 baseEnd_3960919 := by
    simpa [prefixWord, tailWord_3960919, baseEnd_3960919] using wordTrace_append hprefix tailTrace_3960919
  have hstable : (prefixWord ++ tailWord_3960919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960919).length < 2 ^ (prefixWord ++ tailWord_3960919).sum := by decide
  have hdescent : baseEnd_3960919 < baseStart_3960919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960922 : List Nat := [3, 1, 1, 2, 1, 1, 5, 1, 8]
def baseStart_3960922 : Nat := 118140960795 + 3960922 * 2 ^ 59
def prefixEnd_3960922 : Nat := 4983230072969 + 3 ^ 40 * 3960922 * 2
def baseEnd_3960922 : Nat := 225984091218673012017673

theorem tailTrace_3960922 : CollatzResearch.WordTrace tailWord_3960922 prefixEnd_3960922 225984091218673012017673 := by
  unfold tailWord_3960922
  simp only [CollatzResearch.WordTrace]
  refine ⟨36116673439065885116513255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96311129170842360310702013 36116673439065885116513255)
  ·
    refine ⟨54175010158598827674769883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36116673439065885116513255 54175010158598827674769883)
    ·
      refine ⟨81262515237898241512154825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54175010158598827674769883 81262515237898241512154825)
      ·
        refine ⟨60946886428423681134116119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81262515237898241512154825 60946886428423681134116119)
        ·
          refine ⟨91420329642635521701174179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60946886428423681134116119 91420329642635521701174179)
          ·
            refine ⟨137130494463953282551761269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91420329642635521701174179 137130494463953282551761269)
            ·
              refine ⟨12855983855995620239227619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137130494463953282551761269 12855983855995620239227619)
              ·
                refine ⟨19283975783993430358841429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12855983855995620239227619 19283975783993430358841429)
                ·
                  refine ⟨225984091218673012017673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19283975783993430358841429 225984091218673012017673)
                  ·
                    rfl

theorem cell23_3960922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 8].length) (baseStart_3960922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960922 prefixEnd_3960922 := by exact prefixLift 3960922
  have htrace : WordTrace (prefixWord ++ tailWord_3960922) baseStart_3960922 baseEnd_3960922 := by
    simpa [prefixWord, tailWord_3960922, baseEnd_3960922] using wordTrace_append hprefix tailTrace_3960922
  have hstable : (prefixWord ++ tailWord_3960922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960922).length < 2 ^ (prefixWord ++ tailWord_3960922).sum := by decide
  have hdescent : baseEnd_3960922 < baseStart_3960922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960969 : List Nat := [1, 2, 1, 1, 4, 2, 1, 5, 1, 5]
def baseStart_3960969 : Nat := 118140960795 + 3960969 * 2 ^ 59
def prefixEnd_3960969 : Nat := 4983230072969 + 3 ^ 40 * 3960969 * 2
def baseEnd_3960969 : Nat := 677960318186272808090447

theorem tailTrace_3960969 : CollatzResearch.WordTrace tailWord_3960969 prefixEnd_3960969 677960318186272808090447 := by
  unfold tailWord_3960969
  simp only [CollatzResearch.WordTrace]
  refine ⟨144468407987093267493013961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96312271991395511662009307 144468407987093267493013961)
  ·
    refine ⟨108351305990319950619760471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144468407987093267493013961 108351305990319950619760471)
    ·
      refine ⟨162526958985479925929640707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108351305990319950619760471 162526958985479925929640707)
      ·
        refine ⟨243790438478219888894461061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162526958985479925929640707 243790438478219888894461061)
        ·
          refine ⟨45710707214666229167711449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243790438478219888894461061 45710707214666229167711449)
          ·
            refine ⟨34283030410999671875783587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45710707214666229167711449 34283030410999671875783587)
            ·
              refine ⟨51424545616499507813675381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34283030410999671875783587 51424545616499507813675381)
              ·
                refine ⟨4821051151546828857532067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51424545616499507813675381 4821051151546828857532067)
                ·
                  refine ⟨7231576727320243286298101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4821051151546828857532067 7231576727320243286298101)
                  ·
                    refine ⟨677960318186272808090447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7231576727320243286298101 677960318186272808090447)
                    ·
                      rfl

theorem cell23_3960969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 5].length) (baseStart_3960969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960969 prefixEnd_3960969 := by exact prefixLift 3960969
  have htrace : WordTrace (prefixWord ++ tailWord_3960969) baseStart_3960969 baseEnd_3960969 := by
    simpa [prefixWord, tailWord_3960969, baseEnd_3960969] using wordTrace_append hprefix tailTrace_3960969
  have hstable : (prefixWord ++ tailWord_3960969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960969).length < 2 ^ (prefixWord ++ tailWord_3960969).sum := by decide
  have hdescent : baseEnd_3960969 < baseStart_3960969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960976 : List Nat := [2, 1, 1, 1, 1, 1, 7, 2, 2, 3, 2]
def baseStart_3960976 : Nat := 118140960795 + 3960976 * 2 ^ 59
def prefixEnd_3960976 : Nat := 4983230072969 + 3 ^ 40 * 3960976 * 2
def baseEnd_3960976 : Nat := 2033884548923399896883809

theorem tailTrace_3960976 : CollatzResearch.WordTrace tailWord_3960976 prefixEnd_3960976 2033884548923399896883809 := by
  unfold tailWord_3960976
  simp only [CollatzResearch.WordTrace]
  refine ⟨72234331649033953844259391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96312442198711938459012521 72234331649033953844259391)
  ·
    refine ⟨108351497473550930766389087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72234331649033953844259391 108351497473550930766389087)
    ·
      refine ⟨162527246210326396149583631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108351497473550930766389087 162527246210326396149583631)
      ·
        refine ⟨243790869315489594224375447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162527246210326396149583631 243790869315489594224375447)
        ·
          refine ⟨365686303973234391336563171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243790869315489594224375447 365686303973234391336563171)
          ·
            refine ⟨548529455959851587004844757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365686303973234391336563171 548529455959851587004844757)
            ·
              refine ⟨12856159124059021570426049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 548529455959851587004844757 12856159124059021570426049)
              ·
                refine ⟨9642119343044266177819537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12856159124059021570426049 9642119343044266177819537)
                ·
                  refine ⟨7231589507283199633364653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9642119343044266177819537 7231589507283199633364653)
                  ·
                    refine ⟨2711846065231199862511745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7231589507283199633364653 2711846065231199862511745)
                    ·
                      refine ⟨2033884548923399896883809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2711846065231199862511745 2033884548923399896883809)
                      ·
                        rfl

theorem cell23_3960976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 2, 3, 2].length) (baseStart_3960976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960976 prefixEnd_3960976 := by exact prefixLift 3960976
  have htrace : WordTrace (prefixWord ++ tailWord_3960976) baseStart_3960976 baseEnd_3960976 := by
    simpa [prefixWord, tailWord_3960976, baseEnd_3960976] using wordTrace_append hprefix tailTrace_3960976
  have hstable : (prefixWord ++ tailWord_3960976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960976).length < 2 ^ (prefixWord ++ tailWord_3960976).sum := by decide
  have hdescent : baseEnd_3960976 < baseStart_3960976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960990 : List Nat := [4, 3, 1, 1, 3, 2, 2, 1, 6]
def baseStart_3960990 : Nat := 118140960795 + 3960990 * 2 ^ 59
def prefixEnd_3960990 : Nat := 4983230072969 + 3 ^ 40 * 3960990 * 2
def baseEnd_3960990 : Nat := 225987970850284760234305

theorem tailTrace_3960990 : CollatzResearch.WordTrace tailWord_3960990 prefixEnd_3960990 225987970850284760234305 := by
  unfold tailWord_3960990
  simp only [CollatzResearch.WordTrace]
  refine ⟨18058646740002148509941053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96312782613344792053018949 18058646740002148509941053)
  ·
    refine ⟨6771992527500805691227895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18058646740002148509941053 6771992527500805691227895)
    ·
      refine ⟨10157988791251208536841843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6771992527500805691227895 10157988791251208536841843)
      ·
        refine ⟨15236983186876812805262765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10157988791251208536841843 15236983186876812805262765)
        ·
          refine ⟨5713868695078804801973537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15236983186876812805262765 5713868695078804801973537)
          ·
            refine ⟨4285401521309103601480153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5713868695078804801973537 4285401521309103601480153)
            ·
              refine ⟨3214051140981827701110115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4285401521309103601480153 3214051140981827701110115)
              ·
                refine ⟨4821076711472741551665173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3214051140981827701110115 4821076711472741551665173)
                ·
                  refine ⟨225987970850284760234305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4821076711472741551665173 225987970850284760234305)
                  ·
                    rfl

theorem cell23_3960990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_3960990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3960990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3960990 prefixEnd_3960990 := by exact prefixLift 3960990
  have htrace : WordTrace (prefixWord ++ tailWord_3960990) baseStart_3960990 baseEnd_3960990 := by
    simpa [prefixWord, tailWord_3960990, baseEnd_3960990] using wordTrace_append hprefix tailTrace_3960990
  have hstable : (prefixWord ++ tailWord_3960990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960990).length < 2 ^ (prefixWord ++ tailWord_3960990).sum := by decide
  have hdescent : baseEnd_3960990 < baseStart_3960990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961019 : List Nat := [1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 4]
def baseStart_3961019 : Nat := 118140960795 + 3961019 * 2 ^ 59
def prefixEnd_3961019 : Nat := 4983230072969 + 3 ^ 40 * 3961019 * 2
def baseEnd_3961019 : Nat := 2033906628591543228646111

theorem tailTrace_3961019 : CollatzResearch.WordTrace tailWord_3961019 prefixEnd_3961019 2033906628591543228646111 := by
  unfold tailWord_3961019
  simp only [CollatzResearch.WordTrace]
  refine ⟨144470231636912126032334111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96313487757941417354889407 144470231636912126032334111)
  ·
    refine ⟨216705347455368189048501167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144470231636912126032334111 216705347455368189048501167)
    ·
      refine ⟨325058021183052283572751751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216705347455368189048501167 325058021183052283572751751)
      ·
        refine ⟨487587031774578425359127627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325058021183052283572751751 487587031774578425359127627)
        ·
          refine ⟨731380547661867638038691441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487587031774578425359127627 731380547661867638038691441)
          ·
            refine ⟨548535410746400728529018581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 731380547661867638038691441 548535410746400728529018581)
            ·
              refine ⟨12856298689368767074898873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 548535410746400728529018581 12856298689368767074898873)
              ·
                refine ⟨9642224017026575306174155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12856298689368767074898873 9642224017026575306174155)
                ·
                  refine ⟨14463336025539862959261233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9642224017026575306174155 14463336025539862959261233)
                  ·
                    refine ⟨10847502019154897219445925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14463336025539862959261233 10847502019154897219445925)
                    ·
                      refine ⟨2033906628591543228646111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10847502019154897219445925 2033906628591543228646111)
                      ·
                        rfl

theorem cell23_3961019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 4].length) (baseStart_3961019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961019 prefixEnd_3961019 := by exact prefixLift 3961019
  have htrace : WordTrace (prefixWord ++ tailWord_3961019) baseStart_3961019 baseEnd_3961019 := by
    simpa [prefixWord, tailWord_3961019, baseEnd_3961019] using wordTrace_append hprefix tailTrace_3961019
  have hstable : (prefixWord ++ tailWord_3961019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961019).length < 2 ^ (prefixWord ++ tailWord_3961019).sum := by decide
  have hdescent : baseEnd_3961019 < baseStart_3961019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961039 : List Nat := [1, 1, 2, 1, 1, 3, 3, 2, 3, 3, 3]
def baseStart_3961039 : Nat := 118140960795 + 3961039 * 2 ^ 59
def prefixEnd_3961039 : Nat := 4983230072969 + 3 ^ 40 * 3961039 * 2
def baseEnd_3961039 : Nat := 2033916898204633150396019

theorem tailTrace_3961039 : CollatzResearch.WordTrace tailWord_3961039 prefixEnd_3961039 2033916898204633150396019 := by
  unfold tailWord_3961039
  simp only [CollatzResearch.WordTrace]
  refine ⟨144470961096839669448062171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96313974064559779632041447 144470961096839669448062171)
  ·
    refine ⟨216706441645259504172093257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144470961096839669448062171 216706441645259504172093257)
    ·
      refine ⟨162529831233944628129069943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216706441645259504172093257 162529831233944628129069943)
      ·
        refine ⟨243794746850916942193604915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162529831233944628129069943 243794746850916942193604915)
        ·
          refine ⟨365692120276375413290407373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243794746850916942193604915 365692120276375413290407373)
          ·
            refine ⟨137134545103640779983902765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 365692120276375413290407373 137134545103640779983902765)
            ·
              refine ⟨51425454413865292493963537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137134545103640779983902765 51425454413865292493963537)
              ·
                refine ⟨38569090810398969370472653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51425454413865292493963537 38569090810398969370472653)
                ·
                  refine ⟨14463409053899613513927245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38569090810398969370472653 14463409053899613513927245)
                  ·
                    refine ⟨5423778395212355067722717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14463409053899613513927245 5423778395212355067722717)
                    ·
                      refine ⟨2033916898204633150396019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5423778395212355067722717 2033916898204633150396019)
                      ·
                        rfl

theorem cell23_3961039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 3, 3].length) (baseStart_3961039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961039 prefixEnd_3961039 := by exact prefixLift 3961039
  have htrace : WordTrace (prefixWord ++ tailWord_3961039) baseStart_3961039 baseEnd_3961039 := by
    simpa [prefixWord, tailWord_3961039, baseEnd_3961039] using wordTrace_append hprefix tailTrace_3961039
  have hstable : (prefixWord ++ tailWord_3961039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961039).length < 2 ^ (prefixWord ++ tailWord_3961039).sum := by decide
  have hdescent : baseEnd_3961039 < baseStart_3961039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961053 : List Nat := [1, 4, 3, 2, 1, 2, 2, 1, 1, 2, 4]
def baseStart_3961053 : Nat := 118140960795 + 3961053 * 2 ^ 59
def prefixEnd_3961053 : Nat := 4983230072969 + 3 ^ 40 * 3961053 * 2
def baseEnd_3961053 : Nat := 2033924086933796095620955

theorem tailTrace_3961053 : CollatzResearch.WordTrace tailWord_3961053 prefixEnd_3961053 2033924086933796095620955 := by
  unfold tailWord_3961053
  simp only [CollatzResearch.WordTrace]
  refine ⟨144471471718788949839071813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96314314479192633226047875 144471471718788949839071813)
  ·
    refine ⟨27088400947272928094825965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144471471718788949839071813 27088400947272928094825965)
    ·
      refine ⟨10158150355227348035559737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27088400947272928094825965 10158150355227348035559737)
      ·
        refine ⟨7618612766420511026669803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10158150355227348035559737 7618612766420511026669803)
        ·
          refine ⟨11427919149630766540004705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7618612766420511026669803 11427919149630766540004705)
          ·
            refine ⟨8570939362223074905003529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11427919149630766540004705 8570939362223074905003529)
            ·
              refine ⟨6428204521667306178752647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8570939362223074905003529 6428204521667306178752647)
              ·
                refine ⟨9642306782500959268128971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6428204521667306178752647 9642306782500959268128971)
                ·
                  refine ⟨14463460173751438902193457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9642306782500959268128971 14463460173751438902193457)
                  ·
                    refine ⟨10847595130313579176645093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14463460173751438902193457 10847595130313579176645093)
                    ·
                      refine ⟨2033924086933796095620955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10847595130313579176645093 2033924086933796095620955)
                      ·
                        rfl

theorem cell23_3961053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_3961053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961053 prefixEnd_3961053 := by exact prefixLift 3961053
  have htrace : WordTrace (prefixWord ++ tailWord_3961053) baseStart_3961053 baseEnd_3961053 := by
    simpa [prefixWord, tailWord_3961053, baseEnd_3961053] using wordTrace_append hprefix tailTrace_3961053
  have hstable : (prefixWord ++ tailWord_3961053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961053).length < 2 ^ (prefixWord ++ tailWord_3961053).sum := by decide
  have hdescent : baseEnd_3961053 < baseStart_3961053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961056 : List Nat := [2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 3]
def baseStart_3961056 : Nat := 118140960795 + 3961056 * 2 ^ 59
def prefixEnd_3961056 : Nat := 4983230072969 + 3 ^ 40 * 3961056 * 2
def baseEnd_3961056 : Nat := 2033925627375759583883441

theorem tailTrace_3961056 : CollatzResearch.WordTrace tailWord_3961056 prefixEnd_3961056 2033925627375759583883441 := by
  unfold tailWord_3961056
  simp only [CollatzResearch.WordTrace]
  refine ⟨72235790568889040675715511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96314387425185387567620681 72235790568889040675715511)
  ·
    refine ⟨108353685853333561013573267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72235790568889040675715511 108353685853333561013573267)
    ·
      refine ⟨162530528780000341520359901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108353685853333561013573267 162530528780000341520359901)
      ·
        refine ⟨60948948292500128070134963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162530528780000341520359901 60948948292500128070134963)
        ·
          refine ⟨91423422438750192105202445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60948948292500128070134963 91423422438750192105202445)
          ·
            refine ⟨34283783414531322039450917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91423422438750192105202445 34283783414531322039450917)
            ·
              refine ⟨6428209390224622882397047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34283783414531322039450917 6428209390224622882397047)
              ·
                refine ⟨9642314085336934323595571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6428209390224622882397047 9642314085336934323595571)
                ·
                  refine ⟨14463471128005401485393357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9642314085336934323595571 14463471128005401485393357)
                  ·
                    refine ⟨5423801673002025557022509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14463471128005401485393357 5423801673002025557022509)
                    ·
                      refine ⟨2033925627375759583883441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5423801673002025557022509 2033925627375759583883441)
                      ·
                        rfl

theorem cell23_3961056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 3].length) (baseStart_3961056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961056 prefixEnd_3961056 := by exact prefixLift 3961056
  have htrace : WordTrace (prefixWord ++ tailWord_3961056) baseStart_3961056 baseEnd_3961056 := by
    simpa [prefixWord, tailWord_3961056, baseEnd_3961056] using wordTrace_append hprefix tailTrace_3961056
  have hstable : (prefixWord ++ tailWord_3961056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961056).length < 2 ^ (prefixWord ++ tailWord_3961056).sum := by decide
  have hdescent : baseEnd_3961056 < baseStart_3961056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961089 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 4, 6]
def baseStart_3961089 : Nat := 118140960795 + 3961089 * 2 ^ 59
def prefixEnd_3961089 : Nat := 4983230072969 + 3 ^ 40 * 3961089 * 2
def baseEnd_3961089 : Nat := 677980857412452651590263

theorem tailTrace_3961089 : CollatzResearch.WordTrace tailWord_3961089 prefixEnd_3961089 677980857412452651590263 := by
  unfold tailWord_3961089
  simp only [CollatzResearch.WordTrace]
  refine ⟨144472784746658527987382321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96315189831105685324921547 144472784746658527987382321)
  ·
    refine ⟨108354588559993895990536741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144472784746658527987382321 108354588559993895990536741)
    ·
      refine ⟨20316485354998855498225639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108354588559993895990536741 20316485354998855498225639)
      ·
        refine ⟨30474728032498283247338459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20316485354998855498225639 30474728032498283247338459)
        ·
          refine ⟨45712092048747424871007689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30474728032498283247338459 45712092048747424871007689)
          ·
            refine ⟨34284069036560568653255767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45712092048747424871007689 34284069036560568653255767)
            ·
              refine ⟨51426103554840852979883651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34284069036560568653255767 51426103554840852979883651)
              ·
                refine ⟨77139155332261279469825477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51426103554840852979883651 77139155332261279469825477)
                ·
                  refine ⟨14463591624798989900592277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77139155332261279469825477 14463591624798989900592277)
                  ·
                    refine ⟨677980857412452651590263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14463591624798989900592277 677980857412452651590263)
                    ·
                      rfl

theorem cell23_3961089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_3961089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961089 prefixEnd_3961089 := by exact prefixLift 3961089
  have htrace : WordTrace (prefixWord ++ tailWord_3961089) baseStart_3961089 baseEnd_3961089 := by
    simpa [prefixWord, tailWord_3961089, baseEnd_3961089] using wordTrace_append hprefix tailTrace_3961089
  have hstable : (prefixWord ++ tailWord_3961089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961089).length < 2 ^ (prefixWord ++ tailWord_3961089).sum := by decide
  have hdescent : baseEnd_3961089 < baseStart_3961089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961090 : List Nat := [3, 4, 1, 1, 2, 2, 1, 1, 4, 1, 3]
def baseStart_3961090 : Nat := 118140960795 + 3961090 * 2 ^ 59
def prefixEnd_3961090 : Nat := 4983230072969 + 3 ^ 40 * 3961090 * 2
def baseEnd_3961090 : Nat := 2033943085718012450858285

theorem tailTrace_3961090 : CollatzResearch.WordTrace tailWord_3961090 prefixEnd_3961090 2033943085718012450858285 := by
  unfold tailWord_3961090
  simp only [CollatzResearch.WordTrace]
  refine ⟨36118205304913726289542181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96315214146436603438779149 36118205304913726289542181)
  ·
    refine ⟨6772163494671323679289159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36118205304913726289542181 6772163494671323679289159)
    ·
      refine ⟨10158245242006985518933739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6772163494671323679289159 10158245242006985518933739)
      ·
        refine ⟨15237367863010478278400609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10158245242006985518933739 15237367863010478278400609)
        ·
          refine ⟨11428025897257858708800457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15237367863010478278400609 11428025897257858708800457)
          ·
            refine ⟨8571019422943394031600343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11428025897257858708800457 8571019422943394031600343)
            ·
              refine ⟨12856529134415091047400515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8571019422943394031600343 12856529134415091047400515)
              ·
                refine ⟨19284793701622636571100773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12856529134415091047400515 19284793701622636571100773)
                ·
                  refine ⟨3615898819054244357081395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19284793701622636571100773 3615898819054244357081395)
                  ·
                    refine ⟨5423848228581366535622093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3615898819054244357081395 5423848228581366535622093)
                    ·
                      refine ⟨2033943085718012450858285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5423848228581366535622093 2033943085718012450858285)
                      ·
                        rfl

theorem cell23_3961090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_3961090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961090 prefixEnd_3961090 := by exact prefixLift 3961090
  have htrace : WordTrace (prefixWord ++ tailWord_3961090) baseStart_3961090 baseEnd_3961090 := by
    simpa [prefixWord, tailWord_3961090, baseEnd_3961090] using wordTrace_append hprefix tailTrace_3961090
  have hstable : (prefixWord ++ tailWord_3961090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961090).length < 2 ^ (prefixWord ++ tailWord_3961090).sum := by decide
  have hdescent : baseEnd_3961090 < baseStart_3961090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961117 : List Nat := [1, 4, 2, 3, 2, 1, 2, 2, 1, 3, 2]
def baseStart_3961117 : Nat := 118140960795 + 3961117 * 2 ^ 59
def prefixEnd_3961117 : Nat := 4983230072969 + 3 ^ 40 * 3961117 * 2
def baseEnd_3961117 : Nat := 2033956949695683845220661

theorem tailTrace_3961117 : CollatzResearch.WordTrace tailWord_3961117 prefixEnd_3961117 2033956949695683845220661 := by
  unfold tailWord_3961117
  simp only [CollatzResearch.WordTrace]
  refine ⟨144473805990557088769401605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96315870660371392512934403 144473805990557088769401605)
  ·
    refine ⟨27088838623229454144262801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144473805990557088769401605 27088838623229454144262801)
    ·
      refine ⟨20316628967422090608197101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27088838623229454144262801 20316628967422090608197101)
      ·
        refine ⟨7618735862783283978073913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20316628967422090608197101 7618735862783283978073913)
        ·
          refine ⟨5714051897087462983555435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7618735862783283978073913 5714051897087462983555435)
          ·
            refine ⟨8571077845631194475333153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5714051897087462983555435 8571077845631194475333153)
            ·
              refine ⟨6428308384223395856499865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8571077845631194475333153 6428308384223395856499865)
              ·
                refine ⟨4821231288167546892374899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6428308384223395856499865 4821231288167546892374899)
                ·
                  refine ⟨7231846932251320338562349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4821231288167546892374899 7231846932251320338562349)
                  ·
                    refine ⟨2711942599594245126960881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7231846932251320338562349 2711942599594245126960881)
                    ·
                      refine ⟨2033956949695683845220661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2711942599594245126960881 2033956949695683845220661)
                      ·
                        rfl

theorem cell23_3961117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_3961117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961117 prefixEnd_3961117 := by exact prefixLift 3961117
  have htrace : WordTrace (prefixWord ++ tailWord_3961117) baseStart_3961117 baseEnd_3961117 := by
    simpa [prefixWord, tailWord_3961117, baseEnd_3961117] using wordTrace_append hprefix tailTrace_3961117
  have hstable : (prefixWord ++ tailWord_3961117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961117).length < 2 ^ (prefixWord ++ tailWord_3961117).sum := by decide
  have hdescent : baseEnd_3961117 < baseStart_3961117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961136 : List Nat := [2, 1, 1, 1, 2, 2, 2, 7, 5]
def baseStart_3961136 : Nat := 118140960795 + 3961136 * 2 ^ 59
def prefixEnd_3961136 : Nat := 4983230072969 + 3 ^ 40 * 3961136 * 2
def baseEnd_3961136 : Nat := 225996300647568807875897

theorem tailTrace_3961136 : CollatzResearch.WordTrace tailWord_3961136 prefixEnd_3961136 225996300647568807875897 := by
  unfold tailWord_3961136
  simp only [CollatzResearch.WordTrace]
  refine ⟨72237249488744127507171631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96316332651658836676228841 72237249488744127507171631)
  ·
    refine ⟨108355874233116191260757447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72237249488744127507171631 108355874233116191260757447)
    ·
      refine ⟨162533811349674286891136171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108355874233116191260757447 162533811349674286891136171)
      ·
        refine ⟨243800717024511430336704257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162533811349674286891136171 243800717024511430336704257)
        ·
          refine ⟨182850537768383572752528193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243800717024511430336704257 182850537768383572752528193)
          ·
            refine ⟨137137903326287679564396145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182850537768383572752528193 137137903326287679564396145)
            ·
              refine ⟨102853427494715759673297109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137137903326287679564396145 102853427494715759673297109)
              ·
                refine ⟨2410627206907400617342901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 102853427494715759673297109 2410627206907400617342901)
                ·
                  refine ⟨225996300647568807875897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2410627206907400617342901 225996300647568807875897)
                  ·
                    rfl

theorem cell23_3961136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 7, 5].length) (baseStart_3961136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961136 prefixEnd_3961136 := by exact prefixLift 3961136
  have htrace : WordTrace (prefixWord ++ tailWord_3961136) baseStart_3961136 baseEnd_3961136 := by
    simpa [prefixWord, tailWord_3961136, baseEnd_3961136] using wordTrace_append hprefix tailTrace_3961136
  have hstable : (prefixWord ++ tailWord_3961136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961136).length < 2 ^ (prefixWord ++ tailWord_3961136).sum := by decide
  have hdescent : baseEnd_3961136 < baseStart_3961136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961230 : List Nat := [4, 1, 1, 4, 1, 2, 1, 2, 3, 4]
def baseStart_3961230 : Nat := 118140960795 + 3961230 * 2 ^ 59
def prefixEnd_3961230 : Nat := 4983230072969 + 3 ^ 40 * 3961230 * 2
def baseEnd_3961230 : Nat := 678004991003213967702547

theorem tailTrace_3961230 : CollatzResearch.WordTrace tailWord_3961230 prefixEnd_3961230 678004991003213967702547 := by
  unfold tailWord_3961230
  simp only [CollatzResearch.WordTrace]
  refine ⟨18059740929893463633533143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96318618292765139378843429 18059740929893463633533143)
  ·
    refine ⟨27089611394840195450299715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18059740929893463633533143 27089611394840195450299715)
    ·
      refine ⟨40634417092260293175449573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27089611394840195450299715 40634417092260293175449573)
      ·
        refine ⟨7618953204798804970396795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40634417092260293175449573 7618953204798804970396795)
        ·
          refine ⟨11428429807198207455595193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7618953204798804970396795 11428429807198207455595193)
          ·
            refine ⟨8571322355398655591696395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11428429807198207455595193 8571322355398655591696395)
            ·
              refine ⟨12856983533097983387544593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8571322355398655591696395 12856983533097983387544593)
              ·
                refine ⟨9642737649823487540658445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12856983533097983387544593 9642737649823487540658445)
                ·
                  refine ⟨3616026618683807827746917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9642737649823487540658445 3616026618683807827746917)
                  ·
                    refine ⟨678004991003213967702547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3616026618683807827746917 678004991003213967702547)
                    ·
                      rfl

theorem cell23_3961230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 3, 4].length) (baseStart_3961230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961230 prefixEnd_3961230 := by exact prefixLift 3961230
  have htrace : WordTrace (prefixWord ++ tailWord_3961230) baseStart_3961230 baseEnd_3961230 := by
    simpa [prefixWord, tailWord_3961230, baseEnd_3961230] using wordTrace_append hprefix tailTrace_3961230
  have hstable : (prefixWord ++ tailWord_3961230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961230).length < 2 ^ (prefixWord ++ tailWord_3961230).sum := by decide
  have hdescent : baseEnd_3961230 < baseStart_3961230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961240 : List Nat := [2, 1, 2, 5, 1, 1, 3, 1, 2, 2, 3]
def baseStart_3961240 : Nat := 118140960795 + 3961240 * 2 ^ 59
def prefixEnd_3961240 : Nat := 4983230072969 + 3 ^ 40 * 3961240 * 2
def baseEnd_3961240 : Nat := 2034020107816186863982595

theorem tailTrace_3961240 : CollatzResearch.WordTrace tailWord_3961240 prefixEnd_3961240 2034020107816186863982595 := by
  unfold tailWord_3961240
  simp only [CollatzResearch.WordTrace]
  refine ⟨72239146084555740388064587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96318861446074320517419449 72239146084555740388064587)
  ·
    refine ⟨108358719126833610582096881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72239146084555740388064587 108358719126833610582096881)
    ·
      refine ⟨81269039345125207936572661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108358719126833610582096881 81269039345125207936572661)
      ·
        refine ⟨7618972438605488244053687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81269039345125207936572661 7618972438605488244053687)
        ·
          refine ⟨11428458657908232366080531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7618972438605488244053687 11428458657908232366080531)
          ·
            refine ⟨17142687986862348549120797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11428458657908232366080531 17142687986862348549120797)
            ·
              refine ⟨6428507995073380705920299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17142687986862348549120797 6428507995073380705920299)
              ·
                refine ⟨9642761992610071058880449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6428507995073380705920299 9642761992610071058880449)
                ·
                  refine ⟨7232071494457553294160337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9642761992610071058880449 7232071494457553294160337)
                  ·
                    refine ⟨5424053620843164970620253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7232071494457553294160337 5424053620843164970620253)
                    ·
                      refine ⟨2034020107816186863982595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5424053620843164970620253 2034020107816186863982595)
                      ·
                        rfl

theorem cell23_3961240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_3961240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961240 prefixEnd_3961240 := by exact prefixLift 3961240
  have htrace : WordTrace (prefixWord ++ tailWord_3961240) baseStart_3961240 baseEnd_3961240 := by
    simpa [prefixWord, tailWord_3961240, baseEnd_3961240] using wordTrace_append hprefix tailTrace_3961240
  have hstable : (prefixWord ++ tailWord_3961240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961240).length < 2 ^ (prefixWord ++ tailWord_3961240).sum := by decide
  have hdescent : baseEnd_3961240 < baseStart_3961240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961253 : List Nat := [1, 3, 1, 2, 1, 1, 3, 2, 5, 1, 3]
def baseStart_3961253 : Nat := 118140960795 + 3961253 * 2 ^ 59
def prefixEnd_3961253 : Nat := 4983230072969 + 3 ^ 40 * 3961253 * 2
def baseEnd_3961253 : Nat := 2034026783064695313120035

theorem tailTrace_3961253 : CollatzResearch.WordTrace tailWord_3961253 prefixEnd_3961253 2034026783064695313120035 := by
  unfold tailWord_3961253
  simp only [CollatzResearch.WordTrace]
  refine ⟨144478766318064383996352413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96319177545376255997568275 144478766318064383996352413)
  ·
    refine ⟨54179537369274143998632155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144478766318064383996352413 54179537369274143998632155)
    ·
      refine ⟨81269306053911215997948233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54179537369274143998632155 81269306053911215997948233)
      ·
        refine ⟨60951979540433411998461175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81269306053911215997948233 60951979540433411998461175)
        ·
          refine ⟨91427969310650117997691763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60951979540433411998461175 91427969310650117997691763)
          ·
            refine ⟨137141953965975176996537645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91427969310650117997691763 137141953965975176996537645)
            ·
              refine ⟨51428232737240691373701617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137141953965975176996537645 51428232737240691373701617)
              ·
                refine ⟨38571174552930518530276213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51428232737240691373701617 38571174552930518530276213)
                ·
                  refine ⟨3616047614337236112213395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38571174552930518530276213 3616047614337236112213395)
                  ·
                    refine ⟨5424071421505854168320093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3616047614337236112213395 5424071421505854168320093)
                    ·
                      refine ⟨2034026783064695313120035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5424071421505854168320093 2034026783064695313120035)
                      ·
                        rfl

theorem cell23_3961253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 5, 1, 3].length) (baseStart_3961253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961253 prefixEnd_3961253 := by exact prefixLift 3961253
  have htrace : WordTrace (prefixWord ++ tailWord_3961253) baseStart_3961253 baseEnd_3961253 := by
    simpa [prefixWord, tailWord_3961253, baseEnd_3961253] using wordTrace_append hprefix tailTrace_3961253
  have hstable : (prefixWord ++ tailWord_3961253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961253).length < 2 ^ (prefixWord ++ tailWord_3961253).sum := by decide
  have hdescent : baseEnd_3961253 < baseStart_3961253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961313 : List Nat := [1, 2, 3, 1, 2, 2, 4, 1, 1, 1, 5]
def baseStart_3961313 : Nat := 118140960795 + 3961313 * 2 ^ 59
def prefixEnd_3961313 : Nat := 4983230072969 + 3 ^ 40 * 3961313 * 2
def baseEnd_3961313 : Nat := 2034057591903965078369759

theorem tailTrace_3961313 : CollatzResearch.WordTrace tailWord_3961313 prefixEnd_3961313 2034057591903965078369759 := by
  unfold tailWord_3961313
  simp only [CollatzResearch.WordTrace]
  refine ⟨144480954697847014243536593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96320636465231342829024395 144480954697847014243536593)
  ·
    refine ⟨108360716023385260682652445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144480954697847014243536593 108360716023385260682652445)
    ·
      refine ⟨40635268508769472755994667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108360716023385260682652445 40635268508769472755994667)
      ·
        refine ⟨60952902763154209133992001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40635268508769472755994667 60952902763154209133992001)
        ·
          refine ⟨45714677072365656850494001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60952902763154209133992001 45714677072365656850494001)
          ·
            refine ⟨34286007804274242637870501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45714677072365656850494001 34286007804274242637870501)
            ·
              refine ⟨6428626463301420494600719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34286007804274242637870501 6428626463301420494600719)
              ·
                refine ⟨9642939694952130741901079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6428626463301420494600719 9642939694952130741901079)
                ·
                  refine ⟨14464409542428196112851619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9642939694952130741901079 14464409542428196112851619)
                  ·
                    refine ⟨21696614313642294169277429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14464409542428196112851619 21696614313642294169277429)
                    ·
                      refine ⟨2034057591903965078369759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21696614313642294169277429 2034057591903965078369759)
                      ·
                        rfl

theorem cell23_3961313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 1, 5].length) (baseStart_3961313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961313 prefixEnd_3961313 := by exact prefixLift 3961313
  have htrace : WordTrace (prefixWord ++ tailWord_3961313) baseStart_3961313 baseEnd_3961313 := by
    simpa [prefixWord, tailWord_3961313, baseEnd_3961313] using wordTrace_append hprefix tailTrace_3961313
  have hstable : (prefixWord ++ tailWord_3961313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961313).length < 2 ^ (prefixWord ++ tailWord_3961313).sum := by decide
  have hdescent : baseEnd_3961313 < baseStart_3961313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961336 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 2, 2, 6]
def baseStart_3961336 : Nat := 118140960795 + 3961336 * 2 ^ 59
def prefixEnd_3961336 : Nat := 4983230072969 + 3 ^ 40 * 3961336 * 2
def baseEnd_3961336 : Nat := 2034069401959018488382153

theorem tailTrace_3961336 : CollatzResearch.WordTrace tailWord_3961336 prefixEnd_3961336 2034069401959018488382153 := by
  unfold tailWord_3961336
  simp only [CollatzResearch.WordTrace]
  refine ⟨72240896788381844585811931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96321195717842459447749241 72240896788381844585811931)
  ·
    refine ⟨108361345182572766878717897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72240896788381844585811931 108361345182572766878717897)
    ·
      refine ⟨81271008886929575159038423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108361345182572766878717897 81271008886929575159038423)
      ·
        refine ⟨121906513330394362738557635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81271008886929575159038423 121906513330394362738557635)
        ·
          refine ⟨182859769995591544107836453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121906513330394362738557635 182859769995591544107836453)
          ·
            refine ⟨34286206874173414520219335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182859769995591544107836453 34286206874173414520219335)
            ·
              refine ⟨51429310311260121780329003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34286206874173414520219335 51429310311260121780329003)
              ·
                refine ⟨77143965466890182670493505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51429310311260121780329003 77143965466890182670493505)
                ·
                  refine ⟨57857974100167637002870129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77143965466890182670493505 57857974100167637002870129)
                  ·
                    refine ⟨43393480575125727752152597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57857974100167637002870129 43393480575125727752152597)
                    ·
                      refine ⟨2034069401959018488382153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43393480575125727752152597 2034069401959018488382153)
                      ·
                        rfl

theorem cell23_3961336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_3961336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961336 prefixEnd_3961336 := by exact prefixLift 3961336
  have htrace : WordTrace (prefixWord ++ tailWord_3961336) baseStart_3961336 baseEnd_3961336 := by
    simpa [prefixWord, tailWord_3961336, baseEnd_3961336] using wordTrace_append hprefix tailTrace_3961336
  have hstable : (prefixWord ++ tailWord_3961336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961336).length < 2 ^ (prefixWord ++ tailWord_3961336).sum := by decide
  have hdescent : baseEnd_3961336 < baseStart_3961336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961343 : List Nat := [1, 1, 2, 2, 1, 2, 4, 3, 1, 3, 3]
def baseStart_3961343 : Nat := 118140960795 + 3961343 * 2 ^ 59
def prefixEnd_3961343 : Nat := 4983230072969 + 3 ^ 40 * 3961343 * 2
def baseEnd_3961343 : Nat := 2034072996323599960994621

theorem tailTrace_3961343 : CollatzResearch.WordTrace tailWord_3961343 prefixEnd_3961343 2034072996323599960994621 := by
  unfold tailWord_3961343
  simp only [CollatzResearch.WordTrace]
  refine ⟨144482048887738329367128683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96321365925158886244752455 144482048887738329367128683)
  ·
    refine ⟨216723073331607494050693025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144482048887738329367128683 216723073331607494050693025)
    ·
      refine ⟨162542304998705620538019769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216723073331607494050693025 162542304998705620538019769)
      ·
        refine ⟨121906728749029215403514827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162542304998705620538019769 121906728749029215403514827)
        ·
          refine ⟨182860093123543823105272241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121906728749029215403514827 182860093123543823105272241)
          ·
            refine ⟨137145069842657867328954181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182860093123543823105272241 137145069842657867328954181)
            ·
              refine ⟨25714700595498350124178909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137145069842657867328954181 25714700595498350124178909)
              ·
                refine ⟨9643012723311881296567091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25714700595498350124178909 9643012723311881296567091)
                ·
                  refine ⟨14464519084967821944850637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9643012723311881296567091 14464519084967821944850637)
                  ·
                    refine ⟨5424194656862933229318989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14464519084967821944850637 5424194656862933229318989)
                    ·
                      refine ⟨2034072996323599960994621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5424194656862933229318989 2034072996323599960994621)
                      ·
                        rfl

theorem cell23_3961343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 3, 3].length) (baseStart_3961343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961343 prefixEnd_3961343 := by exact prefixLift 3961343
  have htrace : WordTrace (prefixWord ++ tailWord_3961343) baseStart_3961343 baseEnd_3961343 := by
    simpa [prefixWord, tailWord_3961343, baseEnd_3961343] using wordTrace_append hprefix tailTrace_3961343
  have hstable : (prefixWord ++ tailWord_3961343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961343).length < 2 ^ (prefixWord ++ tailWord_3961343).sum := by decide
  have hdescent : baseEnd_3961343 < baseStart_3961343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961357 : List Nat := [1, 7, 1, 1, 1, 1, 1, 1, 3, 2, 4]
def baseStart_3961357 : Nat := 118140960795 + 3961357 * 2 ^ 59
def prefixEnd_3961357 : Nat := 4983230072969 + 3 ^ 40 * 3961357 * 2
def baseEnd_3961357 : Nat := 2034080185052762906219557

theorem tailTrace_3961357 : CollatzResearch.WordTrace tailWord_3961357 prefixEnd_3961357 2034080185052762906219557 := by
  unfold tailWord_3961357
  simp only [CollatzResearch.WordTrace]
  refine ⟨144482559509687609758138325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96321706339791739838758883 144482559509687609758138325)
  ·
    refine ⟨3386309988508303353706367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 144482559509687609758138325 3386309988508303353706367)
    ·
      refine ⟨5079464982762455030559551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3386309988508303353706367 5079464982762455030559551)
      ·
        refine ⟨7619197474143682545839327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5079464982762455030559551 7619197474143682545839327)
        ·
          refine ⟨11428796211215523818758991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7619197474143682545839327 11428796211215523818758991)
          ·
            refine ⟨17143194316823285728138487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11428796211215523818758991 17143194316823285728138487)
            ·
              refine ⟨25714791475234928592207731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17143194316823285728138487 25714791475234928592207731)
              ·
                refine ⟨38572187212852392888311597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25714791475234928592207731 38572187212852392888311597)
                ·
                  refine ⟨14464570204819647333116849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38572187212852392888311597 14464570204819647333116849)
                  ·
                    refine ⟨10848427653614735499837637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14464570204819647333116849 10848427653614735499837637)
                    ·
                      refine ⟨2034080185052762906219557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10848427653614735499837637 2034080185052762906219557)
                      ·
                        rfl

theorem cell23_3961357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_3961357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961357 prefixEnd_3961357 := by exact prefixLift 3961357
  have htrace : WordTrace (prefixWord ++ tailWord_3961357) baseStart_3961357 baseEnd_3961357 := by
    simpa [prefixWord, tailWord_3961357, baseEnd_3961357] using wordTrace_append hprefix tailTrace_3961357
  have hstable : (prefixWord ++ tailWord_3961357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961357).length < 2 ^ (prefixWord ++ tailWord_3961357).sum := by decide
  have hdescent : baseEnd_3961357 < baseStart_3961357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961377 : List Nat := [1, 2, 3, 2, 2, 1, 4, 2, 2, 1, 3]
def baseStart_3961377 : Nat := 118140960795 + 3961377 * 2 ^ 59
def prefixEnd_3961377 : Nat := 4983230072969 + 3 ^ 40 * 3961377 * 2
def baseEnd_3961377 : Nat := 2034090454665852827969465

theorem tailTrace_3961377 : CollatzResearch.WordTrace tailWord_3961377 prefixEnd_3961377 2034090454665852827969465 := by
  unfold tailWord_3961377
  simp only [CollatzResearch.WordTrace]
  refine ⟨144483288969615153173866385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96322192646410102115910923 144483288969615153173866385)
  ·
    refine ⟨108362466727211364880399789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144483288969615153173866385 108362466727211364880399789)
    ·
      refine ⟨40635925022704261830149921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108362466727211364880399789 40635925022704261830149921)
      ·
        refine ⟨30476943767028196372612441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40635925022704261830149921 30476943767028196372612441)
        ·
          refine ⟨22857707825271147279459331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30476943767028196372612441 22857707825271147279459331)
          ·
            refine ⟨34286561737906720919188997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22857707825271147279459331 34286561737906720919188997)
            ·
              refine ⟨6428730325857510172347937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34286561737906720919188997 6428730325857510172347937)
              ·
                refine ⟨4821547744393132629260953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6428730325857510172347937 4821547744393132629260953)
                ·
                  refine ⟨3616160808294849471945715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4821547744393132629260953 3616160808294849471945715)
                  ·
                    refine ⟨5424241212442274207918573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3616160808294849471945715 5424241212442274207918573)
                    ·
                      refine ⟨2034090454665852827969465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5424241212442274207918573 2034090454665852827969465)
                      ·
                        rfl

theorem cell23_3961377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_3961377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961377 prefixEnd_3961377 := by exact prefixLift 3961377
  have htrace : WordTrace (prefixWord ++ tailWord_3961377) baseStart_3961377 baseEnd_3961377 := by
    simpa [prefixWord, tailWord_3961377, baseEnd_3961377] using wordTrace_append hprefix tailTrace_3961377
  have hstable : (prefixWord ++ tailWord_3961377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961377).length < 2 ^ (prefixWord ++ tailWord_3961377).sum := by decide
  have hdescent : baseEnd_3961377 < baseStart_3961377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961421 : List Nat := [1, 6, 1, 1, 2, 1, 4, 1, 1, 3, 2]
def baseStart_3961421 : Nat := 118140960795 + 3961421 * 2 ^ 59
def prefixEnd_3961421 : Nat := 4983230072969 + 3 ^ 40 * 3961421 * 2
def baseEnd_3961421 : Nat := 2034113047814650655819263

theorem tailTrace_3961421 : CollatzResearch.WordTrace tailWord_3961421 prefixEnd_3961421 2034113047814650655819263 := by
  unfold tailWord_3961421
  simp only [CollatzResearch.WordTrace]
  refine ⟨144484893781455748688468117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96323262520970499125645411 144484893781455748688468117)
  ·
    refine ⟨6772729396005738219771943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 144484893781455748688468117 6772729396005738219771943)
    ·
      refine ⟨10159094094008607329657915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6772729396005738219771943 10159094094008607329657915)
      ·
        refine ⟨15238641141012910994486873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10159094094008607329657915 15238641141012910994486873)
        ·
          refine ⟨11428980855759683245865155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15238641141012910994486873 11428980855759683245865155)
          ·
            refine ⟨17143471283639524868797733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11428980855759683245865155 17143471283639524868797733)
            ·
              refine ⟨3214400865682410912899575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17143471283639524868797733 3214400865682410912899575)
              ·
                refine ⟨4821601298523616369349363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3214400865682410912899575 4821601298523616369349363)
                ·
                  refine ⟨7232401947785424554024045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4821601298523616369349363 7232401947785424554024045)
                  ·
                    refine ⟨2712150730419534207759017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7232401947785424554024045 2712150730419534207759017)
                    ·
                      refine ⟨2034113047814650655819263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2712150730419534207759017 2034113047814650655819263)
                      ·
                        rfl

theorem cell23_3961421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_3961421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961421 prefixEnd_3961421 := by exact prefixLift 3961421
  have htrace : WordTrace (prefixWord ++ tailWord_3961421) baseStart_3961421 baseEnd_3961421 := by
    simpa [prefixWord, tailWord_3961421, baseEnd_3961421] using wordTrace_append hprefix tailTrace_3961421
  have hstable : (prefixWord ++ tailWord_3961421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961421).length < 2 ^ (prefixWord ++ tailWord_3961421).sum := by decide
  have hdescent : baseEnd_3961421 < baseStart_3961421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961440 : List Nat := [2, 1, 1, 3, 2, 1, 4, 4, 5]
def baseStart_3961440 : Nat := 118140960795 + 3961440 * 2 ^ 59
def prefixEnd_3961440 : Nat := 4983230072969 + 3 ^ 40 * 3961440 * 2
def baseEnd_3961440 : Nat := 226013644883009564609075

theorem tailTrace_3961440 : CollatzResearch.WordTrace tailWord_3961440 prefixEnd_3961440 226013644883009564609075 := by
  unfold tailWord_3961440
  simp only [CollatzResearch.WordTrace]
  refine ⟨72242793384193457466704887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96323724512257943288939849 72242793384193457466704887)
  ·
    refine ⟨108364190076290186200057331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72242793384193457466704887 108364190076290186200057331)
    ·
      refine ⟨162546285114435279300085997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108364190076290186200057331 162546285114435279300085997)
      ·
        refine ⟨60954856917913229737532249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162546285114435279300085997 60954856917913229737532249)
        ·
          refine ⟨45716142688434922303149187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60954856917913229737532249 45716142688434922303149187)
          ·
            refine ⟨68574214032652383454723781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45716142688434922303149187 68574214032652383454723781)
            ·
              refine ⟨12857665131122321897760709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68574214032652383454723781 12857665131122321897760709)
              ·
                refine ⟨2410812212085435355830133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12857665131122321897760709 2410812212085435355830133)
                ·
                  refine ⟨226013644883009564609075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2410812212085435355830133 226013644883009564609075)
                  ·
                    rfl

theorem cell23_3961440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 4, 5].length) (baseStart_3961440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961440 prefixEnd_3961440 := by exact prefixLift 3961440
  have htrace : WordTrace (prefixWord ++ tailWord_3961440) baseStart_3961440 baseEnd_3961440 := by
    simpa [prefixWord, tailWord_3961440, baseEnd_3961440] using wordTrace_append hprefix tailTrace_3961440
  have hstable : (prefixWord ++ tailWord_3961440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961440).length < 2 ^ (prefixWord ++ tailWord_3961440).sum := by decide
  have hdescent : baseEnd_3961440 < baseStart_3961440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961450 : List Nat := [3, 1, 3, 2, 1, 1, 1, 3, 2, 3, 3]
def baseStart_3961450 : Nat := 118140960795 + 3961450 * 2 ^ 59
def prefixEnd_3961450 : Nat := 4983230072969 + 3 ^ 40 * 3961450 * 2
def baseEnd_3961450 : Nat := 2034127938753631042356629

theorem tailTrace_3961450 : CollatzResearch.WordTrace tailWord_3961450 prefixEnd_3961450 2034127938753631042356629 := by
  unfold tailWord_3961450
  simp only [CollatzResearch.WordTrace]
  refine ⟨36121487874587671660318451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96323967665567124427515869 36121487874587671660318451)
  ·
    refine ⟨54182231811881507490477677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36121487874587671660318451 54182231811881507490477677)
    ·
      refine ⟨20318336929455565308929129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54182231811881507490477677 20318336929455565308929129)
      ·
        refine ⟨15238752697091673981696847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20318336929455565308929129 15238752697091673981696847)
        ·
          refine ⟨22858129045637510972545271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15238752697091673981696847 22858129045637510972545271)
          ·
            refine ⟨34287193568456266458817907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22858129045637510972545271 34287193568456266458817907)
            ·
              refine ⟨51430790352684399688226861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34287193568456266458817907 51430790352684399688226861)
              ·
                refine ⟨19286546382256649883085073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51430790352684399688226861 19286546382256649883085073)
                ·
                  refine ⟨14464909786692487412313805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19286546382256649883085073 14464909786692487412313805)
                  ·
                    refine ⟨5424341170009682779617677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14464909786692487412313805 5424341170009682779617677)
                    ·
                      refine ⟨2034127938753631042356629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5424341170009682779617677 2034127938753631042356629)
                      ·
                        rfl

theorem cell23_3961450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_3961450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961450 prefixEnd_3961450 := by exact prefixLift 3961450
  have htrace : WordTrace (prefixWord ++ tailWord_3961450) baseStart_3961450 baseEnd_3961450 := by
    simpa [prefixWord, tailWord_3961450, baseEnd_3961450] using wordTrace_append hprefix tailTrace_3961450
  have hstable : (prefixWord ++ tailWord_3961450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961450).length < 2 ^ (prefixWord ++ tailWord_3961450).sum := by decide
  have hdescent : baseEnd_3961450 < baseStart_3961450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961534 : List Nat := [4, 2, 1, 1, 2, 1, 2, 5, 1, 4]
def baseStart_3961534 : Nat := 118140960795 + 3961534 * 2 ^ 59
def prefixEnd_3961534 : Nat := 4983230072969 + 3 ^ 40 * 3961534 * 2
def baseEnd_3961534 : Nat := 678057023709536237902081

theorem tailTrace_3961534 : CollatzResearch.WordTrace tailWord_3961534 prefixEnd_3961534 678057023709536237902081 := by
  unfold tailWord_3961534
  simp only [CollatzResearch.WordTrace]
  refine ⟨18061126903755796123416457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96326010153364245991554437 18061126903755796123416457)
  ·
    refine ⟨13545845177816847092562343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18061126903755796123416457 13545845177816847092562343)
    ·
      refine ⟨20318767766725270638843515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13545845177816847092562343 20318767766725270638843515)
      ·
        refine ⟨30478151650087905958265273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20318767766725270638843515 30478151650087905958265273)
        ·
          refine ⟨22858613737565929468698955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30478151650087905958265273 22858613737565929468698955)
          ·
            refine ⟨34287920606348894203048433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22858613737565929468698955 34287920606348894203048433)
            ·
              refine ⟨25715940454761670652286325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34287920606348894203048433 25715940454761670652286325)
              ·
                refine ⟨2410869417633906623651843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25715940454761670652286325 2410869417633906623651843)
                ·
                  refine ⟨3616304126450859935477765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2410869417633906623651843 3616304126450859935477765)
                  ·
                    refine ⟨678057023709536237902081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3616304126450859935477765 678057023709536237902081)
                    ·
                      rfl

theorem cell23_3961534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_3961534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961534 prefixEnd_3961534 := by exact prefixLift 3961534
  have htrace : WordTrace (prefixWord ++ tailWord_3961534) baseStart_3961534 baseEnd_3961534 := by
    simpa [prefixWord, tailWord_3961534, baseEnd_3961534] using wordTrace_append hprefix tailTrace_3961534
  have hstable : (prefixWord ++ tailWord_3961534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961534).length < 2 ^ (prefixWord ++ tailWord_3961534).sum := by decide
  have hdescent : baseEnd_3961534 < baseStart_3961534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961560 : List Nat := [2, 1, 2, 2, 3, 2, 1, 2, 3, 5]
def baseStart_3961560 : Nat := 118140960795 + 3961560 * 2 ^ 59
def prefixEnd_3961560 : Nat := 4983230072969 + 3 ^ 40 * 3961560 * 2
def baseEnd_3961560 : Nat := 678061473875208537327041

theorem tailTrace_3961560 : CollatzResearch.WordTrace tailWord_3961560 prefixEnd_3961560 678061473875208537327041 := by
  unfold tailWord_3961560
  simp only [CollatzResearch.WordTrace]
  refine ⟨72244981763976087713889067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96326642351968116951852089 72244981763976087713889067)
  ·
    refine ⟨108367472645964131570833601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72244981763976087713889067 108367472645964131570833601)
    ·
      refine ⟨81275604484473098678125201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108367472645964131570833601 81275604484473098678125201)
      ·
        refine ⟨60956703363354824008593901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81275604484473098678125201 60956703363354824008593901)
        ·
          refine ⟨22858763761258059003222713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60956703363354824008593901 22858763761258059003222713)
          ·
            refine ⟨17144072820943544252417035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22858763761258059003222713 17144072820943544252417035)
            ·
              refine ⟨25716109231415316378625553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17144072820943544252417035 25716109231415316378625553)
              ·
                refine ⟨19287081923561487283969165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25716109231415316378625553 19287081923561487283969165)
                ·
                  refine ⟨7232655721335557731488437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19287081923561487283969165 7232655721335557731488437)
                  ·
                    refine ⟨678061473875208537327041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7232655721335557731488437 678061473875208537327041)
                    ·
                      rfl

theorem cell23_3961560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 3, 5].length) (baseStart_3961560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961560 prefixEnd_3961560 := by exact prefixLift 3961560
  have htrace : WordTrace (prefixWord ++ tailWord_3961560) baseStart_3961560 baseEnd_3961560 := by
    simpa [prefixWord, tailWord_3961560, baseEnd_3961560] using wordTrace_append hprefix tailTrace_3961560
  have hstable : (prefixWord ++ tailWord_3961560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961560).length < 2 ^ (prefixWord ++ tailWord_3961560).sum := by decide
  have hdescent : baseEnd_3961560 < baseStart_3961560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961597 : List Nat := [1, 4, 1, 1, 1, 1, 5, 3, 1, 1, 4]
def baseStart_3961597 : Nat := 118140960795 + 3961597 * 2 ^ 59
def prefixEnd_3961597 : Nat := 4983230072969 + 3 ^ 40 * 3961597 * 2
def baseEnd_3961597 : Nat := 2034203420409841967218453

theorem tailTrace_3961597 : CollatzResearch.WordTrace tailWord_3961597 prefixEnd_3961597 2034203420409841967218453 := by
  unfold tailWord_3961597
  simp only [CollatzResearch.WordTrace]
  refine ⟨144491313028818130746875045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96327542019212087164583363 144491313028818130746875045)
  ·
    refine ⟨27092121192903399515039071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144491313028818130746875045 27092121192903399515039071)
    ·
      refine ⟨40638181789355099272558607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27092121192903399515039071 40638181789355099272558607)
      ·
        refine ⟨60957272684032648908837911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40638181789355099272558607 60957272684032648908837911)
        ·
          refine ⟨91435909026048973363256867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60957272684032648908837911 91435909026048973363256867)
          ·
            refine ⟨137153863539073460044885301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91435909026048973363256867 137153863539073460044885301)
            ·
              refine ⟨12858174706788136879207997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137153863539073460044885301 12858174706788136879207997)
              ·
                refine ⟨4821815515045551329702999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12858174706788136879207997 4821815515045551329702999)
                ·
                  refine ⟨7232723272568326994554499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4821815515045551329702999 7232723272568326994554499)
                  ·
                    refine ⟨10849084908852490491831749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7232723272568326994554499 10849084908852490491831749)
                    ·
                      refine ⟨2034203420409841967218453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10849084908852490491831749 2034203420409841967218453)
                      ·
                        rfl

theorem cell23_3961597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 1, 4].length) (baseStart_3961597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961597 prefixEnd_3961597 := by exact prefixLift 3961597
  have htrace : WordTrace (prefixWord ++ tailWord_3961597) baseStart_3961597 baseEnd_3961597 := by
    simpa [prefixWord, tailWord_3961597, baseEnd_3961597] using wordTrace_append hprefix tailTrace_3961597
  have hstable : (prefixWord ++ tailWord_3961597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961597).length < 2 ^ (prefixWord ++ tailWord_3961597).sum := by decide
  have hdescent : baseEnd_3961597 < baseStart_3961597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961610 : List Nat := [3, 1, 2, 2, 1, 2, 2, 2, 1, 1, 6]
def baseStart_3961610 : Nat := 118140960795 + 3961610 * 2 ^ 59
def prefixEnd_3961610 : Nat := 4983230072969 + 3 ^ 40 * 3961610 * 2
def baseEnd_3961610 : Nat := 2034210095658350416355893

theorem tailTrace_3961610 : CollatzResearch.WordTrace tailWord_3961610 prefixEnd_3961610 2034210095658350416355893 := by
  unfold tailWord_3961610
  simp only [CollatzResearch.WordTrace]
  refine ⟨36122946794442758491774571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96327858118514022644732189 36122946794442758491774571)
  ·
    refine ⟨54184420191664137737661857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36122946794442758491774571 54184420191664137737661857)
    ·
      refine ⟨40638315143748103303246393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54184420191664137737661857 40638315143748103303246393)
      ·
        refine ⟨30478736357811077477434795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40638315143748103303246393 30478736357811077477434795)
        ·
          refine ⟨45718104536716616216152193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30478736357811077477434795 45718104536716616216152193)
          ·
            refine ⟨34288578402537462162114145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45718104536716616216152193 34288578402537462162114145)
            ·
              refine ⟨25716433801903096621585609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34288578402537462162114145 25716433801903096621585609)
              ·
                refine ⟨19287325351427322466189207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25716433801903096621585609 19287325351427322466189207)
                ·
                  refine ⟨28930988027140983699283811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19287325351427322466189207 28930988027140983699283811)
                  ·
                    refine ⟨43396482040711475548925717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28930988027140983699283811 43396482040711475548925717)
                    ·
                      refine ⟨2034210095658350416355893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43396482040711475548925717 2034210095658350416355893)
                      ·
                        rfl

theorem cell23_3961610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_3961610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961610 prefixEnd_3961610 := by exact prefixLift 3961610
  have htrace : WordTrace (prefixWord ++ tailWord_3961610) baseStart_3961610 baseEnd_3961610 := by
    simpa [prefixWord, tailWord_3961610, baseEnd_3961610] using wordTrace_append hprefix tailTrace_3961610
  have hstable : (prefixWord ++ tailWord_3961610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961610).length < 2 ^ (prefixWord ++ tailWord_3961610).sum := by decide
  have hdescent : baseEnd_3961610 < baseStart_3961610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
