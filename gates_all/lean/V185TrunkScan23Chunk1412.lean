import V185TrunkScan23Chunk1411

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8365107 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 1, 8, 2]
def baseStart_8365107 : Nat := 118140960795 + 8365107 * 2 ^ 59
def prefixEnd_8365107 : Nat := 4983230072969 + 3 ^ 40 * 8365107 * 2
def baseEnd_8365107 : Nat := 4295320617289908214092079

theorem tailTrace_8365107 : CollatzResearch.WordTrace tailWord_8365107 prefixEnd_8365107 4295320617289908214092079 := by
  unfold tailWord_8365107
  simp only [CollatzResearch.WordTrace]
  refine ⟨305100517305653460380349575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203400344870435640253566383 305100517305653460380349575)
  ·
    refine ⟨457650775958480190570524363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305100517305653460380349575 457650775958480190570524363)
    ·
      refine ⟨686476163937720285855786545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457650775958480190570524363 686476163937720285855786545)
      ·
        refine ⟨514857122953290214391839909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 686476163937720285855786545 514857122953290214391839909)
        ·
          refine ⟨96535710553741915198469983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 514857122953290214391839909 96535710553741915198469983)
          ·
            refine ⟨144803565830612872797704975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96535710553741915198469983 144803565830612872797704975)
            ·
              refine ⟨217205348745919309196557463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144803565830612872797704975 217205348745919309196557463)
              ·
                refine ⟨325808023118878963794836195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217205348745919309196557463 325808023118878963794836195)
                ·
                  refine ⟨488712034678318445692254293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 325808023118878963794836195 488712034678318445692254293)
                  ·
                    refine ⟨5727094156386544285456105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 488712034678318445692254293 5727094156386544285456105)
                    ·
                      refine ⟨4295320617289908214092079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5727094156386544285456105 4295320617289908214092079)
                      ·
                        rfl

theorem cell23_8365107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 8, 2].length) (baseStart_8365107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365107 prefixEnd_8365107 := by exact prefixLift 8365107
  have htrace : WordTrace (prefixWord ++ tailWord_8365107) baseStart_8365107 baseEnd_8365107 := by
    simpa [prefixWord, tailWord_8365107, baseEnd_8365107] using wordTrace_append hprefix tailTrace_8365107
  have hstable : (prefixWord ++ tailWord_8365107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365107).length < 2 ^ (prefixWord ++ tailWord_8365107).sum := by decide
  have hdescent : baseEnd_8365107 < baseStart_8365107 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365127 : List Nat := [1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 5]
def baseStart_8365127 : Nat := 118140960795 + 8365127 * 2 ^ 59
def prefixEnd_8365127 : Nat := 4983230072969 + 3 ^ 40 * 8365127 * 2
def baseEnd_8365127 : Nat := 4295330886902998135841987

theorem tailTrace_8365127 : CollatzResearch.WordTrace tailWord_8365127 prefixEnd_8365127 4295330886902998135841987 := by
  unfold tailWord_8365127
  simp only [CollatzResearch.WordTrace]
  refine ⟨305101246765581003796077635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203400831177054002530718423 305101246765581003796077635)
  ·
    refine ⟨457651870148371505694116453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305101246765581003796077635 457651870148371505694116453)
    ·
      refine ⟨85809725652819657317646835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 457651870148371505694116453 85809725652819657317646835)
      ·
        refine ⟨128714588479229485976470253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85809725652819657317646835 128714588479229485976470253)
        ·
          refine ⟨48267970679711057241176345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128714588479229485976470253 48267970679711057241176345)
          ·
            refine ⟨36200978009783292930882259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48267970679711057241176345 36200978009783292930882259)
            ·
              refine ⟨54301467014674939396323389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36200978009783292930882259 54301467014674939396323389)
              ·
                refine ⟨20363050130503102273621271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54301467014674939396323389 20363050130503102273621271)
                ·
                  refine ⟨30544575195754653410431907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20363050130503102273621271 30544575195754653410431907)
                  ·
                    refine ⟨45816862793631980115647861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30544575195754653410431907 45816862793631980115647861)
                    ·
                      refine ⟨4295330886902998135841987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45816862793631980115647861 4295330886902998135841987)
                      ·
                        rfl

theorem cell23_8365127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_8365127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365127 prefixEnd_8365127 := by exact prefixLift 8365127
  have htrace : WordTrace (prefixWord ++ tailWord_8365127) baseStart_8365127 baseEnd_8365127 := by
    simpa [prefixWord, tailWord_8365127, baseEnd_8365127] using wordTrace_append hprefix tailTrace_8365127
  have hstable : (prefixWord ++ tailWord_8365127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365127).length < 2 ^ (prefixWord ++ tailWord_8365127).sum := by decide
  have hdescent : baseEnd_8365127 < baseStart_8365127 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365130 : List Nat := [3, 1, 2, 1, 1, 2, 13]
def baseStart_8365130 : Nat := 118140960795 + 8365130 * 2 ^ 59
def prefixEnd_8365130 : Nat := 4983230072969 + 3 ^ 40 * 8365130 * 2
def baseEnd_8365130 : Nat := 53028795399320513877833

theorem tailTrace_8365130 : CollatzResearch.WordTrace tailWord_8365130 prefixEnd_8365130 53028795399320513877833 := by
  unfold tailWord_8365130
  simp only [CollatzResearch.WordTrace]
  refine ⟨76275339046142533827109211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203400904123046756872291229 76275339046142533827109211)
  ·
    refine ⟨114413008569213800740663817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76275339046142533827109211 114413008569213800740663817)
    ·
      refine ⟨85809756426910350555497863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114413008569213800740663817 85809756426910350555497863)
      ·
        refine ⟨128714634640365525833246795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85809756426910350555497863 128714634640365525833246795)
        ·
          refine ⟨193071951960548288749870193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128714634640365525833246795 193071951960548288749870193)
          ·
            refine ⟨144803963970411216562402645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193071951960548288749870193 144803963970411216562402645)
            ·
              refine ⟨53028795399320513877833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 144803963970411216562402645 53028795399320513877833)
              ·
                rfl

theorem cell23_8365130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 13].length) (baseStart_8365130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365130 prefixEnd_8365130 := by exact prefixLift 8365130
  have htrace : WordTrace (prefixWord ++ tailWord_8365130) baseStart_8365130 baseEnd_8365130 := by
    simpa [prefixWord, tailWord_8365130, baseEnd_8365130] using wordTrace_append hprefix tailTrace_8365130
  have hstable : (prefixWord ++ tailWord_8365130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365130).length < 2 ^ (prefixWord ++ tailWord_8365130).sum := by decide
  have hdescent : baseEnd_8365130 < baseStart_8365130 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365134 : List Nat := [4, 1, 1, 1, 1, 3, 2, 4, 2, 4]
def baseStart_8365134 : Nat := 118140960795 + 8365134 * 2 ^ 59
def prefixEnd_8365134 : Nat := 4983230072969 + 3 ^ 40 * 8365134 * 2
def baseEnd_8365134 : Nat := 1431778160422526536151485

theorem tailTrace_8365134 : CollatzResearch.WordTrace tailWord_8365134 prefixEnd_8365134 1431778160422526536151485 := by
  unfold tailWord_8365134
  simp only [CollatzResearch.WordTrace]
  refine ⟨38137687759569455498947807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203401001384370429327721637 38137687759569455498947807)
  ·
    refine ⟨57206531639354183248421711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38137687759569455498947807 57206531639354183248421711)
    ·
      refine ⟨85809797459031274872632567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57206531639354183248421711 85809797459031274872632567)
      ·
        refine ⟨128714696188546912308948851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85809797459031274872632567 128714696188546912308948851)
        ·
          refine ⟨193072044282820368463423277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128714696188546912308948851 193072044282820368463423277)
          ·
            refine ⟨72402016606057638173783729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193072044282820368463423277 72402016606057638173783729)
            ·
              refine ⟨54301512454543228630337797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72402016606057638173783729 54301512454543228630337797)
              ·
                refine ⟨10181533585226855368188337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54301512454543228630337797 10181533585226855368188337)
                ·
                  refine ⟨7636150188920141526141253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10181533585226855368188337 7636150188920141526141253)
                  ·
                    refine ⟨1431778160422526536151485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7636150188920141526141253 1431778160422526536151485)
                    ·
                      rfl

theorem cell23_8365134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 2, 4].length) (baseStart_8365134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365134 prefixEnd_8365134 := by exact prefixLift 8365134
  have htrace : WordTrace (prefixWord ++ tailWord_8365134) baseStart_8365134 baseEnd_8365134 := by
    simpa [prefixWord, tailWord_8365134, baseEnd_8365134] using wordTrace_append hprefix tailTrace_8365134
  have hstable : (prefixWord ++ tailWord_8365134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365134).length < 2 ^ (prefixWord ++ tailWord_8365134).sum := by decide
  have hdescent : baseEnd_8365134 < baseStart_8365134 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365154 : List Nat := [3, 3, 2, 2, 1, 1, 2, 1, 1, 1, 6]
def baseStart_8365154 : Nat := 118140960795 + 8365154 * 2 ^ 59
def prefixEnd_8365154 : Nat := 4983230072969 + 3 ^ 40 * 8365154 * 2
def baseEnd_8365154 : Nat := 4295344750880669530204363

theorem tailTrace_8365154 : CollatzResearch.WordTrace tailWord_8365154 prefixEnd_8365154 4295344750880669530204363 := by
  unfold tailWord_8365154
  simp only [CollatzResearch.WordTrace]
  refine ⟨76275557884120796851827629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203401487690988791604873677 76275557884120796851827629)
  ·
    refine ⟨28603334206545298819435361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76275557884120796851827629 28603334206545298819435361)
    ·
      refine ⟨21452500654908974114576521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28603334206545298819435361 21452500654908974114576521)
      ·
        refine ⟨16089375491181730585932391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21452500654908974114576521 16089375491181730585932391)
        ·
          refine ⟨24134063236772595878898587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16089375491181730585932391 24134063236772595878898587)
          ·
            refine ⟨36201094855158893818347881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24134063236772595878898587 36201094855158893818347881)
            ·
              refine ⟨27150821141369170363760911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36201094855158893818347881 27150821141369170363760911)
              ·
                refine ⟨40726231712053755545641367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27150821141369170363760911 40726231712053755545641367)
                ·
                  refine ⟨61089347568080633318462051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40726231712053755545641367 61089347568080633318462051)
                  ·
                    refine ⟨91634021352120949977693077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61089347568080633318462051 91634021352120949977693077)
                    ·
                      refine ⟨4295344750880669530204363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91634021352120949977693077 4295344750880669530204363)
                      ·
                        rfl

theorem cell23_8365154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_8365154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365154 prefixEnd_8365154 := by exact prefixLift 8365154
  have htrace : WordTrace (prefixWord ++ tailWord_8365154) baseStart_8365154 baseEnd_8365154 := by
    simpa [prefixWord, tailWord_8365154, baseEnd_8365154] using wordTrace_append hprefix tailTrace_8365154
  have hstable : (prefixWord ++ tailWord_8365154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365154).length < 2 ^ (prefixWord ++ tailWord_8365154).sum := by decide
  have hdescent : baseEnd_8365154 < baseStart_8365154 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365161 : List Nat := [1, 2, 1, 1, 1, 8, 1, 2, 1, 2, 3]
def baseStart_8365161 : Nat := 118140960795 + 8365161 * 2 ^ 59
def prefixEnd_8365161 : Nat := 4983230072969 + 3 ^ 40 * 8365161 * 2
def baseEnd_8365161 : Nat := 4295348345245251002816831

theorem tailTrace_8365161 : CollatzResearch.WordTrace tailWord_8365161 prefixEnd_8365161 4295348345245251002816831 := by
  unfold tailWord_8365161
  simp only [CollatzResearch.WordTrace]
  refine ⟨305102486847457827602815337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203401657898305218401876891 305102486847457827602815337)
  ·
    refine ⟨228826865135593370702111503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305102486847457827602815337 228826865135593370702111503)
    ·
      refine ⟨343240297703390056053167255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228826865135593370702111503 343240297703390056053167255)
      ·
        refine ⟨514860446555085084079750883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343240297703390056053167255 514860446555085084079750883)
        ·
          refine ⟨772290669832627626119626325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514860446555085084079750883 772290669832627626119626325)
          ·
            refine ⟨9050281287101104993589371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 772290669832627626119626325 9050281287101104993589371)
            ·
              refine ⟨13575421930651657490384057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9050281287101104993589371 13575421930651657490384057)
              ·
                refine ⟨10181566447988743117788043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13575421930651657490384057 10181566447988743117788043)
                ·
                  refine ⟨15272349671983114676682065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10181566447988743117788043 15272349671983114676682065)
                  ·
                    refine ⟨11454262253987336007511549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15272349671983114676682065 11454262253987336007511549)
                    ·
                      refine ⟨4295348345245251002816831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11454262253987336007511549 4295348345245251002816831)
                      ·
                        rfl

theorem cell23_8365161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 2, 3].length) (baseStart_8365161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365161 prefixEnd_8365161 := by exact prefixLift 8365161
  have htrace : WordTrace (prefixWord ++ tailWord_8365161) baseStart_8365161 baseEnd_8365161 := by
    simpa [prefixWord, tailWord_8365161, baseEnd_8365161] using wordTrace_append hprefix tailTrace_8365161
  have hstable : (prefixWord ++ tailWord_8365161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365161).length < 2 ^ (prefixWord ++ tailWord_8365161).sum := by decide
  have hdescent : baseEnd_8365161 < baseStart_8365161 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365207 : List Nat := [1, 1, 3, 3, 3, 1, 1, 1, 1, 8]
def baseStart_8365207 : Nat := 118140960795 + 8365207 * 2 ^ 59
def prefixEnd_8365207 : Nat := 4983230072969 + 3 ^ 40 * 8365207 * 2
def baseEnd_8365207 : Nat := 1431790655118452607613873

theorem tailTrace_8365207 : CollatzResearch.WordTrace tailWord_8365207 prefixEnd_8365207 1431790655118452607613873 := by
  unfold tailWord_8365207
  simp only [CollatzResearch.WordTrace]
  refine ⟨305104164605291177458989875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203402776403527451639326583 305104164605291177458989875)
  ·
    refine ⟨457656246907936766188484813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305104164605291177458989875 457656246907936766188484813)
    ·
      refine ⟨171621092590476287320681805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 457656246907936766188484813 171621092590476287320681805)
      ·
        refine ⟨64357909721428607745255677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171621092590476287320681805 64357909721428607745255677)
        ·
          refine ⟨24134216145535727904470879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64357909721428607745255677 24134216145535727904470879)
          ·
            refine ⟨36201324218303591856706319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24134216145535727904470879 36201324218303591856706319)
            ·
              refine ⟨54301986327455387785059479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36201324218303591856706319 54301986327455387785059479)
              ·
                refine ⟨81452979491183081677589219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54301986327455387785059479 81452979491183081677589219)
                ·
                  refine ⟨122179469236774622516383829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81452979491183081677589219 122179469236774622516383829)
                  ·
                    refine ⟨1431790655118452607613873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 122179469236774622516383829 1431790655118452607613873)
                    ·
                      rfl

theorem cell23_8365207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 8].length) (baseStart_8365207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365207 prefixEnd_8365207 := by exact prefixLift 8365207
  have htrace : WordTrace (prefixWord ++ tailWord_8365207) baseStart_8365207 baseEnd_8365207 := by
    simpa [prefixWord, tailWord_8365207, baseEnd_8365207] using wordTrace_append hprefix tailTrace_8365207
  have hstable : (prefixWord ++ tailWord_8365207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365207).length < 2 ^ (prefixWord ++ tailWord_8365207).sum := by decide
  have hdescent : baseEnd_8365207 < baseStart_8365207 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365244 : List Nat := [2, 2, 2, 3, 2, 1, 1, 2, 2, 2, 4]
def baseStart_8365244 : Nat := 118140960795 + 8365244 * 2 ^ 59
def prefixEnd_8365244 : Nat := 4983230072969 + 3 ^ 40 * 8365244 * 2
def baseEnd_8365244 : Nat := 4295390964139574178078949

theorem tailTrace_8365244 : CollatzResearch.WordTrace tailWord_8365244 prefixEnd_8365244 4295390964139574178078949 := by
  unfold tailWord_8365244
  simp only [CollatzResearch.WordTrace]
  refine ⟨152552757053078566389043393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203403676070771421852057857 152552757053078566389043393)
  ·
    refine ⟨114414567789808924791782545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152552757053078566389043393 114414567789808924791782545)
    ·
      refine ⟨85810925842356693593836909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114414567789808924791782545 85810925842356693593836909)
      ·
        refine ⟨32179097190883760097688841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85810925842356693593836909 32179097190883760097688841)
        ·
          refine ⟨24134322893162820073266631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32179097190883760097688841 24134322893162820073266631)
          ·
            refine ⟨36201484339744230109899947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24134322893162820073266631 36201484339744230109899947)
            ·
              refine ⟨54302226509616345164849921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36201484339744230109899947 54302226509616345164849921)
              ·
                refine ⟨40726669882212258873637441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54302226509616345164849921 40726669882212258873637441)
                ·
                  refine ⟨30545002411659194155228081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40726669882212258873637441 30545002411659194155228081)
                  ·
                    refine ⟨22908751808744395616421061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30545002411659194155228081 22908751808744395616421061)
                    ·
                      refine ⟨4295390964139574178078949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22908751808744395616421061 4295390964139574178078949)
                      ·
                        rfl

theorem cell23_8365244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_8365244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365244 prefixEnd_8365244 := by exact prefixLift 8365244
  have htrace : WordTrace (prefixWord ++ tailWord_8365244) baseStart_8365244 baseEnd_8365244 := by
    simpa [prefixWord, tailWord_8365244, baseEnd_8365244] using wordTrace_append hprefix tailTrace_8365244
  have hstable : (prefixWord ++ tailWord_8365244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365244).length < 2 ^ (prefixWord ++ tailWord_8365244).sum := by decide
  have hdescent : baseEnd_8365244 < baseStart_8365244 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365248 : List Nat := [2, 1, 1, 2, 6, 1, 1, 1, 4, 2, 2]
def baseStart_8365248 : Nat := 118140960795 + 8365248 * 2 ^ 59
def prefixEnd_8365248 : Nat := 4983230072969 + 3 ^ 40 * 8365248 * 2
def baseEnd_8365248 : Nat := 4295393018062192162428931

theorem tailTrace_8365248 : CollatzResearch.WordTrace tailWord_8365248 prefixEnd_8365248 4295393018062192162428931 := by
  unfold tailWord_8365248
  simp only [CollatzResearch.WordTrace]
  refine ⟨152552829999071320730616199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203403773332095094307488265 152552829999071320730616199)
  ·
    refine ⟨228829244998606981095924299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152552829999071320730616199 228829244998606981095924299)
    ·
      refine ⟨343243867497910471643886449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228829244998606981095924299 343243867497910471643886449)
      ·
        refine ⟨257432900623432853732914837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343243867497910471643886449 257432900623432853732914837)
        ·
          refine ⟨12067167216723415018730383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 257432900623432853732914837 12067167216723415018730383)
          ·
            refine ⟨18100750825085122528095575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12067167216723415018730383 18100750825085122528095575)
            ·
              refine ⟨27151126237627683792143363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18100750825085122528095575 27151126237627683792143363)
              ·
                refine ⟨40726689356441525688215045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27151126237627683792143363 40726689356441525688215045)
                ·
                  refine ⟨7636254254332786066540321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40726689356441525688215045 7636254254332786066540321)
                  ·
                    refine ⟨5727190690749589549905241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7636254254332786066540321 5727190690749589549905241)
                    ·
                      refine ⟨4295393018062192162428931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5727190690749589549905241 4295393018062192162428931)
                      ·
                        rfl

theorem cell23_8365248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 4, 2, 2].length) (baseStart_8365248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365248 prefixEnd_8365248 := by exact prefixLift 8365248
  have htrace : WordTrace (prefixWord ++ tailWord_8365248) baseStart_8365248 baseEnd_8365248 := by
    simpa [prefixWord, tailWord_8365248, baseEnd_8365248] using wordTrace_append hprefix tailTrace_8365248
  have hstable : (prefixWord ++ tailWord_8365248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365248).length < 2 ^ (prefixWord ++ tailWord_8365248).sum := by decide
  have hdescent : baseEnd_8365248 < baseStart_8365248 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365267 : List Nat := [1, 1, 1, 2, 1, 1, 1, 6, 4, 5]
def baseStart_8365267 : Nat := 118140960795 + 8365267 * 2 ^ 59
def prefixEnd_8365267 : Nat := 4983230072969 + 3 ^ 40 * 8365267 * 2
def baseEnd_8365267 : Nat := 1431800924731542529363781

theorem tailTrace_8365267 : CollatzResearch.WordTrace tailWord_8365267 prefixEnd_8365267 1431800924731542529363781 := by
  unfold tailWord_8365267
  simp only [CollatzResearch.WordTrace]
  refine ⟨305106352985073807706174055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203404235323382538470782703 305106352985073807706174055)
  ·
    refine ⟨457659529477610711559261083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305106352985073807706174055 457659529477610711559261083)
    ·
      refine ⟨686489294216416067338891625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457659529477610711559261083 686489294216416067338891625)
      ·
        refine ⟨514866970662312050504168719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 686489294216416067338891625 514866970662312050504168719)
        ·
          refine ⟨772300455993468075756253079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514866970662312050504168719 772300455993468075756253079)
          ·
            refine ⟨1158450683990202113634379619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 772300455993468075756253079 1158450683990202113634379619)
            ·
              refine ⟨1737676025985303170451569429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1158450683990202113634379619 1737676025985303170451569429)
              ·
                refine ⟨81453563718061086114917317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1737676025985303170451569429 81453563718061086114917317)
                ·
                  refine ⟨15272543197136453646546997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81453563718061086114917317 15272543197136453646546997)
                  ·
                    refine ⟨1431800924731542529363781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15272543197136453646546997 1431800924731542529363781)
                    ·
                      rfl

theorem cell23_8365267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 5].length) (baseStart_8365267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365267 prefixEnd_8365267 := by exact prefixLift 8365267
  have htrace : WordTrace (prefixWord ++ tailWord_8365267) baseStart_8365267 baseEnd_8365267 := by
    simpa [prefixWord, tailWord_8365267, baseEnd_8365267] using wordTrace_append hprefix tailTrace_8365267
  have hstable : (prefixWord ++ tailWord_8365267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365267).length < 2 ^ (prefixWord ++ tailWord_8365267).sum := by decide
  have hdescent : baseEnd_8365267 < baseStart_8365267 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365348 : List Nat := [2, 3, 1, 3, 1, 1, 2, 5, 1, 4]
def baseStart_8365348 : Nat := 118140960795 + 8365348 * 2 ^ 59
def prefixEnd_8365348 : Nat := 4983230072969 + 3 ^ 40 * 8365348 * 2
def baseEnd_8365348 : Nat := 1431814788709213923726157

theorem tailTrace_8365348 : CollatzResearch.WordTrace tailWord_8365348 prefixEnd_8365348 1431814788709213923726157 := by
  unfold tailWord_8365348
  simp only [CollatzResearch.WordTrace]
  refine ⟨152554653648890179269936349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203406204865186905693248465 152554653648890179269936349)
  ·
    refine ⟨57207995118333817226226131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152554653648890179269936349 57207995118333817226226131)
    ·
      refine ⟨85811992677500725839339197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57207995118333817226226131 85811992677500725839339197)
      ·
        refine ⟨32179497254062772189752199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85811992677500725839339197 32179497254062772189752199)
        ·
          refine ⟨48269245881094158284628299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32179497254062772189752199 48269245881094158284628299)
          ·
            refine ⟨72403868821641237426942449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48269245881094158284628299 72403868821641237426942449)
            ·
              refine ⟨54302901616230928070206837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72403868821641237426942449 54302901616230928070206837)
              ·
                refine ⟨5090897026521649506581891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54302901616230928070206837 5090897026521649506581891)
                ·
                  refine ⟨7636345539782474259872837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5090897026521649506581891 7636345539782474259872837)
                  ·
                    refine ⟨1431814788709213923726157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7636345539782474259872837 1431814788709213923726157)
                    ·
                      rfl

theorem cell23_8365348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 5, 1, 4].length) (baseStart_8365348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365348 prefixEnd_8365348 := by exact prefixLift 8365348
  have htrace : WordTrace (prefixWord ++ tailWord_8365348) baseStart_8365348 baseEnd_8365348 := by
    simpa [prefixWord, tailWord_8365348, baseEnd_8365348] using wordTrace_append hprefix tailTrace_8365348
  have hstable : (prefixWord ++ tailWord_8365348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365348).length < 2 ^ (prefixWord ++ tailWord_8365348).sum := by decide
  have hdescent : baseEnd_8365348 < baseStart_8365348 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365361 : List Nat := [1, 2, 2, 3, 3, 2, 2, 2, 6]
def baseStart_8365361 : Nat := 118140960795 + 8365361 * 2 ^ 59
def prefixEnd_8365361 : Nat := 4983230072969 + 3 ^ 40 * 8365361 * 2
def baseEnd_8365361 : Nat := 477272337930683357812879

theorem tailTrace_8365361 : CollatzResearch.WordTrace tailWord_8365361 prefixEnd_8365361 477272337930683357812879 := by
  unfold tailWord_8365361
  simp only [CollatzResearch.WordTrace]
  refine ⟨305109781446733261760095937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203406520964488841173397291 305109781446733261760095937)
  ·
    refine ⟨228832336085049946320071953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305109781446733261760095937 228832336085049946320071953)
    ·
      refine ⟨171624252063787459740053965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228832336085049946320071953 171624252063787459740053965)
      ·
        refine ⟨64359094523920297402520237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171624252063787459740053965 64359094523920297402520237)
        ·
          refine ⟨24134660446470111525945089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64359094523920297402520237 24134660446470111525945089)
          ·
            refine ⟨18100995334852583644458817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24134660446470111525945089 18100995334852583644458817)
            ·
              refine ⟨13575746501139437733344113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18100995334852583644458817 13575746501139437733344113)
              ·
                refine ⟨10181809875854578300008085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13575746501139437733344113 10181809875854578300008085)
                ·
                  refine ⟨477272337930683357812879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10181809875854578300008085 477272337930683357812879)
                  ·
                    rfl

theorem cell23_8365361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 6].length) (baseStart_8365361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365361 prefixEnd_8365361 := by exact prefixLift 8365361
  have htrace : WordTrace (prefixWord ++ tailWord_8365361) baseStart_8365361 baseEnd_8365361 := by
    simpa [prefixWord, tailWord_8365361, baseEnd_8365361] using wordTrace_append hprefix tailTrace_8365361
  have hstable : (prefixWord ++ tailWord_8365361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365361).length < 2 ^ (prefixWord ++ tailWord_8365361).sum := by decide
  have hdescent : baseEnd_8365361 < baseStart_8365361 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365365 : List Nat := [1, 3, 3, 1, 2, 2, 4, 2, 1, 4]
def baseStart_8365365 : Nat := 118140960795 + 8365365 * 2 ^ 59
def prefixEnd_8365365 : Nat := 4983230072969 + 3 ^ 40 * 8365365 * 2
def baseEnd_8365365 : Nat := 1431817698432922734888631

theorem tailTrace_8365365 : CollatzResearch.WordTrace tailWord_8365365 prefixEnd_8365365 1431817698432922734888631 := by
  unfold tailWord_8365365
  simp only [CollatzResearch.WordTrace]
  refine ⟨305109927338718770443241549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203406618225812513628827699 305109927338718770443241549)
  ·
    refine ⟨114416222752019538916215581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305109927338718770443241549 114416222752019538916215581)
    ·
      refine ⟨42906083532007327093580843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114416222752019538916215581 42906083532007327093580843)
      ·
        refine ⟨64359125298010990640371265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42906083532007327093580843 64359125298010990640371265)
        ·
          refine ⟨48269343973508242980278449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64359125298010990640371265 48269343973508242980278449)
          ·
            refine ⟨36202007980131182235208837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48269343973508242980278449 36202007980131182235208837)
            ·
              refine ⟨6787876496274596669101657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36202007980131182235208837 6787876496274596669101657)
              ·
                refine ⟨5090907372205947501826243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6787876496274596669101657 5090907372205947501826243)
                ·
                  refine ⟨7636361058308921252739365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5090907372205947501826243 7636361058308921252739365)
                  ·
                    refine ⟨1431817698432922734888631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7636361058308921252739365 1431817698432922734888631)
                    ·
                      rfl

theorem cell23_8365365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_8365365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365365 prefixEnd_8365365 := by exact prefixLift 8365365
  have htrace : WordTrace (prefixWord ++ tailWord_8365365) baseStart_8365365 baseEnd_8365365 := by
    simpa [prefixWord, tailWord_8365365, baseEnd_8365365] using wordTrace_append hprefix tailTrace_8365365
  have hstable : (prefixWord ++ tailWord_8365365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365365).length < 2 ^ (prefixWord ++ tailWord_8365365).sum := by decide
  have hdescent : baseEnd_8365365 < baseStart_8365365 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365381 : List Nat := [1, 3, 1, 1, 1, 2, 1, 4, 4, 3, 2]
def baseStart_8365381 : Nat := 118140960795 + 8365381 * 2 ^ 59
def prefixEnd_8365381 : Nat := 4983230072969 + 3 ^ 40 * 8365381 * 2
def baseEnd_8365381 : Nat := 4295461310989240142065819

theorem tailTrace_8365381 : CollatzResearch.WordTrace tailWord_8365381 prefixEnd_8365381 4295461310989240142065819 := by
  unfold tailWord_8365381
  simp only [CollatzResearch.WordTrace]
  refine ⟨305110510906660805175823997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203407007271107203450549331 305110510906660805175823997)
  ·
    refine ⟨114416441589997801940933999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305110510906660805175823997 114416441589997801940933999)
    ·
      refine ⟨171624662384996702911400999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114416441589997801940933999 171624662384996702911400999)
      ·
        refine ⟨257436993577495054367101499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171624662384996702911400999 257436993577495054367101499)
        ·
          refine ⟨386155490366242581550652249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257436993577495054367101499 386155490366242581550652249)
          ·
            refine ⟨289616617774681936162989187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386155490366242581550652249 289616617774681936162989187)
            ·
              refine ⟨434424926662022904244483781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289616617774681936162989187 434424926662022904244483781)
              ·
                refine ⟨81454673749129294545840709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 434424926662022904244483781 81454673749129294545840709)
                ·
                  refine ⟨15272751327961742727345133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81454673749129294545840709 15272751327961742727345133)
                  ·
                    refine ⟨5727281747985653522754425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15272751327961742727345133 5727281747985653522754425)
                    ·
                      refine ⟨4295461310989240142065819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5727281747985653522754425 4295461310989240142065819)
                      ·
                        rfl

theorem cell23_8365381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 3, 2].length) (baseStart_8365381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365381 prefixEnd_8365381 := by exact prefixLift 8365381
  have htrace : WordTrace (prefixWord ++ tailWord_8365381) baseStart_8365381 baseEnd_8365381 := by
    simpa [prefixWord, tailWord_8365381, baseEnd_8365381] using wordTrace_append hprefix tailTrace_8365381
  have hstable : (prefixWord ++ tailWord_8365381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365381).length < 2 ^ (prefixWord ++ tailWord_8365381).sum := by decide
  have hdescent : baseEnd_8365381 < baseStart_8365381 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365382 : List Nat := [6, 1, 1, 3, 1, 1, 1, 2, 3, 4]
def baseStart_8365382 : Nat := 118140960795 + 8365382 * 2 ^ 59
def prefixEnd_8365382 : Nat := 4983230072969 + 3 ^ 40 * 8365382 * 2
def baseEnd_8365382 : Nat := 1431820608156631546051105

theorem tailTrace_8365382 : CollatzResearch.WordTrace tailWord_8365382 prefixEnd_8365382 1431820608156631546051105 := by
  unfold tailWord_8365382
  simp only [CollatzResearch.WordTrace]
  refine ⟨9534704605614286948331575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 203407031586438121564406933 9534704605614286948331575)
  ·
    refine ⟨14302056908421430422497363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9534704605614286948331575 14302056908421430422497363)
    ·
      refine ⟨21453085362632145633746045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14302056908421430422497363 21453085362632145633746045)
      ·
        refine ⟨8044907010987054612654767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21453085362632145633746045 8044907010987054612654767)
        ·
          refine ⟨12067360516480581918982151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8044907010987054612654767 12067360516480581918982151)
          ·
            refine ⟨18101040774720872878473227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12067360516480581918982151 18101040774720872878473227)
            ·
              refine ⟨27151561162081309317709841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18101040774720872878473227 27151561162081309317709841)
              ·
                refine ⟨20363670871560981988282381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27151561162081309317709841 20363670871560981988282381)
                ·
                  refine ⟨7636376576835368245605893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20363670871560981988282381 7636376576835368245605893)
                  ·
                    refine ⟨1431820608156631546051105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7636376576835368245605893 1431820608156631546051105)
                    ·
                      rfl

theorem cell23_8365382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_8365382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365382 prefixEnd_8365382 := by exact prefixLift 8365382
  have htrace : WordTrace (prefixWord ++ tailWord_8365382) baseStart_8365382 baseEnd_8365382 := by
    simpa [prefixWord, tailWord_8365382, baseEnd_8365382] using wordTrace_append hprefix tailTrace_8365382
  have hstable : (prefixWord ++ tailWord_8365382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365382).length < 2 ^ (prefixWord ++ tailWord_8365382).sum := by decide
  have hdescent : baseEnd_8365382 < baseStart_8365382 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365388 : List Nat := [2, 2, 1, 3, 2, 3, 1, 2, 3, 1, 3]
def baseStart_8365388 : Nat := 118140960795 + 8365388 * 2 ^ 59
def prefixEnd_8365388 : Nat := 4983230072969 + 3 ^ 40 * 8365388 * 2
def baseEnd_8365388 : Nat := 4295464905353821614678287

theorem tailTrace_8365388 : CollatzResearch.WordTrace tailWord_8365388 prefixEnd_8365388 4295464905353821614678287 := by
  unfold tailWord_8365388
  simp only [CollatzResearch.WordTrace]
  refine ⟨152555383108817722685664409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203407177478423630247552545 152555383108817722685664409)
  ·
    refine ⟨114416537331613292014248307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152555383108817722685664409 114416537331613292014248307)
    ·
      refine ⟨171624805997419938021372461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114416537331613292014248307 171624805997419938021372461)
      ·
        refine ⟨64359302249032476758014673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171624805997419938021372461 64359302249032476758014673)
        ·
          refine ⟨48269476686774357568511005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64359302249032476758014673 48269476686774357568511005)
          ·
            refine ⟨18101053757540384088191627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48269476686774357568511005 18101053757540384088191627)
            ·
              refine ⟨27151580636310576132287441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18101053757540384088191627 27151580636310576132287441)
              ·
                refine ⟨20363685477232932099215581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27151580636310576132287441 20363685477232932099215581)
                ·
                  refine ⟨7636382053962349537205843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20363685477232932099215581 7636382053962349537205843)
                  ·
                    refine ⟨11454573080943524305808765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7636382053962349537205843 11454573080943524305808765)
                    ·
                      refine ⟨4295464905353821614678287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11454573080943524305808765 4295464905353821614678287)
                      ·
                        rfl

theorem cell23_8365388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_8365388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365388 prefixEnd_8365388 := by exact prefixLift 8365388
  have htrace : WordTrace (prefixWord ++ tailWord_8365388) baseStart_8365388 baseEnd_8365388 := by
    simpa [prefixWord, tailWord_8365388, baseEnd_8365388] using wordTrace_append hprefix tailTrace_8365388
  have hstable : (prefixWord ++ tailWord_8365388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365388).length < 2 ^ (prefixWord ++ tailWord_8365388).sum := by decide
  have hdescent : baseEnd_8365388 < baseStart_8365388 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365408 : List Nat := [2, 1, 1, 3, 4, 1, 4, 1, 1, 5]
def baseStart_8365408 : Nat := 118140960795 + 8365408 * 2 ^ 59
def prefixEnd_8365408 : Nat := 4983230072969 + 3 ^ 40 * 8365408 * 2
def baseEnd_8365408 : Nat := 1431825058322303845476065

theorem tailTrace_8365408 : CollatzResearch.WordTrace tailWord_8365408 prefixEnd_8365408 1431825058322303845476065 := by
  unfold tailWord_8365408
  simp only [CollatzResearch.WordTrace]
  refine ⟨152555747838781494393528439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203407663785041992524704585 152555747838781494393528439)
  ·
    refine ⟨228833621758172241590292659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152555747838781494393528439 228833621758172241590292659)
    ·
      refine ⟨343250432637258362385438989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228833621758172241590292659 343250432637258362385438989)
      ·
        refine ⟨128718912238971885894539621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343250432637258362385438989 128718912238971885894539621)
        ·
          refine ⟨24134796044807228605226179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128718912238971885894539621 24134796044807228605226179)
          ·
            refine ⟨36202194067210842907839269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24134796044807228605226179 36202194067210842907839269)
            ·
              refine ⟨6787911387602033045219863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36202194067210842907839269 6787911387602033045219863)
              ·
                refine ⟨10181867081403049567829795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6787911387602033045219863 10181867081403049567829795)
                ·
                  refine ⟨15272800622104574351744693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10181867081403049567829795 15272800622104574351744693)
                  ·
                    refine ⟨1431825058322303845476065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15272800622104574351744693 1431825058322303845476065)
                    ·
                      rfl

theorem cell23_8365408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 1, 5].length) (baseStart_8365408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365408 prefixEnd_8365408 := by exact prefixLift 8365408
  have htrace : WordTrace (prefixWord ++ tailWord_8365408) baseStart_8365408 baseEnd_8365408 := by
    simpa [prefixWord, tailWord_8365408, baseEnd_8365408] using wordTrace_append hprefix tailTrace_8365408
  have hstable : (prefixWord ++ tailWord_8365408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365408).length < 2 ^ (prefixWord ++ tailWord_8365408).sum := by decide
  have hdescent : baseEnd_8365408 < baseStart_8365408 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365422 : List Nat := [4, 1, 2, 4, 1, 1, 2, 1, 3, 1, 3]
def baseStart_8365422 : Nat := 118140960795 + 8365422 * 2 ^ 59
def prefixEnd_8365422 : Nat := 4983230072969 + 3 ^ 40 * 8365422 * 2
def baseEnd_8365422 : Nat := 4295482363696074481653131

theorem tailTrace_8365422 : CollatzResearch.WordTrace tailWord_8365422 prefixEnd_8365422 4295482363696074481653131 := by
  unfold tailWord_8365422
  simp only [CollatzResearch.WordTrace]
  refine ⟨38139000787439033647258315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203408004199674846118711013 38139000787439033647258315)
  ·
    refine ⟨57208501181158550470887473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38139000787439033647258315 57208501181158550470887473)
    ·
      refine ⟨42906375885868912853165605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57208501181158550470887473 42906375885868912853165605)
      ·
        refine ⟨8044945478600421159968551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42906375885868912853165605 8044945478600421159968551)
        ·
          refine ⟨12067418217900631739952827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8044945478600421159968551 12067418217900631739952827)
          ·
            refine ⟨18101127326850947609929241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12067418217900631739952827 18101127326850947609929241)
            ·
              refine ⟨13575845495138210707446931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18101127326850947609929241 13575845495138210707446931)
              ·
                refine ⟨20363768242707316061170397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13575845495138210707446931 20363768242707316061170397)
                ·
                  refine ⟨7636413091015243522938899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20363768242707316061170397 7636413091015243522938899)
                  ·
                    refine ⟨11454619636522865284408349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7636413091015243522938899 11454619636522865284408349)
                    ·
                      refine ⟨4295482363696074481653131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11454619636522865284408349 4295482363696074481653131)
                      ·
                        rfl

theorem cell23_8365422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_8365422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365422 prefixEnd_8365422 := by exact prefixLift 8365422
  have htrace : WordTrace (prefixWord ++ tailWord_8365422) baseStart_8365422 baseEnd_8365422 := by
    simpa [prefixWord, tailWord_8365422, baseEnd_8365422] using wordTrace_append hprefix tailTrace_8365422
  have hstable : (prefixWord ++ tailWord_8365422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365422).length < 2 ^ (prefixWord ++ tailWord_8365422).sum := by decide
  have hdescent : baseEnd_8365422 < baseStart_8365422 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365424 : List Nat := [2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 6]
def baseStart_8365424 : Nat := 118140960795 + 8365424 * 2 ^ 59
def prefixEnd_8365424 : Nat := 4983230072969 + 3 ^ 40 * 8365424 * 2
def baseEnd_8365424 : Nat := 4295483390657383473828121

theorem tailTrace_8365424 : CollatzResearch.WordTrace tailWord_8365424 prefixEnd_8365424 4295483390657383473828121 := by
  unfold tailWord_8365424
  simp only [CollatzResearch.WordTrace]
  refine ⟨152556039622752511759819663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203408052830336682346426217 152556039622752511759819663)
  ·
    refine ⟨228834059434128767639729495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152556039622752511759819663 228834059434128767639729495)
    ·
      refine ⟨343251089151193151459594243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228834059434128767639729495 343251089151193151459594243)
      ·
        refine ⟨514876633726789727189391365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343251089151193151459594243 514876633726789727189391365)
        ·
          refine ⟨96539368823773073848010881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 514876633726789727189391365 96539368823773073848010881)
          ·
            refine ⟨72404526617829805386008161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96539368823773073848010881 72404526617829805386008161)
            ·
              refine ⟨54303394963372354039506121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72404526617829805386008161 54303394963372354039506121)
              ·
                refine ⟨40727546222529265529629591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54303394963372354039506121 40727546222529265529629591)
                ·
                  refine ⟨61091319333793898294444387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40727546222529265529629591 61091319333793898294444387)
                  ·
                    refine ⟨91636979000690847441666581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61091319333793898294444387 91636979000690847441666581)
                    ·
                      refine ⟨4295483390657383473828121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91636979000690847441666581 4295483390657383473828121)
                      ·
                        rfl

theorem cell23_8365424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 6].length) (baseStart_8365424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365424 prefixEnd_8365424 := by exact prefixLift 8365424
  have htrace : WordTrace (prefixWord ++ tailWord_8365424) baseStart_8365424 baseEnd_8365424 := by
    simpa [prefixWord, tailWord_8365424, baseEnd_8365424] using wordTrace_append hprefix tailTrace_8365424
  have hstable : (prefixWord ++ tailWord_8365424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365424).length < 2 ^ (prefixWord ++ tailWord_8365424).sum := by decide
  have hdescent : baseEnd_8365424 < baseStart_8365424 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365448 : List Nat := [2, 1, 3, 3, 1, 2, 1, 4, 1, 2, 3]
def baseStart_8365448 : Nat := 118140960795 + 8365448 * 2 ^ 59
def prefixEnd_8365448 : Nat := 4983230072969 + 3 ^ 40 * 8365448 * 2
def baseEnd_8365448 : Nat := 4295495714193091379928011

theorem tailTrace_8365448 : CollatzResearch.WordTrace tailWord_8365448 prefixEnd_8365448 4295495714193091379928011 := by
  unfold tailWord_8365448
  simp only [CollatzResearch.WordTrace]
  refine ⟨152556477298709037809256499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203408636398278717079008665 152556477298709037809256499)
  ·
    refine ⟨228834715948063556713884749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152556477298709037809256499 228834715948063556713884749)
    ·
      refine ⟨85813018480523833767706781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228834715948063556713884749 85813018480523833767706781)
      ·
        refine ⟨32179881930196437662890043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85813018480523833767706781 32179881930196437662890043)
        ·
          refine ⟨48269822895294656494335065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32179881930196437662890043 48269822895294656494335065)
          ·
            refine ⟨36202367171470992370751299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48269822895294656494335065 36202367171470992370751299)
            ·
              refine ⟨54303550757206488556126949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36202367171470992370751299 54303550757206488556126949)
              ·
                refine ⟨10181915766976216604273803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54303550757206488556126949 10181915766976216604273803)
                ·
                  refine ⟨15272873650464324906410705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10181915766976216604273803 15272873650464324906410705)
                  ·
                    refine ⟨11454655237848243679808029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15272873650464324906410705 11454655237848243679808029)
                    ·
                      refine ⟨4295495714193091379928011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11454655237848243679808029 4295495714193091379928011)
                      ·
                        rfl

theorem cell23_8365448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_8365448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365448 prefixEnd_8365448 := by exact prefixLift 8365448
  have htrace : WordTrace (prefixWord ++ tailWord_8365448) baseStart_8365448 baseEnd_8365448 := by
    simpa [prefixWord, tailWord_8365448, baseEnd_8365448] using wordTrace_append hprefix tailTrace_8365448
  have hstable : (prefixWord ++ tailWord_8365448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365448).length < 2 ^ (prefixWord ++ tailWord_8365448).sum := by decide
  have hdescent : baseEnd_8365448 < baseStart_8365448 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365461 : List Nat := [1, 3, 2, 1, 1, 2, 2, 4, 1, 3, 3]
def baseStart_8365461 : Nat := 118140960795 + 8365461 * 2 ^ 59
def prefixEnd_8365461 : Nat := 4983230072969 + 3 ^ 40 * 8365461 * 2
def baseEnd_8365461 : Nat := 4295502389441599829065451

theorem tailTrace_8365461 : CollatzResearch.WordTrace tailWord_8365461 prefixEnd_8365461 4295502389441599829065451 := by
  unfold tailWord_8365461
  simp only [CollatzResearch.WordTrace]
  refine ⟨305113428746370978838736237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203408952497580652559157491 305113428746370978838736237)
  ·
    refine ⟨114417535779889117064526089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305113428746370978838736237 114417535779889117064526089)
    ·
      refine ⟨85813151834916837798394567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114417535779889117064526089 85813151834916837798394567)
      ·
        refine ⟨128719727752375256697591851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85813151834916837798394567 128719727752375256697591851)
        ·
          refine ⟨193079591628562885046387777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128719727752375256697591851 193079591628562885046387777)
          ·
            refine ⟨144809693721422163784790833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193079591628562885046387777 144809693721422163784790833)
            ·
              refine ⟨108607270291066622838593125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144809693721422163784790833 108607270291066622838593125)
              ·
                refine ⟨20363863179574991782236211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108607270291066622838593125 20363863179574991782236211)
                ·
                  refine ⟨30545794769362487673354317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20363863179574991782236211 30545794769362487673354317)
                  ·
                    refine ⟨11454673038510932877507869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30545794769362487673354317 11454673038510932877507869)
                    ·
                      refine ⟨4295502389441599829065451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11454673038510932877507869 4295502389441599829065451)
                      ·
                        rfl

theorem cell23_8365461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 3, 3].length) (baseStart_8365461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365461 prefixEnd_8365461 := by exact prefixLift 8365461
  have htrace : WordTrace (prefixWord ++ tailWord_8365461) baseStart_8365461 baseEnd_8365461 := by
    simpa [prefixWord, tailWord_8365461, baseEnd_8365461] using wordTrace_append hprefix tailTrace_8365461
  have hstable : (prefixWord ++ tailWord_8365461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365461).length < 2 ^ (prefixWord ++ tailWord_8365461).sum := by decide
  have hdescent : baseEnd_8365461 < baseStart_8365461 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365468 : List Nat := [2, 2, 3, 4, 1, 2, 9]
def baseStart_8365468 : Nat := 118140960795 + 8365468 * 2 ^ 59
def prefixEnd_8365468 : Nat := 4983230072969 + 3 ^ 40 * 8365468 * 2
def baseEnd_8365468 : Nat := 53030938071681250637999

theorem tailTrace_8365468 : CollatzResearch.WordTrace tailWord_8365468 prefixEnd_8365468 53030938071681250637999 := by
  unfold tailWord_8365468
  simp only [CollatzResearch.WordTrace]
  refine ⟨152556842028672809517120529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203409122704897079356160705 152556842028672809517120529)
  ·
    refine ⟨114417631521504607137840397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152556842028672809517120529 114417631521504607137840397)
    ·
      refine ⟨42906611820564227676690149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114417631521504607137840397 42906611820564227676690149)
      ·
        refine ⟨8044989716355792689379403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42906611820564227676690149 8044989716355792689379403)
        ·
          refine ⟨12067484574533689034069105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8044989716355792689379403 12067484574533689034069105)
          ·
            refine ⟨9050613430900266775551829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12067484574533689034069105 9050613430900266775551829)
            ·
              refine ⟨53030938071681250637999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 9050613430900266775551829 53030938071681250637999)
              ·
                rfl

theorem cell23_8365468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 9].length) (baseStart_8365468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365468 prefixEnd_8365468 := by exact prefixLift 8365468
  have htrace : WordTrace (prefixWord ++ tailWord_8365468) baseStart_8365468 baseEnd_8365468 := by
    simpa [prefixWord, tailWord_8365468, baseEnd_8365468] using wordTrace_append hprefix tailTrace_8365468
  have hstable : (prefixWord ++ tailWord_8365468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365468).length < 2 ^ (prefixWord ++ tailWord_8365468).sum := by decide
  have hdescent : baseEnd_8365468 < baseStart_8365468 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365479 : List Nat := [1, 1, 6, 1, 1, 1, 5, 2, 1, 2, 2]
def baseStart_8365479 : Nat := 118140960795 + 8365479 * 2 ^ 59
def prefixEnd_8365479 : Nat := 4983230072969 + 3 ^ 40 * 8365479 * 2
def baseEnd_8365479 : Nat := 4295511632093380758640369

theorem tailTrace_8365479 : CollatzResearch.WordTrace tailWord_8365479 prefixEnd_8365479 4295511632093380758640369 := by
  unfold tailWord_8365479
  simp only [CollatzResearch.WordTrace]
  refine ⟨305114085260305767912891491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203409390173537178608594327 305114085260305767912891491)
  ·
    refine ⟨457671127890458651869337237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305114085260305767912891491 457671127890458651869337237)
    ·
      refine ⟨21453334119865249306375183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 457671127890458651869337237 21453334119865249306375183)
      ·
        refine ⟨32180001179797873959562775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21453334119865249306375183 32180001179797873959562775)
        ·
          refine ⟨48270001769696810939344163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32180001179797873959562775 48270001769696810939344163)
          ·
            refine ⟨72405002654545216409016245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48270001769696810939344163 72405002654545216409016245)
            ·
              refine ⟨6787968998863614038345273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72405002654545216409016245 6787968998863614038345273)
              ·
                refine ⟨5090976749147710528758955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6787968998863614038345273 5090976749147710528758955)
                ·
                  refine ⟨7636465123721565793138433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5090976749147710528758955 7636465123721565793138433)
                  ·
                    refine ⟨5727348842791174344853825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7636465123721565793138433 5727348842791174344853825)
                    ·
                      refine ⟨4295511632093380758640369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5727348842791174344853825 4295511632093380758640369)
                      ·
                        rfl

theorem cell23_8365479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_8365479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365479 prefixEnd_8365479 := by exact prefixLift 8365479
  have htrace : WordTrace (prefixWord ++ tailWord_8365479) baseStart_8365479 baseEnd_8365479 := by
    simpa [prefixWord, tailWord_8365479, baseEnd_8365479] using wordTrace_append hprefix tailTrace_8365479
  have hstable : (prefixWord ++ tailWord_8365479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365479).length < 2 ^ (prefixWord ++ tailWord_8365479).sum := by decide
  have hdescent : baseEnd_8365479 < baseStart_8365479 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365518 : List Nat := [4, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2]
def baseStart_8365518 : Nat := 118140960795 + 8365518 * 2 ^ 59
def prefixEnd_8365518 : Nat := 4983230072969 + 3 ^ 40 * 8365518 * 2
def baseEnd_8365518 : Nat := 4295531657838906106052689

theorem tailTrace_8365518 : CollatzResearch.WordTrace tailWord_8365518 prefixEnd_8365518 4295531657838906106052689 := by
  unfold tailWord_8365518
  simp only [CollatzResearch.WordTrace]
  refine ⟨38139438463395559696695151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203410338471442985049040805 38139438463395559696695151)
  ·
    refine ⟨57209157695093339545042727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38139438463395559696695151 57209157695093339545042727)
    ·
      refine ⟨85813736542640009317564091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57209157695093339545042727 85813736542640009317564091)
      ·
        refine ⟨128720604813960013976346137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85813736542640009317564091 128720604813960013976346137)
        ·
          refine ⟨96540453610470010482259603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128720604813960013976346137 96540453610470010482259603)
          ·
            refine ⟨144810680415705015723389405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96540453610470010482259603 144810680415705015723389405)
            ·
              refine ⟨54304005155889380896271027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144810680415705015723389405 54304005155889380896271027)
              ·
                refine ⟨81456007733834071344406541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54304005155889380896271027 81456007733834071344406541)
                ·
                  refine ⟨30546002900187776754152453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81456007733834071344406541 30546002900187776754152453)
                  ·
                    refine ⟨5727375543785208141403585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30546002900187776754152453 5727375543785208141403585)
                    ·
                      refine ⟨4295531657838906106052689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5727375543785208141403585 4295531657838906106052689)
                      ·
                        rfl

theorem cell23_8365518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2].length) (baseStart_8365518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365518 prefixEnd_8365518 := by exact prefixLift 8365518
  have htrace : WordTrace (prefixWord ++ tailWord_8365518) baseStart_8365518 baseEnd_8365518 := by
    simpa [prefixWord, tailWord_8365518, baseEnd_8365518] using wordTrace_append hprefix tailTrace_8365518
  have hstable : (prefixWord ++ tailWord_8365518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365518).length < 2 ^ (prefixWord ++ tailWord_8365518).sum := by decide
  have hdescent : baseEnd_8365518 < baseStart_8365518 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365551 : List Nat := [1, 1, 2, 1, 4, 1, 3, 1, 1, 5, 3]
def baseStart_8365551 : Nat := 118140960795 + 8365551 * 2 ^ 59
def prefixEnd_8365551 : Nat := 4983230072969 + 3 ^ 40 * 8365551 * 2
def baseEnd_8365551 : Nat := 4295548602700504476940037

theorem tailTrace_8365551 : CollatzResearch.WordTrace tailWord_8365551 prefixEnd_8365551 4295548602700504476940037 := by
  unfold tailWord_8365551
  simp only [CollatzResearch.WordTrace]
  refine ⟨305116711316044924209512507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203411140877363282806341671 305116711316044924209512507)
  ·
    refine ⟨457675066974067386314268761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305116711316044924209512507 457675066974067386314268761)
    ·
      refine ⟨343256300230550539735701571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457675066974067386314268761 343256300230550539735701571)
      ·
        refine ⟨514884450345825809603552357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343256300230550539735701571 514884450345825809603552357)
        ·
          refine ⟨96540834439842339300666067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 514884450345825809603552357 96540834439842339300666067)
          ·
            refine ⟨144811251659763508950999101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96540834439842339300666067 144811251659763508950999101)
            ·
              refine ⟨54304219372411315856624663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144811251659763508950999101 54304219372411315856624663)
              ·
                refine ⟨81456329058616973784936995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54304219372411315856624663 81456329058616973784936995)
                ·
                  refine ⟨122184493587925460677405493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81456329058616973784936995 122184493587925460677405493)
                  ·
                    refine ⟨11454796273868011938506765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 122184493587925460677405493 11454796273868011938506765)
                    ·
                      refine ⟨4295548602700504476940037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11454796273868011938506765 4295548602700504476940037)
                      ·
                        rfl

theorem cell23_8365551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 5, 3].length) (baseStart_8365551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365551 prefixEnd_8365551 := by exact prefixLift 8365551
  have htrace : WordTrace (prefixWord ++ tailWord_8365551) baseStart_8365551 baseEnd_8365551 := by
    simpa [prefixWord, tailWord_8365551, baseEnd_8365551] using wordTrace_append hprefix tailTrace_8365551
  have hstable : (prefixWord ++ tailWord_8365551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365551).length < 2 ^ (prefixWord ++ tailWord_8365551).sum := by decide
  have hdescent : baseEnd_8365551 < baseStart_8365551 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365558 : List Nat := [5, 1, 1, 1, 2, 3, 1, 2, 7]
def baseStart_8365558 : Nat := 118140960795 + 8365558 * 2 ^ 59
def prefixEnd_8365558 : Nat := 4983230072969 + 3 ^ 40 * 8365558 * 2
def baseEnd_8365558 : Nat := 477283577451676216616945

theorem tailTrace_8365558 : CollatzResearch.WordTrace tailWord_8365558 prefixEnd_8365558 477283577451676216616945 := by
  unfold tailWord_8365558
  simp only [CollatzResearch.WordTrace]
  refine ⟨19069810414188722775313583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203411311084679709603344885 19069810414188722775313583)
  ·
    refine ⟨28604715621283084162970375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19069810414188722775313583 28604715621283084162970375)
    ·
      refine ⟨42907073431924626244455563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28604715621283084162970375 42907073431924626244455563)
      ·
        refine ⟨64360610147886939366683345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42907073431924626244455563 64360610147886939366683345)
        ·
          refine ⟨48270457610915204525012509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64360610147886939366683345 48270457610915204525012509)
          ·
            refine ⟨18101421604093201696879691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48270457610915204525012509 18101421604093201696879691)
            ·
              refine ⟨27152132406139802545319537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18101421604093201696879691 27152132406139802545319537)
              ·
                refine ⟨20364099304604851908989653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27152132406139802545319537 20364099304604851908989653)
                ·
                  refine ⟨477283577451676216616945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20364099304604851908989653 477283577451676216616945)
                  ·
                    rfl

theorem cell23_8365558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_8365558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365558 prefixEnd_8365558 := by exact prefixLift 8365558
  have htrace : WordTrace (prefixWord ++ tailWord_8365558) baseStart_8365558 baseEnd_8365558 := by
    simpa [prefixWord, tailWord_8365558, baseEnd_8365558] using wordTrace_append hprefix tailTrace_8365558
  have hstable : (prefixWord ++ tailWord_8365558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365558).length < 2 ^ (prefixWord ++ tailWord_8365558).sum := by decide
  have hdescent : baseEnd_8365558 < baseStart_8365558 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365571 : List Nat := [1, 1, 1, 3, 2, 1, 2, 5, 2, 5]
def baseStart_8365571 : Nat := 118140960795 + 8365571 * 2 ^ 59
def prefixEnd_8365571 : Nat := 4983230072969 + 3 ^ 40 * 8365571 * 2
def baseEnd_8365571 : Nat := 1431852957437864799563315

theorem tailTrace_8365571 : CollatzResearch.WordTrace tailWord_8365571 prefixEnd_8365571 1431852957437864799563315 := by
  unfold tailWord_8365571
  simp only [CollatzResearch.WordTrace]
  refine ⟨305117440775972467625240567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203411627183981645083493711 305117440775972467625240567)
  ·
    refine ⟨457676161163958701437860851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305117440775972467625240567 457676161163958701437860851)
    ·
      refine ⟨686514241745938052156791277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457676161163958701437860851 686514241745938052156791277)
      ·
        refine ⟨257442840654726769558796729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 686514241745938052156791277 257442840654726769558796729)
        ·
          refine ⟨193082130491045077169097547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257442840654726769558796729 193082130491045077169097547)
          ·
            refine ⟨289623195736567615753646321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193082130491045077169097547 289623195736567615753646321)
            ·
              refine ⟨217217396802425711815234741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289623195736567615753646321 217217396802425711815234741)
              ·
                refine ⟨20364130950227410482678257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 217217396802425711815234741 20364130950227410482678257)
                ·
                  refine ⟨15273098212670557862008693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20364130950227410482678257 15273098212670557862008693)
                  ·
                    refine ⟨1431852957437864799563315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15273098212670557862008693 1431852957437864799563315)
                    ·
                      rfl

theorem cell23_8365571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 5].length) (baseStart_8365571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365571 prefixEnd_8365571 := by exact prefixLift 8365571
  have htrace : WordTrace (prefixWord ++ tailWord_8365571) baseStart_8365571 baseEnd_8365571 := by
    simpa [prefixWord, tailWord_8365571, baseEnd_8365571] using wordTrace_append hprefix tailTrace_8365571
  have hstable : (prefixWord ++ tailWord_8365571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365571).length < 2 ^ (prefixWord ++ tailWord_8365571).sum := by decide
  have hdescent : baseEnd_8365571 < baseStart_8365571 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365575 : List Nat := [1, 1, 4, 3, 2, 2, 2, 3, 5]
def baseStart_8365575 : Nat := 118140960795 + 8365575 * 2 ^ 59
def prefixEnd_8365575 : Nat := 4983230072969 + 3 ^ 40 * 8365575 * 2
def baseEnd_8365575 : Nat := 477284547359579153671103

theorem tailTrace_8365575 : CollatzResearch.WordTrace tailWord_8365575 prefixEnd_8365575 477284547359579153671103 := by
  unfold tailWord_8365575
  simp only [CollatzResearch.WordTrace]
  refine ⟨305117586667957976308386179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203411724445305317538924119 305117586667957976308386179)
  ·
    refine ⟨457676380001936964462579269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305117586667957976308386179 457676380001936964462579269)
    ·
      refine ⟨85814321250363180836733613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 457676380001936964462579269 85814321250363180836733613)
      ·
        refine ⟨32180370468886192813775105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85814321250363180836733613 32180370468886192813775105)
        ·
          refine ⟨24135277851664644610331329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32180370468886192813775105 24135277851664644610331329)
          ·
            refine ⟨18101458388748483457748497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24135277851664644610331329 18101458388748483457748497)
            ·
              refine ⟨13576093791561362593311373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18101458388748483457748497 13576093791561362593311373)
              ·
                refine ⟨5091035171835510972491765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13576093791561362593311373 5091035171835510972491765)
                ·
                  refine ⟨477284547359579153671103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5091035171835510972491765 477284547359579153671103)
                  ·
                    rfl

theorem cell23_8365575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 3, 5].length) (baseStart_8365575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365575 prefixEnd_8365575 := by exact prefixLift 8365575
  have htrace : WordTrace (prefixWord ++ tailWord_8365575) baseStart_8365575 baseEnd_8365575 := by
    simpa [prefixWord, tailWord_8365575, baseEnd_8365575] using wordTrace_append hprefix tailTrace_8365575
  have hstable : (prefixWord ++ tailWord_8365575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365575).length < 2 ^ (prefixWord ++ tailWord_8365575).sum := by decide
  have hdescent : baseEnd_8365575 < baseStart_8365575 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365631 : List Nat := [1, 1, 2, 2, 3, 3, 1, 2, 8]
def baseStart_8365631 : Nat := 118140960795 + 8365631 * 2 ^ 59
def prefixEnd_8365631 : Nat := 4983230072969 + 3 ^ 40 * 8365631 * 2
def baseEnd_8365631 : Nat := 477287742350318240437741

theorem tailTrace_8365631 : CollatzResearch.WordTrace tailWord_8365631 prefixEnd_8365631 477287742350318240437741 := by
  unfold tailWord_8365631
  simp only [CollatzResearch.WordTrace]
  refine ⟨305119629155755097872424747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203413086103836731914949831 305119629155755097872424747)
  ·
    refine ⟨457679443733632646808637121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305119629155755097872424747 457679443733632646808637121)
    ·
      refine ⟨343259582800224485106477841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457679443733632646808637121 343259582800224485106477841)
      ·
        refine ⟨257444687100168363829858381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343259582800224485106477841 257444687100168363829858381)
        ·
          refine ⟨96541757662563136436196893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257444687100168363829858381 96541757662563136436196893)
          ·
            refine ⟨36203159123461176163573835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96541757662563136436196893 36203159123461176163573835)
            ·
              refine ⟨54304738685191764245360753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36203159123461176163573835 54304738685191764245360753)
              ·
                refine ⟨40728554013893823184020565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54304738685191764245360753 40728554013893823184020565)
                ·
                  refine ⟨477287742350318240437741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40728554013893823184020565 477287742350318240437741)
                  ·
                    rfl

theorem cell23_8365631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 8].length) (baseStart_8365631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365631 prefixEnd_8365631 := by exact prefixLift 8365631
  have htrace : WordTrace (prefixWord ++ tailWord_8365631) baseStart_8365631 baseEnd_8365631 := by
    simpa [prefixWord, tailWord_8365631, baseEnd_8365631] using wordTrace_append hprefix tailTrace_8365631
  have hstable : (prefixWord ++ tailWord_8365631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365631).length < 2 ^ (prefixWord ++ tailWord_8365631).sum := by decide
  have hdescent : baseEnd_8365631 < baseStart_8365631 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365692 : List Nat := [2, 2, 2, 1, 1, 2, 1, 7, 1, 1, 3]
def baseStart_8365692 : Nat := 118140960795 + 8365692 * 2 ^ 59
def prefixEnd_8365692 : Nat := 4983230072969 + 3 ^ 40 * 8365692 * 2
def baseEnd_8365692 : Nat := 4295621003472788425276889

theorem tailTrace_8365692 : CollatzResearch.WordTrace tailWord_8365692 prefixEnd_8365692 4295621003472788425276889 := by
  unfold tailWord_8365692
  simp only [CollatzResearch.WordTrace]
  refine ⟨152560927004267052645197665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203414569339022736860263553 152560927004267052645197665)
  ·
    refine ⟨114420695253200289483898249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152560927004267052645197665 114420695253200289483898249)
    ·
      refine ⟨85815521439900217112923687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114420695253200289483898249 85815521439900217112923687)
      ·
        refine ⟨128723282159850325669385531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85815521439900217112923687 128723282159850325669385531)
        ·
          refine ⟨193084923239775488504078297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128723282159850325669385531 193084923239775488504078297)
          ·
            refine ⟨144813692429831616378058723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193084923239775488504078297 144813692429831616378058723)
            ·
              refine ⟨217220538644747424567088085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144813692429831616378058723 217220538644747424567088085)
              ·
                refine ⟨5091106374486267763291127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 217220538644747424567088085 5091106374486267763291127)
                ·
                  refine ⟨7636659561729401644936691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5091106374486267763291127 7636659561729401644936691)
                  ·
                    refine ⟨11454989342594102467405037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7636659561729401644936691 11454989342594102467405037)
                    ·
                      refine ⟨4295621003472788425276889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11454989342594102467405037 4295621003472788425276889)
                      ·
                        rfl

theorem cell23_8365692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 7, 1, 1, 3].length) (baseStart_8365692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365692 prefixEnd_8365692 := by exact prefixLift 8365692
  have htrace : WordTrace (prefixWord ++ tailWord_8365692) baseStart_8365692 baseEnd_8365692 := by
    simpa [prefixWord, tailWord_8365692, baseEnd_8365692] using wordTrace_append hprefix tailTrace_8365692
  have hstable : (prefixWord ++ tailWord_8365692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365692).length < 2 ^ (prefixWord ++ tailWord_8365692).sum := by decide
  have hdescent : baseEnd_8365692 < baseStart_8365692 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365721 : List Nat := [1, 2, 1, 2, 1, 2, 2, 12]
def baseStart_8365721 : Nat := 118140960795 + 8365721 * 2 ^ 59
def prefixEnd_8365721 : Nat := 4983230072969 + 3 ^ 40 * 8365721 * 2
def baseEnd_8365721 : Nat := 159097625718954400437565

theorem tailTrace_8365721 : CollatzResearch.WordTrace tailWord_8365721 prefixEnd_8365721 159097625718954400437565 := by
  unfold tailWord_8365721
  simp only [CollatzResearch.WordTrace]
  refine ⟨305122911725429043243201017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203415274483619362162134011 305122911725429043243201017)
  ·
    refine ⟨228842183794071782432400763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305122911725429043243201017 228842183794071782432400763)
    ·
      refine ⟨343263275691107673648601145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228842183794071782432400763 343263275691107673648601145)
      ·
        refine ⟨257447456768330755236450859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343263275691107673648601145 257447456768330755236450859)
        ·
          refine ⟨386171185152496132854676289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257447456768330755236450859 386171185152496132854676289)
          ·
            refine ⟨289628388864372099641007217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386171185152496132854676289 289628388864372099641007217)
            ·
              refine ⟨217221291648279074730755413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289628388864372099641007217 217221291648279074730755413)
              ·
                refine ⟨159097625718954400437565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 217221291648279074730755413 159097625718954400437565)
                ·
                  rfl

theorem cell23_8365721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 12].length) (baseStart_8365721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365721 prefixEnd_8365721 := by exact prefixLift 8365721
  have htrace : WordTrace (prefixWord ++ tailWord_8365721) baseStart_8365721 baseEnd_8365721 := by
    simpa [prefixWord, tailWord_8365721, baseEnd_8365721] using wordTrace_append hprefix tailTrace_8365721
  have hstable : (prefixWord ++ tailWord_8365721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365721).length < 2 ^ (prefixWord ++ tailWord_8365721).sum := by decide
  have hdescent : baseEnd_8365721 < baseStart_8365721 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365732 : List Nat := [2, 3, 1, 2, 2, 2, 1, 1, 5, 2, 2]
def baseStart_8365732 : Nat := 118140960795 + 8365732 * 2 ^ 59
def prefixEnd_8365732 : Nat := 4983230072969 + 3 ^ 40 * 8365732 * 2
def baseEnd_8365732 : Nat := 4295641542698968268776705

theorem tailTrace_8365732 : CollatzResearch.WordTrace tailWord_8365732 prefixEnd_8365732 4295641542698968268776705 := by
  unfold tailWord_8365732
  simp only [CollatzResearch.WordTrace]
  refine ⟨152561656464194596060925725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203415541952259461414567633 152561656464194596060925725)
  ·
    refine ⟨57210621174072973522847147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152561656464194596060925725 57210621174072973522847147)
    ·
      refine ⟨85815931761109460284270721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57210621174072973522847147 85815931761109460284270721)
      ·
        refine ⟨64361948820832095213203041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85815931761109460284270721 64361948820832095213203041)
        ·
          refine ⟨48271461615624071409902281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64361948820832095213203041 48271461615624071409902281)
          ·
            refine ⟨36203596211718053557426711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48271461615624071409902281 36203596211718053557426711)
            ·
              refine ⟨54305394317577080336140067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36203596211718053557426711 54305394317577080336140067)
              ·
                refine ⟨81458091476365620504210101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54305394317577080336140067 81458091476365620504210101)
                ·
                  refine ⟨7636696075909276922269697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81458091476365620504210101 7636696075909276922269697)
                  ·
                    refine ⟨5727522056931957691702273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7636696075909276922269697 5727522056931957691702273)
                    ·
                      refine ⟨4295641542698968268776705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5727522056931957691702273 4295641542698968268776705)
                      ·
                        rfl

theorem cell23_8365732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_8365732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365732 prefixEnd_8365732 := by exact prefixLift 8365732
  have htrace : WordTrace (prefixWord ++ tailWord_8365732) baseStart_8365732 baseEnd_8365732 := by
    simpa [prefixWord, tailWord_8365732, baseEnd_8365732] using wordTrace_append hprefix tailTrace_8365732
  have hstable : (prefixWord ++ tailWord_8365732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365732).length < 2 ^ (prefixWord ++ tailWord_8365732).sum := by decide
  have hdescent : baseEnd_8365732 < baseStart_8365732 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365736 : List Nat := [2, 1, 7, 1, 1, 1, 1, 1, 1, 5, 2]
def baseStart_8365736 : Nat := 118140960795 + 8365736 * 2 ^ 59
def prefixEnd_8365736 : Nat := 4983230072969 + 3 ^ 40 * 8365736 * 2
def baseEnd_8365736 : Nat := 4295643596621586253126687

theorem tailTrace_8365736 : CollatzResearch.WordTrace tailWord_8365736 prefixEnd_8365736 4295643596621586253126687 := by
  unfold tailWord_8365736
  simp only [CollatzResearch.WordTrace]
  refine ⟨152561729410187350402498531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203415639213583133869998041 152561729410187350402498531)
  ·
    refine ⟨228842594115281025603747797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152561729410187350402498531 228842594115281025603747797)
    ·
      refine ⟨5363498299576899037587839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 228842594115281025603747797 5363498299576899037587839)
      ·
        refine ⟨8045247449365348556381759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5363498299576899037587839 8045247449365348556381759)
        ·
          refine ⟨12067871174048022834572639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8045247449365348556381759 12067871174048022834572639)
          ·
            refine ⟨18101806761072034251858959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12067871174048022834572639 18101806761072034251858959)
            ·
              refine ⟨27152710141608051377788439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18101806761072034251858959 27152710141608051377788439)
              ·
                refine ⟨40729065212412077066682659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27152710141608051377788439 40729065212412077066682659)
                ·
                  refine ⟨61093597818618115600023989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40729065212412077066682659 61093597818618115600023989)
                  ·
                    refine ⟨5727524795495448337502249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61093597818618115600023989 5727524795495448337502249)
                    ·
                      refine ⟨4295643596621586253126687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5727524795495448337502249 4295643596621586253126687)
                      ·
                        rfl

theorem cell23_8365736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_8365736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365736 prefixEnd_8365736 := by exact prefixLift 8365736
  have htrace : WordTrace (prefixWord ++ tailWord_8365736) baseStart_8365736 baseEnd_8365736 := by
    simpa [prefixWord, tailWord_8365736, baseEnd_8365736] using wordTrace_append hprefix tailTrace_8365736
  have hstable : (prefixWord ++ tailWord_8365736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365736).length < 2 ^ (prefixWord ++ tailWord_8365736).sum := by decide
  have hdescent : baseEnd_8365736 < baseStart_8365736 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365765 : List Nat := [1, 3, 1, 1, 1, 1, 2, 5, 4, 1, 3]
def baseStart_8365765 : Nat := 118140960795 + 8365765 * 2 ^ 59
def prefixEnd_8365765 : Nat := 4983230072969 + 3 ^ 40 * 8365765 * 2
def baseEnd_8365765 : Nat := 4295658487560566639664053

theorem tailTrace_8365765 : CollatzResearch.WordTrace tailWord_8365765 prefixEnd_8365765 4295658487560566639664053 := by
  unfold tailWord_8365765
  simp only [CollatzResearch.WordTrace]
  refine ⟨305124516537269638757802749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203416344358179759171868499 305124516537269638757802749)
  ·
    refine ⟨114421693701476114534176031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305124516537269638757802749 114421693701476114534176031)
    ·
      refine ⟨171632540552214171801264047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114421693701476114534176031 171632540552214171801264047)
      ·
        refine ⟨257448810828321257701896071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171632540552214171801264047 257448810828321257701896071)
        ·
          refine ⟨386173216242481886552844107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257448810828321257701896071 386173216242481886552844107)
          ·
            refine ⟨579259824363722829829266161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386173216242481886552844107 579259824363722829829266161)
            ·
              refine ⟨434444868272792122371949621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 579259824363722829829266161 434444868272792122371949621)
              ·
                refine ⟨40729206400574261472370277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 434444868272792122371949621 40729206400574261472370277)
                ·
                  refine ⟨7636726200107674026069427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40729206400574261472370277 7636726200107674026069427)
                  ·
                    refine ⟨11455089300161511039104141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7636726200107674026069427 11455089300161511039104141)
                    ·
                      refine ⟨4295658487560566639664053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11455089300161511039104141 4295658487560566639664053)
                      ·
                        rfl

theorem cell23_8365765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 4, 1, 3].length) (baseStart_8365765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365765 prefixEnd_8365765 := by exact prefixLift 8365765
  have htrace : WordTrace (prefixWord ++ tailWord_8365765) baseStart_8365765 baseEnd_8365765 := by
    simpa [prefixWord, tailWord_8365765, baseEnd_8365765] using wordTrace_append hprefix tailTrace_8365765
  have hstable : (prefixWord ++ tailWord_8365765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365765).length < 2 ^ (prefixWord ++ tailWord_8365765).sum := by decide
  have hdescent : baseEnd_8365765 < baseStart_8365765 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365775 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 5, 3, 2]
def baseStart_8365775 : Nat := 118140960795 + 8365775 * 2 ^ 59
def prefixEnd_8365775 : Nat := 4983230072969 + 3 ^ 40 * 8365775 * 2
def baseEnd_8365775 : Nat := 4295663622367111600539007

theorem tailTrace_8365775 : CollatzResearch.WordTrace tailWord_8365775 prefixEnd_8365775 4295663622367111600539007 := by
  unfold tailWord_8365775
  simp only [CollatzResearch.WordTrace]
  refine ⟨305124881267233410465666779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203416587511488940310444519 305124881267233410465666779)
  ·
    refine ⟨457687321900850115698500169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305124881267233410465666779 457687321900850115698500169)
    ·
      refine ⟨343265491425637586773875127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457687321900850115698500169 343265491425637586773875127)
      ·
        refine ⟨514898237138456380160812691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343265491425637586773875127 514898237138456380160812691)
        ·
          refine ⟨772347355707684570241219037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514898237138456380160812691 772347355707684570241219037)
          ·
            refine ⟨289630258390381713840457139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 772347355707684570241219037 289630258390381713840457139)
            ·
              refine ⟨434445387585572570760685709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289630258390381713840457139 434445387585572570760685709)
              ·
                refine ⟨162917020344589714035257141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 434445387585572570760685709 162917020344589714035257141)
                ·
                  refine ⟨15273470657305285690805357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 162917020344589714035257141 15273470657305285690805357)
                  ·
                    refine ⟨5727551496489482134052009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15273470657305285690805357 5727551496489482134052009)
                    ·
                      refine ⟨4295663622367111600539007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5727551496489482134052009 4295663622367111600539007)
                      ·
                        rfl

theorem cell23_8365775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 3, 2].length) (baseStart_8365775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365775 prefixEnd_8365775 := by exact prefixLift 8365775
  have htrace : WordTrace (prefixWord ++ tailWord_8365775) baseStart_8365775 baseEnd_8365775 := by
    simpa [prefixWord, tailWord_8365775, baseEnd_8365775] using wordTrace_append hprefix tailTrace_8365775
  have hstable : (prefixWord ++ tailWord_8365775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365775).length < 2 ^ (prefixWord ++ tailWord_8365775).sum := by decide
  have hdescent : baseEnd_8365775 < baseStart_8365775 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365789 : List Nat := [1, 4, 3, 3, 1, 2, 2, 7]
def baseStart_8365789 : Nat := 118140960795 + 8365789 * 2 ^ 59
def prefixEnd_8365789 : Nat := 4983230072969 + 3 ^ 40 * 8365789 * 2
def baseEnd_8365789 : Nat := 159098918929491649843109

theorem tailTrace_8365789 : CollatzResearch.WordTrace tailWord_8365789 prefixEnd_8365789 159098918929491649843109 := by
  unfold tailWord_8365789
  simp only [CollatzResearch.WordTrace]
  refine ⟨305125391889182690856676421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203416927926121793904450947 305125391889182690856676421)
  ·
    refine ⟨57211010979221754535626829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305125391889182690856676421 57211010979221754535626829)
    ·
      refine ⟨21454129117208157950860061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57211010979221754535626829 21454129117208157950860061)
      ·
        refine ⟨8045298418953059231572523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21454129117208157950860061 8045298418953059231572523)
        ·
          refine ⟨12067947628429588847358785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8045298418953059231572523 12067947628429588847358785)
          ·
            refine ⟨9050960721322191635519089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12067947628429588847358785 9050960721322191635519089)
            ·
              refine ⟨6788220540991643726639317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9050960721322191635519089 6788220540991643726639317)
              ·
                refine ⟨159098918929491649843109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6788220540991643726639317 159098918929491649843109)
                ·
                  rfl

theorem cell23_8365789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 7].length) (baseStart_8365789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365789 prefixEnd_8365789 := by exact prefixLift 8365789
  have htrace : WordTrace (prefixWord ++ tailWord_8365789) baseStart_8365789 baseEnd_8365789 := by
    simpa [prefixWord, tailWord_8365789, baseEnd_8365789] using wordTrace_append hprefix tailTrace_8365789
  have hstable : (prefixWord ++ tailWord_8365789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365789).length < 2 ^ (prefixWord ++ tailWord_8365789).sum := by decide
  have hdescent : baseEnd_8365789 < baseStart_8365789 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365792 : List Nat := [2, 1, 1, 3, 1, 2, 3, 4, 1, 3, 2]
def baseStart_8365792 : Nat := 118140960795 + 8365792 * 2 ^ 59
def prefixEnd_8365792 : Nat := 4983230072969 + 3 ^ 40 * 8365792 * 2
def baseEnd_8365792 : Nat := 4295672351538238034026429

theorem tailTrace_8365792 : CollatzResearch.WordTrace tailWord_8365792 prefixEnd_8365792 4295672351538238034026429 := by
  unfold tailWord_8365792
  simp only [CollatzResearch.WordTrace]
  refine ⟨152562750654085911184517815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203417000872114548246023753 152562750654085911184517815)
  ·
    refine ⟨228844125981128866776776723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152562750654085911184517815 228844125981128866776776723)
    ·
      refine ⟨343266188971693300165165085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228844125981128866776776723 343266188971693300165165085)
      ·
        refine ⟨128724820864384987561936907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343266188971693300165165085 128724820864384987561936907)
        ·
          refine ⟨193087231296577481342905361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128724820864384987561936907 193087231296577481342905361)
          ·
            refine ⟨144815423472433111007179021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193087231296577481342905361 144815423472433111007179021)
            ·
              refine ⟨54305783802162416627692133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144815423472433111007179021 54305783802162416627692133)
              ·
                refine ⟨10182334462905453117692275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54305783802162416627692133 10182334462905453117692275)
                ·
                  refine ⟨15273501694358179676538413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10182334462905453117692275 15273501694358179676538413)
                  ·
                    refine ⟨5727563135384317378701905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15273501694358179676538413 5727563135384317378701905)
                    ·
                      refine ⟨4295672351538238034026429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5727563135384317378701905 4295672351538238034026429)
                      ·
                        rfl

theorem cell23_8365792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 1, 3, 2].length) (baseStart_8365792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365792 prefixEnd_8365792 := by exact prefixLift 8365792
  have htrace : WordTrace (prefixWord ++ tailWord_8365792) baseStart_8365792 baseEnd_8365792 := by
    simpa [prefixWord, tailWord_8365792, baseEnd_8365792] using wordTrace_append hprefix tailTrace_8365792
  have hstable : (prefixWord ++ tailWord_8365792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365792).length < 2 ^ (prefixWord ++ tailWord_8365792).sum := by decide
  have hdescent : baseEnd_8365792 < baseStart_8365792 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365837 : List Nat := [1, 7, 2, 1, 2, 1, 1, 2, 1, 2, 3]
def baseStart_8365837 : Nat := 118140960795 + 8365837 * 2 ^ 59
def prefixEnd_8365837 : Nat := 4983230072969 + 3 ^ 40 * 8365837 * 2
def baseEnd_8365837 : Nat := 4295695458167690357963723

theorem tailTrace_8365837 : CollatzResearch.WordTrace tailWord_8365837 prefixEnd_8365837 4295695458167690357963723 := by
  unfold tailWord_8365837
  simp only [CollatzResearch.WordTrace]
  refine ⟨305127142593008795054423765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203418095062005863369615843 305127142593008795054423765)
  ·
    refine ⟨7151417404523643634088057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 305127142593008795054423765 7151417404523643634088057)
    ·
      refine ⟨5363563053392732725566043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7151417404523643634088057 5363563053392732725566043)
      ·
        refine ⟨8045344580089099088349065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5363563053392732725566043 8045344580089099088349065)
        ·
          refine ⟨6034008435066824316261799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8045344580089099088349065 6034008435066824316261799)
          ·
            refine ⟨9051012652600236474392699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6034008435066824316261799 9051012652600236474392699)
            ·
              refine ⟨13576518978900354711589049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9051012652600236474392699 13576518978900354711589049)
              ·
                refine ⟨10182389234175266033691787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13576518978900354711589049 10182389234175266033691787)
                ·
                  refine ⟨15273583851262899050537681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10182389234175266033691787 15273583851262899050537681)
                  ·
                    refine ⟨11455187888447174287903261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15273583851262899050537681 11455187888447174287903261)
                    ·
                      refine ⟨4295695458167690357963723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11455187888447174287903261 4295695458167690357963723)
                      ·
                        rfl

theorem cell23_8365837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_8365837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365837 prefixEnd_8365837 := by exact prefixLift 8365837
  have htrace : WordTrace (prefixWord ++ tailWord_8365837) baseStart_8365837 baseEnd_8365837 := by
    simpa [prefixWord, tailWord_8365837, baseEnd_8365837] using wordTrace_append hprefix tailTrace_8365837
  have hstable : (prefixWord ++ tailWord_8365837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365837).length < 2 ^ (prefixWord ++ tailWord_8365837).sum := by decide
  have hdescent : baseEnd_8365837 < baseStart_8365837 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365842 : List Nat := [3, 2, 4, 1, 1, 1, 1, 2, 2, 1, 5]
def baseStart_8365842 : Nat := 118140960795 + 8365842 * 2 ^ 59
def prefixEnd_8365842 : Nat := 4983230072969 + 3 ^ 40 * 8365842 * 2
def baseEnd_8365842 : Nat := 4295698025570962838401199

theorem tailTrace_8365842 : CollatzResearch.WordTrace tailWord_8365842 prefixEnd_8365842 4295698025570962838401199 := by
  unfold tailWord_8365842
  simp only [CollatzResearch.WordTrace]
  refine ⟨76281831239497670227088945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203418216638660453938903853 76281831239497670227088945)
  ·
    refine ⟨57211373429623252670316709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76281831239497670227088945 57211373429623252670316709)
    ·
      refine ⟨10727132518054359875684383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57211373429623252670316709 10727132518054359875684383)
      ·
        refine ⟨16090698777081539813526575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10727132518054359875684383 16090698777081539813526575)
        ·
          refine ⟨24136048165622309720289863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16090698777081539813526575 24136048165622309720289863)
          ·
            refine ⟨36204072248433464580434795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24136048165622309720289863 36204072248433464580434795)
            ·
              refine ⟨54306108372650196870652193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36204072248433464580434795 54306108372650196870652193)
              ·
                refine ⟨40729581279487647652989145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54306108372650196870652193 40729581279487647652989145)
                ·
                  refine ⟨30547185959615735739741859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40729581279487647652989145 30547185959615735739741859)
                  ·
                    refine ⟨45820778939423603609612789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30547185959615735739741859 45820778939423603609612789)
                    ·
                      refine ⟨4295698025570962838401199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45820778939423603609612789 4295698025570962838401199)
                      ·
                        rfl

theorem cell23_8365842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_8365842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365842 prefixEnd_8365842 := by exact prefixLift 8365842
  have htrace : WordTrace (prefixWord ++ tailWord_8365842) baseStart_8365842 baseEnd_8365842 := by
    simpa [prefixWord, tailWord_8365842, baseEnd_8365842] using wordTrace_append hprefix tailTrace_8365842
  have hstable : (prefixWord ++ tailWord_8365842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365842).length < 2 ^ (prefixWord ++ tailWord_8365842).sum := by decide
  have hdescent : baseEnd_8365842 < baseStart_8365842 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365865 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 3, 7, 2]
def baseStart_8365865 : Nat := 118140960795 + 8365865 * 2 ^ 59
def prefixEnd_8365865 : Nat := 4983230072969 + 3 ^ 40 * 8365865 * 2
def baseEnd_8365865 : Nat := 4295709835626016248413593

theorem tailTrace_8365865 : CollatzResearch.WordTrace tailWord_8365865 prefixEnd_8365865 4295709835626016248413593 := by
  unfold tailWord_8365865
  simp only [CollatzResearch.WordTrace]
  refine ⟨305128163836907355836443049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203418775891271570557628699 305128163836907355836443049)
  ·
    refine ⟨228846122877680516877332287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305128163836907355836443049 228846122877680516877332287)
    ·
      refine ⟨343269184316520775315998431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228846122877680516877332287 343269184316520775315998431)
      ·
        refine ⟨514903776474781162973997647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343269184316520775315998431 514903776474781162973997647)
        ·
          refine ⟨772355664712171744460996471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514903776474781162973997647 772355664712171744460996471)
          ·
            refine ⟨1158533497068257616691494707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 772355664712171744460996471 1158533497068257616691494707)
            ·
              refine ⟨1737800245602386425037242061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1158533497068257616691494707 1737800245602386425037242061)
              ·
                refine ⟨651675092100894909388965773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1737800245602386425037242061 651675092100894909388965773)
                ·
                  refine ⟨244378159537835591020862165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 651675092100894909388965773 244378159537835591020862165)
                  ·
                    refine ⟨5727613114168021664551457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 244378159537835591020862165 5727613114168021664551457)
                    ·
                      refine ⟨4295709835626016248413593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5727613114168021664551457 4295709835626016248413593)
                      ·
                        rfl

theorem cell23_8365865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 7, 2].length) (baseStart_8365865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365865 prefixEnd_8365865 := by exact prefixLift 8365865
  have htrace : WordTrace (prefixWord ++ tailWord_8365865) baseStart_8365865 baseEnd_8365865 := by
    simpa [prefixWord, tailWord_8365865, baseEnd_8365865] using wordTrace_append hprefix tailTrace_8365865
  have hstable : (prefixWord ++ tailWord_8365865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365865).length < 2 ^ (prefixWord ++ tailWord_8365865).sum := by decide
  have hdescent : baseEnd_8365865 < baseStart_8365865 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365882 : List Nat := [3, 1, 1, 1, 5, 1, 1, 1, 2, 5, 2]
def baseStart_8365882 : Nat := 118140960795 + 8365882 * 2 ^ 59
def prefixEnd_8365882 : Nat := 4983230072969 + 3 ^ 40 * 8365882 * 2
def baseEnd_8365882 : Nat := 4295718564797142681901015

theorem tailTrace_8365882 : CollatzResearch.WordTrace tailWord_8365882 prefixEnd_8365882 4295718564797142681901015 := by
  unfold tailWord_8365882
  simp only [CollatzResearch.WordTrace]
  refine ⟨76282195969461441934952975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203419189251897178493207933 76282195969461441934952975)
  ·
    refine ⟨114423293954192162902429463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76282195969461441934952975 114423293954192162902429463)
    ·
      refine ⟨171634940931288244353644195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114423293954192162902429463 171634940931288244353644195)
      ·
        refine ⟨257452411396932366530466293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171634940931288244353644195 257452411396932366530466293)
        ·
          refine ⟨24136163568462409362231215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 257452411396932366530466293 24136163568462409362231215)
          ·
            refine ⟨36204245352693614043346823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24136163568462409362231215 36204245352693614043346823)
            ·
              refine ⟨54306368029040421065020235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36204245352693614043346823 54306368029040421065020235)
              ·
                refine ⟨81459552043560631597530353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54306368029040421065020235 81459552043560631597530353)
                ·
                  refine ⟨61094664032670473698147765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81459552043560631597530353 61094664032670473698147765)
                  ·
                    refine ⟨5727624753062856909201353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61094664032670473698147765 5727624753062856909201353)
                    ·
                      refine ⟨4295718564797142681901015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5727624753062856909201353 4295718564797142681901015)
                      ·
                        rfl

theorem cell23_8365882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 2, 5, 2].length) (baseStart_8365882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365882 prefixEnd_8365882 := by exact prefixLift 8365882
  have htrace : WordTrace (prefixWord ++ tailWord_8365882) baseStart_8365882 baseEnd_8365882 := by
    simpa [prefixWord, tailWord_8365882, baseEnd_8365882] using wordTrace_append hprefix tailTrace_8365882
  have hstable : (prefixWord ++ tailWord_8365882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365882).length < 2 ^ (prefixWord ++ tailWord_8365882).sum := by decide
  have hdescent : baseEnd_8365882 < baseStart_8365882 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365888 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 4, 8]
def baseStart_8365888 : Nat := 118140960795 + 8365888 * 2 ^ 59
def prefixEnd_8365888 : Nat := 4983230072969 + 3 ^ 40 * 8365888 * 2
def baseEnd_8365888 : Nat := 1431907215227023219475329

theorem tailTrace_8365888 : CollatzResearch.WordTrace tailWord_8365888 prefixEnd_8365888 1431907215227023219475329 := by
  unfold tailWord_8365888
  simp only [CollatzResearch.WordTrace]
  refine ⟨152564501357912015382265159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203419335143882687176353545 152564501357912015382265159)
  ·
    refine ⟨228846752036868023073397739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152564501357912015382265159 228846752036868023073397739)
    ·
      refine ⟨343270128055302034610096609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228846752036868023073397739 343270128055302034610096609)
      ·
        refine ⟨257452596041476525957572457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343270128055302034610096609 257452596041476525957572457)
        ·
          refine ⟨193089447031107394468179343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257452596041476525957572457 193089447031107394468179343)
          ·
            refine ⟨289634170546661091702269015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193089447031107394468179343 289634170546661091702269015)
            ·
              refine ⟨434451255819991637553403523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289634170546661091702269015 434451255819991637553403523)
              ·
                refine ⟨651676883729987456330105285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434451255819991637553403523 651676883729987456330105285)
                ·
                  refine ⟨122189415699372648061894741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 651676883729987456330105285 122189415699372648061894741)
                  ·
                    refine ⟨1431907215227023219475329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 122189415699372648061894741 1431907215227023219475329)
                    ·
                      rfl

theorem cell23_8365888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 4, 8].length) (baseStart_8365888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365888 prefixEnd_8365888 := by exact prefixLift 8365888
  have htrace : WordTrace (prefixWord ++ tailWord_8365888) baseStart_8365888 baseEnd_8365888 := by
    simpa [prefixWord, tailWord_8365888, baseEnd_8365888] using wordTrace_append hprefix tailTrace_8365888
  have hstable : (prefixWord ++ tailWord_8365888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365888).length < 2 ^ (prefixWord ++ tailWord_8365888).sum := by decide
  have hdescent : baseEnd_8365888 < baseStart_8365888 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365895 : List Nat := [1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 4]
def baseStart_8365895 : Nat := 118140960795 + 8365895 * 2 ^ 59
def prefixEnd_8365895 : Nat := 4983230072969 + 3 ^ 40 * 8365895 * 2
def baseEnd_8365895 : Nat := 4295725240045651131038455

theorem tailTrace_8365895 : CollatzResearch.WordTrace tailWord_8365895 prefixEnd_8365895 4295725240045651131038455 := by
  unfold tailWord_8365895
  simp only [CollatzResearch.WordTrace]
  refine ⟨305129258026798670960035139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203419505351199113973356759 305129258026798670960035139)
  ·
    refine ⟨457693887040198006440052709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305129258026798670960035139 457693887040198006440052709)
    ·
      refine ⟨85817603820037126207509883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 457693887040198006440052709 85817603820037126207509883)
      ·
        refine ⟨128726405730055689311264825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85817603820037126207509883 128726405730055689311264825)
        ·
          refine ⟨96544804297541766983448619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128726405730055689311264825 96544804297541766983448619)
          ·
            refine ⟨144817206446312650475172929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96544804297541766983448619 144817206446312650475172929)
            ·
              refine ⟨108612904834734487856379697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144817206446312650475172929 108612904834734487856379697)
              ·
                refine ⟨81459678626050865892284773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108612904834734487856379697 81459678626050865892284773)
                ·
                  refine ⟨15273689742384537354803395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81459678626050865892284773 15273689742384537354803395)
                  ·
                    refine ⟨22910534613576806032205093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15273689742384537354803395 22910534613576806032205093)
                    ·
                      refine ⟨4295725240045651131038455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22910534613576806032205093 4295725240045651131038455)
                      ·
                        rfl

theorem cell23_8365895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_8365895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365895 prefixEnd_8365895 := by exact prefixLift 8365895
  have htrace : WordTrace (prefixWord ++ tailWord_8365895) baseStart_8365895 baseEnd_8365895 := by
    simpa [prefixWord, tailWord_8365895, baseEnd_8365895] using wordTrace_append hprefix tailTrace_8365895
  have hstable : (prefixWord ++ tailWord_8365895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365895).length < 2 ^ (prefixWord ++ tailWord_8365895).sum := by decide
  have hdescent : baseEnd_8365895 < baseStart_8365895 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365952 : List Nat := [2, 1, 1, 2, 1, 2, 7, 1, 6]
def baseStart_8365952 : Nat := 118140960795 + 8365952 * 2 ^ 59
def prefixEnd_8365952 : Nat := 4983230072969 + 3 ^ 40 * 8365952 * 2
def baseEnd_8365952 : Nat := 477306056493661934225077

theorem tailTrace_8365952 : CollatzResearch.WordTrace tailWord_8365952 prefixEnd_8365952 477306056493661934225077 := by
  unfold tailWord_8365952
  simp only [CollatzResearch.WordTrace]
  refine ⟨152565668493796084847430055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203420891325061446463240073 152565668493796084847430055)
  ·
    refine ⟨228848502740694127271145083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152565668493796084847430055 228848502740694127271145083)
    ·
      refine ⟨343272754111041190906717625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228848502740694127271145083 343272754111041190906717625)
      ·
        refine ⟨257454565583280893180038219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343272754111041190906717625 257454565583280893180038219)
        ·
          refine ⟨386181848374921339770057329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257454565583280893180038219 386181848374921339770057329)
          ·
            refine ⟨289636386281191004827542997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386181848374921339770057329 289636386281191004827542997)
            ·
              refine ⟨6788352803465414175645539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 289636386281191004827542997 6788352803465414175645539)
              ·
                refine ⟨10182529205198121263468309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6788352803465414175645539 10182529205198121263468309)
                ·
                  refine ⟨477306056493661934225077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10182529205198121263468309 477306056493661934225077)
                  ·
                    rfl

theorem cell23_8365952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 6].length) (baseStart_8365952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365952 prefixEnd_8365952 := by exact prefixLift 8365952
  have htrace : WordTrace (prefixWord ++ tailWord_8365952) baseStart_8365952 baseEnd_8365952 := by
    simpa [prefixWord, tailWord_8365952, baseEnd_8365952] using wordTrace_append hprefix tailTrace_8365952
  have hstable : (prefixWord ++ tailWord_8365952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365952).length < 2 ^ (prefixWord ++ tailWord_8365952).sum := by decide
  have hdescent : baseEnd_8365952 < baseStart_8365952 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366015 : List Nat := [1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 6]
def baseStart_8366015 : Nat := 118140960795 + 8366015 * 2 ^ 59
def prefixEnd_8366015 : Nat := 4983230072969 + 3 ^ 40 * 8366015 * 2
def baseEnd_8366015 : Nat := 4295786857724190661537903

theorem tailTrace_8366015 : CollatzResearch.WordTrace tailWord_8366015 prefixEnd_8366015 4295786857724190661537903 := by
  unfold tailWord_8366015
  simp only [CollatzResearch.WordTrace]
  refine ⟨305133634786363931454403499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203422423190909287636268999 305133634786363931454403499)
  ·
    refine ⟨457700452179545897181605249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305133634786363931454403499 457700452179545897181605249)
    ·
      refine ⟨343275339134659422886203937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457700452179545897181605249 343275339134659422886203937)
      ·
        refine ⟨257456504350994567164652953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343275339134659422886203937 257456504350994567164652953)
        ·
          refine ⟨193092378263245925373489715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257456504350994567164652953 193092378263245925373489715)
          ·
            refine ⟨289638567394868888060234573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193092378263245925373489715 289638567394868888060234573)
            ·
              refine ⟨108614462773075833022587965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 289638567394868888060234573 108614462773075833022587965)
              ·
                refine ⟨40730423539903437383470487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108614462773075833022587965 40730423539903437383470487)
                ·
                  refine ⟨61095635309855156075205731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40730423539903437383470487 61095635309855156075205731)
                  ·
                    refine ⟨91643452964782734112808597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61095635309855156075205731 91643452964782734112808597)
                    ·
                      refine ⟨4295786857724190661537903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91643452964782734112808597 4295786857724190661537903)
                      ·
                        rfl

theorem cell23_8366015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 6].length) (baseStart_8366015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366015 prefixEnd_8366015 := by exact prefixLift 8366015
  have htrace : WordTrace (prefixWord ++ tailWord_8366015) baseStart_8366015 baseEnd_8366015 := by
    simpa [prefixWord, tailWord_8366015, baseEnd_8366015] using wordTrace_append hprefix tailTrace_8366015
  have hstable : (prefixWord ++ tailWord_8366015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366015).length < 2 ^ (prefixWord ++ tailWord_8366015).sum := by decide
  have hdescent : baseEnd_8366015 < baseStart_8366015 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366036 : List Nat := [2, 4, 1, 2, 1, 1, 5, 1, 1, 1, 4]
def baseStart_8366036 : Nat := 118140960795 + 8366036 * 2 ^ 59
def prefixEnd_8366036 : Nat := 4983230072969 + 3 ^ 40 * 8366036 * 2
def baseEnd_8366036 : Nat := 4295797640817935079375307

theorem tailTrace_8366036 : CollatzResearch.WordTrace tailWord_8366036 prefixEnd_8366036 4295797640817935079375307 := by
  unfold tailWord_8366036
  simp only [CollatzResearch.WordTrace]
  refine ⟨152567200359643926020458981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203422933812858568027278641 152567200359643926020458981)
  ·
    refine ⟨28606350067433236128836059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152567200359643926020458981 28606350067433236128836059)
    ·
      refine ⟨42909525101149854193254089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28606350067433236128836059 42909525101149854193254089)
      ·
        refine ⟨32182143825862390644940567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42909525101149854193254089 32182143825862390644940567)
        ·
          refine ⟨48273215738793585967410851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32182143825862390644940567 48273215738793585967410851)
          ·
            refine ⟨72409823608190378951116277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48273215738793585967410851 72409823608190378951116277)
            ·
              refine ⟨6788420963267848026667151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72409823608190378951116277 6788420963267848026667151)
              ·
                refine ⟨10182631444901772040000727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6788420963267848026667151 10182631444901772040000727)
                ·
                  refine ⟨15273947167352658060001091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10182631444901772040000727 15273947167352658060001091)
                  ·
                    refine ⟨22910920751028987090001637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15273947167352658060001091 22910920751028987090001637)
                    ·
                      refine ⟨4295797640817935079375307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22910920751028987090001637 4295797640817935079375307)
                      ·
                        rfl

theorem cell23_8366036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_8366036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366036 prefixEnd_8366036 := by exact prefixLift 8366036
  have htrace : WordTrace (prefixWord ++ tailWord_8366036) baseStart_8366036 baseEnd_8366036 := by
    simpa [prefixWord, tailWord_8366036, baseEnd_8366036] using wordTrace_append hprefix tailTrace_8366036
  have hstable : (prefixWord ++ tailWord_8366036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366036).length < 2 ^ (prefixWord ++ tailWord_8366036).sum := by decide
  have hdescent : baseEnd_8366036 < baseStart_8366036 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366042 : List Nat := [3, 1, 1, 2, 6, 10]
def baseStart_8366042 : Nat := 118140960795 + 8366042 * 2 ^ 59
def prefixEnd_8366042 : Nat := 4983230072969 + 3 ^ 40 * 8366042 * 2
def baseEnd_8366042 : Nat := 17678192270378033151853

theorem tailTrace_8366042 : CollatzResearch.WordTrace tailWord_8366042 prefixEnd_8366042 17678192270378033151853 := by
  unfold tailWord_8366042
  simp only [CollatzResearch.WordTrace]
  refine ⟨76283654889316528766409095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203423079704844076710424253 76283654889316528766409095)
  ·
    refine ⟨114425482333974793149613643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76283654889316528766409095 114425482333974793149613643)
    ·
      refine ⟨171638223500962189724420465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114425482333974793149613643 171638223500962189724420465)
      ·
        refine ⟨128728667625721642293315349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171638223500962189724420465 128728667625721642293315349)
        ·
          refine ⟨6034156294955701982499157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 128728667625721642293315349 6034156294955701982499157)
          ·
            refine ⟨17678192270378033151853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 6034156294955701982499157 17678192270378033151853)
            ·
              rfl

theorem cell23_8366042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 10].length) (baseStart_8366042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366042 prefixEnd_8366042 := by exact prefixLift 8366042
  have htrace : WordTrace (prefixWord ++ tailWord_8366042) baseStart_8366042 baseEnd_8366042 := by
    simpa [prefixWord, tailWord_8366042, baseEnd_8366042] using wordTrace_append hprefix tailTrace_8366042
  have hstable : (prefixWord ++ tailWord_8366042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366042).length < 2 ^ (prefixWord ++ tailWord_8366042).sum := by decide
  have hdescent : baseEnd_8366042 < baseStart_8366042 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366052 : List Nat := [2, 3, 1, 1, 1, 1, 3, 2, 3, 3, 3]
def baseStart_8366052 : Nat := 118140960795 + 8366052 * 2 ^ 59
def prefixEnd_8366052 : Nat := 4983230072969 + 3 ^ 40 * 8366052 * 2
def baseEnd_8366052 : Nat := 4295805856508407016775233

theorem tailTrace_8366052 : CollatzResearch.WordTrace tailWord_8366052 prefixEnd_8366052 4295805856508407016775233 := by
  unfold tailWord_8366052
  simp only [CollatzResearch.WordTrace]
  refine ⟨152567492143614943386750205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203423322858153257849000273 152567492143614943386750205)
  ·
    refine ⟨57212809553855603770031327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152567492143614943386750205 57212809553855603770031327)
    ·
      refine ⟨85819214330783405655046991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57212809553855603770031327 85819214330783405655046991)
      ·
        refine ⟨128728821496175108482570487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85819214330783405655046991 128728821496175108482570487)
        ·
          refine ⟨193093232244262662723855731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128728821496175108482570487 193093232244262662723855731)
          ·
            refine ⟨289639848366393994085783597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193093232244262662723855731 289639848366393994085783597)
            ·
              refine ⟨108614943137397747782168849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 289639848366393994085783597 108614943137397747782168849)
              ·
                refine ⟨81461207353048310836626637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108614943137397747782168849 81461207353048310836626637)
                ·
                  refine ⟨30547952757393116563734989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81461207353048310836626637 30547952757393116563734989)
                  ·
                    refine ⟨11455482284022418711400621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30547952757393116563734989 11455482284022418711400621)
                    ·
                      refine ⟨4295805856508407016775233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11455482284022418711400621 4295805856508407016775233)
                      ·
                        rfl

theorem cell23_8366052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 3, 3, 3].length) (baseStart_8366052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366052 prefixEnd_8366052 := by exact prefixLift 8366052
  have htrace : WordTrace (prefixWord ++ tailWord_8366052) baseStart_8366052 baseEnd_8366052 := by
    simpa [prefixWord, tailWord_8366052, baseEnd_8366052] using wordTrace_append hprefix tailTrace_8366052
  have hstable : (prefixWord ++ tailWord_8366052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366052).length < 2 ^ (prefixWord ++ tailWord_8366052).sum := by decide
  have hdescent : baseEnd_8366052 < baseStart_8366052 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366090 : List Nat := [3, 1, 2, 2, 5, 1, 2, 1, 1, 2, 3]
def baseStart_8366090 : Nat := 118140960795 + 8366090 * 2 ^ 59
def prefixEnd_8366090 : Nat := 4983230072969 + 3 ^ 40 * 8366090 * 2
def baseEnd_8366090 : Nat := 4295825368773277868100059

theorem tailTrace_8366090 : CollatzResearch.WordTrace tailWord_8366090 prefixEnd_8366090 4295825368773277868100059 := by
  unfold tailWord_8366090
  simp only [CollatzResearch.WordTrace]
  refine ⟨76284092565273054815845931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203424246840728146175589149 76284092565273054815845931)
  ·
    refine ⟨114426138847909582223768897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76284092565273054815845931 114426138847909582223768897)
    ·
      refine ⟨85819604135932186667826673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114426138847909582223768897 85819604135932186667826673)
      ·
        refine ⟨64364703101949140000870005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85819604135932186667826673 64364703101949140000870005)
        ·
          refine ⟨6034190915807731875081563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64364703101949140000870005 6034190915807731875081563)
          ·
            refine ⟨9051286373711597812622345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6034190915807731875081563 9051286373711597812622345)
            ·
              refine ⟨6788464780283698359466759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9051286373711597812622345 6788464780283698359466759)
              ·
                refine ⟨10182697170425547539200139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6788464780283698359466759 10182697170425547539200139)
                ·
                  refine ⟨15274045755638321308800209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10182697170425547539200139 15274045755638321308800209)
                  ·
                    refine ⟨11455534316728740981600157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15274045755638321308800209 11455534316728740981600157)
                    ·
                      refine ⟨4295825368773277868100059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11455534316728740981600157 4295825368773277868100059)
                      ·
                        rfl

theorem cell23_8366090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_8366090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366090 prefixEnd_8366090 := by exact prefixLift 8366090
  have htrace : WordTrace (prefixWord ++ tailWord_8366090) baseStart_8366090 baseEnd_8366090 := by
    simpa [prefixWord, tailWord_8366090, baseEnd_8366090] using wordTrace_append hprefix tailTrace_8366090
  have hstable : (prefixWord ++ tailWord_8366090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366090).length < 2 ^ (prefixWord ++ tailWord_8366090).sum := by decide
  have hdescent : baseEnd_8366090 < baseStart_8366090 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366120 : List Nat := [2, 1, 5, 3, 2, 1, 1, 1, 1, 3, 3]
def baseStart_8366120 : Nat := 118140960795 + 8366120 * 2 ^ 59
def prefixEnd_8366120 : Nat := 4983230072969 + 3 ^ 40 * 8366120 * 2
def baseEnd_8366120 : Nat := 4295840773192912750724921

theorem tailTrace_8366120 : CollatzResearch.WordTrace tailWord_8366120 prefixEnd_8366120 4295840773192912750724921 := by
  unfold tailWord_8366120
  simp only [CollatzResearch.WordTrace]
  refine ⟨152568732225491767193487907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203424976300655689591317209 152568732225491767193487907)
  ·
    refine ⟨228853098338237650790231861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152568732225491767193487907 228853098338237650790231861)
    ·
      refine ⟨21454977969209779761584237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 228853098338237650790231861 21454977969209779761584237)
      ·
        refine ⟨8045616738453667410594089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21454977969209779761584237 8045616738453667410594089)
        ·
          refine ⟨6034212553840250557945567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8045616738453667410594089 6034212553840250557945567)
          ·
            refine ⟨9051318830760375836918351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6034212553840250557945567 9051318830760375836918351)
            ·
              refine ⟨13576978246140563755377527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9051318830760375836918351 13576978246140563755377527)
              ·
                refine ⟨20365467369210845633066291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13576978246140563755377527 20365467369210845633066291)
                ·
                  refine ⟨30548201053816268449599437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20365467369210845633066291 30548201053816268449599437)
                  ·
                    refine ⟨11455575395181100668599789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30548201053816268449599437 11455575395181100668599789)
                    ·
                      refine ⟨4295840773192912750724921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11455575395181100668599789 4295840773192912750724921)
                      ·
                        rfl

theorem cell23_8366120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_8366120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366120 prefixEnd_8366120 := by exact prefixLift 8366120
  have htrace : WordTrace (prefixWord ++ tailWord_8366120) baseStart_8366120 baseEnd_8366120 := by
    simpa [prefixWord, tailWord_8366120, baseEnd_8366120] using wordTrace_append hprefix tailTrace_8366120
  have hstable : (prefixWord ++ tailWord_8366120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366120).length < 2 ^ (prefixWord ++ tailWord_8366120).sum := by decide
  have hdescent : baseEnd_8366120 < baseStart_8366120 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366169 : List Nat := [1, 2, 1, 2, 2, 1, 4, 1, 2, 5, 2]
def baseStart_8366169 : Nat := 118140960795 + 8366169 * 2 ^ 59
def prefixEnd_8366169 : Nat := 4983230072969 + 3 ^ 40 * 8366169 * 2
def baseEnd_8366169 : Nat := 4295865933744983059012195

theorem tailTrace_8366169 : CollatzResearch.WordTrace tailWord_8366169 prefixEnd_8366169 4295865933744983059012195 := by
  unfold tailWord_8366169
  simp only [CollatzResearch.WordTrace]
  refine ⟨305139251627806015755509561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203426167751870677170339707 305139251627806015755509561)
  ·
    refine ⟨228854438720854511816632171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305139251627806015755509561 228854438720854511816632171)
    ·
      refine ⟨343281658081281767724948257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228854438720854511816632171 343281658081281767724948257)
      ·
        refine ⟨257461243560961325793711193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343281658081281767724948257 257461243560961325793711193)
        ·
          refine ⟨193095932670720994345283395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257461243560961325793711193 193095932670720994345283395)
          ·
            refine ⟨289643899006081491517925093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193095932670720994345283395 289643899006081491517925093)
            ·
              refine ⟨54308231063640279659610955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 289643899006081491517925093 54308231063640279659610955)
              ·
                refine ⟨81462346595460419489416433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54308231063640279659610955 81462346595460419489416433)
                ·
                  refine ⟨61096759946595314617062325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81462346595460419489416433 61096759946595314617062325)
                  ·
                    refine ⟨5727821244993310745349593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61096759946595314617062325 5727821244993310745349593)
                    ·
                      refine ⟨4295865933744983059012195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5727821244993310745349593 4295865933744983059012195)
                      ·
                        rfl

theorem cell23_8366169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 5, 2].length) (baseStart_8366169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366169 prefixEnd_8366169 := by exact prefixLift 8366169
  have htrace : WordTrace (prefixWord ++ tailWord_8366169) baseStart_8366169 baseEnd_8366169 := by
    simpa [prefixWord, tailWord_8366169, baseEnd_8366169] using wordTrace_append hprefix tailTrace_8366169
  have hstable : (prefixWord ++ tailWord_8366169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366169).length < 2 ^ (prefixWord ++ tailWord_8366169).sum := by decide
  have hdescent : baseEnd_8366169 < baseStart_8366169 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366199 : List Nat := [1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 4]
def baseStart_8366199 : Nat := 118140960795 + 8366199 * 2 ^ 59
def prefixEnd_8366199 : Nat := 4983230072969 + 3 ^ 40 * 8366199 * 2
def baseEnd_8366199 : Nat := 4295881338164617941637057

theorem tailTrace_8366199 : CollatzResearch.WordTrace tailWord_8366199 prefixEnd_8366199 4295881338164617941637057 := by
  unfold tailWord_8366199
  simp only [CollatzResearch.WordTrace]
  refine ⟨305140345817697330879101651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203426897211798220586067767 305140345817697330879101651)
  ·
    refine ⟨457710518726545996318652477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305140345817697330879101651 457710518726545996318652477)
    ·
      refine ⟨171641444522454748619494679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 457710518726545996318652477 171641444522454748619494679)
      ·
        refine ⟨257462166783682122929242019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171641444522454748619494679 257462166783682122929242019)
        ·
          refine ⟨386193250175523184393863029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257462166783682122929242019 386193250175523184393863029)
          ·
            refine ⟨36205617203955298536924659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 386193250175523184393863029 36205617203955298536924659)
            ·
              refine ⟨54308425805932947805386989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36205617203955298536924659 54308425805932947805386989)
              ·
                refine ⟨20365659677224855427020121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54308425805932947805386989 20365659677224855427020121)
                ·
                  refine ⟨15274244757918641570265091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20365659677224855427020121 15274244757918641570265091)
                  ·
                    refine ⟨22911367136877962355397637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15274244757918641570265091 22911367136877962355397637)
                    ·
                      refine ⟨4295881338164617941637057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22911367136877962355397637 4295881338164617941637057)
                      ·
                        rfl

theorem cell23_8366199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 4].length) (baseStart_8366199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366199 prefixEnd_8366199 := by exact prefixLift 8366199
  have htrace : WordTrace (prefixWord ++ tailWord_8366199) baseStart_8366199 baseEnd_8366199 := by
    simpa [prefixWord, tailWord_8366199, baseEnd_8366199] using wordTrace_append hprefix tailTrace_8366199
  have hstable : (prefixWord ++ tailWord_8366199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366199).length < 2 ^ (prefixWord ++ tailWord_8366199).sum := by decide
  have hdescent : baseEnd_8366199 < baseStart_8366199 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366216 : List Nat := [2, 1, 3, 4, 1, 1, 2, 2, 2, 1, 4]
def baseStart_8366216 : Nat := 118140960795 + 8366216 * 2 ^ 59
def prefixEnd_8366216 : Nat := 4983230072969 + 3 ^ 40 * 8366216 * 2
def baseEnd_8366216 : Nat := 4295890067335744375124479

theorem tailTrace_8366216 : CollatzResearch.WordTrace tailWord_8366216 prefixEnd_8366216 4295890067335744375124479 := by
  unfold tailWord_8366216
  simp only [CollatzResearch.WordTrace]
  refine ⟨152570482929317871391235251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203427310572423828521647001 152570482929317871391235251)
  ·
    refine ⟨228855724393976807086852877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152570482929317871391235251 228855724393976807086852877)
    ·
      refine ⟨85820896647741302657569829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228855724393976807086852877 85820896647741302657569829)
      ·
        refine ⟨16091418121451494248294343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85820896647741302657569829 16091418121451494248294343)
        ·
          refine ⟨24137127182177241372441515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16091418121451494248294343 24137127182177241372441515)
          ·
            refine ⟨36205690773265862058662273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24137127182177241372441515 36205690773265862058662273)
            ·
              refine ⟨27154268079949396543996705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36205690773265862058662273 27154268079949396543996705)
              ·
                refine ⟨20365701059962047407997529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27154268079949396543996705 20365701059962047407997529)
                ·
                  refine ⟨15274275794971535555998147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20365701059962047407997529 15274275794971535555998147)
                  ·
                    refine ⟨22911413692457303333997221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15274275794971535555998147 22911413692457303333997221)
                    ·
                      refine ⟨4295890067335744375124479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22911413692457303333997221 4295890067335744375124479)
                      ·
                        rfl

theorem cell23_8366216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_8366216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366216 prefixEnd_8366216 := by exact prefixLift 8366216
  have htrace : WordTrace (prefixWord ++ tailWord_8366216) baseStart_8366216 baseEnd_8366216 := by
    simpa [prefixWord, tailWord_8366216, baseEnd_8366216] using wordTrace_append hprefix tailTrace_8366216
  have hstable : (prefixWord ++ tailWord_8366216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366216).length < 2 ^ (prefixWord ++ tailWord_8366216).sum := by decide
  have hdescent : baseEnd_8366216 < baseStart_8366216 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366226 : List Nat := [3, 2, 3, 1, 1, 1, 2, 3, 3, 4]
def baseStart_8366226 : Nat := 118140960795 + 8366226 * 2 ^ 59
def prefixEnd_8366226 : Nat := 4983230072969 + 3 ^ 40 * 8366226 * 2
def baseEnd_8366226 : Nat := 1431965067380763111999811

theorem tailTrace_8366226 : CollatzResearch.WordTrace tailWord_8366226 prefixEnd_8366226 1431965067380763111999811 := by
  unfold tailWord_8366226
  simp only [CollatzResearch.WordTrace]
  refine ⟨76285332647149878622583633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203427553725733009660223021 76285332647149878622583633)
  ·
    refine ⟨57213999485362408966937725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76285332647149878622583633 57213999485362408966937725)
    ·
      refine ⟨21455249807010903362601647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57213999485362408966937725 21455249807010903362601647)
      ·
        refine ⟨32182874710516355043902471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21455249807010903362601647 32182874710516355043902471)
        ·
          refine ⟨48274312065774532565853707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32182874710516355043902471 48274312065774532565853707)
          ·
            refine ⟨72411468098661798848780561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48274312065774532565853707 72411468098661798848780561)
            ·
              refine ⟨54308601073996349136585421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72411468098661798848780561 54308601073996349136585421)
              ·
                refine ⟨20365725402748630926219533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54308601073996349136585421 20365725402748630926219533)
                ·
                  refine ⟨7637147026030736597332325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20365725402748630926219533 7637147026030736597332325)
                  ·
                    refine ⟨1431965067380763111999811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7637147026030736597332325 1431965067380763111999811)
                    ·
                      rfl

theorem cell23_8366226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_8366226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366226 prefixEnd_8366226 := by exact prefixLift 8366226
  have htrace : WordTrace (prefixWord ++ tailWord_8366226) baseStart_8366226 baseEnd_8366226 := by
    simpa [prefixWord, tailWord_8366226, baseEnd_8366226] using wordTrace_append hprefix tailTrace_8366226
  have hstable : (prefixWord ++ tailWord_8366226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366226).length < 2 ^ (prefixWord ++ tailWord_8366226).sum := by decide
  have hdescent : baseEnd_8366226 < baseStart_8366226 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366250 : List Nat := [3, 1, 5, 1, 2, 2, 1, 1, 2, 1, 4]
def baseStart_8366250 : Nat := 118140960795 + 8366250 * 2 ^ 59
def prefixEnd_8366250 : Nat := 4983230072969 + 3 ^ 40 * 8366250 * 2
def baseEnd_8366250 : Nat := 4295907525677997242099323

theorem tailTrace_8366250 : CollatzResearch.WordTrace tailWord_8366250 prefixEnd_8366250 4295907525677997242099323 := by
  unfold tailWord_8366250
  simp only [CollatzResearch.WordTrace]
  refine ⟨76285551485128141647302051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203428137293675044392805469 76285551485128141647302051)
  ·
    refine ⟨114428327227692212470953077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76285551485128141647302051 114428327227692212470953077)
    ·
      refine ⟨10727655677596144919151851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114428327227692212470953077 10727655677596144919151851)
      ·
        refine ⟨16091483516394217378727777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10727655677596144919151851 16091483516394217378727777)
        ·
          refine ⟨12068612637295663034045833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16091483516394217378727777 12068612637295663034045833)
          ·
            refine ⟨9051459477971747275534375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12068612637295663034045833 9051459477971747275534375)
            ·
              refine ⟨13577189216957620913301563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9051459477971747275534375 13577189216957620913301563)
              ·
                refine ⟨20365783825436431369952345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13577189216957620913301563 20365783825436431369952345)
                ·
                  refine ⟨15274337869077323527464259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20365783825436431369952345 15274337869077323527464259)
                  ·
                    refine ⟨22911506803615985291196389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15274337869077323527464259 22911506803615985291196389)
                    ·
                      refine ⟨4295907525677997242099323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22911506803615985291196389 4295907525677997242099323)
                      ·
                        rfl

theorem cell23_8366250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_8366250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366250 prefixEnd_8366250 := by exact prefixLift 8366250
  have htrace : WordTrace (prefixWord ++ tailWord_8366250) baseStart_8366250 baseEnd_8366250 := by
    simpa [prefixWord, tailWord_8366250, baseEnd_8366250] using wordTrace_append hprefix tailTrace_8366250
  have hstable : (prefixWord ++ tailWord_8366250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366250).length < 2 ^ (prefixWord ++ tailWord_8366250).sum := by decide
  have hdescent : baseEnd_8366250 < baseStart_8366250 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366253 : List Nat := [1, 5, 2, 1, 2, 1, 3, 1, 2, 2, 3]
def baseStart_8366253 : Nat := 118140960795 + 8366253 * 2 ^ 59
def prefixEnd_8366253 : Nat := 4983230072969 + 3 ^ 40 * 8366253 * 2
def baseEnd_8366253 : Nat := 4295909066119960730361809

theorem tailTrace_8366253 : CollatzResearch.WordTrace tailWord_8366253 prefixEnd_8366253 4295909066119960730361809 := by
  unfold tailWord_8366253
  simp only [CollatzResearch.WordTrace]
  refine ⟨305142315359501698101567413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203428210239667798734378275 305142315359501698101567413)
  ·
    refine ⟨28607092064953284197021945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 305142315359501698101567413 28607092064953284197021945)
    ·
      refine ⟨21455319048714963147766459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28607092064953284197021945 21455319048714963147766459)
      ·
        refine ⟨32182978573072444721649689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21455319048714963147766459 32182978573072444721649689)
        ·
          refine ⟨24137233929804333541237267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32182978573072444721649689 24137233929804333541237267)
          ·
            refine ⟨36205850894706500311855901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24137233929804333541237267 36205850894706500311855901)
            ·
              refine ⟨13577194085514937616945963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36205850894706500311855901 13577194085514937616945963)
              ·
                refine ⟨20365791128272406425418945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13577194085514937616945963 20365791128272406425418945)
                ·
                  refine ⟨15274343346204304819064209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20365791128272406425418945 15274343346204304819064209)
                  ·
                    refine ⟨11455757509653228614298157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15274343346204304819064209 11455757509653228614298157)
                    ·
                      refine ⟨4295909066119960730361809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11455757509653228614298157 4295909066119960730361809)
                      ·
                        rfl

theorem cell23_8366253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_8366253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366253 prefixEnd_8366253 := by exact prefixLift 8366253
  have htrace : WordTrace (prefixWord ++ tailWord_8366253) baseStart_8366253 baseEnd_8366253 := by
    simpa [prefixWord, tailWord_8366253, baseEnd_8366253] using wordTrace_append hprefix tailTrace_8366253
  have hstable : (prefixWord ++ tailWord_8366253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366253).length < 2 ^ (prefixWord ++ tailWord_8366253).sum := by decide
  have hdescent : baseEnd_8366253 < baseStart_8366253 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366283 : List Nat := [1, 1, 1, 1, 3, 2, 3, 6, 1, 1, 3]
def baseStart_8366283 : Nat := 118140960795 + 8366283 * 2 ^ 59
def prefixEnd_8366283 : Nat := 4983230072969 + 3 ^ 40 * 8366283 * 2
def baseEnd_8366283 : Nat := 4295924470539595612986671

theorem tailTrace_8366283 : CollatzResearch.WordTrace tailWord_8366283 prefixEnd_8366283 4295924470539595612986671 := by
  unfold tailWord_8366283
  simp only [CollatzResearch.WordTrace]
  refine ⟨305143409549393013225159503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203428939699595342150106335 305143409549393013225159503)
  ·
    refine ⟨457715114324089519837739255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305143409549393013225159503 457715114324089519837739255)
    ·
      refine ⟨686572671486134279756608883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457715114324089519837739255 686572671486134279756608883)
      ·
        refine ⟨1029859007229201419634913325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 686572671486134279756608883 1029859007229201419634913325)
        ·
          refine ⟨386197127710950532363092497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1029859007229201419634913325 386197127710950532363092497)
          ·
            refine ⟨289647845783212899272319373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386197127710950532363092497 289647845783212899272319373)
            ·
              refine ⟨108617942168704837227119765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 289647845783212899272319373 108617942168704837227119765)
              ·
                refine ⟨5091466039158039245021239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 108617942168704837227119765 5091466039158039245021239)
                ·
                  refine ⟨7637199058737058867531859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5091466039158039245021239 7637199058737058867531859)
                  ·
                    refine ⟨11455798588105588301297789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7637199058737058867531859 11455798588105588301297789)
                    ·
                      refine ⟨4295924470539595612986671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11455798588105588301297789 4295924470539595612986671)
                      ·
                        rfl

theorem cell23_8366283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 6, 1, 1, 3].length) (baseStart_8366283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366283 prefixEnd_8366283 := by exact prefixLift 8366283
  have htrace : WordTrace (prefixWord ++ tailWord_8366283) baseStart_8366283 baseEnd_8366283 := by
    simpa [prefixWord, tailWord_8366283, baseEnd_8366283] using wordTrace_append hprefix tailTrace_8366283
  have hstable : (prefixWord ++ tailWord_8366283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366283).length < 2 ^ (prefixWord ++ tailWord_8366283).sum := by decide
  have hdescent : baseEnd_8366283 < baseStart_8366283 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366289 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 5, 1, 4]
def baseStart_8366289 : Nat := 118140960795 + 8366289 * 2 ^ 59
def prefixEnd_8366289 : Nat := 4983230072969 + 3 ^ 40 * 8366289 * 2
def baseEnd_8366289 : Nat := 4295927551423522589511643

theorem tailTrace_8366289 : CollatzResearch.WordTrace tailWord_8366289 prefixEnd_8366289 4295927551423522589511643 := by
  unfold tailWord_8366289
  simp only [CollatzResearch.WordTrace]
  refine ⟨305143628387371276249877921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203429085591580850833251947 305143628387371276249877921)
  ·
    refine ⟨228857721290528457187408441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305143628387371276249877921 228857721290528457187408441)
    ·
      refine ⟨171643290967896342890556331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228857721290528457187408441 171643290967896342890556331)
      ·
        refine ⟨257464936451844514335834497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171643290967896342890556331 257464936451844514335834497)
        ·
          refine ⟨193098702338883385751875873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257464936451844514335834497 193098702338883385751875873)
          ·
            refine ⟨144824026754162539313906905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193098702338883385751875873 144824026754162539313906905)
            ·
              refine ⟨108618020065621904485430179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144824026754162539313906905 108618020065621904485430179)
              ·
                refine ⟨162927030098432856728145269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108618020065621904485430179 162927030098432856728145269)
                ·
                  refine ⟨15274409071728080318263619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 162927030098432856728145269 15274409071728080318263619)
                  ·
                    refine ⟨22911613607592120477395429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15274409071728080318263619 22911613607592120477395429)
                    ·
                      refine ⟨4295927551423522589511643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22911613607592120477395429 4295927551423522589511643)
                      ·
                        rfl

theorem cell23_8366289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 1, 4].length) (baseStart_8366289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366289 prefixEnd_8366289 := by exact prefixLift 8366289
  have htrace : WordTrace (prefixWord ++ tailWord_8366289) baseStart_8366289 baseEnd_8366289 := by
    simpa [prefixWord, tailWord_8366289, baseEnd_8366289] using wordTrace_append hprefix tailTrace_8366289
  have hstable : (prefixWord ++ tailWord_8366289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366289).length < 2 ^ (prefixWord ++ tailWord_8366289).sum := by decide
  have hdescent : baseEnd_8366289 < baseStart_8366289 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366299 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 6, 4]
def baseStart_8366299 : Nat := 118140960795 + 8366299 * 2 ^ 59
def prefixEnd_8366299 : Nat := 4983230072969 + 3 ^ 40 * 8366299 * 2
def baseEnd_8366299 : Nat := 1431977562076689183462199

theorem tailTrace_8366299 : CollatzResearch.WordTrace tailWord_8366299 prefixEnd_8366299 1431977562076689183462199 := by
  unfold tailWord_8366299
  simp only [CollatzResearch.WordTrace]
  refine ⟨305143993117335047957741951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203429328744890031971827967 305143993117335047957741951)
  ·
    refine ⟨457715989676002571936612927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305143993117335047957741951 457715989676002571936612927)
    ·
      refine ⟨686573984514003857904919391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457715989676002571936612927 686573984514003857904919391)
      ·
        refine ⟨1029860976771005786857379087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 686573984514003857904919391 1029860976771005786857379087)
        ·
          refine ⟨1544791465156508680286068631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1029860976771005786857379087 1544791465156508680286068631)
          ·
            refine ⟨2317187197734763020429102947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1544791465156508680286068631 2317187197734763020429102947)
            ·
              refine ⟨3475780796602144530643654421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2317187197734763020429102947 3475780796602144530643654421)
              ·
                refine ⟨162927224840725524873921301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3475780796602144530643654421 162927224840725524873921301)
                ·
                  refine ⟨7637213664409008978465061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 162927224840725524873921301 7637213664409008978465061)
                  ·
                    refine ⟨1431977562076689183462199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7637213664409008978465061 1431977562076689183462199)
                    ·
                      rfl

theorem cell23_8366299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 4].length) (baseStart_8366299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366299 prefixEnd_8366299 := by exact prefixLift 8366299
  have htrace : WordTrace (prefixWord ++ tailWord_8366299) baseStart_8366299 baseEnd_8366299 := by
    simpa [prefixWord, tailWord_8366299, baseEnd_8366299] using wordTrace_append hprefix tailTrace_8366299
  have hstable : (prefixWord ++ tailWord_8366299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366299).length < 2 ^ (prefixWord ++ tailWord_8366299).sum := by decide
  have hdescent : baseEnd_8366299 < baseStart_8366299 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366326 : List Nat := [5, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5]
def baseStart_8366326 : Nat := 118140960795 + 8366326 * 2 ^ 59
def prefixEnd_8366326 : Nat := 4983230072969 + 3 ^ 40 * 8366326 * 2
def baseEnd_8366326 : Nat := 4295946550207738944748973

theorem tailTrace_8366326 : CollatzResearch.WordTrace tailWord_8366326 prefixEnd_8366326 4295946550207738944748973 := by
  unfold tailWord_8366326
  simp only [CollatzResearch.WordTrace]
  refine ⟨19071561118014826973060927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203429985258824821045983221 19071561118014826973060927)
  ·
    refine ⟨28607341677022240459591391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19071561118014826973060927 28607341677022240459591391)
    ·
      refine ⟨42911012515533360689387087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28607341677022240459591391 42911012515533360689387087)
      ·
        refine ⟨64366518773300041034080631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42911012515533360689387087 64366518773300041034080631)
        ·
          refine ⟨96549778159950061551120947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64366518773300041034080631 96549778159950061551120947)
          ·
            refine ⟨144824667239925092326681421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96549778159950061551120947 144824667239925092326681421)
            ·
              refine ⟨54309250214971909622505533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144824667239925092326681421 54309250214971909622505533)
              ·
                refine ⟨20365968830614466108439575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54309250214971909622505533 20365968830614466108439575)
                ·
                  refine ⟨30548953245921699162659363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20365968830614466108439575 30548953245921699162659363)
                  ·
                    refine ⟨45823429868882548743989045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30548953245921699162659363 45823429868882548743989045)
                    ·
                      refine ⟨4295946550207738944748973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45823429868882548743989045 4295946550207738944748973)
                      ·
                        rfl

theorem cell23_8366326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_8366326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366326 prefixEnd_8366326 := by exact prefixLift 8366326
  have htrace : WordTrace (prefixWord ++ tailWord_8366326) baseStart_8366326 baseEnd_8366326 := by
    simpa [prefixWord, tailWord_8366326, baseEnd_8366326] using wordTrace_append hprefix tailTrace_8366326
  have hstable : (prefixWord ++ tailWord_8366326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366326).length < 2 ^ (prefixWord ++ tailWord_8366326).sum := by decide
  have hdescent : baseEnd_8366326 < baseStart_8366326 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366369 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 1, 4, 5]
def baseStart_8366369 : Nat := 118140960795 + 8366369 * 2 ^ 59
def prefixEnd_8366369 : Nat := 4983230072969 + 3 ^ 40 * 8366369 * 2
def baseEnd_8366369 : Nat := 4295968629875882276511275

theorem tailTrace_8366369 : CollatzResearch.WordTrace tailWord_8366369 prefixEnd_8366369 4295968629875882276511275 := by
  unfold tailWord_8366369
  simp only [CollatzResearch.WordTrace]
  refine ⟨305146546227081449912790161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203431030818054299941860107 305146546227081449912790161)
  ·
    refine ⟨228859909670311087434592621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305146546227081449912790161 228859909670311087434592621)
    ·
      refine ⟨85822466126366657787972233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228859909670311087434592621 85822466126366657787972233)
      ·
        refine ⟨64366849594774993340979175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85822466126366657787972233 64366849594774993340979175)
        ·
          refine ⟨96550274392162490011468763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64366849594774993340979175 96550274392162490011468763)
          ·
            refine ⟨144825411588243735017203145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96550274392162490011468763 144825411588243735017203145)
            ·
              refine ⟨108619058691182801262902359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144825411588243735017203145 108619058691182801262902359)
              ·
                refine ⟨162928588036774201894353539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108619058691182801262902359 162928588036774201894353539)
                ·
                  refine ⟨244392882055161302841530309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162928588036774201894353539 244392882055161302841530309)
                  ·
                    refine ⟨45823665385342744282786933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 244392882055161302841530309 45823665385342744282786933)
                    ·
                      refine ⟨4295968629875882276511275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45823665385342744282786933 4295968629875882276511275)
                      ·
                        rfl

theorem cell23_8366369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_8366369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366369 prefixEnd_8366369 := by exact prefixLift 8366369
  have htrace : WordTrace (prefixWord ++ tailWord_8366369) baseStart_8366369 baseEnd_8366369 := by
    simpa [prefixWord, tailWord_8366369, baseEnd_8366369] using wordTrace_append hprefix tailTrace_8366369
  have hstable : (prefixWord ++ tailWord_8366369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366369).length < 2 ^ (prefixWord ++ tailWord_8366369).sum := by decide
  have hdescent : baseEnd_8366369 < baseStart_8366369 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366373 : List Nat := [1, 3, 1, 2, 5, 1, 1, 2, 1, 3, 3]
def baseStart_8366373 : Nat := 118140960795 + 8366373 * 2 ^ 59
def prefixEnd_8366373 : Nat := 4983230072969 + 3 ^ 40 * 8366373 * 2
def baseEnd_8366373 : Nat := 4295970683798500260861257

theorem tailTrace_8366373 : CollatzResearch.WordTrace tailWord_8366373 prefixEnd_8366373 4295970683798500260861257 := by
  unfold tailWord_8366373
  simp only [CollatzResearch.WordTrace]
  refine ⟨305146692119066958595935773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203431128079377972397290515 305146692119066958595935773)
  ·
    refine ⟨114430009544650109473475915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305146692119066958595935773 114430009544650109473475915)
    ·
      refine ⟨171645014316975164210213873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114430009544650109473475915 171645014316975164210213873)
      ·
        refine ⟨128733760737731373157660405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171645014316975164210213873 128733760737731373157660405)
        ·
          refine ⟨12068790069162316233530663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128733760737731373157660405 12068790069162316233530663)
          ·
            refine ⟨18103185103743474350295995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12068790069162316233530663 18103185103743474350295995)
            ·
              refine ⟨27154777655615211525443993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18103185103743474350295995 27154777655615211525443993)
              ·
                refine ⟨20366083241711408644082995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27154777655615211525443993 20366083241711408644082995)
                ·
                  refine ⟨30549124862567112966124493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20366083241711408644082995 30549124862567112966124493)
                  ·
                    refine ⟨11455921823462667362296685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30549124862567112966124493 11455921823462667362296685)
                    ·
                      refine ⟨4295970683798500260861257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11455921823462667362296685 4295970683798500260861257)
                      ·
                        rfl

theorem cell23_8366373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 3, 3].length) (baseStart_8366373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366373 prefixEnd_8366373 := by exact prefixLift 8366373
  have htrace : WordTrace (prefixWord ++ tailWord_8366373) baseStart_8366373 baseEnd_8366373 := by
    simpa [prefixWord, tailWord_8366373, baseEnd_8366373] using wordTrace_append hprefix tailTrace_8366373
  have hstable : (prefixWord ++ tailWord_8366373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366373).length < 2 ^ (prefixWord ++ tailWord_8366373).sum := by decide
  have hdescent : baseEnd_8366373 < baseStart_8366373 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366383 : List Nat := [1, 1, 2, 1, 2, 1, 4, 5, 1, 3, 2]
def baseStart_8366383 : Nat := 118140960795 + 8366383 * 2 ^ 59
def prefixEnd_8366383 : Nat := 4983230072969 + 3 ^ 40 * 8366383 * 2
def baseEnd_8366383 : Nat := 4295975818605045221736211

theorem tailTrace_8366383 : CollatzResearch.WordTrace tailWord_8366383 prefixEnd_8366383 4295975818605045221736211 := by
  unfold tailWord_8366383
  simp only [CollatzResearch.WordTrace]
  refine ⟨305147056849030730303799803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203431371232687153535866535 305147056849030730303799803)
  ·
    refine ⟨457720585273546095455699705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305147056849030730303799803 457720585273546095455699705)
    ·
      refine ⟨343290438955159571591774779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457720585273546095455699705 343290438955159571591774779)
      ·
        refine ⟨514935658432739357387662169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343290438955159571591774779 514935658432739357387662169)
        ·
          refine ⟨386201743824554518040746627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 514935658432739357387662169 386201743824554518040746627)
          ·
            refine ⟨579302615736831777061119941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386201743824554518040746627 579302615736831777061119941)
            ·
              refine ⟨108619240450655958198959989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 579302615736831777061119941 108619240450655958198959989)
              ·
                refine ⟨10183053792248996081152499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108619240450655958198959989 10183053792248996081152499)
                ·
                  refine ⟨15274580688373494121728749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10183053792248996081152499 15274580688373494121728749)
                  ·
                    refine ⟨5727967758140060295648281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15274580688373494121728749 5727967758140060295648281)
                    ·
                      refine ⟨4295975818605045221736211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5727967758140060295648281 4295975818605045221736211)
                      ·
                        rfl

theorem cell23_8366383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 3, 2].length) (baseStart_8366383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366383 prefixEnd_8366383 := by exact prefixLift 8366383
  have htrace : WordTrace (prefixWord ++ tailWord_8366383) baseStart_8366383 baseEnd_8366383 := by
    simpa [prefixWord, tailWord_8366383, baseEnd_8366383] using wordTrace_append hprefix tailTrace_8366383
  have hstable : (prefixWord ++ tailWord_8366383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366383).length < 2 ^ (prefixWord ++ tailWord_8366383).sum := by decide
  have hdescent : baseEnd_8366383 < baseStart_8366383 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366434 : List Nat := [3, 3, 2, 1, 1, 4, 2, 1, 1, 3, 2]
def baseStart_8366434 : Nat := 118140960795 + 8366434 * 2 ^ 59
def prefixEnd_8366434 : Nat := 4983230072969 + 3 ^ 40 * 8366434 * 2
def baseEnd_8366434 : Nat := 4296002006118424522198477

theorem tailTrace_8366434 : CollatzResearch.WordTrace tailWord_8366434 prefixEnd_8366434 4296002006118424522198477 := by
  unfold tailWord_8366434
  simp only [CollatzResearch.WordTrace]
  refine ⟨76287229242961491503476589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203432611314563977342604237 76287229242961491503476589)
  ·
    refine ⟨28607710966110559313803721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76287229242961491503476589 28607710966110559313803721)
    ·
      refine ⟨21455783224582919485352791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28607710966110559313803721 21455783224582919485352791)
      ·
        refine ⟨32183674836874379228029187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21455783224582919485352791 32183674836874379228029187)
        ·
          refine ⟨48275512255311568842043781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32183674836874379228029187 48275512255311568842043781)
          ·
            refine ⟨9051658547870919157883209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48275512255311568842043781 9051658547870919157883209)
            ·
              refine ⟨6788743910903189368412407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9051658547870919157883209 6788743910903189368412407)
              ·
                refine ⟨10183115866354784052618611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6788743910903189368412407 10183115866354784052618611)
                ·
                  refine ⟨15274673799532176078927917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10183115866354784052618611 15274673799532176078927917)
                  ·
                    refine ⟨5728002674824566029597969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15274673799532176078927917 5728002674824566029597969)
                    ·
                      refine ⟨4296002006118424522198477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5728002674824566029597969 4296002006118424522198477)
                      ·
                        rfl

theorem cell23_8366434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_8366434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366434 prefixEnd_8366434 := by exact prefixLift 8366434
  have htrace : WordTrace (prefixWord ++ tailWord_8366434) baseStart_8366434 baseEnd_8366434 := by
    simpa [prefixWord, tailWord_8366434, baseEnd_8366434] using wordTrace_append hprefix tailTrace_8366434
  have hstable : (prefixWord ++ tailWord_8366434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366434).length < 2 ^ (prefixWord ++ tailWord_8366434).sum := by decide
  have hdescent : baseEnd_8366434 < baseStart_8366434 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366453 : List Nat := [1, 3, 4, 1, 2, 2, 2, 1, 7]
def baseStart_8366453 : Nat := 118140960795 + 8366453 * 2 ^ 59
def prefixEnd_8366453 : Nat := 4983230072969 + 3 ^ 40 * 8366453 * 2
def baseEnd_8366453 : Nat := 477334640250095549762321

theorem tailTrace_8366453 : CollatzResearch.WordTrace tailWord_8366453 prefixEnd_8366453 477334640250095549762321 := by
  unfold tailWord_8366453
  simp only [CollatzResearch.WordTrace]
  refine ⟨305149609958777132258848013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203433073305851421505898675 305149609958777132258848013)
  ·
    refine ⟨114431103734541424597068005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305149609958777132258848013 114431103734541424597068005)
    ·
      refine ⟨21455831950226517111950251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114431103734541424597068005 21455831950226517111950251)
      ·
        refine ⟨32183747925339775667925377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21455831950226517111950251 32183747925339775667925377)
        ·
          refine ⟨24137810944004831750944033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32183747925339775667925377 24137810944004831750944033)
          ·
            refine ⟨18103358208003623813208025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24137810944004831750944033 18103358208003623813208025)
            ·
              refine ⟨13577518656002717859906019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18103358208003623813208025 13577518656002717859906019)
              ·
                refine ⟨20366277984004076789859029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13577518656002717859906019 20366277984004076789859029)
                ·
                  refine ⟨477334640250095549762321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20366277984004076789859029 477334640250095549762321)
                  ·
                    rfl

theorem cell23_8366453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 7].length) (baseStart_8366453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366453 prefixEnd_8366453 := by exact prefixLift 8366453
  have htrace : WordTrace (prefixWord ++ tailWord_8366453) baseStart_8366453 baseEnd_8366453 := by
    simpa [prefixWord, tailWord_8366453, baseEnd_8366453] using wordTrace_append hprefix tailTrace_8366453
  have hstable : (prefixWord ++ tailWord_8366453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366453).length < 2 ^ (prefixWord ++ tailWord_8366453).sum := by decide
  have hdescent : baseEnd_8366453 < baseStart_8366453 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366503 : List Nat := [1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 4]
def baseStart_8366503 : Nat := 118140960795 + 8366503 * 2 ^ 59
def prefixEnd_8366503 : Nat := 4983230072969 + 3 ^ 40 * 8366503 * 2
def baseEnd_8366503 : Nat := 4296037436283584752235659

theorem tailTrace_8366503 : CollatzResearch.WordTrace tailWord_8366503 prefixEnd_8366503 4296037436283584752235659 := by
  unfold tailWord_8366503
  simp only [CollatzResearch.WordTrace]
  refine ⟨305151433608595990798168163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203434289072397327198778775 305151433608595990798168163)
  ·
    refine ⟨457727150412893986197252245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305151433608595990798168163 457727150412893986197252245)
    ·
      refine ⟨21455960175604405602996199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 457727150412893986197252245 21455960175604405602996199)
      ·
        refine ⟨32183940263406608404494299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21455960175604405602996199 32183940263406608404494299)
        ·
          refine ⟨48275910395109912606741449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32183940263406608404494299 48275910395109912606741449)
          ·
            refine ⟨36206932796332434455056087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48275910395109912606741449 36206932796332434455056087)
            ·
              refine ⟨54310399194498651682584131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36206932796332434455056087 54310399194498651682584131)
              ·
                refine ⟨81465598791747977523876197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54310399194498651682584131 81465598791747977523876197)
                ·
                  refine ⟨15274799773452745785726787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81465598791747977523876197 15274799773452745785726787)
                  ·
                    refine ⟨22912199660179118678590181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15274799773452745785726787 22912199660179118678590181)
                    ·
                      refine ⟨4296037436283584752235659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22912199660179118678590181 4296037436283584752235659)
                      ·
                        rfl

theorem cell23_8366503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_8366503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366503 prefixEnd_8366503 := by exact prefixLift 8366503
  have htrace : WordTrace (prefixWord ++ tailWord_8366503) baseStart_8366503 baseEnd_8366503 := by
    simpa [prefixWord, tailWord_8366503, baseEnd_8366503] using wordTrace_append hprefix tailTrace_8366503
  have hstable : (prefixWord ++ tailWord_8366503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366503).length < 2 ^ (prefixWord ++ tailWord_8366503).sum := by decide
  have hdescent : baseEnd_8366503 < baseStart_8366503 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366598 : List Nat := [6, 2, 1, 1, 1, 2, 2, 3, 1, 4]
def baseStart_8366598 : Nat := 118140960795 + 8366598 * 2 ^ 59
def prefixEnd_8366598 : Nat := 4983230072969 + 3 ^ 40 * 8366598 * 2
def baseEnd_8366598 : Nat := 1432028738981920626849241

theorem tailTrace_8366598 : CollatzResearch.WordTrace tailWord_8366598 prefixEnd_8366598 1432028738981920626849241 := by
  unfold tailWord_8366598
  simp only [CollatzResearch.WordTrace]
  refine ⟨9536090579476619438214889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 203436599028834548015250965 9536090579476619438214889)
  ·
    refine ⟨7152067934607464578661167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9536090579476619438214889 7152067934607464578661167)
    ·
      refine ⟨10728101901911196867991751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7152067934607464578661167 10728101901911196867991751)
      ·
        refine ⟨16092152852866795301987627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10728101901911196867991751 16092152852866795301987627)
        ·
          refine ⟨24138229279300192952981441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16092152852866795301987627 24138229279300192952981441)
          ·
            refine ⟨18103671959475144714736081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24138229279300192952981441 18103671959475144714736081)
            ·
              refine ⟨13577753969606358536052061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18103671959475144714736081 13577753969606358536052061)
              ·
                refine ⟨5091657738602384451019523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13577753969606358536052061 5091657738602384451019523)
                ·
                  refine ⟨7637486607903576676529285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5091657738602384451019523 7637486607903576676529285)
                  ·
                    refine ⟨1432028738981920626849241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7637486607903576676529285 1432028738981920626849241)
                    ·
                      rfl

theorem cell23_8366598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_8366598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366598 prefixEnd_8366598 := by exact prefixLift 8366598
  have htrace : WordTrace (prefixWord ++ tailWord_8366598) baseStart_8366598 baseEnd_8366598 := by
    simpa [prefixWord, tailWord_8366598, baseEnd_8366598] using wordTrace_append hprefix tailTrace_8366598
  have hstable : (prefixWord ++ tailWord_8366598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366598).length < 2 ^ (prefixWord ++ tailWord_8366598).sum := by decide
  have hdescent : baseEnd_8366598 < baseStart_8366598 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366603 : List Nat := [1, 1, 1, 1, 7, 1, 2, 2, 1, 6]
def baseStart_8366603 : Nat := 118140960795 + 8366603 * 2 ^ 59
def prefixEnd_8366603 : Nat := 4983230072969 + 3 ^ 40 * 8366603 * 2
def baseEnd_8366603 : Nat := 1432029594783011453661733

theorem tailTrace_8366603 : CollatzResearch.WordTrace tailWord_8366603 prefixEnd_8366603 1432029594783011453661733 := by
  unfold tailWord_8366603
  simp only [CollatzResearch.WordTrace]
  refine ⟨305155080908233707876808463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203436720605489138584538975 305155080908233707876808463)
  ·
    refine ⟨457732621362350561815212695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305155080908233707876808463 457732621362350561815212695)
    ·
      refine ⟨686598932043525842722819043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457732621362350561815212695 686598932043525842722819043)
      ·
        refine ⟨1029898398065288764084228565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 686598932043525842722819043 1029898398065288764084228565)
        ·
          refine ⟨24138243704655205408224107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 1029898398065288764084228565 24138243704655205408224107)
          ·
            refine ⟨36207365556982808112336161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24138243704655205408224107 36207365556982808112336161)
            ·
              refine ⟨27155524167737106084252121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36207365556982808112336161 27155524167737106084252121)
              ·
                refine ⟨20366643125802829563189091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27155524167737106084252121 20366643125802829563189091)
                ·
                  refine ⟨30549964688704244344783637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20366643125802829563189091 30549964688704244344783637)
                  ·
                    refine ⟨1432029594783011453661733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30549964688704244344783637 1432029594783011453661733)
                    ·
                      rfl

theorem cell23_8366603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 6].length) (baseStart_8366603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366603 prefixEnd_8366603 := by exact prefixLift 8366603
  have htrace : WordTrace (prefixWord ++ tailWord_8366603) baseStart_8366603 baseEnd_8366603 := by
    simpa [prefixWord, tailWord_8366603, baseEnd_8366603] using wordTrace_append hprefix tailTrace_8366603
  have hstable : (prefixWord ++ tailWord_8366603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366603).length < 2 ^ (prefixWord ++ tailWord_8366603).sum := by decide
  have hdescent : baseEnd_8366603 < baseStart_8366603 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366604 : List Nat := [2, 2, 1, 2, 4, 2, 2, 3, 1, 1, 3]
def baseStart_8366604 : Nat := 118140960795 + 8366604 * 2 ^ 59
def prefixEnd_8366604 : Nat := 4983230072969 + 3 ^ 40 * 8366604 * 2
def baseEnd_8366604 : Nat := 4296089297829688857072695

theorem tailTrace_8366604 : CollatzResearch.WordTrace tailWord_8366604 prefixEnd_8366604 4296089297829688857072695 := by
  unfold tailWord_8366604
  simp only [CollatzResearch.WordTrace]
  refine ⟨152577558690615042523797433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203436744920820056698396577 152577558690615042523797433)
  ·
    refine ⟨114433169017961281892848075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152577558690615042523797433 114433169017961281892848075)
    ·
      refine ⟨171649753526941922839272113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114433169017961281892848075 171649753526941922839272113)
      ·
        refine ⟨128737315145206442129454085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171649753526941922839272113 128737315145206442129454085)
        ·
          refine ⟨24138246589726207899272641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128737315145206442129454085 24138246589726207899272641)
          ·
            refine ⟨18103684942294655924454481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24138246589726207899272641 18103684942294655924454481)
            ·
              refine ⟨13577763706720991943340861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18103684942294655924454481 13577763706720991943340861)
              ·
                refine ⟨5091661390020371978752823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13577763706720991943340861 5091661390020371978752823)
                ·
                  refine ⟨7637492085030557968129235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5091661390020371978752823 7637492085030557968129235)
                  ·
                    refine ⟨11456238127545836952193853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7637492085030557968129235 11456238127545836952193853)
                    ·
                      refine ⟨4296089297829688857072695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11456238127545836952193853 4296089297829688857072695)
                      ·
                        rfl

theorem cell23_8366604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 3, 1, 1, 3].length) (baseStart_8366604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366604 prefixEnd_8366604 := by exact prefixLift 8366604
  have htrace : WordTrace (prefixWord ++ tailWord_8366604) baseStart_8366604 baseEnd_8366604 := by
    simpa [prefixWord, tailWord_8366604, baseEnd_8366604] using wordTrace_append hprefix tailTrace_8366604
  have hstable : (prefixWord ++ tailWord_8366604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366604).length < 2 ^ (prefixWord ++ tailWord_8366604).sum := by decide
  have hdescent : baseEnd_8366604 < baseStart_8366604 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366613 : List Nat := [1, 3, 2, 1, 3, 1, 2, 3, 1, 1, 5]
def baseStart_8366613 : Nat := 118140960795 + 8366613 * 2 ^ 59
def prefixEnd_8366613 : Nat := 4983230072969 + 3 ^ 40 * 8366613 * 2
def baseEnd_8366613 : Nat := 4296093919155579321860153

theorem tailTrace_8366613 : CollatzResearch.WordTrace tailWord_8366613 prefixEnd_8366613 4296093919155579321860153 := by
  unfold tailWord_8366613
  simp only [CollatzResearch.WordTrace]
  refine ⟨305155445638197479584672493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203436963758798319723114995 305155445638197479584672493)
  ·
    refine ⟨114433292114324054844252185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305155445638197479584672493 114433292114324054844252185)
    ·
      refine ⟨85824969085743041133189139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114433292114324054844252185 85824969085743041133189139)
      ·
        refine ⟨128737453628614561699783709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85824969085743041133189139 128737453628614561699783709)
        ·
          refine ⟨48276545110730460637418891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128737453628614561699783709 48276545110730460637418891)
          ·
            refine ⟨72414817666095690956128337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48276545110730460637418891 72414817666095690956128337)
            ·
              refine ⟨54311113249571768217096253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72414817666095690956128337 54311113249571768217096253)
              ·
                refine ⟨20366667468589413081411095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54311113249571768217096253 20366667468589413081411095)
                ·
                  refine ⟨30550001202884119622116643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20366667468589413081411095 30550001202884119622116643)
                  ·
                    refine ⟨45825001804326179433174965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30550001202884119622116643 45825001804326179433174965)
                    ·
                      refine ⟨4296093919155579321860153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45825001804326179433174965 4296093919155579321860153)
                      ·
                        rfl

theorem cell23_8366613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_8366613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366613 prefixEnd_8366613 := by exact prefixLift 8366613
  have htrace : WordTrace (prefixWord ++ tailWord_8366613) baseStart_8366613 baseEnd_8366613 := by
    simpa [prefixWord, tailWord_8366613, baseEnd_8366613] using wordTrace_append hprefix tailTrace_8366613
  have hstable : (prefixWord ++ tailWord_8366613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366613).length < 2 ^ (prefixWord ++ tailWord_8366613).sum := by decide
  have hdescent : baseEnd_8366613 < baseStart_8366613 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366620 : List Nat := [2, 2, 3, 1, 2, 3, 1, 1, 4, 4]
def baseStart_8366620 : Nat := 118140960795 + 8366620 * 2 ^ 59
def prefixEnd_8366620 : Nat := 4983230072969 + 3 ^ 40 * 8366620 * 2
def baseEnd_8366620 : Nat := 1432032504506720264824207

theorem tailTrace_8366620 : CollatzResearch.WordTrace tailWord_8366620 prefixEnd_8366620 1432032504506720264824207 := by
  unfold tailWord_8366620
  simp only [CollatzResearch.WordTrace]
  refine ⟨152577850474586059890088657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203437133966114746520118209 152577850474586059890088657)
  ·
    refine ⟨114433387855939544917566493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152577850474586059890088657 114433387855939544917566493)
    ·
      refine ⟨42912520445977329344087435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114433387855939544917566493 42912520445977329344087435)
      ·
        refine ⟨64368780668965994016131153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42912520445977329344087435 64368780668965994016131153)
        ·
          refine ⟨48276585501724495512098365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64368780668965994016131153 48276585501724495512098365)
          ·
            refine ⟨18103719563146685817036887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48276585501724495512098365 18103719563146685817036887)
            ·
              refine ⟨27155579344720028725555331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18103719563146685817036887 27155579344720028725555331)
              ·
                refine ⟨40733369017080043088332997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27155579344720028725555331 40733369017080043088332997)
                ·
                  refine ⟨7637506690702508079062437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40733369017080043088332997 7637506690702508079062437)
                  ·
                    refine ⟨1432032504506720264824207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7637506690702508079062437 1432032504506720264824207)
                    ·
                      rfl

theorem cell23_8366620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_8366620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366620 prefixEnd_8366620 := by exact prefixLift 8366620
  have htrace : WordTrace (prefixWord ++ tailWord_8366620) baseStart_8366620 baseEnd_8366620 := by
    simpa [prefixWord, tailWord_8366620, baseEnd_8366620] using wordTrace_append hprefix tailTrace_8366620
  have hstable : (prefixWord ++ tailWord_8366620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366620).length < 2 ^ (prefixWord ++ tailWord_8366620).sum := by decide
  have hdescent : baseEnd_8366620 < baseStart_8366620 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366627 : List Nat := [1, 1, 1, 4, 4, 1, 1, 3, 3, 2, 2]
def baseStart_8366627 : Nat := 118140960795 + 8366627 * 2 ^ 59
def prefixEnd_8366627 : Nat := 4983230072969 + 3 ^ 40 * 8366627 * 2
def baseEnd_8366627 : Nat := 4296101107884742267085089

theorem tailTrace_8366627 : CollatzResearch.WordTrace tailWord_8366627 prefixEnd_8366627 4296101107884742267085089 := by
  unfold tailWord_8366627
  simp only [CollatzResearch.WordTrace]
  refine ⟨305155956260146759975682135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203437304173431173317121423 305155956260146759975682135)
  ·
    refine ⟨457733934390220139963523203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305155956260146759975682135 457733934390220139963523203)
    ·
      refine ⟨686600901585330209945284805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457733934390220139963523203 686600901585330209945284805)
      ·
        refine ⟨128737669047249414364740901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 686600901585330209945284805 128737669047249414364740901)
        ·
          refine ⟨24138312946359265193388919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128737669047249414364740901 24138312946359265193388919)
          ·
            refine ⟨36207469419538897790083379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24138312946359265193388919 36207469419538897790083379)
            ·
              refine ⟨54311204129308346685125069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36207469419538897790083379 54311204129308346685125069)
              ·
                refine ⟨20366701548490630006921901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54311204129308346685125069 20366701548490630006921901)
                ·
                  refine ⟨7637513080683986252595713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20366701548490630006921901 7637513080683986252595713)
                  ·
                    refine ⟨5728134810512989689446785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7637513080683986252595713 5728134810512989689446785)
                    ·
                      refine ⟨4296101107884742267085089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5728134810512989689446785 4296101107884742267085089)
                      ·
                        rfl

theorem cell23_8366627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 3, 2, 2].length) (baseStart_8366627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366627 prefixEnd_8366627 := by exact prefixLift 8366627
  have htrace : WordTrace (prefixWord ++ tailWord_8366627) baseStart_8366627 baseEnd_8366627 := by
    simpa [prefixWord, tailWord_8366627, baseEnd_8366627] using wordTrace_append hprefix tailTrace_8366627
  have hstable : (prefixWord ++ tailWord_8366627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366627).length < 2 ^ (prefixWord ++ tailWord_8366627).sum := by decide
  have hdescent : baseEnd_8366627 < baseStart_8366627 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366650 : List Nat := [3, 1, 1, 1, 3, 5, 2, 7]
def baseStart_8366650 : Nat := 118140960795 + 8366650 * 2 ^ 59
def prefixEnd_8366650 : Nat := 4983230072969 + 3 ^ 40 * 8366650 * 2
def baseEnd_8366650 : Nat := 159115293257029469522129

theorem tailTrace_8366650 : CollatzResearch.WordTrace tailWord_8366650 prefixEnd_8366650 159115293257029469522129 := by
  unfold tailWord_8366650
  simp only [CollatzResearch.WordTrace]
  refine ⟨76289198784765858725942351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203437863426042289935846269 76289198784765858725942351)
  ·
    refine ⟨114433798177148788088913527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76289198784765858725942351 114433798177148788088913527)
    ·
      refine ⟨171650697265723182133370291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114433798177148788088913527 171650697265723182133370291)
      ·
        refine ⟨257476045898584773200055437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171650697265723182133370291 257476045898584773200055437)
        ·
          refine ⟨96553517211969289950020789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257476045898584773200055437 96553517211969289950020789)
          ·
            refine ⟨9051892238622120932814449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96553517211969289950020789 9051892238622120932814449)
            ·
              refine ⟨6788919178966590699610837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9051892238622120932814449 6788919178966590699610837)
              ·
                refine ⟨159115293257029469522129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6788919178966590699610837 159115293257029469522129)
                ·
                  rfl

theorem cell23_8366650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 7].length) (baseStart_8366650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366650 prefixEnd_8366650 := by exact prefixLift 8366650
  have htrace : WordTrace (prefixWord ++ tailWord_8366650) baseStart_8366650 baseEnd_8366650 := by
    simpa [prefixWord, tailWord_8366650, baseEnd_8366650] using wordTrace_append hprefix tailTrace_8366650
  have hstable : (prefixWord ++ tailWord_8366650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366650).length < 2 ^ (prefixWord ++ tailWord_8366650).sum := by decide
  have hdescent : baseEnd_8366650 < baseStart_8366650 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366661 : List Nat := [1, 3, 1, 1, 1, 7, 1, 3, 1, 2, 2]
def baseStart_8366661 : Nat := 118140960795 + 8366661 * 2 ^ 59
def prefixEnd_8366661 : Nat := 4983230072969 + 3 ^ 40 * 8366661 * 2
def baseEnd_8366661 : Nat := 4296118566226995134059933

theorem tailTrace_8366661 : CollatzResearch.WordTrace tailWord_8366661 prefixEnd_8366661 4296118566226995134059933 := by
  unfold tailWord_8366661
  simp only [CollatzResearch.WordTrace]
  refine ⟨305157196342023583782419837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203438130894682389188279891 305157196342023583782419837)
  ·
    refine ⟨114433948628258843918407439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305157196342023583782419837 114433948628258843918407439)
    ·
      refine ⟨171650922942388265877611159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114433948628258843918407439 171650922942388265877611159)
      ·
        refine ⟨257476384413582398816416739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171650922942388265877611159 257476384413582398816416739)
        ·
          refine ⟨386214576620373598224625109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257476384413582398816416739 386214576620373598224625109)
          ·
            refine ⟨9051904139540006208389651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 386214576620373598224625109 9051904139540006208389651)
            ·
              refine ⟨13577856209310009312584477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9051904139540006208389651 13577856209310009312584477)
              ·
                refine ⟨5091696078491253492219179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13577856209310009312584477 5091696078491253492219179)
                ·
                  refine ⟨7637544117736880238328769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5091696078491253492219179 7637544117736880238328769)
                  ·
                    refine ⟨5728158088302660178746577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7637544117736880238328769 5728158088302660178746577)
                    ·
                      refine ⟨4296118566226995134059933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5728158088302660178746577 4296118566226995134059933)
                      ·
                        rfl

theorem cell23_8366661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 3, 1, 2, 2].length) (baseStart_8366661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366661 prefixEnd_8366661 := by exact prefixLift 8366661
  have htrace : WordTrace (prefixWord ++ tailWord_8366661) baseStart_8366661 baseEnd_8366661 := by
    simpa [prefixWord, tailWord_8366661, baseEnd_8366661] using wordTrace_append hprefix tailTrace_8366661
  have hstable : (prefixWord ++ tailWord_8366661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366661).length < 2 ^ (prefixWord ++ tailWord_8366661).sum := by decide
  have hdescent : baseEnd_8366661 < baseStart_8366661 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366703 : List Nat := [1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 5]
def baseStart_8366703 : Nat := 118140960795 + 8366703 * 2 ^ 59
def prefixEnd_8366703 : Nat := 4983230072969 + 3 ^ 40 * 8366703 * 2
def baseEnd_8366703 : Nat := 4296140132414483969734739

theorem tailTrace_8366703 : CollatzResearch.WordTrace tailWord_8366703 prefixEnd_8366703 4296140132414483969734739 := by
  unfold tailWord_8366703
  simp only [CollatzResearch.WordTrace]
  refine ⟨305158728207871424955448763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203439152138580949970299175 305158728207871424955448763)
  ·
    refine ⟨457738092311807137433173145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305158728207871424955448763 457738092311807137433173145)
    ·
      refine ⟨343303569233855353074879859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457738092311807137433173145 343303569233855353074879859)
      ·
        refine ⟨514955353850783029612319789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343303569233855353074879859 514955353850783029612319789)
        ·
          refine ⟨193108257694043636104619921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 514955353850783029612319789 193108257694043636104619921)
          ·
            refine ⟨144831193270532727078464941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193108257694043636104619921 144831193270532727078464941)
            ·
              refine ⟨54311697476449772654424353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144831193270532727078464941 54311697476449772654424353)
              ·
                refine ⟨40733773107337329490818265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54311697476449772654424353 40733773107337329490818265)
                ·
                  refine ⟨30550329830502997118113699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40733773107337329490818265 30550329830502997118113699)
                  ·
                    refine ⟨45825494745754495677170549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30550329830502997118113699 45825494745754495677170549)
                    ·
                      refine ⟨4296140132414483969734739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45825494745754495677170549 4296140132414483969734739)
                      ·
                        rfl

theorem cell23_8366703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 5].length) (baseStart_8366703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366703 prefixEnd_8366703 := by exact prefixLift 8366703
  have htrace : WordTrace (prefixWord ++ tailWord_8366703) baseStart_8366703 baseEnd_8366703 := by
    simpa [prefixWord, tailWord_8366703, baseEnd_8366703] using wordTrace_append hprefix tailTrace_8366703
  have hstable : (prefixWord ++ tailWord_8366703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366703).length < 2 ^ (prefixWord ++ tailWord_8366703).sum := by decide
  have hdescent : baseEnd_8366703 < baseStart_8366703 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366785 : List Nat := [1, 2, 6, 2, 1, 2, 1, 2, 2, 2, 2]
def baseStart_8366785 : Nat := 118140960795 + 8366785 * 2 ^ 59
def prefixEnd_8366785 : Nat := 4983230072969 + 3 ^ 40 * 8366785 * 2
def baseEnd_8366785 : Nat := 4296182237828152648909363

theorem tailTrace_8366785 : CollatzResearch.WordTrace tailWord_8366785 prefixEnd_8366785 4296182237828152648909363 := by
  unfold tailWord_8366785
  simp only [CollatzResearch.WordTrace]
  refine ⟨305161718993574352959933809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203441145995716235306622539 305161718993574352959933809)
  ·
    refine ⟨228871289245180764719950357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305161718993574352959933809 228871289245180764719950357)
    ·
      refine ⟨10728341683367848346247673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 228871289245180764719950357 10728341683367848346247673)
      ·
        refine ⟨8046256262525886259685755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10728341683367848346247673 8046256262525886259685755)
        ·
          refine ⟨12069384393788829389528633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8046256262525886259685755 12069384393788829389528633)
          ·
            refine ⟨9052038295341622042146475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12069384393788829389528633 9052038295341622042146475)
            ·
              refine ⟨13578057443012433063219713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9052038295341622042146475 13578057443012433063219713)
              ·
                refine ⟨10183543082259324797414785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13578057443012433063219713 10183543082259324797414785)
                ·
                  refine ⟨7637657311694493598061089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10183543082259324797414785 7637657311694493598061089)
                  ·
                    refine ⟨5728242983770870198545817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7637657311694493598061089 5728242983770870198545817)
                    ·
                      refine ⟨4296182237828152648909363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5728242983770870198545817 4296182237828152648909363)
                      ·
                        rfl

theorem cell23_8366785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_8366785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366785 prefixEnd_8366785 := by exact prefixLift 8366785
  have htrace : WordTrace (prefixWord ++ tailWord_8366785) baseStart_8366785 baseEnd_8366785 := by
    simpa [prefixWord, tailWord_8366785, baseEnd_8366785] using wordTrace_append hprefix tailTrace_8366785
  have hstable : (prefixWord ++ tailWord_8366785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366785).length < 2 ^ (prefixWord ++ tailWord_8366785).sum := by decide
  have hdescent : baseEnd_8366785 < baseStart_8366785 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366807 : List Nat := [1, 1, 3, 2, 1, 4, 2, 1, 2, 4, 2]
def baseStart_8366807 : Nat := 118140960795 + 8366807 * 2 ^ 59
def prefixEnd_8366807 : Nat := 4983230072969 + 3 ^ 40 * 8366807 * 2
def baseEnd_8366807 : Nat := 4296193534402551562834261

theorem tailTrace_8366807 : CollatzResearch.WordTrace tailWord_8366807 prefixEnd_8366807 4296193534402551562834261 := by
  unfold tailWord_8366807
  simp only [CollatzResearch.WordTrace]
  refine ⟨305162521399494650717234675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203441680932996433811489783 305162521399494650717234675)
  ·
    refine ⟨457743782099241976075852013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305162521399494650717234675 457743782099241976075852013)
    ·
      refine ⟨171653918287215741028444505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 457743782099241976075852013 171653918287215741028444505)
      ·
        refine ⟨128740438715411805771333379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171653918287215741028444505 128740438715411805771333379)
        ·
          refine ⟨193110658073117708657000069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128740438715411805771333379 193110658073117708657000069)
          ·
            refine ⟨36208248388709570373187513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 193110658073117708657000069 36208248388709570373187513)
            ·
              refine ⟨27156186291532177779890635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36208248388709570373187513 27156186291532177779890635)
              ·
                refine ⟨40734279437298266669835953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27156186291532177779890635 40734279437298266669835953)
                ·
                  refine ⟨30550709577973700002376965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40734279437298266669835953 30550709577973700002376965)
                  ·
                    refine ⟨5728258045870068750445681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30550709577973700002376965 5728258045870068750445681)
                    ·
                      refine ⟨4296193534402551562834261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5728258045870068750445681 4296193534402551562834261)
                      ·
                        rfl

theorem cell23_8366807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 4, 2].length) (baseStart_8366807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366807 prefixEnd_8366807 := by exact prefixLift 8366807
  have htrace : WordTrace (prefixWord ++ tailWord_8366807) baseStart_8366807 baseEnd_8366807 := by
    simpa [prefixWord, tailWord_8366807, baseEnd_8366807] using wordTrace_append hprefix tailTrace_8366807
  have hstable : (prefixWord ++ tailWord_8366807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366807).length < 2 ^ (prefixWord ++ tailWord_8366807).sum := by decide
  have hdescent : baseEnd_8366807 < baseStart_8366807 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366810 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 3, 4, 3]
def baseStart_8366810 : Nat := 118140960795 + 8366810 * 2 ^ 59
def prefixEnd_8366810 : Nat := 4983230072969 + 3 ^ 40 * 8366810 * 2
def baseEnd_8366810 : Nat := 4296195074844515051096747

theorem tailTrace_8366810 : CollatzResearch.WordTrace tailWord_8366810 prefixEnd_8366810 4296195074844515051096747 := by
  unfold tailWord_8366810
  simp only [CollatzResearch.WordTrace]
  refine ⟨76290657704620945557398471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203441753878989188153062589 76290657704620945557398471)
  ·
    refine ⟨114435986556931418336097707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76290657704620945557398471 114435986556931418336097707)
    ·
      refine ⟨171653979835397127504146561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114435986556931418336097707 171653979835397127504146561)
      ·
        refine ⟨128740484876547845628109921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171653979835397127504146561 128740484876547845628109921)
        ·
          refine ⟨96555363657410884221082441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128740484876547845628109921 96555363657410884221082441)
          ·
            refine ⟨72416522743058163165811831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96555363657410884221082441 72416522743058163165811831)
            ·
              refine ⟨108624784114587244748717747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72416522743058163165811831 108624784114587244748717747)
              ·
                refine ⟨162937176171880867123076621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108624784114587244748717747 162937176171880867123076621)
                ·
                  refine ⟨61101441064455325171153733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162937176171880867123076621 61101441064455325171153733)
                  ·
                    refine ⟨11456520199585373469591325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61101441064455325171153733 11456520199585373469591325)
                    ·
                      refine ⟨4296195074844515051096747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11456520199585373469591325 4296195074844515051096747)
                      ·
                        rfl

theorem cell23_8366810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 3, 4, 3].length) (baseStart_8366810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366810 prefixEnd_8366810 := by exact prefixLift 8366810
  have htrace : WordTrace (prefixWord ++ tailWord_8366810) baseStart_8366810 baseEnd_8366810 := by
    simpa [prefixWord, tailWord_8366810, baseEnd_8366810] using wordTrace_append hprefix tailTrace_8366810
  have hstable : (prefixWord ++ tailWord_8366810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366810).length < 2 ^ (prefixWord ++ tailWord_8366810).sum := by decide
  have hdescent : baseEnd_8366810 < baseStart_8366810 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366817 : List Nat := [1, 2, 3, 1, 4, 1, 2, 2, 3, 4]
def baseStart_8366817 : Nat := 118140960795 + 8366817 * 2 ^ 59
def prefixEnd_8366817 : Nat := 4983230072969 + 3 ^ 40 * 8366817 * 2
def baseEnd_8366817 : Nat := 1432066223069698841236405

theorem tailTrace_8366817 : CollatzResearch.WordTrace tailWord_8366817 prefixEnd_8366817 1432066223069698841236405 := by
  unfold tailWord_8366817
  simp only [CollatzResearch.WordTrace]
  refine ⟨305162886129458422425098705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203441924086305614950065803 305162886129458422425098705)
  ·
    refine ⟨228872164597093816818824029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305162886129458422425098705 228872164597093816818824029)
    ·
      refine ⟨85827061723910181307059011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228872164597093816818824029 85827061723910181307059011)
      ·
        refine ⟨128740592585865271960588517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85827061723910181307059011 128740592585865271960588517)
        ·
          refine ⟨24138861109849738492610347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128740592585865271960588517 24138861109849738492610347)
          ·
            refine ⟨36208291664774607738915521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24138861109849738492610347 36208291664774607738915521)
            ·
              refine ⟨27156218748580955804186641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36208291664774607738915521 27156218748580955804186641)
              ·
                refine ⟨20367164061435716853139981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27156218748580955804186641 20367164061435716853139981)
                ·
                  refine ⟨7637686523038393819927493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20367164061435716853139981 7637686523038393819927493)
                  ·
                    refine ⟨1432066223069698841236405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7637686523038393819927493 1432066223069698841236405)
                    ·
                      rfl

theorem cell23_8366817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 3, 4].length) (baseStart_8366817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366817 prefixEnd_8366817 := by exact prefixLift 8366817
  have htrace : WordTrace (prefixWord ++ tailWord_8366817) baseStart_8366817 baseEnd_8366817 := by
    simpa [prefixWord, tailWord_8366817, baseEnd_8366817] using wordTrace_append hprefix tailTrace_8366817
  have hstable : (prefixWord ++ tailWord_8366817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366817).length < 2 ^ (prefixWord ++ tailWord_8366817).sum := by decide
  have hdescent : baseEnd_8366817 < baseStart_8366817 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366830 : List Nat := [4, 1, 2, 1, 1, 3, 1, 2, 8]
def baseStart_8366830 : Nat := 118140960795 + 8366830 * 2 ^ 59
def prefixEnd_8366830 : Nat := 4983230072969 + 3 ^ 40 * 8366830 * 2
def baseEnd_8366830 : Nat := 477356149384178330316295

theorem tailTrace_8366830 : CollatzResearch.WordTrace tailWord_8366830 prefixEnd_8366830 477356149384178330316295 := by
  unfold tailWord_8366830
  simp only [CollatzResearch.WordTrace]
  refine ⟨38145420034801415705665243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203442240185607550430214629 38145420034801415705665243)
  ·
    refine ⟨57218130052202123558497865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38145420034801415705665243 57218130052202123558497865)
    ·
      refine ⟨42913597539151592668873399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57218130052202123558497865 42913597539151592668873399)
      ·
        refine ⟨64370396308727389003310099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42913597539151592668873399 64370396308727389003310099)
        ·
          refine ⟨96555594463091083504965149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64370396308727389003310099 96555594463091083504965149)
          ·
            refine ⟨36208347923659156314361931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96555594463091083504965149 36208347923659156314361931)
            ·
              refine ⟨54312521885488734471542897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36208347923659156314361931 54312521885488734471542897)
              ·
                refine ⟨40734391414116550853657173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54312521885488734471542897 40734391414116550853657173)
                ·
                  refine ⟨477356149384178330316295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40734391414116550853657173 477356149384178330316295)
                  ·
                    rfl

theorem cell23_8366830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 8].length) (baseStart_8366830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366830 prefixEnd_8366830 := by exact prefixLift 8366830
  have htrace : WordTrace (prefixWord ++ tailWord_8366830) baseStart_8366830 baseEnd_8366830 := by
    simpa [prefixWord, tailWord_8366830, baseEnd_8366830] using wordTrace_append hprefix tailTrace_8366830
  have hstable : (prefixWord ++ tailWord_8366830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366830).length < 2 ^ (prefixWord ++ tailWord_8366830).sum := by decide
  have hdescent : baseEnd_8366830 < baseStart_8366830 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366843 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 1, 11]
def baseStart_8366843 : Nat := 118140960795 + 8366843 * 2 ^ 59
def prefixEnd_8366843 : Nat := 4983230072969 + 3 ^ 40 * 8366843 * 2
def baseEnd_8366843 : Nat := 1432070673235371140661365

theorem tailTrace_8366843 : CollatzResearch.WordTrace tailWord_8366843 prefixEnd_8366843 1432070673235371140661365 := by
  unfold tailWord_8366843
  simp only [CollatzResearch.WordTrace]
  refine ⟨305163834427364228865545183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203442556284909485910363455 305163834427364228865545183)
  ·
    refine ⟨457745751641046343298317775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305163834427364228865545183 457745751641046343298317775)
    ·
      refine ⟨686618627461569514947476663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457745751641046343298317775 686618627461569514947476663)
      ·
        refine ⟨1029927941192354272421214995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 686618627461569514947476663 1029927941192354272421214995)
        ·
          refine ⟨1544891911788531408631822493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1029927941192354272421214995 1544891911788531408631822493)
          ·
            refine ⟨579334466920699278236933435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1544891911788531408631822493 579334466920699278236933435)
            ·
              refine ⟨869001700381048917355400153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579334466920699278236933435 869001700381048917355400153)
              ·
                refine ⟨651751275285786688016550115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 869001700381048917355400153 651751275285786688016550115)
                ·
                  refine ⟨977626912928680032024825173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 651751275285786688016550115 977626912928680032024825173)
                  ·
                    refine ⟨1432070673235371140661365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 977626912928680032024825173 1432070673235371140661365)
                    ·
                      rfl

theorem cell23_8366843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 11].length) (baseStart_8366843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366843 prefixEnd_8366843 := by exact prefixLift 8366843
  have htrace : WordTrace (prefixWord ++ tailWord_8366843) baseStart_8366843 baseEnd_8366843 := by
    simpa [prefixWord, tailWord_8366843, baseEnd_8366843] using wordTrace_append hprefix tailTrace_8366843
  have hstable : (prefixWord ++ tailWord_8366843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366843).length < 2 ^ (prefixWord ++ tailWord_8366843).sum := by decide
  have hdescent : baseEnd_8366843 < baseStart_8366843 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366860 : List Nat := [2, 2, 1, 2, 2, 1, 1, 4, 3, 5]
def baseStart_8366860 : Nat := 118140960795 + 8366860 * 2 ^ 59
def prefixEnd_8366860 : Nat := 4983230072969 + 3 ^ 40 * 8366860 * 2
def baseEnd_8366860 : Nat := 1432073582959079951823839

theorem tailTrace_8366860 : CollatzResearch.WordTrace tailWord_8366860 prefixEnd_8366860 1432073582959079951823839 := by
  unfold tailWord_8366860
  simp only [CollatzResearch.WordTrace]
  refine ⟨152582227234151320384457017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203442969645535093845942689 152582227234151320384457017)
  ·
    refine ⟨114436670425613490288342763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152582227234151320384457017 114436670425613490288342763)
    ·
      refine ⟨171655005638420235432514145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114436670425613490288342763 171655005638420235432514145)
      ·
        refine ⟨128741254228815176574385609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171655005638420235432514145 128741254228815176574385609)
        ·
          refine ⟨96555940671611382430789207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128741254228815176574385609 96555940671611382430789207)
          ·
            refine ⟨144833911007417073646183811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96555940671611382430789207 144833911007417073646183811)
            ·
              refine ⟨217250866511125610469275717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144833911007417073646183811 217250866511125610469275717)
              ·
                refine ⟨40734537470836051962989197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 217250866511125610469275717 40734537470836051962989197)
                ·
                  refine ⟨15275451551563519486120949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40734537470836051962989197 15275451551563519486120949)
                  ·
                    refine ⟨1432073582959079951823839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15275451551563519486120949 1432073582959079951823839)
                    ·
                      rfl

theorem cell23_8366860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 3, 5].length) (baseStart_8366860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366860 prefixEnd_8366860 := by exact prefixLift 8366860
  have htrace : WordTrace (prefixWord ++ tailWord_8366860) baseStart_8366860 baseEnd_8366860 := by
    simpa [prefixWord, tailWord_8366860, baseEnd_8366860] using wordTrace_append hprefix tailTrace_8366860
  have hstable : (prefixWord ++ tailWord_8366860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366860).length < 2 ^ (prefixWord ++ tailWord_8366860).sum := by decide
  have hdescent : baseEnd_8366860 < baseStart_8366860 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366867 : List Nat := [1, 1, 1, 2, 1, 3, 3, 2, 4, 3, 2]
def baseStart_8366867 : Nat := 118140960795 + 8366867 * 2 ^ 59
def prefixEnd_8366867 : Nat := 4983230072969 + 3 ^ 40 * 8366867 * 2
def baseEnd_8366867 : Nat := 4296224343241821328083985

theorem tailTrace_8366867 : CollatzResearch.WordTrace tailWord_8366867 prefixEnd_8366867 4296224343241821328083985 := by
  unfold tailWord_8366867
  simp only [CollatzResearch.WordTrace]
  refine ⟨305164709779277280964418855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203443139852851520642945903 305164709779277280964418855)
  ·
    refine ⟨457747064668915921446628283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305164709779277280964418855 457747064668915921446628283)
    ·
      refine ⟨686620597003373882169942425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457747064668915921446628283 686620597003373882169942425)
      ·
        refine ⟨514965447752530411627456819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 686620597003373882169942425 514965447752530411627456819)
        ·
          refine ⟨772448171628795617441185229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514965447752530411627456819 772448171628795617441185229)
          ·
            refine ⟨289668064360798356540444461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 772448171628795617441185229 289668064360798356540444461)
            ·
              refine ⟨108625524135299383702666673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 289668064360798356540444461 108625524135299383702666673)
              ·
                refine ⟨81469143101474537777000005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108625524135299383702666673 81469143101474537777000005)
                ·
                  refine ⟨15275464331526475833187501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81469143101474537777000005 15275464331526475833187501)
                  ·
                    refine ⟨5728299124322428437445313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15275464331526475833187501 5728299124322428437445313)
                    ·
                      refine ⟨4296224343241821328083985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5728299124322428437445313 4296224343241821328083985)
                      ·
                        rfl

theorem cell23_8366867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 3, 2].length) (baseStart_8366867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366867 prefixEnd_8366867 := by exact prefixLift 8366867
  have htrace : WordTrace (prefixWord ++ tailWord_8366867) baseStart_8366867 baseEnd_8366867 := by
    simpa [prefixWord, tailWord_8366867, baseEnd_8366867] using wordTrace_append hprefix tailTrace_8366867
  have hstable : (prefixWord ++ tailWord_8366867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366867).length < 2 ^ (prefixWord ++ tailWord_8366867).sum := by decide
  have hdescent : baseEnd_8366867 < baseStart_8366867 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366902 : List Nat := [5, 1, 2, 2, 3, 1, 2, 2, 1, 4]
def baseStart_8366902 : Nat := 118140960795 + 8366902 * 2 ^ 59
def prefixEnd_8366902 : Nat := 4983230072969 + 3 ^ 40 * 8366902 * 2
def baseEnd_8366902 : Nat := 1432080771688242897048775

theorem tailTrace_8366902 : CollatzResearch.WordTrace tailWord_8366902 prefixEnd_8366902 1432080771688242897048775 := by
  unfold tailWord_8366902
  simp only [CollatzResearch.WordTrace]
  refine ⟨19072874145884405121371435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203443990889433654627961973 19072874145884405121371435)
  ·
    refine ⟨28609311218826607682057153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19072874145884405121371435 28609311218826607682057153)
    ·
      refine ⟨21456983414119955761542865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28609311218826607682057153 21456983414119955761542865)
      ·
        refine ⟨16092737560589966821157149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21456983414119955761542865 16092737560589966821157149)
        ·
          refine ⟨6034776585221237557933931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16092737560589966821157149 6034776585221237557933931)
          ·
            refine ⟨9052164877831856336900897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6034776585221237557933931 9052164877831856336900897)
            ·
              refine ⟨6789123658373892252675673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9052164877831856336900897 6789123658373892252675673)
              ·
                refine ⟨5091842743780419189506755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6789123658373892252675673 5091842743780419189506755)
                ·
                  refine ⟨7637764115670628784260133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5091842743780419189506755 7637764115670628784260133)
                  ·
                    refine ⟨1432080771688242897048775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7637764115670628784260133 1432080771688242897048775)
                    ·
                      rfl

theorem cell23_8366902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_8366902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366902 prefixEnd_8366902 := by exact prefixLift 8366902
  have htrace : WordTrace (prefixWord ++ tailWord_8366902) baseStart_8366902 baseEnd_8366902 := by
    simpa [prefixWord, tailWord_8366902, baseEnd_8366902] using wordTrace_append hprefix tailTrace_8366902
  have hstable : (prefixWord ++ tailWord_8366902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366902).length < 2 ^ (prefixWord ++ tailWord_8366902).sum := by decide
  have hdescent : baseEnd_8366902 < baseStart_8366902 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366924 : List Nat := [2, 2, 1, 3, 3, 1, 2, 3, 2, 4]
def baseStart_8366924 : Nat := 118140960795 + 8366924 * 2 ^ 59
def prefixEnd_8366924 : Nat := 4983230072969 + 3 ^ 40 * 8366924 * 2
def baseEnd_8366924 : Nat := 1432084537213042535023741

theorem tailTrace_8366924 : CollatzResearch.WordTrace tailWord_8366924 prefixEnd_8366924 1432084537213042535023741 := by
  unfold tailWord_8366924
  simp only [CollatzResearch.WordTrace]
  refine ⟨152583394370035389849621913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203444525826713853132829217 152583394370035389849621913)
  ·
    refine ⟨114437545777526542387216435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152583394370035389849621913 114437545777526542387216435)
    ·
      refine ⟨171656318666289813580824653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114437545777526542387216435 171656318666289813580824653)
      ·
        refine ⟨64371119499858680092809245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171656318666289813580824653 64371119499858680092809245)
        ·
          refine ⟨24139169812447005034803467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64371119499858680092809245 24139169812447005034803467)
          ·
            refine ⟨36208754718670507552205201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24139169812447005034803467 36208754718670507552205201)
            ·
              refine ⟨27156566039002880664153901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36208754718670507552205201 27156566039002880664153901)
              ·
                refine ⟨10183712264626080249057713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27156566039002880664153901 10183712264626080249057713)
                ·
                  refine ⟨7637784198469560186793285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10183712264626080249057713 7637784198469560186793285)
                  ·
                    refine ⟨1432084537213042535023741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7637784198469560186793285 1432084537213042535023741)
                    ·
                      rfl

theorem cell23_8366924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 2, 4].length) (baseStart_8366924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366924 prefixEnd_8366924 := by exact prefixLift 8366924
  have htrace : WordTrace (prefixWord ++ tailWord_8366924) baseStart_8366924 baseEnd_8366924 := by
    simpa [prefixWord, tailWord_8366924, baseEnd_8366924] using wordTrace_append hprefix tailTrace_8366924
  have hstable : (prefixWord ++ tailWord_8366924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366924).length < 2 ^ (prefixWord ++ tailWord_8366924).sum := by decide
  have hdescent : baseEnd_8366924 < baseStart_8366924 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366937 : List Nat := [1, 2, 1, 2, 2, 5, 3, 7]
def baseStart_8366937 : Nat := 118140960795 + 8366937 * 2 ^ 59
def prefixEnd_8366937 : Nat := 4983230072969 + 3 ^ 40 * 8366937 * 2
def baseEnd_8366937 : Nat := 159120751366208742748469

theorem tailTrace_8366937 : CollatzResearch.WordTrace tailWord_8366937 prefixEnd_8366937 159120751366208742748469 := by
  unfold tailWord_8366937
  simp only [CollatzResearch.WordTrace]
  refine ⟨305167262889023682919467065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203444841926015788612978043 305167262889023682919467065)
  ·
    refine ⟨228875447166767762189600299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305167262889023682919467065 228875447166767762189600299)
    ·
      refine ⟨343313170750151643284400449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228875447166767762189600299 343313170750151643284400449)
      ·
        refine ⟨257484878062613732463300337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343313170750151643284400449 257484878062613732463300337)
        ·
          refine ⟨193113658546960299347475253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257484878062613732463300337 193113658546960299347475253)
          ·
            refine ⟨18104405488777528063825805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 193113658546960299347475253 18104405488777528063825805)
            ·
              refine ⟨6789152058291573023934677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18104405488777528063825805 6789152058291573023934677)
              ·
                refine ⟨159120751366208742748469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6789152058291573023934677 159120751366208742748469)
                ·
                  rfl

theorem cell23_8366937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 7].length) (baseStart_8366937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366937 prefixEnd_8366937 := by exact prefixLift 8366937
  have htrace : WordTrace (prefixWord ++ tailWord_8366937) baseStart_8366937 baseEnd_8366937 := by
    simpa [prefixWord, tailWord_8366937, baseEnd_8366937] using wordTrace_append hprefix tailTrace_8366937
  have hstable : (prefixWord ++ tailWord_8366937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366937).length < 2 ^ (prefixWord ++ tailWord_8366937).sum := by decide
  have hdescent : baseEnd_8366937 < baseStart_8366937 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366948 : List Nat := [2, 3, 1, 1, 4, 1, 1, 5, 1, 2, 2]
def baseStart_8366948 : Nat := 118140960795 + 8366948 * 2 ^ 59
def prefixEnd_8366948 : Nat := 4983230072969 + 3 ^ 40 * 8366948 * 2
def baseEnd_8366948 : Nat := 4296265935174835511171113

theorem tailTrace_8366948 : CollatzResearch.WordTrace tailWord_8366948 prefixEnd_8366948 4296265935174835511171113 := by
  unfold tailWord_8366948
  simp only [CollatzResearch.WordTrace]
  refine ⟨152583832045991915899058749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203445109394655887865411665 152583832045991915899058749)
  ·
    refine ⟨57218937017246968462147031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152583832045991915899058749 57218937017246968462147031)
    ·
      refine ⟨85828405525870452693220547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57218937017246968462147031 85828405525870452693220547)
      ·
        refine ⟨128742608288805679039830821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85828405525870452693220547 128742608288805679039830821)
        ·
          refine ⟨24139239054151064819968279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128742608288805679039830821 24139239054151064819968279)
          ·
            refine ⟨36208858581226597229952419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24139239054151064819968279 36208858581226597229952419)
            ·
              refine ⟨54313287871839895844928629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36208858581226597229952419 54313287871839895844928629)
              ·
                refine ⟨5091870737984990235462059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54313287871839895844928629 5091870737984990235462059)
                ·
                  refine ⟨7637806106977485353193089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5091870737984990235462059 7637806106977485353193089)
                  ·
                    refine ⟨5728354580233114014894817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7637806106977485353193089 5728354580233114014894817)
                    ·
                      refine ⟨4296265935174835511171113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5728354580233114014894817 4296265935174835511171113)
                      ·
                        rfl

theorem cell23_8366948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 5, 1, 2, 2].length) (baseStart_8366948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366948 prefixEnd_8366948 := by exact prefixLift 8366948
  have htrace : WordTrace (prefixWord ++ tailWord_8366948) baseStart_8366948 baseEnd_8366948 := by
    simpa [prefixWord, tailWord_8366948, baseEnd_8366948] using wordTrace_append hprefix tailTrace_8366948
  have hstable : (prefixWord ++ tailWord_8366948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366948).length < 2 ^ (prefixWord ++ tailWord_8366948).sum := by decide
  have hdescent : baseEnd_8366948 < baseStart_8366948 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366951 : List Nat := [1, 1, 5, 1, 2, 2, 4, 1, 1, 2, 3]
def baseStart_8366951 : Nat := 118140960795 + 8366951 * 2 ^ 59
def prefixEnd_8366951 : Nat := 4983230072969 + 3 ^ 40 * 8366951 * 2
def baseEnd_8366951 : Nat := 4296267475616798999433599

theorem tailTrace_8366951 : CollatzResearch.WordTrace tailWord_8366951 prefixEnd_8366951 4296267475616798999433599 := by
  unfold tailWord_8366951
  simp only [CollatzResearch.WordTrace]
  refine ⟨305167773510972963310476707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203445182340648642206984471 305167773510972963310476707)
  ·
    refine ⟨457751660266459444965715061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305167773510972963310476707 457751660266459444965715061)
    ·
      refine ⟨42914218149980572965535787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 457751660266459444965715061 42914218149980572965535787)
      ·
        refine ⟨64371327224970859448303681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42914218149980572965535787 64371327224970859448303681)
        ·
          refine ⟨48278495418728144586227761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64371327224970859448303681 48278495418728144586227761)
          ·
            refine ⟨36208871564046108439670821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48278495418728144586227761 36208871564046108439670821)
            ·
              refine ⟨6789163418258645332438279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36208871564046108439670821 6789163418258645332438279)
              ·
                refine ⟨10183745127387967998657419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6789163418258645332438279 10183745127387967998657419)
                ·
                  refine ⟨15275617691081951997986129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10183745127387967998657419 15275617691081951997986129)
                  ·
                    refine ⟨11456713268311463998489597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15275617691081951997986129 11456713268311463998489597)
                    ·
                      refine ⟨4296267475616798999433599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11456713268311463998489597 4296267475616798999433599)
                      ·
                        rfl

theorem cell23_8366951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_8366951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366951 prefixEnd_8366951 := by exact prefixLift 8366951
  have htrace : WordTrace (prefixWord ++ tailWord_8366951) baseStart_8366951 baseEnd_8366951 := by
    simpa [prefixWord, tailWord_8366951, baseEnd_8366951] using wordTrace_append hprefix tailTrace_8366951
  have hstable : (prefixWord ++ tailWord_8366951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366951).length < 2 ^ (prefixWord ++ tailWord_8366951).sum := by decide
  have hdescent : baseEnd_8366951 < baseStart_8366951 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8366958 : List Nat := [4, 1, 2, 3, 2, 2, 1, 2, 2, 4]
def baseStart_8366958 : Nat := 118140960795 + 8366958 * 2 ^ 59
def prefixEnd_8366958 : Nat := 4983230072969 + 3 ^ 40 * 8366958 * 2
def baseEnd_8366958 : Nat := 1432090356660460157348689

theorem tailTrace_8366958 : CollatzResearch.WordTrace tailWord_8366958 prefixEnd_8366958 1432090356660460157348689 := by
  unfold tailWord_8366958
  simp only [CollatzResearch.WordTrace]
  refine ⟨38146003602743450438247691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203445352547965069003987685 38146003602743450438247691)
  ·
    refine ⟨57219005404115175657371537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38146003602743450438247691 57219005404115175657371537)
    ·
      refine ⟨42914254053086381743028653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57219005404115175657371537 42914254053086381743028653)
      ·
        refine ⟨16092845269907393153635745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42914254053086381743028653 16092845269907393153635745)
        ·
          refine ⟨12069633952430544865226809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16092845269907393153635745 12069633952430544865226809)
          ·
            refine ⟨9052225464322908648920107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12069633952430544865226809 9052225464322908648920107)
            ·
              refine ⟨13578338196484362973380161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9052225464322908648920107 13578338196484362973380161)
              ·
                refine ⟨10183753647363272230035121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13578338196484362973380161 10183753647363272230035121)
                ·
                  refine ⟨7637815235522454172526341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10183753647363272230035121 7637815235522454172526341)
                  ·
                    refine ⟨1432090356660460157348689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7637815235522454172526341 1432090356660460157348689)
                    ·
                      rfl

theorem cell23_8366958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_8366958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8366958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8366958 prefixEnd_8366958 := by exact prefixLift 8366958
  have htrace : WordTrace (prefixWord ++ tailWord_8366958) baseStart_8366958 baseEnd_8366958 := by
    simpa [prefixWord, tailWord_8366958, baseEnd_8366958] using wordTrace_append hprefix tailTrace_8366958
  have hstable : (prefixWord ++ tailWord_8366958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8366958).length < 2 ^ (prefixWord ++ tailWord_8366958).sum := by decide
  have hdescent : baseEnd_8366958 < baseStart_8366958 := by decide
  rcases family_descends (prefixWord ++ tailWord_8366958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367007 : List Nat := [1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 5]
def baseStart_8367007 : Nat := 118140960795 + 8367007 * 2 ^ 59
def prefixEnd_8367007 : Nat := 4983230072969 + 3 ^ 40 * 8367007 * 2
def baseEnd_8367007 : Nat := 4296296230533450780333341

theorem tailTrace_8367007 : CollatzResearch.WordTrace tailWord_8367007 prefixEnd_8367007 4296296230533450780333341 := by
  unfold tailWord_8367007
  simp only [CollatzResearch.WordTrace]
  refine ⟨305169815998770084874515275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203446543999180056583010183 305169815998770084874515275)
  ·
    refine ⟨457754723998155127311772913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305169815998770084874515275 457754723998155127311772913)
    ·
      refine ⟨343316042998616345483829685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457754723998155127311772913 343316042998616345483829685)
      ·
        refine ⟨32185879031120282389109033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 343316042998616345483829685 32185879031120282389109033)
        ·
          refine ⟨24139409273340211791831775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32185879031120282389109033 24139409273340211791831775)
          ·
            refine ⟨36209113910010317687747663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24139409273340211791831775 36209113910010317687747663)
            ·
              refine ⟨54313670865015476531621495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36209113910010317687747663 54313670865015476531621495)
              ·
                refine ⟨81470506297523214797432243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54313670865015476531621495 81470506297523214797432243)
                ·
                  refine ⟨122205759446284822196148365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81470506297523214797432243 122205759446284822196148365)
                  ·
                    refine ⟨45827159792356808323555637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 122205759446284822196148365 45827159792356808323555637)
                    ·
                      refine ⟨4296296230533450780333341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45827159792356808323555637 4296296230533450780333341)
                      ·
                        rfl

theorem cell23_8367007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_8367007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367007 prefixEnd_8367007 := by exact prefixLift 8367007
  have htrace : WordTrace (prefixWord ++ tailWord_8367007) baseStart_8367007 baseEnd_8367007 := by
    simpa [prefixWord, tailWord_8367007, baseEnd_8367007] using wordTrace_append hprefix tailTrace_8367007
  have hstable : (prefixWord ++ tailWord_8367007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367007).length < 2 ^ (prefixWord ++ tailWord_8367007).sum := by decide
  have hdescent : baseEnd_8367007 < baseStart_8367007 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367038 : List Nat := [4, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2]
def baseStart_8367038 : Nat := 118140960795 + 8367038 * 2 ^ 59
def prefixEnd_8367038 : Nat := 4983230072969 + 3 ^ 40 * 8367038 * 2
def baseEnd_8367038 : Nat := 4296312148433740159045699

theorem tailTrace_8367038 : CollatzResearch.WordTrace tailWord_8367038 prefixEnd_8367038 4296312148433740159045699 := by
  unfold tailWord_8367038
  simp only [CollatzResearch.WordTrace]
  refine ⟨38146368332707222146111721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203447297774438518112595845 38146368332707222146111721)
  ·
    refine ⟨28609776249530416609583791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38146368332707222146111721 28609776249530416609583791)
    ·
      refine ⟨42914664374295624914375687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28609776249530416609583791 42914664374295624914375687)
      ·
        refine ⟨64371996561443437371563531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42914664374295624914375687 64371996561443437371563531)
        ·
          refine ⟨96557994842165156057345297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64371996561443437371563531 96557994842165156057345297)
          ·
            refine ⟨72418496131623867043008973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96557994842165156057345297 72418496131623867043008973)
            ·
              refine ⟨27156936049358950141128365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72418496131623867043008973 27156936049358950141128365)
              ·
                refine ⟨10183851018509606302923137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27156936049358950141128365 10183851018509606302923137)
                ·
                  refine ⟨7637888263882204727192353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10183851018509606302923137 7637888263882204727192353)
                  ·
                    refine ⟨5728416197911653545394265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7637888263882204727192353 5728416197911653545394265)
                    ·
                      refine ⟨4296312148433740159045699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5728416197911653545394265 4296312148433740159045699)
                      ·
                        rfl

theorem cell23_8367038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_8367038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367038 prefixEnd_8367038 := by exact prefixLift 8367038
  have htrace : WordTrace (prefixWord ++ tailWord_8367038) baseStart_8367038 baseEnd_8367038 := by
    simpa [prefixWord, tailWord_8367038, baseEnd_8367038] using wordTrace_append hprefix tailTrace_8367038
  have hstable : (prefixWord ++ tailWord_8367038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367038).length < 2 ^ (prefixWord ++ tailWord_8367038).sum := by decide
  have hdescent : baseEnd_8367038 < baseStart_8367038 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367138 : List Nat := [3, 3, 1, 1, 1, 3, 2, 4, 1, 4]
def baseStart_8367138 : Nat := 118140960795 + 8367138 * 2 ^ 59
def prefixEnd_8367138 : Nat := 4983230072969 + 3 ^ 40 * 8367138 * 2
def baseEnd_8367138 : Nat := 1432121165499729922598413

theorem tailTrace_8367138 : CollatzResearch.WordTrace tailWord_8367138 prefixEnd_8367138 1432121165499729922598413 := by
  unfold tailWord_8367138
  simp only [CollatzResearch.WordTrace]
  refine ⟨76293648490323873561883517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203449729307530329498356045 76293648490323873561883517)
  ·
    refine ⟨28610118183871452585706319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76293648490323873561883517 28610118183871452585706319)
    ·
      refine ⟨42915177275807178878559479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28610118183871452585706319 42915177275807178878559479)
      ·
        refine ⟨64372765913710768317839219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42915177275807178878559479 64372765913710768317839219)
        ·
          refine ⟨96559148870566152476758829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64372765913710768317839219 96559148870566152476758829)
          ·
            refine ⟨36209680826462307178784561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96559148870566152476758829 36209680826462307178784561)
            ·
              refine ⟨27157260619846730384088421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36209680826462307178784561 27157260619846730384088421)
              ·
                refine ⟨5091986366221261947016579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27157260619846730384088421 5091986366221261947016579)
                ·
                  refine ⟨7637979549331892920524869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5091986366221261947016579 7637979549331892920524869)
                  ·
                    refine ⟨1432121165499729922598413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7637979549331892920524869 1432121165499729922598413)
                    ·
                      rfl

theorem cell23_8367138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_8367138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367138 prefixEnd_8367138 := by exact prefixLift 8367138
  have htrace : WordTrace (prefixWord ++ tailWord_8367138) baseStart_8367138 baseEnd_8367138 := by
    simpa [prefixWord, tailWord_8367138, baseEnd_8367138] using wordTrace_append hprefix tailTrace_8367138
  have hstable : (prefixWord ++ tailWord_8367138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367138).length < 2 ^ (prefixWord ++ tailWord_8367138).sum := by decide
  have hdescent : baseEnd_8367138 < baseStart_8367138 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367171 : List Nat := [1, 1, 1, 3, 1, 2, 4, 3, 2, 3, 2]
def baseStart_8367171 : Nat := 118140960795 + 8367171 * 2 ^ 59
def prefixEnd_8367171 : Nat := 4983230072969 + 3 ^ 40 * 8367171 * 2
def baseEnd_8367171 : Nat := 4296380441360788138682587

theorem tailTrace_8367171 : CollatzResearch.WordTrace tailWord_8367171 prefixEnd_8367171 4296380441360788138682587 := by
  unfold tailWord_8367171
  simp only [CollatzResearch.WordTrace]
  refine ⟨305175797570175940883485367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203450531713450627255656911 305175797570175940883485367)
  ·
    refine ⟨457763696355263911325228051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305175797570175940883485367 457763696355263911325228051)
    ·
      refine ⟨686645544532895866987842077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457763696355263911325228051 686645544532895866987842077)
      ·
        refine ⟨257492079199835950120440779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 686645544532895866987842077 257492079199835950120440779)
        ·
          refine ⟨386238118799753925180661169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257492079199835950120440779 386238118799753925180661169)
          ·
            refine ⟨289678589099815443885495877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386238118799753925180661169 289678589099815443885495877)
            ·
              refine ⟨54314735456215395728530477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 289678589099815443885495877 54314735456215395728530477)
              ·
                refine ⟨20368025796080773398198929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54314735456215395728530477 20368025796080773398198929)
                ·
                  refine ⟨15276019347060580048649197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20368025796080773398198929 15276019347060580048649197)
                  ·
                    refine ⟨5728507255147717518243449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15276019347060580048649197 5728507255147717518243449)
                    ·
                      refine ⟨4296380441360788138682587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5728507255147717518243449 4296380441360788138682587)
                      ·
                        rfl

theorem cell23_8367171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 3, 2].length) (baseStart_8367171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367171 prefixEnd_8367171 := by exact prefixLift 8367171
  have htrace : WordTrace (prefixWord ++ tailWord_8367171) baseStart_8367171 baseEnd_8367171 := by
    simpa [prefixWord, tailWord_8367171, baseEnd_8367171] using wordTrace_append hprefix tailTrace_8367171
  have hstable : (prefixWord ++ tailWord_8367171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367171).length < 2 ^ (prefixWord ++ tailWord_8367171).sum := by decide
  have hdescent : baseEnd_8367171 < baseStart_8367171 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367204 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 2, 6, 3]
def baseStart_8367204 : Nat := 118140960795 + 8367204 * 2 ^ 59
def prefixEnd_8367204 : Nat := 4983230072969 + 3 ^ 40 * 8367204 * 2
def baseEnd_8367204 : Nat := 4296397386222386509569935

theorem tailTrace_8367204 : CollatzResearch.WordTrace tailWord_8367204 prefixEnd_8367204 4296397386222386509569935 := by
  unfold tailWord_8367204
  simp only [CollatzResearch.WordTrace]
  refine ⟨152588500589528193759718333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203451334119370925012957777 152588500589528193759718333)
  ·
    refine ⟨57220687721073072659894375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152588500589528193759718333 57220687721073072659894375)
    ·
      refine ⟨85831031581609608989841563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57220687721073072659894375 85831031581609608989841563)
      ·
        refine ⟨128746547372414413484762345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85831031581609608989841563 128746547372414413484762345)
        ·
          refine ⟨96559910529310810113571759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128746547372414413484762345 96559910529310810113571759)
          ·
            refine ⟨144839865793966215170357639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96559910529310810113571759 144839865793966215170357639)
            ·
              refine ⟨217259798690949322755536459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144839865793966215170357639 217259798690949322755536459)
              ·
                refine ⟨325889698036423984133304689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217259798690949322755536459 325889698036423984133304689)
                ·
                  refine ⟨244417273527317988099978517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 325889698036423984133304689 244417273527317988099978517)
                  ·
                    refine ⟨11457059696593030692186493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 244417273527317988099978517 11457059696593030692186493)
                    ·
                      refine ⟨4296397386222386509569935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11457059696593030692186493 4296397386222386509569935)
                      ·
                        rfl

theorem cell23_8367204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_8367204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367204 prefixEnd_8367204 := by exact prefixLift 8367204
  have htrace : WordTrace (prefixWord ++ tailWord_8367204) baseStart_8367204 baseEnd_8367204 := by
    simpa [prefixWord, tailWord_8367204, baseEnd_8367204] using wordTrace_append hprefix tailTrace_8367204
  have hstable : (prefixWord ++ tailWord_8367204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367204).length < 2 ^ (prefixWord ++ tailWord_8367204).sum := by decide
  have hdescent : baseEnd_8367204 < baseStart_8367204 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367218 : List Nat := [3, 2, 1, 2, 2, 1, 2, 1, 5, 2, 2]
def baseStart_8367218 : Nat := 118140960795 + 8367218 * 2 ^ 59
def prefixEnd_8367218 : Nat := 4983230072969 + 3 ^ 40 * 8367218 * 2
def baseEnd_8367218 : Nat := 4296404574951549454794871

theorem tailTrace_8367218 : CollatzResearch.WordTrace tailWord_8367218 prefixEnd_8367218 4296404574951549454794871 := by
  unfold tailWord_8367218
  simp only [CollatzResearch.WordTrace]
  refine ⟨76294377950251416977611577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203451674534003778606964205 76294377950251416977611577)
  ·
    refine ⟨57220783462688562733208683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76294377950251416977611577 57220783462688562733208683)
    ·
      refine ⟨85831175194032844099813025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57220783462688562733208683 85831175194032844099813025)
      ·
        refine ⟨64373381395524633074859769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85831175194032844099813025 64373381395524633074859769)
        ·
          refine ⟨48280036046643474806144827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64373381395524633074859769 48280036046643474806144827)
          ·
            refine ⟨72420054069965212209217241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48280036046643474806144827 72420054069965212209217241)
            ·
              refine ⟨54315040552473909156912931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72420054069965212209217241 54315040552473909156912931)
              ·
                refine ⟨81472560828710863735369397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54315040552473909156912931 81472560828710863735369397)
                ·
                  refine ⟨7638052577691643475190881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81472560828710863735369397 7638052577691643475190881)
                  ·
                    refine ⟨5728539433268732606393161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7638052577691643475190881 5728539433268732606393161)
                    ·
                      refine ⟨4296404574951549454794871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5728539433268732606393161 4296404574951549454794871)
                      ·
                        rfl

theorem cell23_8367218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_8367218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367218 prefixEnd_8367218 := by exact prefixLift 8367218
  have htrace : WordTrace (prefixWord ++ tailWord_8367218) baseStart_8367218 baseEnd_8367218 := by
    simpa [prefixWord, tailWord_8367218, baseEnd_8367218] using wordTrace_append hprefix tailTrace_8367218
  have hstable : (prefixWord ++ tailWord_8367218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367218).length < 2 ^ (prefixWord ++ tailWord_8367218).sum := by decide
  have hdescent : baseEnd_8367218 < baseStart_8367218 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367235 : List Nat := [1, 1, 1, 3, 3, 2, 2, 5, 1, 2, 2]
def baseStart_8367235 : Nat := 118140960795 + 8367235 * 2 ^ 59
def prefixEnd_8367235 : Nat := 4983230072969 + 3 ^ 40 * 8367235 * 2
def baseEnd_8367235 : Nat := 4296413304122675888282293

theorem tailTrace_8367235 : CollatzResearch.WordTrace tailWord_8367235 prefixEnd_8367235 4296413304122675888282293 := by
  unfold tailWord_8367235
  simp only [CollatzResearch.WordTrace]
  refine ⟨305178131841944079813815159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203452087894629386542543439 305178131841944079813815159)
  ·
    refine ⟨457767197762916119720722739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305178131841944079813815159 457767197762916119720722739)
    ·
      refine ⟨686650796644374179581084109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457767197762916119720722739 686650796644374179581084109)
      ·
        refine ⟨257494048741640317342906541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 686650796644374179581084109 257494048741640317342906541)
        ·
          refine ⟨96560268278115119003589953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257494048741640317342906541 96560268278115119003589953)
          ·
            refine ⟨72420201208586339252692465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96560268278115119003589953 72420201208586339252692465)
            ·
              refine ⟨54315150906439754439519349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72420201208586339252692465 54315150906439754439519349)
              ·
                refine ⟨5092045397478726978704939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54315150906439754439519349 5092045397478726978704939)
                ·
                  refine ⟨7638068096218090468057409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5092045397478726978704939 7638068096218090468057409)
                  ·
                    refine ⟨5728551072163567851043057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7638068096218090468057409 5728551072163567851043057)
                    ·
                      refine ⟨4296413304122675888282293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5728551072163567851043057 4296413304122675888282293)
                      ·
                        rfl

theorem cell23_8367235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 5, 1, 2, 2].length) (baseStart_8367235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367235 prefixEnd_8367235 := by exact prefixLift 8367235
  have htrace : WordTrace (prefixWord ++ tailWord_8367235) baseStart_8367235 baseEnd_8367235 := by
    simpa [prefixWord, tailWord_8367235, baseEnd_8367235] using wordTrace_append hprefix tailTrace_8367235
  have hstable : (prefixWord ++ tailWord_8367235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367235).length < 2 ^ (prefixWord ++ tailWord_8367235).sum := by decide
  have hdescent : baseEnd_8367235 < baseStart_8367235 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367251 : List Nat := [1, 1, 1, 2, 1, 2, 4, 3, 4, 1, 3]
def baseStart_8367251 : Nat := 118140960795 + 8367251 * 2 ^ 59
def prefixEnd_8367251 : Nat := 4983230072969 + 3 ^ 40 * 8367251 * 2
def baseEnd_8367251 : Nat := 4296421519813147825682219

theorem tailTrace_8367251 : CollatzResearch.WordTrace tailWord_8367251 prefixEnd_8367251 4296421519813147825682219 := by
  unfold tailWord_8367251
  simp only [CollatzResearch.WordTrace]
  refine ⟨305178715409886114546397607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203452476939924076364265071 305178715409886114546397607)
  ·
    refine ⟨457768073114829171819596411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305178715409886114546397607 457768073114829171819596411)
    ·
      refine ⟨686652109672243757729394617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457768073114829171819596411 686652109672243757729394617)
      ·
        refine ⟨514989082254182818297045963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 686652109672243757729394617 514989082254182818297045963)
        ·
          refine ⟨772483623381274227445568945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514989082254182818297045963 772483623381274227445568945)
          ·
            refine ⟨579362717535955670584176709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 772483623381274227445568945 579362717535955670584176709)
            ·
              refine ⟨108630509537991688234533133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 579362717535955670584176709 108630509537991688234533133)
              ·
                refine ⟨40736441076746883087949925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108630509537991688234533133 40736441076746883087949925)
                ·
                  refine ⟨7638082701890040578990611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40736441076746883087949925 7638082701890040578990611)
                  ·
                    refine ⟨11457124052835060868485917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7638082701890040578990611 11457124052835060868485917)
                    ·
                      refine ⟨4296421519813147825682219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11457124052835060868485917 4296421519813147825682219)
                      ·
                        rfl

theorem cell23_8367251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 4, 1, 3].length) (baseStart_8367251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367251 prefixEnd_8367251 := by exact prefixLift 8367251
  have htrace : WordTrace (prefixWord ++ tailWord_8367251) baseStart_8367251 baseEnd_8367251 := by
    simpa [prefixWord, tailWord_8367251, baseEnd_8367251] using wordTrace_append hprefix tailTrace_8367251
  have hstable : (prefixWord ++ tailWord_8367251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367251).length < 2 ^ (prefixWord ++ tailWord_8367251).sum := by decide
  have hdescent : baseEnd_8367251 < baseStart_8367251 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367268 : List Nat := [2, 3, 1, 2, 3, 2, 2, 1, 1, 3, 3]
def baseStart_8367268 : Nat := 118140960795 + 8367268 * 2 ^ 59
def prefixEnd_8367268 : Nat := 4983230072969 + 3 ^ 40 * 8367268 * 2
def baseEnd_8367268 : Nat := 4296430248984274259169641

theorem tailTrace_8367268 : CollatzResearch.WordTrace tailWord_8367268 prefixEnd_8367268 4296430248984274259169641 := by
  unfold tailWord_8367268
  simp only [CollatzResearch.WordTrace]
  refine ⟨152589667725412263224883229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203452890300549684299844305 152589667725412263224883229)
  ·
    refine ⟨57221125397029598709331211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152589667725412263224883229 57221125397029598709331211)
    ·
      refine ⟨85831688095544398063996817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57221125397029598709331211 85831688095544398063996817)
      ·
        refine ⟨64373766071658298547997613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85831688095544398063996817 64373766071658298547997613)
        ·
          refine ⟨24140162276871861955499105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64373766071658298547997613 24140162276871861955499105)
          ·
            refine ⟨18105121707653896466624329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24140162276871861955499105 18105121707653896466624329)
            ·
              refine ⟨13578841280740422349968247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18105121707653896466624329 13578841280740422349968247)
              ·
                refine ⟨20368261921110633524952371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13578841280740422349968247 20368261921110633524952371)
                ·
                  refine ⟨30552392881665950287428557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20368261921110633524952371 30552392881665950287428557)
                  ·
                    refine ⟨11457147330624731357785709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30552392881665950287428557 11457147330624731357785709)
                    ·
                      refine ⟨4296430248984274259169641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11457147330624731357785709 4296430248984274259169641)
                      ·
                        rfl

theorem cell23_8367268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_8367268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367268 prefixEnd_8367268 := by exact prefixLift 8367268
  have htrace : WordTrace (prefixWord ++ tailWord_8367268) baseStart_8367268 baseEnd_8367268 := by
    simpa [prefixWord, tailWord_8367268, baseEnd_8367268] using wordTrace_append hprefix tailTrace_8367268
  have hstable : (prefixWord ++ tailWord_8367268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367268).length < 2 ^ (prefixWord ++ tailWord_8367268).sum := by decide
  have hdescent : baseEnd_8367268 < baseStart_8367268 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367286 : List Nat := [5, 1, 3, 2, 2, 1, 2, 1, 1, 1, 4]
def baseStart_8367286 : Nat := 118140960795 + 8367286 * 2 ^ 59
def prefixEnd_8367286 : Nat := 4983230072969 + 3 ^ 40 * 8367286 * 2
def baseEnd_8367286 : Nat := 4296439491636055188744559

theorem tailTrace_8367286 : CollatzResearch.WordTrace tailWord_8367286 prefixEnd_8367286 4296439491636055188744559 := by
  unfold tailWord_8367286
  simp only [CollatzResearch.WordTrace]
  refine ⟨19073749497797457220245107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203453327976506210349281141 19073749497797457220245107)
  ·
    refine ⟨28610624246696185830367661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19073749497797457220245107 28610624246696185830367661)
    ·
      refine ⟨10728984092511069686387873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28610624246696185830367661 10728984092511069686387873)
      ·
        refine ⟨8046738069383302264790905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10728984092511069686387873 8046738069383302264790905)
        ·
          refine ⟨6035053552037476698593179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8046738069383302264790905 6035053552037476698593179)
          ·
            refine ⟨9052580328056215047889769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6035053552037476698593179 9052580328056215047889769)
            ·
              refine ⟨6789435246042161285917327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9052580328056215047889769 6789435246042161285917327)
              ·
                refine ⟨10184152869063241928875991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6789435246042161285917327 10184152869063241928875991)
                ·
                  refine ⟨15276229303594862893313987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10184152869063241928875991 15276229303594862893313987)
                  ·
                    refine ⟨22914343955392294339970981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15276229303594862893313987 22914343955392294339970981)
                    ·
                      refine ⟨4296439491636055188744559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22914343955392294339970981 4296439491636055188744559)
                      ·
                        rfl

theorem cell23_8367286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_8367286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367286 prefixEnd_8367286 := by exact prefixLift 8367286
  have htrace : WordTrace (prefixWord ++ tailWord_8367286) baseStart_8367286 baseEnd_8367286 := by
    simpa [prefixWord, tailWord_8367286, baseEnd_8367286] using wordTrace_append hprefix tailTrace_8367286
  have hstable : (prefixWord ++ tailWord_8367286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367286).length < 2 ^ (prefixWord ++ tailWord_8367286).sum := by decide
  have hdescent : baseEnd_8367286 < baseStart_8367286 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367291 : List Nat := [1, 1, 1, 1, 1, 2, 4, 3, 3, 4, 2]
def baseStart_8367291 : Nat := 118140960795 + 8367291 * 2 ^ 59
def prefixEnd_8367291 : Nat := 4983230072969 + 3 ^ 40 * 8367291 * 2
def baseEnd_8367291 : Nat := 4296442059039327669182035

theorem tailTrace_8367291 : CollatzResearch.WordTrace tailWord_8367291 prefixEnd_8367291 4296442059039327669182035 := by
  unfold tailWord_8367291
  simp only [CollatzResearch.WordTrace]
  refine ⟨305180174329741201377853727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203453449553160800918569151 305180174329741201377853727)
  ·
    refine ⟨457770261494611802066780591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305180174329741201377853727 457770261494611802066780591)
    ·
      refine ⟨686655392241917703100170887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457770261494611802066780591 686655392241917703100170887)
      ·
        refine ⟨1029983088362876554650256331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 686655392241917703100170887 1029983088362876554650256331)
        ·
          refine ⟨1544974632544314831975384497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1029983088362876554650256331 1544974632544314831975384497)
          ·
            refine ⟨1158730974408236123981538373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1544974632544314831975384497 1158730974408236123981538373)
            ·
              refine ⟨217262057701544273246538445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1158730974408236123981538373 217262057701544273246538445)
              ·
                refine ⟨81473271638079102467451917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217262057701544273246538445 81473271638079102467451917)
                ·
                  refine ⟨30552476864279663425294469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81473271638079102467451917 30552476864279663425294469)
                  ·
                    refine ⟨5728589412052436892242713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30552476864279663425294469 5728589412052436892242713)
                    ·
                      refine ⟨4296442059039327669182035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5728589412052436892242713 4296442059039327669182035)
                      ·
                        rfl

theorem cell23_8367291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 4, 2].length) (baseStart_8367291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367291 prefixEnd_8367291 := by exact prefixLift 8367291
  have htrace : WordTrace (prefixWord ++ tailWord_8367291) baseStart_8367291 baseEnd_8367291 := by
    simpa [prefixWord, tailWord_8367291, baseEnd_8367291] using wordTrace_append hprefix tailTrace_8367291
  have hstable : (prefixWord ++ tailWord_8367291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367291).length < 2 ^ (prefixWord ++ tailWord_8367291).sum := by decide
  have hdescent : baseEnd_8367291 < baseStart_8367291 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367295 : List Nat := [1, 1, 2, 2, 2, 2, 6, 1, 1, 3, 2]
def baseStart_8367295 : Nat := 118140960795 + 8367295 * 2 ^ 59
def prefixEnd_8367295 : Nat := 4983230072969 + 3 ^ 40 * 8367295 * 2
def baseEnd_8367295 : Nat := 4296444112961945653532017

theorem tailTrace_8367295 : CollatzResearch.WordTrace tailWord_8367295 prefixEnd_8367295 4296444112961945653532017 := by
  unfold tailWord_8367295
  simp only [CollatzResearch.WordTrace]
  refine ⟨305180320221726710060999339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203453546814484473373999559 305180320221726710060999339)
  ·
    refine ⟨457770480332590065091499009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305180320221726710060999339 457770480332590065091499009)
    ·
      refine ⟨343327860249442548818624257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457770480332590065091499009 343327860249442548818624257)
      ·
        refine ⟨257495895187081911613968193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343327860249442548818624257 257495895187081911613968193)
        ·
          refine ⟨193121921390311433710476145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257495895187081911613968193 193121921390311433710476145)
          ·
            refine ⟨144841441042733575282857109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193121921390311433710476145 144841441042733575282857109)
            ·
              refine ⟨6789442548878136341383927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 144841441042733575282857109 6789442548878136341383927)
              ·
                refine ⟨10184163823317204512075891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6789442548878136341383927 10184163823317204512075891)
                ·
                  refine ⟨15276245734975806768113837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10184163823317204512075891 15276245734975806768113837)
                  ·
                    refine ⟨5728592150615927538042689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15276245734975806768113837 5728592150615927538042689)
                    ·
                      refine ⟨4296444112961945653532017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5728592150615927538042689 4296444112961945653532017)
                      ·
                        rfl

theorem cell23_8367295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 1, 3, 2].length) (baseStart_8367295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367295 prefixEnd_8367295 := by exact prefixLift 8367295
  have htrace : WordTrace (prefixWord ++ tailWord_8367295) baseStart_8367295 baseEnd_8367295 := by
    simpa [prefixWord, tailWord_8367295, baseEnd_8367295] using wordTrace_append hprefix tailTrace_8367295
  have hstable : (prefixWord ++ tailWord_8367295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367295).length < 2 ^ (prefixWord ++ tailWord_8367295).sum := by decide
  have hdescent : baseEnd_8367295 < baseStart_8367295 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367361 : List Nat := [1, 2, 4, 1, 1, 3, 1, 1, 4, 5]
def baseStart_8367361 : Nat := 118140960795 + 8367361 * 2 ^ 59
def prefixEnd_8367361 : Nat := 4983230072969 + 3 ^ 40 * 8367361 * 2
def baseEnd_8367361 : Nat := 1432159334228380798435571

theorem tailTrace_8367361 : CollatzResearch.WordTrace tailWord_8367361 prefixEnd_8367361 1432159334228380798435571 := by
  unfold tailWord_8367361
  simp only [CollatzResearch.WordTrace]
  refine ⟨305182727439487603332901937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203455151626325068888601291 305182727439487603332901937)
  ·
    refine ⟨228887045579615702499676453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305182727439487603332901937 228887045579615702499676453)
    ·
      refine ⟨42916321046177944218689335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228887045579615702499676453 42916321046177944218689335)
      ·
        refine ⟨64374481569266916328034003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42916321046177944218689335 64374481569266916328034003)
        ·
          refine ⟨96561722353900374492051005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64374481569266916328034003 96561722353900374492051005)
          ·
            refine ⟨36210645882712640434519127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96561722353900374492051005 36210645882712640434519127)
            ·
              refine ⟨54315968824068960651778691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36210645882712640434519127 54315968824068960651778691)
              ·
                refine ⟨81473953236103440977668037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54315968824068960651778691 81473953236103440977668037)
                ·
                  refine ⟨15276366231769395183312757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81473953236103440977668037 15276366231769395183312757)
                  ·
                    refine ⟨1432159334228380798435571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15276366231769395183312757 1432159334228380798435571)
                    ·
                      rfl

theorem cell23_8367361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_8367361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367361 prefixEnd_8367361 := by exact prefixLift 8367361
  have htrace : WordTrace (prefixWord ++ tailWord_8367361) baseStart_8367361 baseEnd_8367361 := by
    simpa [prefixWord, tailWord_8367361, baseEnd_8367361] using wordTrace_append hprefix tailTrace_8367361
  have hstable : (prefixWord ++ tailWord_8367361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367361).length < 2 ^ (prefixWord ++ tailWord_8367361).sum := by decide
  have hdescent : baseEnd_8367361 < baseStart_8367361 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367371 : List Nat := [1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 5]
def baseStart_8367371 : Nat := 118140960795 + 8367371 * 2 ^ 59
def prefixEnd_8367371 : Nat := 4983230072969 + 3 ^ 40 * 8367371 * 2
def baseEnd_8367371 : Nat := 4296483137491687356181667

theorem tailTrace_8367371 : CollatzResearch.WordTrace tailWord_8367371 prefixEnd_8367371 4296483137491687356181667 := by
  unfold tailWord_8367371
  simp only [CollatzResearch.WordTrace]
  refine ⟨305183092169451375040765967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203455394779634250027177311 305183092169451375040765967)
  ·
    refine ⟨457774638254177062561148951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305183092169451375040765967 457774638254177062561148951)
    ·
      refine ⟨686661957381265593841723427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457774638254177062561148951 686661957381265593841723427)
      ·
        refine ⟨1029992936071898390762585141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 686661957381265593841723427 1029992936071898390762585141)
        ·
          refine ⟨96561837756740474133992357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1029992936071898390762585141 96561837756740474133992357)
          ·
            refine ⟨18105344579388838900123567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96561837756740474133992357 18105344579388838900123567)
            ·
              refine ⟨27158016869083258350185351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18105344579388838900123567 27158016869083258350185351)
              ·
                refine ⟨40737025303624887525278027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27158016869083258350185351 40737025303624887525278027)
                ·
                  refine ⟨61105537955437331287917041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40737025303624887525278027 61105537955437331287917041)
                  ·
                    refine ⟨45829153466577998465937781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61105537955437331287917041 45829153466577998465937781)
                    ·
                      refine ⟨4296483137491687356181667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45829153466577998465937781 4296483137491687356181667)
                      ·
                        rfl

theorem cell23_8367371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 5].length) (baseStart_8367371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367371 prefixEnd_8367371 := by exact prefixLift 8367371
  have htrace : WordTrace (prefixWord ++ tailWord_8367371) baseStart_8367371 baseEnd_8367371 := by
    simpa [prefixWord, tailWord_8367371, baseEnd_8367371] using wordTrace_append hprefix tailTrace_8367371
  have hstable : (prefixWord ++ tailWord_8367371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367371).length < 2 ^ (prefixWord ++ tailWord_8367371).sum := by decide
  have hdescent : baseEnd_8367371 < baseStart_8367371 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367381 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 6, 1, 4]
def baseStart_8367381 : Nat := 118140960795 + 8367381 * 2 ^ 59
def prefixEnd_8367381 : Nat := 4983230072969 + 3 ^ 40 * 8367381 * 2
def baseEnd_8367381 : Nat := 4296488272298232317056621

theorem tailTrace_8367381 : CollatzResearch.WordTrace tailWord_8367381 prefixEnd_8367381 4296488272298232317056621 := by
  unfold tailWord_8367381
  simp only [CollatzResearch.WordTrace]
  refine ⟨305183456899415146748629997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203455637932943431165753331 305183456899415146748629997)
  ·
    refine ⟨114443796337280680030736249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305183456899415146748629997 114443796337280680030736249)
    ·
      refine ⟨85832847252960510023052187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114443796337280680030736249 85832847252960510023052187)
      ·
        refine ⟨128749270879440765034578281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85832847252960510023052187 128749270879440765034578281)
        ·
          refine ⟨96561953159580573775933711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128749270879440765034578281 96561953159580573775933711)
          ·
            refine ⟨144842929739370860663900567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96561953159580573775933711 144842929739370860663900567)
            ·
              refine ⟨217264394609056290995850851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144842929739370860663900567 217264394609056290995850851)
              ·
                refine ⟨325896591913584436493776277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217264394609056290995850851 325896591913584436493776277)
                ·
                  refine ⟨15276402745949270460645763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 325896591913584436493776277 15276402745949270460645763)
                  ·
                    refine ⟨22914604118923905690968645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15276402745949270460645763 22914604118923905690968645)
                    ·
                      refine ⟨4296488272298232317056621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22914604118923905690968645 4296488272298232317056621)
                      ·
                        rfl

theorem cell23_8367381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_8367381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367381 prefixEnd_8367381 := by exact prefixLift 8367381
  have htrace : WordTrace (prefixWord ++ tailWord_8367381) baseStart_8367381 baseEnd_8367381 := by
    simpa [prefixWord, tailWord_8367381, baseEnd_8367381] using wordTrace_append hprefix tailTrace_8367381
  have hstable : (prefixWord ++ tailWord_8367381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367381).length < 2 ^ (prefixWord ++ tailWord_8367381).sum := by decide
  have hdescent : baseEnd_8367381 < baseStart_8367381 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367418 : List Nat := [3, 1, 1, 1, 4, 1, 1, 4, 2, 2, 3]
def baseStart_8367418 : Nat := 118140960795 + 8367418 * 2 ^ 59
def prefixEnd_8367418 : Nat := 4983230072969 + 3 ^ 40 * 8367418 * 2
def baseEnd_8367418 : Nat := 4296507271082448672293951

theorem tailTrace_8367418 : CollatzResearch.WordTrace tailWord_8367418 prefixEnd_8367418 4296507271082448672293951 := by
  unfold tailWord_8367418
  simp only [CollatzResearch.WordTrace]
  refine ⟨76296201600070275516931727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203456537600187401378484605 76296201600070275516931727)
  ·
    refine ⟨114444302400105413275397591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76296201600070275516931727 114444302400105413275397591)
    ·
      refine ⟨171666453600158119913096387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114444302400105413275397591 171666453600158119913096387)
      ·
        refine ⟨257499680400237179869644581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171666453600158119913096387 257499680400237179869644581)
        ·
          refine ⟨48281190075044471225558359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 257499680400237179869644581 48281190075044471225558359)
          ·
            refine ⟨72421785112566706838337539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48281190075044471225558359 72421785112566706838337539)
            ·
              refine ⟨108632677668850060257506309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72421785112566706838337539 108632677668850060257506309)
              ·
                refine ⟨20368627062909386298282433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108632677668850060257506309 20368627062909386298282433)
                ·
                  refine ⟨15276470297182039723711825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20368627062909386298282433 15276470297182039723711825)
                  ·
                    refine ⟨11457352722886529792783869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15276470297182039723711825 11457352722886529792783869)
                    ·
                      refine ⟨4296507271082448672293951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11457352722886529792783869 4296507271082448672293951)
                      ·
                        rfl

theorem cell23_8367418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 2, 2, 3].length) (baseStart_8367418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367418 prefixEnd_8367418 := by exact prefixLift 8367418
  have htrace : WordTrace (prefixWord ++ tailWord_8367418) baseStart_8367418 baseEnd_8367418 := by
    simpa [prefixWord, tailWord_8367418, baseEnd_8367418] using wordTrace_append hprefix tailTrace_8367418
  have hstable : (prefixWord ++ tailWord_8367418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367418).length < 2 ^ (prefixWord ++ tailWord_8367418).sum := by decide
  have hdescent : baseEnd_8367418 < baseStart_8367418 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367446 : List Nat := [5, 2, 3, 1, 1, 2, 1, 1, 2, 5]
def baseStart_8367446 : Nat := 118140960795 + 8367446 * 2 ^ 59
def prefixEnd_8367446 : Nat := 4983230072969 + 3 ^ 40 * 8367446 * 2
def baseEnd_8367446 : Nat := 1432173882846924854247941

theorem tailTrace_8367446 : CollatzResearch.WordTrace tailWord_8367446 prefixEnd_8367446 1432173882846924854247941 := by
  unfold tailWord_8367446
  simp only [CollatzResearch.WordTrace]
  refine ⟨19074114227761228928109137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203457218429453108566497461 19074114227761228928109137)
  ·
    refine ⟨14305585670820921696081853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19074114227761228928109137 14305585670820921696081853)
    ·
      refine ⟨5364594626557845636030695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14305585670820921696081853 5364594626557845636030695)
      ·
        refine ⟨8046891939836768454046043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5364594626557845636030695 8046891939836768454046043)
        ·
          refine ⟨12070337909755152681069065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8046891939836768454046043 12070337909755152681069065)
          ·
            refine ⟨9052753432316364510801799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12070337909755152681069065 9052753432316364510801799)
            ·
              refine ⟨13579130148474546766202699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9052753432316364510801799 13579130148474546766202699)
              ·
                refine ⟨20368695222711820149304049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13579130148474546766202699 20368695222711820149304049)
                ·
                  refine ⟨15276521417033865111978037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20368695222711820149304049 15276521417033865111978037)
                  ·
                    refine ⟨1432173882846924854247941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15276521417033865111978037 1432173882846924854247941)
                    ·
                      rfl

theorem cell23_8367446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_8367446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367446 prefixEnd_8367446 := by exact prefixLift 8367446
  have htrace : WordTrace (prefixWord ++ tailWord_8367446) baseStart_8367446 baseEnd_8367446 := by
    simpa [prefixWord, tailWord_8367446, baseEnd_8367446] using wordTrace_append hprefix tailTrace_8367446
  have hstable : (prefixWord ++ tailWord_8367446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367446).length < 2 ^ (prefixWord ++ tailWord_8367446).sum := by decide
  have hdescent : baseEnd_8367446 < baseStart_8367446 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367481 : List Nat := [1, 2, 1, 3, 2, 1, 2, 2, 3, 6]
def baseStart_8367481 : Nat := 118140960795 + 8367481 * 2 ^ 59
def prefixEnd_8367481 : Nat := 4983230072969 + 3 ^ 40 * 8367481 * 2
def baseEnd_8367481 : Nat := 1432179873454560641935387

theorem tailTrace_8367481 : CollatzResearch.WordTrace tailWord_8367481 prefixEnd_8367481 1432179873454560641935387 := by
  unfold tailWord_8367481
  simp only [CollatzResearch.WordTrace]
  refine ⟨305187104199052863827270297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203458069466035242551513531 305187104199052863827270297)
  ·
    refine ⟨228890328149289647870452723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305187104199052863827270297 228890328149289647870452723)
    ·
      refine ⟨343335492223934471805679085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228890328149289647870452723 343335492223934471805679085)
      ·
        refine ⟨128750809583975426927129657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343335492223934471805679085 128750809583975426927129657)
        ·
          refine ⟨96563107187981570195347243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128750809583975426927129657 96563107187981570195347243)
          ·
            refine ⟨144844660781972355293020865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96563107187981570195347243 144844660781972355293020865)
            ·
              refine ⟨108633495586479266469765649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144844660781972355293020865 108633495586479266469765649)
              ·
                refine ⟨81475121689859449852324237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108633495586479266469765649 81475121689859449852324237)
                ·
                  refine ⟨30553170633697293694621589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81475121689859449852324237 30553170633697293694621589)
                  ·
                    refine ⟨1432179873454560641935387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30553170633697293694621589 1432179873454560641935387)
                    ·
                      rfl

theorem cell23_8367481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 6].length) (baseStart_8367481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367481 prefixEnd_8367481 := by exact prefixLift 8367481
  have htrace : WordTrace (prefixWord ++ tailWord_8367481) baseStart_8367481 baseEnd_8367481 := by
    simpa [prefixWord, tailWord_8367481, baseEnd_8367481] using wordTrace_append hprefix tailTrace_8367481
  have hstable : (prefixWord ++ tailWord_8367481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367481).length < 2 ^ (prefixWord ++ tailWord_8367481).sum := by decide
  have hdescent : baseEnd_8367481 < baseStart_8367481 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367502 : List Nat := [4, 1, 1, 4, 2, 1, 2, 2, 1, 5]
def baseStart_8367502 : Nat := 118140960795 + 8367502 * 2 ^ 59
def prefixEnd_8367502 : Nat := 4983230072969 + 3 ^ 40 * 8367502 * 2
def baseEnd_8367502 : Nat := 1432183467819142114547855

theorem tailTrace_8367502 : CollatzResearch.WordTrace tailWord_8367502 prefixEnd_8367502 1432183467819142114547855 := by
  unfold tailWord_8367502
  simp only [CollatzResearch.WordTrace]
  refine ⟨38148483766497098051723095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203458580087984522942523173 38148483766497098051723095)
  ·
    refine ⟨57222725649745647077584643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38148483766497098051723095 57222725649745647077584643)
    ·
      refine ⟨85834088474618470616376965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57222725649745647077584643 85834088474618470616376965)
      ·
        refine ⟨16093891588990963240570681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85834088474618470616376965 16093891588990963240570681)
        ·
          refine ⟨12070418691743222430428011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16093891588990963240570681 12070418691743222430428011)
          ·
            refine ⟨18105628037614833645642017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12070418691743222430428011 18105628037614833645642017)
            ·
              refine ⟨13579221028211125234231513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18105628037614833645642017 13579221028211125234231513)
              ·
                refine ⟨10184415771158343925673635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13579221028211125234231513 10184415771158343925673635)
                ·
                  refine ⟨15276623656737515888510453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10184415771158343925673635 15276623656737515888510453)
                  ·
                    refine ⟨1432183467819142114547855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15276623656737515888510453 1432183467819142114547855)
                    ·
                      rfl

theorem cell23_8367502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 1, 5].length) (baseStart_8367502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367502 prefixEnd_8367502 := by exact prefixLift 8367502
  have htrace : WordTrace (prefixWord ++ tailWord_8367502) baseStart_8367502 baseEnd_8367502 := by
    simpa [prefixWord, tailWord_8367502, baseEnd_8367502] using wordTrace_append hprefix tailTrace_8367502
  have hstable : (prefixWord ++ tailWord_8367502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367502).length < 2 ^ (prefixWord ++ tailWord_8367502).sum := by decide
  have hdescent : baseEnd_8367502 < baseStart_8367502 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367538 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3]
def baseStart_8367538 : Nat := 118140960795 + 8367538 * 2 ^ 59
def prefixEnd_8367538 : Nat := 4983230072969 + 3 ^ 40 * 8367538 * 2
def baseEnd_8367538 : Nat := 4296568888760988202793399

theorem tailTrace_8367538 : CollatzResearch.WordTrace tailWord_8367538 prefixEnd_8367538 4296568888760988202793399 := by
  unfold tailWord_8367538
  simp only [CollatzResearch.WordTrace]
  refine ⟨76297295789961590640523817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203459455439897575041396845 76297295789961590640523817)
  ·
    refine ⟨57222971842471192980392863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76297295789961590640523817 57222971842471192980392863)
    ·
      refine ⟨85834457763706789470589295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57222971842471192980392863 85834457763706789470589295)
      ·
        refine ⟨128751686645560184205883943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85834457763706789470589295 128751686645560184205883943)
        ·
          refine ⟨193127529968340276308825915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128751686645560184205883943 193127529968340276308825915)
          ·
            refine ⟨289691294952510414463238873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193127529968340276308825915 289691294952510414463238873)
            ·
              refine ⟨217268471214382810847429155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289691294952510414463238873 217268471214382810847429155)
              ·
                refine ⟨325902706821574216271143733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217268471214382810847429155 325902706821574216271143733)
                ·
                  refine ⟨30553378764522582775419725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 325902706821574216271143733 30553378764522582775419725)
                  ·
                    refine ⟨11457517036695968540782397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30553378764522582775419725 11457517036695968540782397)
                    ·
                      refine ⟨4296568888760988202793399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11457517036695968540782397 4296568888760988202793399)
                      ·
                        rfl

theorem cell23_8367538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3].length) (baseStart_8367538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367538 prefixEnd_8367538 := by exact prefixLift 8367538
  have htrace : WordTrace (prefixWord ++ tailWord_8367538) baseStart_8367538 baseEnd_8367538 := by
    simpa [prefixWord, tailWord_8367538, baseEnd_8367538] using wordTrace_append hprefix tailTrace_8367538
  have hstable : (prefixWord ++ tailWord_8367538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367538).length < 2 ^ (prefixWord ++ tailWord_8367538).sum := by decide
  have hdescent : baseEnd_8367538 < baseStart_8367538 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367561 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 1, 2, 8]
def baseStart_8367561 : Nat := 118140960795 + 8367561 * 2 ^ 59
def prefixEnd_8367561 : Nat := 4983230072969 + 3 ^ 40 * 8367561 * 2
def baseEnd_8367561 : Nat := 4296580698816041612805793

theorem tailTrace_8367561 : CollatzResearch.WordTrace tailWord_8367561 prefixEnd_8367561 4296580698816041612805793 := by
  unfold tailWord_8367561
  simp only [CollatzResearch.WordTrace]
  refine ⟨305190022038763037490182537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203460014692508691660121691 305190022038763037490182537)
  ·
    refine ⟨228892516529072278117636903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305190022038763037490182537 228892516529072278117636903)
    ·
      refine ⟨343338774793608417176455355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228892516529072278117636903 343338774793608417176455355)
      ·
        refine ⟨515008162190412625764683033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343338774793608417176455355 515008162190412625764683033)
        ·
          refine ⟨386256121642809469323512275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515008162190412625764683033 386256121642809469323512275)
          ·
            refine ⟨579384182464214203985268413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386256121642809469323512275 579384182464214203985268413)
            ·
              refine ⟨217269068424080326494475655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 579384182464214203985268413 217269068424080326494475655)
              ·
                refine ⟨325903602636120489741713483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217269068424080326494475655 325903602636120489741713483)
                ·
                  refine ⟨488855403954180734612570225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 325903602636120489741713483 488855403954180734612570225)
                  ·
                    refine ⟨366641552965635550959427669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 488855403954180734612570225 366641552965635550959427669)
                    ·
                      refine ⟨4296580698816041612805793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 366641552965635550959427669 4296580698816041612805793)
                      ·
                        rfl

theorem cell23_8367561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 2, 8].length) (baseStart_8367561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367561 prefixEnd_8367561 := by exact prefixLift 8367561
  have htrace : WordTrace (prefixWord ++ tailWord_8367561) baseStart_8367561 baseEnd_8367561 := by
    simpa [prefixWord, tailWord_8367561, baseEnd_8367561] using wordTrace_append hprefix tailTrace_8367561
  have hstable : (prefixWord ++ tailWord_8367561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367561).length < 2 ^ (prefixWord ++ tailWord_8367561).sum := by decide
  have hdescent : baseEnd_8367561 < baseStart_8367561 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367572 : List Nat := [2, 4, 1, 2, 3, 1, 1, 2, 1, 3, 3]
def baseStart_8367572 : Nat := 118140960795 + 8367572 * 2 ^ 59
def prefixEnd_8367572 : Nat := 4983230072969 + 3 ^ 40 * 8367572 * 2
def baseEnd_8367572 : Nat := 4296586347103241069768243

theorem tailTrace_8367572 : CollatzResearch.WordTrace tailWord_8367572 prefixEnd_8367572 4296586347103241069768243 := by
  unfold tailWord_8367572
  simp only [CollatzResearch.WordTrace]
  refine ⟨152595211620861593184416485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203460282161148790912555313 152595211620861593184416485)
  ·
    refine ⟨28611602178911548722078091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152595211620861593184416485 28611602178911548722078091)
    ·
      refine ⟨42917403268367323083117137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28611602178911548722078091 42917403268367323083117137)
      ·
        refine ⟨32188052451275492312337853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42917403268367323083117137 32188052451275492312337853)
        ·
          refine ⟨12070519669228309617126695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32188052451275492312337853 12070519669228309617126695)
          ·
            refine ⟨18105779503842464425690043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12070519669228309617126695 18105779503842464425690043)
            ·
              refine ⟨27158669255763696638535065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18105779503842464425690043 27158669255763696638535065)
              ·
                refine ⟨20369001941822772478901299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27158669255763696638535065 20369001941822772478901299)
                ·
                  refine ⟨30553502912734158718351949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20369001941822772478901299 30553502912734158718351949)
                  ·
                    refine ⟨11457563592275309519381981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30553502912734158718351949 11457563592275309519381981)
                    ·
                      refine ⟨4296586347103241069768243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11457563592275309519381981 4296586347103241069768243)
                      ·
                        rfl

theorem cell23_8367572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_8367572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367572 prefixEnd_8367572 := by exact prefixLift 8367572
  have htrace : WordTrace (prefixWord ++ tailWord_8367572) baseStart_8367572 baseEnd_8367572 := by
    simpa [prefixWord, tailWord_8367572, baseEnd_8367572] using wordTrace_append hprefix tailTrace_8367572
  have hstable : (prefixWord ++ tailWord_8367572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367572).length < 2 ^ (prefixWord ++ tailWord_8367572).sum := by decide
  have hdescent : baseEnd_8367572 < baseStart_8367572 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367589 : List Nat := [1, 3, 1, 5, 1, 2, 2, 2, 2, 1, 3]
def baseStart_8367589 : Nat := 118140960795 + 8367589 * 2 ^ 59
def prefixEnd_8367589 : Nat := 4983230072969 + 3 ^ 40 * 8367589 * 2
def baseEnd_8367589 : Nat := 4296595076274367503255665

theorem tailTrace_8367589 : CollatzResearch.WordTrace tailWord_8367589 prefixEnd_8367589 4296595076274367503255665 := by
  unfold tailWord_8367589
  simp only [CollatzResearch.WordTrace]
  refine ⟨305191043282661598272201821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203460695521774398848134547 305191043282661598272201821)
  ·
    refine ⟨114446641230998099352075683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305191043282661598272201821 114446641230998099352075683)
    ·
      refine ⟨171669961846497149028113525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114446641230998099352075683 171669961846497149028113525)
      ·
        refine ⟨16094058923109107721385643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 171669961846497149028113525 16094058923109107721385643)
        ·
          refine ⟨24141088384663661582078465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16094058923109107721385643 24141088384663661582078465)
          ·
            refine ⟨18105816288497746186558849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24141088384663661582078465 18105816288497746186558849)
            ·
              refine ⟨13579362216373309639919137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18105816288497746186558849 13579362216373309639919137)
              ·
                refine ⟨10184521662279982229939353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13579362216373309639919137 10184521662279982229939353)
                ·
                  refine ⟨7638391246709986672454515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10184521662279982229939353 7638391246709986672454515)
                  ·
                    refine ⟨11457586870064980008681773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7638391246709986672454515 11457586870064980008681773)
                    ·
                      refine ⟨4296595076274367503255665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11457586870064980008681773 4296595076274367503255665)
                      ·
                        rfl

theorem cell23_8367589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_8367589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367589 prefixEnd_8367589 := by exact prefixLift 8367589
  have htrace : WordTrace (prefixWord ++ tailWord_8367589) baseStart_8367589 baseEnd_8367589 := by
    simpa [prefixWord, tailWord_8367589, baseEnd_8367589] using wordTrace_append hprefix tailTrace_8367589
  have hstable : (prefixWord ++ tailWord_8367589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367589).length < 2 ^ (prefixWord ++ tailWord_8367589).sum := by decide
  have hdescent : baseEnd_8367589 < baseStart_8367589 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367605 : List Nat := [1, 3, 5, 1, 1, 1, 1, 1, 1, 8]
def baseStart_8367605 : Nat := 118140960795 + 8367605 * 2 ^ 59
def prefixEnd_8367605 : Nat := 4983230072969 + 3 ^ 40 * 8367605 * 2
def baseEnd_8367605 : Nat := 1432201097321613146885197

theorem tailTrace_8367605 : CollatzResearch.WordTrace tailWord_8367605 prefixEnd_8367605 1432201097321613146885197 := by
  unfold tailWord_8367605
  simp only [CollatzResearch.WordTrace]
  refine ⟨305191626850603633004784269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203461084567069088669856179 305191626850603633004784269)
  ·
    refine ⟨114446860068976362376794101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305191626850603633004784269 114446860068976362376794101)
    ·
      refine ⟨10729393131466533972824447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114446860068976362376794101 10729393131466533972824447)
      ·
        refine ⟨16094089697199800959236671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10729393131466533972824447 16094089697199800959236671)
        ·
          refine ⟨24141134545799701438855007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16094089697199800959236671 24141134545799701438855007)
          ·
            refine ⟨36211701818699552158282511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24141134545799701438855007 36211701818699552158282511)
            ·
              refine ⟨54317552728049328237423767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36211701818699552158282511 54317552728049328237423767)
              ·
                refine ⟨81476329092073992356135651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54317552728049328237423767 81476329092073992356135651)
                ·
                  refine ⟨122214493638110988534203477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81476329092073992356135651 122214493638110988534203477)
                  ·
                    refine ⟨1432201097321613146885197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 122214493638110988534203477 1432201097321613146885197)
                    ·
                      rfl

theorem cell23_8367605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_8367605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367605 prefixEnd_8367605 := by exact prefixLift 8367605
  have htrace : WordTrace (prefixWord ++ tailWord_8367605) baseStart_8367605 baseEnd_8367605 := by
    simpa [prefixWord, tailWord_8367605, baseEnd_8367605] using wordTrace_append hprefix tailTrace_8367605
  have hstable : (prefixWord ++ tailWord_8367605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367605).length < 2 ^ (prefixWord ++ tailWord_8367605).sum := by decide
  have hdescent : baseEnd_8367605 < baseStart_8367605 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367608 : List Nat := [2, 1, 2, 1, 1, 5, 1, 1, 1, 4, 4]
def baseStart_8367608 : Nat := 118140960795 + 8367608 * 2 ^ 59
def prefixEnd_8367608 : Nat := 4983230072969 + 3 ^ 40 * 8367608 * 2
def baseEnd_8367608 : Nat := 4296604832406802928918077

theorem tailTrace_8367608 : CollatzResearch.WordTrace tailWord_8367608 prefixEnd_8367608 4296604832406802928918077 := by
  unfold tailWord_8367608
  simp only [CollatzResearch.WordTrace]
  refine ⟨152595868134796382258571739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203461157513061843011428985 152595868134796382258571739)
  ·
    refine ⟨228893802202194573387857609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152595868134796382258571739 228893802202194573387857609)
    ·
      refine ⟨171670351651645930040893207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228893802202194573387857609 171670351651645930040893207)
      ·
        refine ⟨257505527477468895061339811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171670351651645930040893207 257505527477468895061339811)
        ·
          refine ⟨386258291216203342592009717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257505527477468895061339811 386258291216203342592009717)
          ·
            refine ⟨36211714801519063368000911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 386258291216203342592009717 36211714801519063368000911)
            ·
              refine ⟨54317572202278595052001367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36211714801519063368000911 54317572202278595052001367)
              ·
                refine ⟨81476358303417892578002051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54317572202278595052001367 81476358303417892578002051)
                ·
                  refine ⟨122214537455126838867003077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81476358303417892578002051 122214537455126838867003077)
                  ·
                    refine ⟨22915225772836282287563077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 122214537455126838867003077 22915225772836282287563077)
                    ·
                      refine ⟨4296604832406802928918077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22915225772836282287563077 4296604832406802928918077)
                      ·
                        rfl

theorem cell23_8367608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 1, 4, 4].length) (baseStart_8367608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367608 prefixEnd_8367608 := by exact prefixLift 8367608
  have htrace : WordTrace (prefixWord ++ tailWord_8367608) baseStart_8367608 baseEnd_8367608 := by
    simpa [prefixWord, tailWord_8367608, baseEnd_8367608] using wordTrace_append hprefix tailTrace_8367608
  have hstable : (prefixWord ++ tailWord_8367608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367608).length < 2 ^ (prefixWord ++ tailWord_8367608).sum := by decide
  have hdescent : baseEnd_8367608 < baseStart_8367608 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367635 : List Nat := [1, 1, 1, 2, 1, 6, 1, 5, 5]
def baseStart_8367635 : Nat := 118140960795 + 8367635 * 2 ^ 59
def prefixEnd_8367635 : Nat := 4983230072969 + 3 ^ 40 * 8367635 * 2
def baseEnd_8367635 : Nat := 477402077376052702586717

theorem tailTrace_8367635 : CollatzResearch.WordTrace tailWord_8367635 prefixEnd_8367635 477402077376052702586717 := by
  unfold tailWord_8367635
  simp only [CollatzResearch.WordTrace]
  refine ⟨305192721040494948128376359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203461814026996632085584239 305192721040494948128376359)
  ·
    refine ⟨457789081560742422192564539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305192721040494948128376359 457789081560742422192564539)
    ·
      refine ⟨686683622341113633288846809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457789081560742422192564539 686683622341113633288846809)
      ·
        refine ⟨515012716755835224966635107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 686683622341113633288846809 515012716755835224966635107)
        ·
          refine ⟨772519075133752837449952661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515012716755835224966635107 772519075133752837449952661)
          ·
            refine ⟨36211831646894664255466531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 772519075133752837449952661 36211831646894664255466531)
            ·
              refine ⟨54317747470341996383199797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36211831646894664255466531 54317747470341996383199797)
              ·
                refine ⟨5092288825344562160924981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54317747470341996383199797 5092288825344562160924981)
                ·
                  refine ⟨477402077376052702586717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5092288825344562160924981 477402077376052702586717)
                  ·
                    rfl

theorem cell23_8367635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 5, 5].length) (baseStart_8367635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367635 prefixEnd_8367635 := by exact prefixLift 8367635
  have htrace : WordTrace (prefixWord ++ tailWord_8367635) baseStart_8367635 baseEnd_8367635 := by
    simpa [prefixWord, tailWord_8367635, baseEnd_8367635] using wordTrace_append hprefix tailTrace_8367635
  have hstable : (prefixWord ++ tailWord_8367635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367635).length < 2 ^ (prefixWord ++ tailWord_8367635).sum := by decide
  have hdescent : baseEnd_8367635 < baseStart_8367635 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367645 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 4, 3, 3]
def baseStart_8367645 : Nat := 118140960795 + 8367645 * 2 ^ 59
def prefixEnd_8367645 : Nat := 4983230072969 + 3 ^ 40 * 8367645 * 2
def baseEnd_8367645 : Nat := 4296623831191019284155407

theorem tailTrace_8367645 : CollatzResearch.WordTrace tailWord_8367645 prefixEnd_8367645 4296623831191019284155407 := by
  unfold tailWord_8367645
  simp only [CollatzResearch.WordTrace]
  refine ⟨305193085770458719836240389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203462057180305813224160259 305193085770458719836240389)
  ·
    refine ⟨57223703581961009969295073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305193085770458719836240389 57223703581961009969295073)
    ·
      refine ⟨42917777686470757476971305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57223703581961009969295073 42917777686470757476971305)
      ·
        refine ⟨32188333264853068107728479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42917777686470757476971305 32188333264853068107728479)
        ·
          refine ⟨48282499897279602161592719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32188333264853068107728479 48282499897279602161592719)
          ·
            refine ⟨72423749845919403242389079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48282499897279602161592719 72423749845919403242389079)
            ·
              refine ⟨108635624768879104863583619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72423749845919403242389079 108635624768879104863583619)
              ·
                refine ⟨162953437153318657295375429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108635624768879104863583619 162953437153318657295375429)
                ·
                  refine ⟨30553769466247248242882893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162953437153318657295375429 30553769466247248242882893)
                  ·
                    refine ⟨11457663549842718091081085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30553769466247248242882893 11457663549842718091081085)
                    ·
                      refine ⟨4296623831191019284155407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11457663549842718091081085 4296623831191019284155407)
                      ·
                        rfl

theorem cell23_8367645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_8367645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367645 prefixEnd_8367645 := by exact prefixLift 8367645
  have htrace : WordTrace (prefixWord ++ tailWord_8367645) baseStart_8367645 baseEnd_8367645 := by
    simpa [prefixWord, tailWord_8367645, baseEnd_8367645] using wordTrace_append hprefix tailTrace_8367645
  have hstable : (prefixWord ++ tailWord_8367645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367645).length < 2 ^ (prefixWord ++ tailWord_8367645).sum := by decide
  have hdescent : baseEnd_8367645 < baseStart_8367645 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367662 : List Nat := [4, 1, 3, 1, 2, 1, 2, 1, 2, 3, 3]
def baseStart_8367662 : Nat := 118140960795 + 8367662 * 2 ^ 59
def prefixEnd_8367662 : Nat := 4983230072969 + 3 ^ 40 * 8367662 * 2
def baseEnd_8367662 : Nat := 4296632560362145717642829

theorem tailTrace_8367662 : CollatzResearch.WordTrace tailWord_8367662 prefixEnd_8367662 4296632560362145717642829 := by
  unfold tailWord_8367662
  simp only [CollatzResearch.WordTrace]
  refine ⟨38149213226424641467451155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203462470540931421159739493 38149213226424641467451155)
  ·
    refine ⟨57223819839636962201176733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38149213226424641467451155 57223819839636962201176733)
    ·
      refine ⟨21458932439863860825441275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57223819839636962201176733 21458932439863860825441275)
      ·
        refine ⟨32188398659795791238161913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21458932439863860825441275 32188398659795791238161913)
        ·
          refine ⟨24141298994846843428621435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32188398659795791238161913 24141298994846843428621435)
          ·
            refine ⟨36211948492270265142932153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24141298994846843428621435 36211948492270265142932153)
            ·
              refine ⟨27158961369202698857199115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36211948492270265142932153 27158961369202698857199115)
              ·
                refine ⟨40738442053804048285798673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27158961369202698857199115 40738442053804048285798673)
                ·
                  refine ⟨30553831540353036214349005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40738442053804048285798673 30553831540353036214349005)
                  ·
                    refine ⟨11457686827632388580380877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30553831540353036214349005 11457686827632388580380877)
                    ·
                      refine ⟨4296632560362145717642829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11457686827632388580380877 4296632560362145717642829)
                      ·
                        rfl

theorem cell23_8367662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_8367662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367662 prefixEnd_8367662 := by exact prefixLift 8367662
  have htrace : WordTrace (prefixWord ++ tailWord_8367662) baseStart_8367662 baseEnd_8367662 := by
    simpa [prefixWord, tailWord_8367662, baseEnd_8367662] using wordTrace_append hprefix tailTrace_8367662
  have hstable : (prefixWord ++ tailWord_8367662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367662).length < 2 ^ (prefixWord ++ tailWord_8367662).sum := by decide
  have hdescent : baseEnd_8367662 < baseStart_8367662 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367685 : List Nat := [1, 3, 1, 1, 1, 4, 2, 3, 2, 1, 4]
def baseStart_8367685 : Nat := 118140960795 + 8367685 * 2 ^ 59
def prefixEnd_8367685 : Nat := 4983230072969 + 3 ^ 40 * 8367685 * 2
def baseEnd_8367685 : Nat := 4296644370417199127655223

theorem tailTrace_8367685 : CollatzResearch.WordTrace tailWord_8367685 prefixEnd_8367685 4296644370417199127655223 := by
  unfold tailWord_8367685
  simp only [CollatzResearch.WordTrace]
  refine ⟨305194544690313806667696509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203463029793542537778464339 305194544690313806667696509)
  ·
    refine ⟨114447954258867677500386191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305194544690313806667696509 114447954258867677500386191)
    ·
      refine ⟨171671931388301516250579287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114447954258867677500386191 171671931388301516250579287)
      ·
        refine ⟨257507897082452274375868931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171671931388301516250579287 257507897082452274375868931)
        ·
          refine ⟨386261845623678411563803397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257507897082452274375868931 386261845623678411563803397)
          ·
            refine ⟨72424096054439702168213137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 386261845623678411563803397 72424096054439702168213137)
            ·
              refine ⟨54318072040829776626159853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72424096054439702168213137 54318072040829776626159853)
              ·
                refine ⟨20369277015311166234809945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54318072040829776626159853 20369277015311166234809945)
                ·
                  refine ⟨15276957761483374676107459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20369277015311166234809945 15276957761483374676107459)
                  ·
                    refine ⟨22915436642225062014161189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15276957761483374676107459 22915436642225062014161189)
                    ·
                      refine ⟨4296644370417199127655223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22915436642225062014161189 4296644370417199127655223)
                      ·
                        rfl

theorem cell23_8367685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 1, 4].length) (baseStart_8367685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367685 prefixEnd_8367685 := by exact prefixLift 8367685
  have htrace : WordTrace (prefixWord ++ tailWord_8367685) baseStart_8367685 baseEnd_8367685 := by
    simpa [prefixWord, tailWord_8367685, baseEnd_8367685] using wordTrace_append hprefix tailTrace_8367685
  have hstable : (prefixWord ++ tailWord_8367685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367685).length < 2 ^ (prefixWord ++ tailWord_8367685).sum := by decide
  have hdescent : baseEnd_8367685 < baseStart_8367685 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367688 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 4, 3, 5]
def baseStart_8367688 : Nat := 118140960795 + 8367688 * 2 ^ 59
def prefixEnd_8367688 : Nat := 4983230072969 + 3 ^ 40 * 8367688 * 2
def baseEnd_8367688 : Nat := 4296645910859162615917709

theorem tailTrace_8367688 : CollatzResearch.WordTrace tailWord_8367688 prefixEnd_8367688 4296645910859162615917709 := by
  unfold tailWord_8367688
  simp only [CollatzResearch.WordTrace]
  refine ⟨152597327054651469090027859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203463102739535292120037145 152597327054651469090027859)
  ·
    refine ⟨228895990581977203635041789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152597327054651469090027859 228895990581977203635041789)
    ·
      refine ⟨85835996468241451363140671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228895990581977203635041789 85835996468241451363140671)
      ·
        refine ⟨128753994702362177044711007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85835996468241451363140671 128753994702362177044711007)
        ·
          refine ⟨193130992053543265567066511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128753994702362177044711007 193130992053543265567066511)
          ·
            refine ⟨289696488080314898350599767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193130992053543265567066511 289696488080314898350599767)
            ·
              refine ⟨434544732120472347525899651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289696488080314898350599767 434544732120472347525899651)
              ·
                refine ⟨651817098180708521288849477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434544732120472347525899651 651817098180708521288849477)
                ·
                  refine ⟨122215705908882847741659277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 651817098180708521288849477 122215705908882847741659277)
                  ·
                    refine ⟨45830889715831067903122229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 122215705908882847741659277 45830889715831067903122229)
                    ·
                      refine ⟨4296645910859162615917709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45830889715831067903122229 4296645910859162615917709)
                      ·
                        rfl

theorem cell23_8367688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_8367688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367688 prefixEnd_8367688 := by exact prefixLift 8367688
  have htrace : WordTrace (prefixWord ++ tailWord_8367688) baseStart_8367688 baseEnd_8367688 := by
    simpa [prefixWord, tailWord_8367688, baseEnd_8367688] using wordTrace_append hprefix tailTrace_8367688
  have hstable : (prefixWord ++ tailWord_8367688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367688).length < 2 ^ (prefixWord ++ tailWord_8367688).sum := by decide
  have hdescent : baseEnd_8367688 < baseStart_8367688 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367709 : List Nat := [1, 4, 4, 2, 1, 1, 1, 1, 1, 2, 5]
def baseStart_8367709 : Nat := 118140960795 + 8367709 * 2 ^ 59
def prefixEnd_8367709 : Nat := 4983230072969 + 3 ^ 40 * 8367709 * 2
def baseEnd_8367709 : Nat := 4296656693952907033755113

theorem tailTrace_8367709 : CollatzResearch.WordTrace tailWord_8367709 prefixEnd_8367709 4296656693952907033755113 := by
  unfold tailWord_8367709
  simp only [CollatzResearch.WordTrace]
  refine ⟨305195420042226858766570181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203463613361484572511046787 305195420042226858766570181)
  ·
    refine ⟨57224141257917536018731909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305195420042226858766570181 57224141257917536018731909)
    ·
      refine ⟨10729526485859538003512233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57224141257917536018731909 10729526485859538003512233)
      ·
        refine ⟨8047144864394653502634175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10729526485859538003512233 8047144864394653502634175)
        ·
          refine ⟨12070717296591980253951263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8047144864394653502634175 12070717296591980253951263)
          ·
            refine ⟨18106075944887970380926895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12070717296591980253951263 18106075944887970380926895)
            ·
              refine ⟨27159113917331955571390343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18106075944887970380926895 27159113917331955571390343)
              ·
                refine ⟨40738670875997933357085515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27159113917331955571390343 40738670875997933357085515)
                ·
                  refine ⟨61108006313996900035628273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40738670875997933357085515 61108006313996900035628273)
                  ·
                    refine ⟨45831004735497675026721205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61108006313996900035628273 45831004735497675026721205)
                    ·
                      refine ⟨4296656693952907033755113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45831004735497675026721205 4296656693952907033755113)
                      ·
                        rfl

theorem cell23_8367709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_8367709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367709 prefixEnd_8367709 := by exact prefixLift 8367709
  have htrace : WordTrace (prefixWord ++ tailWord_8367709) baseStart_8367709 baseEnd_8367709 := by
    simpa [prefixWord, tailWord_8367709, baseEnd_8367709] using wordTrace_append hprefix tailTrace_8367709
  have hstable : (prefixWord ++ tailWord_8367709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367709).length < 2 ^ (prefixWord ++ tailWord_8367709).sum := by decide
  have hdescent : baseEnd_8367709 < baseStart_8367709 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367806 : List Nat := [4, 2, 1, 1, 2, 4, 2, 1, 1, 5]
def baseStart_8367806 : Nat := 118140960795 + 8367806 * 2 ^ 59
def prefixEnd_8367806 : Nat := 4983230072969 + 3 ^ 40 * 8367806 * 2
def baseEnd_8367806 : Nat := 1432235500525464384747389

theorem tailTrace_8367806 : CollatzResearch.WordTrace tailWord_8367806 prefixEnd_8367806 1432235500525464384747389 := by
  unfold tailWord_8367806
  simp only [CollatzResearch.WordTrace]
  refine ⟨38149869740359430541606409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203465971948583629555234181 38149869740359430541606409)
  ·
    refine ⟨28612402305269572906204807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38149869740359430541606409 28612402305269572906204807)
    ·
      refine ⟨42918603457904359359307211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28612402305269572906204807 42918603457904359359307211)
      ·
        refine ⟨64377905186856539038960817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42918603457904359359307211 64377905186856539038960817)
        ·
          refine ⟨48283428890142404279220613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64377905186856539038960817 48283428890142404279220613)
          ·
            refine ⟨9053142916901700802353865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48283428890142404279220613 9053142916901700802353865)
            ·
              refine ⟨6789857187676275601765399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9053142916901700802353865 6789857187676275601765399)
              ·
                refine ⟨10184785781514413402648099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6789857187676275601765399 10184785781514413402648099)
                ·
                  refine ⟨15277178672271620103972149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10184785781514413402648099 15277178672271620103972149)
                  ·
                    refine ⟨1432235500525464384747389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15277178672271620103972149 1432235500525464384747389)
                    ·
                      rfl

theorem cell23_8367806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_8367806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367806 prefixEnd_8367806 := by exact prefixLift 8367806
  have htrace : WordTrace (prefixWord ++ tailWord_8367806) baseStart_8367806 baseEnd_8367806 := by
    simpa [prefixWord, tailWord_8367806, baseEnd_8367806] using wordTrace_append hprefix tailTrace_8367806
  have hstable : (prefixWord ++ tailWord_8367806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367806).length < 2 ^ (prefixWord ++ tailWord_8367806).sum := by decide
  have hdescent : baseEnd_8367806 < baseStart_8367806 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367810 : List Nat := [3, 5, 1, 2, 2, 1, 1, 2, 6]
def baseStart_8367810 : Nat := 118140960795 + 8367810 * 2 ^ 59
def prefixEnd_8367810 : Nat := 4983230072969 + 3 ^ 40 * 8367810 * 2
def baseEnd_8367810 : Nat := 477412061722112348732461

theorem tailTrace_8367810 : CollatzResearch.WordTrace tailWord_8367810 prefixEnd_8367810 477412061722112348732461 := by
  unfold tailWord_8367810
  simp only [CollatzResearch.WordTrace]
  refine ⟨76299775953715238253999221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203466069209907302010664589 76299775953715238253999221)
  ·
    refine ⟨7153103995660803586312427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76299775953715238253999221 7153103995660803586312427)
    ·
      refine ⟨10729655993491205379468641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7153103995660803586312427 10729655993491205379468641)
      ·
        refine ⟨8047241995118404034601481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10729655993491205379468641 8047241995118404034601481)
        ·
          refine ⟨6035431496338803025951111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8047241995118404034601481 6035431496338803025951111)
          ·
            refine ⟨9053147244508204538926667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6035431496338803025951111 9053147244508204538926667)
            ·
              refine ⟨13579720866762306808390001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9053147244508204538926667 13579720866762306808390001)
              ·
                refine ⟨10184790650071730106292501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13579720866762306808390001 10184790650071730106292501)
                ·
                  refine ⟨477412061722112348732461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10184790650071730106292501 477412061722112348732461)
                  ·
                    rfl

theorem cell23_8367810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_8367810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367810 prefixEnd_8367810 := by exact prefixLift 8367810
  have htrace : WordTrace (prefixWord ++ tailWord_8367810) baseStart_8367810 baseEnd_8367810 := by
    simpa [prefixWord, tailWord_8367810, baseEnd_8367810] using wordTrace_append hprefix tailTrace_8367810
  have hstable : (prefixWord ++ tailWord_8367810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367810).length < 2 ^ (prefixWord ++ tailWord_8367810).sum := by decide
  have hdescent : baseEnd_8367810 < baseStart_8367810 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367812 : List Nat := [2, 3, 3, 1, 1, 1, 2, 3, 1, 1, 5]
def baseStart_8367812 : Nat := 118140960795 + 8367812 * 2 ^ 59
def prefixEnd_8367812 : Nat := 4983230072969 + 3 ^ 40 * 8367812 * 2
def baseEnd_8367812 : Nat := 4296709582460320130767139

theorem tailTrace_8367812 : CollatzResearch.WordTrace tailWord_8367812 prefixEnd_8367812 4296709582460320130767139 := by
  unfold tailWord_8367812
  simp only [CollatzResearch.WordTrace]
  refine ⟨152599588380426853678784845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203466117840569138238379793 152599588380426853678784845)
  ·
    refine ⟨57224845642660070129544317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152599588380426853678784845 57224845642660070129544317)
    ·
      refine ⟨21459317115997526298579119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57224845642660070129544317 21459317115997526298579119)
      ·
        refine ⟨32188975673996289447868679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21459317115997526298579119 32188975673996289447868679)
        ·
          refine ⟨48283463510994434171803019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32188975673996289447868679 48283463510994434171803019)
          ·
            refine ⟨72425195266491651257704529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48283463510994434171803019 72425195266491651257704529)
            ·
              refine ⟨54318896449868738443278397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72425195266491651257704529 54318896449868738443278397)
              ·
                refine ⟨20369586168700776916229399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54318896449868738443278397 20369586168700776916229399)
                ·
                  refine ⟨30554379253051165374344099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20369586168700776916229399 30554379253051165374344099)
                  ·
                    refine ⟨45831568879576748061516149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30554379253051165374344099 45831568879576748061516149)
                    ·
                      refine ⟨4296709582460320130767139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45831568879576748061516149 4296709582460320130767139)
                      ·
                        rfl

theorem cell23_8367812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_8367812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367812 prefixEnd_8367812 := by exact prefixLift 8367812
  have htrace : WordTrace (prefixWord ++ tailWord_8367812) baseStart_8367812 baseEnd_8367812 := by
    simpa [prefixWord, tailWord_8367812, baseEnd_8367812] using wordTrace_append hprefix tailTrace_8367812
  have hstable : (prefixWord ++ tailWord_8367812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367812).length < 2 ^ (prefixWord ++ tailWord_8367812).sum := by decide
  have hdescent : baseEnd_8367812 < baseStart_8367812 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367826 : List Nat := [3, 2, 2, 2, 2, 1, 1, 3, 3, 2, 2]
def baseStart_8367826 : Nat := 118140960795 + 8367826 * 2 ^ 59
def prefixEnd_8367826 : Nat := 4983230072969 + 3 ^ 40 * 8367826 * 2
def baseEnd_8367826 : Nat := 4296716771189483075992075

theorem tailTrace_8367826 : CollatzResearch.WordTrace tailWord_8367826 prefixEnd_8367826 4296716771189483075992075 := by
  unfold tailWord_8367826
  simp only [CollatzResearch.WordTrace]
  refine ⟨76299921845700746937144833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203466458255201991832386221 76299921845700746937144833)
  ·
    refine ⟨57224941384275560202858625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76299921845700746937144833 57224941384275560202858625)
    ·
      refine ⟨42918706038206670152143969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57224941384275560202858625 42918706038206670152143969)
      ·
        refine ⟨32189029528655002614107977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42918706038206670152143969 32189029528655002614107977)
        ·
          refine ⟨24141772146491251960580983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32189029528655002614107977 24141772146491251960580983)
          ·
            refine ⟨36212658219736877940871475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24141772146491251960580983 36212658219736877940871475)
            ·
              refine ⟨54318987329605316911307213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36212658219736877940871475 54318987329605316911307213)
              ·
                refine ⟨20369620248601993841740205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54318987329605316911307213 20369620248601993841740205)
                ·
                  refine ⟨7638607593225747690652577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20369620248601993841740205 7638607593225747690652577)
                  ·
                    refine ⟨5728955694919310767989433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7638607593225747690652577 5728955694919310767989433)
                    ·
                      refine ⟨4296716771189483075992075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5728955694919310767989433 4296716771189483075992075)
                      ·
                        rfl

theorem cell23_8367826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_8367826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367826 prefixEnd_8367826 := by exact prefixLift 8367826
  have htrace : WordTrace (prefixWord ++ tailWord_8367826) baseStart_8367826 baseEnd_8367826 := by
    simpa [prefixWord, tailWord_8367826, baseEnd_8367826] using wordTrace_append hprefix tailTrace_8367826
  have hstable : (prefixWord ++ tailWord_8367826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367826).length < 2 ^ (prefixWord ++ tailWord_8367826).sum := by decide
  have hdescent : baseEnd_8367826 < baseStart_8367826 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367836 : List Nat := [2, 2, 5, 1, 2, 2, 1, 1, 1, 6]
def baseStart_8367836 : Nat := 118140960795 + 8367836 * 2 ^ 59
def prefixEnd_8367836 : Nat := 4983230072969 + 3 ^ 40 * 8367836 * 2
def baseEnd_8367836 : Nat := 1432240635332009345622343

theorem tailTrace_8367836 : CollatzResearch.WordTrace tailWord_8367836 prefixEnd_8367836 1432240635332009345622343 := by
  unfold tailWord_8367836
  simp only [CollatzResearch.WordTrace]
  refine ⟨152600026056383379728221681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203466701408511172970962241 152600026056383379728221681)
  ·
    refine ⟨114450019542287534796166261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152600026056383379728221681 114450019542287534796166261)
    ·
      refine ⟨10729689332089456387140587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114450019542287534796166261 10729689332089456387140587)
      ·
        refine ⟨16094533998134184580710881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10729689332089456387140587 16094533998134184580710881)
        ·
          refine ⟨12070900498600638435533161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16094533998134184580710881 12070900498600638435533161)
          ·
            refine ⟨9053175373950478826649871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12070900498600638435533161 9053175373950478826649871)
            ·
              refine ⟨13579763060925718239974807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9053175373950478826649871 13579763060925718239974807)
              ·
                refine ⟨20369644591388577359962211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13579763060925718239974807 20369644591388577359962211)
                ·
                  refine ⟨30554466887082866039943317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20369644591388577359962211 30554466887082866039943317)
                  ·
                    refine ⟨1432240635332009345622343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30554466887082866039943317 1432240635332009345622343)
                    ·
                      rfl

theorem cell23_8367836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_8367836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367836 prefixEnd_8367836 := by exact prefixLift 8367836
  have htrace : WordTrace (prefixWord ++ tailWord_8367836) baseStart_8367836 baseEnd_8367836 := by
    simpa [prefixWord, tailWord_8367836, baseEnd_8367836] using wordTrace_append hprefix tailTrace_8367836
  have hstable : (prefixWord ++ tailWord_8367836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367836).length < 2 ^ (prefixWord ++ tailWord_8367836).sum := by decide
  have hdescent : baseEnd_8367836 < baseStart_8367836 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367855 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 5]
def baseStart_8367855 : Nat := 118140960795 + 8367855 * 2 ^ 59
def prefixEnd_8367855 : Nat := 4983230072969 + 3 ^ 40 * 8367855 * 2
def baseEnd_8367855 : Nat := 4296731662128463462529441

theorem tailTrace_8367855 : CollatzResearch.WordTrace tailWord_8367855 prefixEnd_8367855 4296731662128463462529441 := by
  unfold tailWord_8367855
  simp only [CollatzResearch.WordTrace]
  refine ⟨305200745099697925701385019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203467163399798617134256679 305200745099697925701385019)
  ·
    refine ⟨457801117649546888552077529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305200745099697925701385019 457801117649546888552077529)
    ·
      refine ⟨343350838237160166414058147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457801117649546888552077529 343350838237160166414058147)
      ·
        refine ⟨515026257355740249621087221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343350838237160166414058147 515026257355740249621087221)
        ·
          refine ⟨48283711627100648401976927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 515026257355740249621087221 48283711627100648401976927)
          ·
            refine ⟨72425567440650972602965391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48283711627100648401976927 72425567440650972602965391)
            ·
              refine ⟨108638351160976458904448087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72425567440650972602965391 108638351160976458904448087)
              ·
                refine ⟨162957526741464688356672131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108638351160976458904448087 162957526741464688356672131)
                ·
                  refine ⟨244436290112197032535008197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162957526741464688356672131 244436290112197032535008197)
                  ·
                    refine ⟨45831804396036943600314037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 244436290112197032535008197 45831804396036943600314037)
                    ·
                      refine ⟨4296731662128463462529441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45831804396036943600314037 4296731662128463462529441)
                      ·
                        rfl

theorem cell23_8367855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 5].length) (baseStart_8367855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367855 prefixEnd_8367855 := by exact prefixLift 8367855
  have htrace : WordTrace (prefixWord ++ tailWord_8367855) baseStart_8367855 baseEnd_8367855 := by
    simpa [prefixWord, tailWord_8367855, baseEnd_8367855] using wordTrace_append hprefix tailTrace_8367855
  have hstable : (prefixWord ++ tailWord_8367855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367855).length < 2 ^ (prefixWord ++ tailWord_8367855).sum := by decide
  have hdescent : baseEnd_8367855 < baseStart_8367855 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367865 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 3, 5, 4]
def baseStart_8367865 : Nat := 118140960795 + 8367865 * 2 ^ 59
def prefixEnd_8367865 : Nat := 4983230072969 + 3 ^ 40 * 8367865 * 2
def baseEnd_8367865 : Nat := 4296736796935008423404395

theorem tailTrace_8367865 : CollatzResearch.WordTrace tailWord_8367865 prefixEnd_8367865 4296736796935008423404395 := by
  unfold tailWord_8367865
  simp only [CollatzResearch.WordTrace]
  refine ⟨305201109829661697409249049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203467406553107798272832699 305201109829661697409249049)
  ·
    refine ⟨228900832372246273056936787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305201109829661697409249049 228900832372246273056936787)
    ·
      refine ⟨343351248558369409585405181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228900832372246273056936787 343351248558369409585405181)
      ·
        refine ⟨128756718209388528594526943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343351248558369409585405181 128756718209388528594526943)
        ·
          refine ⟨193135077314082792891790415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128756718209388528594526943 193135077314082792891790415)
          ·
            refine ⟨289702615971124189337685623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193135077314082792891790415 289702615971124189337685623)
            ·
              refine ⟨434553923956686284006528435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289702615971124189337685623 434553923956686284006528435)
              ·
                refine ⟨651830885935029426009792653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434553923956686284006528435 651830885935029426009792653)
                ·
                  refine ⟨244436582225636034753672245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 651830885935029426009792653 244436582225636034753672245)
                  ·
                    refine ⟨22915929583653378258156773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 244436582225636034753672245 22915929583653378258156773)
                    ·
                      refine ⟨4296736796935008423404395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22915929583653378258156773 4296736796935008423404395)
                      ·
                        rfl

theorem cell23_8367865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_8367865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367865 prefixEnd_8367865 := by exact prefixLift 8367865
  have htrace : WordTrace (prefixWord ++ tailWord_8367865) baseStart_8367865 baseEnd_8367865 := by
    simpa [prefixWord, tailWord_8367865, baseEnd_8367865] using wordTrace_append hprefix tailTrace_8367865
  have hstable : (prefixWord ++ tailWord_8367865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367865).length < 2 ^ (prefixWord ++ tailWord_8367865).sum := by decide
  have hdescent : baseEnd_8367865 < baseStart_8367865 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367875 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 4, 6]
def baseStart_8367875 : Nat := 118140960795 + 8367875 * 2 ^ 59
def prefixEnd_8367875 : Nat := 4983230072969 + 3 ^ 40 * 8367875 * 2
def baseEnd_8367875 : Nat := 1432247310580517794759783

theorem tailTrace_8367875 : CollatzResearch.WordTrace tailWord_8367875 prefixEnd_8367875 1432247310580517794759783 := by
  unfold tailWord_8367875
  simp only [CollatzResearch.WordTrace]
  refine ⟨305201474559625469117113079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203467649706416979411408719 305201474559625469117113079)
  ·
    refine ⟨457802211839438203675669619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305201474559625469117113079 457802211839438203675669619)
    ·
      refine ⟨686703317759157305513504429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457802211839438203675669619 686703317759157305513504429)
      ·
        refine ⟨257513744159683989567564161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 686703317759157305513504429 257513744159683989567564161)
        ·
          refine ⟨193135308119762992175673121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257513744159683989567564161 193135308119762992175673121)
          ·
            refine ⟨144851481089822244131754841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193135308119762992175673121 144851481089822244131754841)
            ·
              refine ⟨108638610817366683098816131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144851481089822244131754841 108638610817366683098816131)
              ·
                refine ⟨162957916226050024648224197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108638610817366683098816131 162957916226050024648224197)
                ·
                  refine ⟨30554609292384379621542037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162957916226050024648224197 30554609292384379621542037)
                  ·
                    refine ⟨1432247310580517794759783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30554609292384379621542037 1432247310580517794759783)
                    ·
                      rfl

theorem cell23_8367875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 6].length) (baseStart_8367875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367875 prefixEnd_8367875 := by exact prefixLift 8367875
  have htrace : WordTrace (prefixWord ++ tailWord_8367875) baseStart_8367875 baseEnd_8367875 := by
    simpa [prefixWord, tailWord_8367875, baseEnd_8367875] using wordTrace_append hprefix tailTrace_8367875
  have hstable : (prefixWord ++ tailWord_8367875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367875).length < 2 ^ (prefixWord ++ tailWord_8367875).sum := by decide
  have hdescent : baseEnd_8367875 < baseStart_8367875 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367893 : List Nat := [1, 3, 2, 1, 2, 5, 2, 1, 2, 1, 3]
def baseStart_8367893 : Nat := 118140960795 + 8367893 * 2 ^ 59
def prefixEnd_8367893 : Nat := 4983230072969 + 3 ^ 40 * 8367893 * 2
def baseEnd_8367893 : Nat := 4296751174393334313854267

theorem tailTrace_8367893 : CollatzResearch.WordTrace tailWord_8367893 prefixEnd_8367893 4296751174393334313854267 := by
  unfold tailWord_8367893
  simp only [CollatzResearch.WordTrace]
  refine ⟨305202131073560258191268333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203468087382373505460845555 305202131073560258191268333)
  ·
    refine ⟨114450799152585096821725625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305202131073560258191268333 114450799152585096821725625)
    ·
      refine ⟨85838099364438822616294219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114450799152585096821725625 85838099364438822616294219)
      ·
        refine ⟨128757149046658233924441329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85838099364438822616294219 128757149046658233924441329)
        ·
          refine ⟨96567861784993675443330997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128757149046658233924441329 96567861784993675443330997)
          ·
            refine ⟨9053237042343157072812281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96567861784993675443330997 9053237042343157072812281)
            ·
              refine ⟨6789927781757367804609211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9053237042343157072812281 6789927781757367804609211)
              ·
                refine ⟨10184891672636051706913817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6789927781757367804609211 10184891672636051706913817)
                ·
                  refine ⟨7638668754477038780185363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10184891672636051706913817 7638668754477038780185363)
                  ·
                    refine ⟨11458003131715558170278045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7638668754477038780185363 11458003131715558170278045)
                    ·
                      refine ⟨4296751174393334313854267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11458003131715558170278045 4296751174393334313854267)
                      ·
                        rfl

theorem cell23_8367893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 2, 1, 3].length) (baseStart_8367893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367893 prefixEnd_8367893 := by exact prefixLift 8367893
  have htrace : WordTrace (prefixWord ++ tailWord_8367893) baseStart_8367893 baseEnd_8367893 := by
    simpa [prefixWord, tailWord_8367893, baseEnd_8367893] using wordTrace_append hprefix tailTrace_8367893
  have hstable : (prefixWord ++ tailWord_8367893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367893).length < 2 ^ (prefixWord ++ tailWord_8367893).sum := by decide
  have hdescent : baseEnd_8367893 < baseStart_8367893 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367933 : List Nat := [1, 4, 1, 4, 1, 1, 1, 4, 2, 2, 2]
def baseStart_8367933 : Nat := 118140960795 + 8367933 * 2 ^ 59
def prefixEnd_8367933 : Nat := 4983230072969 + 3 ^ 40 * 8367933 * 2
def baseEnd_8367933 : Nat := 4296771713619514157354083

theorem tailTrace_8367933 : CollatzResearch.WordTrace tailWord_8367933 prefixEnd_8367933 4296771713619514157354083 := by
  unfold tailWord_8367933
  simp only [CollatzResearch.WordTrace]
  refine ⟨305203589993415345022724453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203469059995610230015149635 305203589993415345022724453)
  ·
    refine ⟨57225673123765377191760835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305203589993415345022724453 57225673123765377191760835)
    ·
      refine ⟨85838509685648065787641253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57225673123765377191760835 85838509685648065787641253)
      ·
        refine ⟨16094720566059012335182735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85838509685648065787641253 16094720566059012335182735)
        ·
          refine ⟨24142080849088518502774103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16094720566059012335182735 24142080849088518502774103)
          ·
            refine ⟨36213121273632777754161155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24142080849088518502774103 36213121273632777754161155)
            ·
              refine ⟨54319681910449166631241733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36213121273632777754161155 54319681910449166631241733)
              ·
                refine ⟨10184940358209218743357825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54319681910449166631241733 10184940358209218743357825)
                ·
                  refine ⟨7638705268656914057518369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10184940358209218743357825 7638705268656914057518369)
                  ·
                    refine ⟨5729028951492685543138777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7638705268656914057518369 5729028951492685543138777)
                    ·
                      refine ⟨4296771713619514157354083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5729028951492685543138777 4296771713619514157354083)
                      ·
                        rfl

theorem cell23_8367933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_8367933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367933 prefixEnd_8367933 := by exact prefixLift 8367933
  have htrace : WordTrace (prefixWord ++ tailWord_8367933) baseStart_8367933 baseEnd_8367933 := by
    simpa [prefixWord, tailWord_8367933, baseEnd_8367933] using wordTrace_append hprefix tailTrace_8367933
  have hstable : (prefixWord ++ tailWord_8367933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367933).length < 2 ^ (prefixWord ++ tailWord_8367933).sum := by decide
  have hdescent : baseEnd_8367933 < baseStart_8367933 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367939 : List Nat := [1, 1, 1, 3, 1, 6, 1, 4, 5]
def baseStart_8367939 : Nat := 118140960795 + 8367939 * 2 ^ 59
def prefixEnd_8367939 : Nat := 4983230072969 + 3 ^ 40 * 8367939 * 2
def baseEnd_8367939 : Nat := 477419421611493459319895

theorem tailTrace_8367939 : CollatzResearch.WordTrace tailWord_8367939 prefixEnd_8367939 477419421611493459319895 := by
  unfold tailWord_8367939
  simp only [CollatzResearch.WordTrace]
  refine ⟨305203808831393608047442871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203469205887595738698295247 305203808831393608047442871)
  ·
    refine ⟨457805713247090412071164307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305203808831393608047442871 457805713247090412071164307)
    ·
      refine ⟨686708569870635618106746461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457805713247090412071164307 686708569870635618106746461)
      ·
        refine ⟨257515713701488356790029923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 686708569870635618106746461 257515713701488356790029923)
        ·
          refine ⟨386273570552232535185044885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257515713701488356790029923 386273570552232535185044885)
          ·
            refine ⟨18106573619635900086798979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 386273570552232535185044885 18106573619635900086798979)
            ·
              refine ⟨27159860429453850130198469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18106573619635900086798979 27159860429453850130198469)
              ·
                refine ⟨5092473830522596899412213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27159860429453850130198469 5092473830522596899412213)
                ·
                  refine ⟨477419421611493459319895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5092473830522596899412213 477419421611493459319895)
                  ·
                    rfl

theorem cell23_8367939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 4, 5].length) (baseStart_8367939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367939 prefixEnd_8367939 := by exact prefixLift 8367939
  have htrace : WordTrace (prefixWord ++ tailWord_8367939) baseStart_8367939 baseEnd_8367939 := by
    simpa [prefixWord, tailWord_8367939, baseEnd_8367939] using wordTrace_append hprefix tailTrace_8367939
  have hstable : (prefixWord ++ tailWord_8367939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367939).length < 2 ^ (prefixWord ++ tailWord_8367939).sum := by decide
  have hdescent : baseEnd_8367939 < baseStart_8367939 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8367989 : List Nat := [1, 3, 4, 1, 1, 1, 2, 1, 4, 1, 4]
def baseStart_8367989 : Nat := 118140960795 + 8367989 * 2 ^ 59
def prefixEnd_8367989 : Nat := 4983230072969 + 3 ^ 40 * 8367989 * 2
def baseEnd_8367989 : Nat := 4296800468536165938253825

theorem tailTrace_8367989 : CollatzResearch.WordTrace tailWord_8367989 prefixEnd_8367989 4296800468536165938253825 := by
  unfold tailWord_8367989
  simp only [CollatzResearch.WordTrace]
  refine ⟨305205632481212466586763021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203470421654141644391175347 305205632481212466586763021)
  ·
    refine ⟨114452112180454674970036133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305205632481212466586763021 114452112180454674970036133)
    ·
      refine ⟨21459771033835251556881775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114452112180454674970036133 21459771033835251556881775)
      ·
        refine ⟨32189656550752877335322663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21459771033835251556881775 32189656550752877335322663)
        ·
          refine ⟨48284484826129316002983995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32189656550752877335322663 48284484826129316002983995)
          ·
            refine ⟨72426727239193974004475993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48284484826129316002983995 72426727239193974004475993)
            ·
              refine ⟨54320045429395480503356995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72426727239193974004475993 54320045429395480503356995)
              ·
                refine ⟨81480068144093220755035493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54320045429395480503356995 81480068144093220755035493)
                ·
                  refine ⟨15277512777017478891569155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81480068144093220755035493 15277512777017478891569155)
                  ·
                    refine ⟨22916269165526218337353733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15277512777017478891569155 22916269165526218337353733)
                    ·
                      refine ⟨4296800468536165938253825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22916269165526218337353733 4296800468536165938253825)
                      ·
                        rfl

theorem cell23_8367989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_8367989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8367989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8367989 prefixEnd_8367989 := by exact prefixLift 8367989
  have htrace : WordTrace (prefixWord ++ tailWord_8367989) baseStart_8367989 baseEnd_8367989 := by
    simpa [prefixWord, tailWord_8367989, baseEnd_8367989] using wordTrace_append hprefix tailTrace_8367989
  have hstable : (prefixWord ++ tailWord_8367989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8367989).length < 2 ^ (prefixWord ++ tailWord_8367989).sum := by decide
  have hdescent : baseEnd_8367989 < baseStart_8367989 := by decide
  rcases family_descends (prefixWord ++ tailWord_8367989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368076 : List Nat := [2, 2, 1, 4, 1, 2, 3, 2, 1, 5]
def baseStart_8368076 : Nat := 118140960795 + 8368076 * 2 ^ 59
def prefixEnd_8368076 : Nat := 4983230072969 + 3 ^ 40 * 8368076 * 2
def baseEnd_8368076 : Nat := 1432281713784369032621975

theorem tailTrace_8368076 : CollatzResearch.WordTrace tailWord_8368076 prefixEnd_8368076 1432281713784369032621975 := by
  unfold tailWord_8368076
  simp only [CollatzResearch.WordTrace]
  refine ⟨152604402815948640222590041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203472537087931520296786721 152604402815948640222590041)
  ·
    refine ⟨114453302111961480166942531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152604402815948640222590041 114453302111961480166942531)
    ·
      refine ⟨171679953167942220250413797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114453302111961480166942531 171679953167942220250413797)
      ·
        refine ⟨32189991218989166296952587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171679953167942220250413797 32189991218989166296952587)
        ·
          refine ⟨48284986828483749445428881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32189991218989166296952587 48284986828483749445428881)
          ·
            refine ⟨36213740121362812084071661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48284986828483749445428881 36213740121362812084071661)
            ·
              refine ⟨13580152545511054531526873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36213740121362812084071661 13580152545511054531526873)
              ·
                refine ⟨10185114409133290898645155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13580152545511054531526873 10185114409133290898645155)
                ·
                  refine ⟨15277671613699936347967733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10185114409133290898645155 15277671613699936347967733)
                  ·
                    refine ⟨1432281713784369032621975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15277671613699936347967733 1432281713784369032621975)
                    ·
                      rfl

theorem cell23_8368076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 1, 5].length) (baseStart_8368076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368076 prefixEnd_8368076 := by exact prefixLift 8368076
  have htrace : WordTrace (prefixWord ++ tailWord_8368076) baseStart_8368076 baseEnd_8368076 := by
    simpa [prefixWord, tailWord_8368076, baseEnd_8368076] using wordTrace_append hprefix tailTrace_8368076
  have hstable : (prefixWord ++ tailWord_8368076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368076).length < 2 ^ (prefixWord ++ tailWord_8368076).sum := by decide
  have hdescent : baseEnd_8368076 < baseStart_8368076 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368079 : List Nat := [1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 4]
def baseStart_8368079 : Nat := 118140960795 + 8368079 * 2 ^ 59
def prefixEnd_8368079 : Nat := 4983230072969 + 3 ^ 40 * 8368079 * 2
def baseEnd_8368079 : Nat := 4296846681795070586128411

theorem tailTrace_8368079 : CollatzResearch.WordTrace tailWord_8368079 prefixEnd_8368079 4296846681795070586128411 := by
  unfold tailWord_8368079
  simp only [CollatzResearch.WordTrace]
  refine ⟨305208915050886411957539291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203472610033924274638359527 305208915050886411957539291)
  ·
    refine ⟨457813372576329617936308937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305208915050886411957539291 457813372576329617936308937)
    ·
      refine ⟨343360029432247213452231703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457813372576329617936308937 343360029432247213452231703)
      ·
        refine ⟨515040044148370820178347555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343360029432247213452231703 515040044148370820178347555)
        ·
          refine ⟨772560066222556230267521333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515040044148370820178347555 772560066222556230267521333)
          ·
            refine ⟨72427506208364646587580125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 772560066222556230267521333 72427506208364646587580125)
            ·
              refine ⟨27160314828136742470342547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72427506208364646587580125 27160314828136742470342547)
              ·
                refine ⟨40740472242205113705513821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27160314828136742470342547 40740472242205113705513821)
                ·
                  refine ⟨15277677090826917639567683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40740472242205113705513821 15277677090826917639567683)
                  ·
                    refine ⟨22916515636240376459351525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15277677090826917639567683 22916515636240376459351525)
                    ·
                      refine ⟨4296846681795070586128411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22916515636240376459351525 4296846681795070586128411)
                      ·
                        rfl

theorem cell23_8368079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 4].length) (baseStart_8368079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368079 prefixEnd_8368079 := by exact prefixLift 8368079
  have htrace : WordTrace (prefixWord ++ tailWord_8368079) baseStart_8368079 baseEnd_8368079 := by
    simpa [prefixWord, tailWord_8368079, baseEnd_8368079] using wordTrace_append hprefix tailTrace_8368079
  have hstable : (prefixWord ++ tailWord_8368079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368079).length < 2 ^ (prefixWord ++ tailWord_8368079).sum := by decide
  have hdescent : baseEnd_8368079 < baseStart_8368079 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368134 : List Nat := [6, 2, 1, 2, 1, 1, 1, 1, 1, 5, 2]
def baseStart_8368134 : Nat := 118140960795 + 8368134 * 2 ^ 59
def prefixEnd_8368134 : Nat := 4983230072969 + 3 ^ 40 * 8368134 * 2
def baseEnd_8368134 : Nat := 4296874923231067870940659

theorem tailTrace_8368134 : CollatzResearch.WordTrace tailWord_8368134 prefixEnd_8368134 4296874923231067870940659 := by
  unfold tailWord_8368134
  simp only [CollatzResearch.WordTrace]
  refine ⟨9537841283302723635962233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 203473947377124770900527637 9537841283302723635962233)
  ·
    refine ⟨7153380962477042726971675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9537841283302723635962233 7153380962477042726971675)
    ·
      refine ⟨10730071443715564090457513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7153380962477042726971675 10730071443715564090457513)
      ·
        refine ⟨8047553582786673067843135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10730071443715564090457513 8047553582786673067843135)
        ·
          refine ⟨12071330374180009601764703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8047553582786673067843135 12071330374180009601764703)
          ·
            refine ⟨18106995561270014402647055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12071330374180009601764703 18106995561270014402647055)
            ·
              refine ⟨27160493341905021603970583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18106995561270014402647055 27160493341905021603970583)
              ·
                refine ⟨40740740012857532405955875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27160493341905021603970583 40740740012857532405955875)
                ·
                  refine ⟨61111110019286298608933813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40740740012857532405955875 61111110019286298608933813)
                  ·
                    refine ⟨5729166564308090494587545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61111110019286298608933813 5729166564308090494587545)
                    ·
                      refine ⟨4296874923231067870940659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5729166564308090494587545 4296874923231067870940659)
                      ·
                        rfl

theorem cell23_8368134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_8368134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368134 prefixEnd_8368134 := by exact prefixLift 8368134
  have htrace : WordTrace (prefixWord ++ tailWord_8368134) baseStart_8368134 baseEnd_8368134 := by
    simpa [prefixWord, tailWord_8368134, baseEnd_8368134] using wordTrace_append hprefix tailTrace_8368134
  have hstable : (prefixWord ++ tailWord_8368134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368134).length < 2 ^ (prefixWord ++ tailWord_8368134).sum := by decide
  have hdescent : baseEnd_8368134 < baseStart_8368134 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368141 : List Nat := [1, 7, 1, 2, 1, 1, 2, 3, 1, 1, 3]
def baseStart_8368141 : Nat := 118140960795 + 8368141 * 2 ^ 59
def prefixEnd_8368141 : Nat := 4983230072969 + 3 ^ 40 * 8368141 * 2
def baseEnd_8368141 : Nat := 4296878517595649343553127

theorem tailTrace_8368141 : CollatzResearch.WordTrace tailWord_8368141 prefixEnd_8368141 4296878517595649343553127 := by
  unfold tailWord_8368141
  simp only [CollatzResearch.WordTrace]
  refine ⟨305211176376661796546296277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203474117584441197697530851 305211176376661796546296277)
  ·
    refine ⟨7153386946328010856553819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 305211176376661796546296277 7153386946328010856553819)
    ·
      refine ⟨10730080419492016284830729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7153386946328010856553819 10730080419492016284830729)
      ·
        refine ⟨8047560314619012213623047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10730080419492016284830729 8047560314619012213623047)
        ·
          refine ⟨12071340471928518320434571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8047560314619012213623047 12071340471928518320434571)
          ·
            refine ⟨18107010707892777480651857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12071340471928518320434571 18107010707892777480651857)
            ·
              refine ⟨13580258030919583110488893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18107010707892777480651857 13580258030919583110488893)
              ·
                refine ⟨5092596761594843666433335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13580258030919583110488893 5092596761594843666433335)
                ·
                  refine ⟨7638895142392265499650003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5092596761594843666433335 7638895142392265499650003)
                  ·
                    refine ⟨11458342713588398249475005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7638895142392265499650003 11458342713588398249475005)
                    ·
                      refine ⟨4296878517595649343553127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11458342713588398249475005 4296878517595649343553127)
                      ·
                        rfl

theorem cell23_8368141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_8368141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368141 prefixEnd_8368141 := by exact prefixLift 8368141
  have htrace : WordTrace (prefixWord ++ tailWord_8368141) baseStart_8368141 baseEnd_8368141 := by
    simpa [prefixWord, tailWord_8368141, baseEnd_8368141] using wordTrace_append hprefix tailTrace_8368141
  have hstable : (prefixWord ++ tailWord_8368141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368141).length < 2 ^ (prefixWord ++ tailWord_8368141).sum := by decide
  have hdescent : baseEnd_8368141 < baseStart_8368141 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368179 : List Nat := [1, 1, 1, 2, 4, 1, 4, 1, 2, 6]
def baseStart_8368179 : Nat := 118140960795 + 8368179 * 2 ^ 59
def prefixEnd_8368179 : Nat := 4983230072969 + 3 ^ 40 * 8368179 * 2
def baseEnd_8368179 : Nat := 1432299343286840064959317

theorem tailTrace_8368179 : CollatzResearch.WordTrace tailWord_8368179 prefixEnd_8368179 1432299343286840064959317 := by
  unfold tailWord_8368179
  simp only [CollatzResearch.WordTrace]
  refine ⟨305212562350524129036179591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203475041567016086024119727 305212562350524129036179591)
  ·
    refine ⟨457818843525786193554269387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305212562350524129036179591 457818843525786193554269387)
    ·
      refine ⟨686728265288679290331404081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457818843525786193554269387 686728265288679290331404081)
      ·
        refine ⟨515046198966509467748553061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 686728265288679290331404081 515046198966509467748553061)
        ·
          refine ⟨96571162306220525202853699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 515046198966509467748553061 96571162306220525202853699)
          ·
            refine ⟨144856743459330787804280549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96571162306220525202853699 144856743459330787804280549)
            ·
              refine ⟨27160639398624522713302603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144856743459330787804280549 27160639398624522713302603)
              ·
                refine ⟨40740959097936784069953905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27160639398624522713302603 40740959097936784069953905)
                ·
                  refine ⟨30555719323452588052465429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40740959097936784069953905 30555719323452588052465429)
                  ·
                    refine ⟨1432299343286840064959317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30555719323452588052465429 1432299343286840064959317)
                    ·
                      rfl

theorem cell23_8368179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 6].length) (baseStart_8368179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368179 prefixEnd_8368179 := by exact prefixLift 8368179
  have htrace : WordTrace (prefixWord ++ tailWord_8368179) baseStart_8368179 baseEnd_8368179 := by
    simpa [prefixWord, tailWord_8368179, baseEnd_8368179] using wordTrace_append hprefix tailTrace_8368179
  have hstable : (prefixWord ++ tailWord_8368179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368179).length < 2 ^ (prefixWord ++ tailWord_8368179).sum := by decide
  have hdescent : baseEnd_8368179 < baseStart_8368179 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368206 : List Nat := [4, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5]
def baseStart_8368206 : Nat := 118140960795 + 8368206 * 2 ^ 59
def prefixEnd_8368206 : Nat := 4983230072969 + 3 ^ 40 * 8368206 * 2
def baseEnd_8368206 : Nat := 4296911893838191589240327

theorem tailTrace_8368206 : CollatzResearch.WordTrace tailWord_8368206 prefixEnd_8368206 4296911893838191589240327 := by
  unfold tailWord_8368206
  simp only [CollatzResearch.WordTrace]
  refine ⟨38151693390178289080926559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203475698080950875098274981 38151693390178289080926559)
  ·
    refine ⟨57227540085267433621389839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38151693390178289080926559 57227540085267433621389839)
    ·
      refine ⟨85841310127901150432084759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57227540085267433621389839 85841310127901150432084759)
      ·
        refine ⟨128761965191851725648127139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85841310127901150432084759 128761965191851725648127139)
        ·
          refine ⟨193142947787777588472190709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128761965191851725648127139 193142947787777588472190709)
          ·
            refine ⟨18107151355104148919267879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 193142947787777588472190709 18107151355104148919267879)
            ·
              refine ⟨27160727032656223378901819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18107151355104148919267879 27160727032656223378901819)
              ·
                refine ⟨40741090548984335068352729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27160727032656223378901819 40741090548984335068352729)
                ·
                  refine ⟨30555817911738251301264547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40741090548984335068352729 30555817911738251301264547)
                  ·
                    refine ⟨45833726867607376951896821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30555817911738251301264547 45833726867607376951896821)
                    ·
                      refine ⟨4296911893838191589240327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45833726867607376951896821 4296911893838191589240327)
                      ·
                        rfl

theorem cell23_8368206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_8368206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368206 prefixEnd_8368206 := by exact prefixLift 8368206
  have htrace : WordTrace (prefixWord ++ tailWord_8368206) baseStart_8368206 baseEnd_8368206 := by
    simpa [prefixWord, tailWord_8368206, baseEnd_8368206] using wordTrace_append hprefix tailTrace_8368206
  have hstable : (prefixWord ++ tailWord_8368206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368206).length < 2 ^ (prefixWord ++ tailWord_8368206).sum := by decide
  have hdescent : baseEnd_8368206 < baseStart_8368206 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368220 : List Nat := [2, 2, 4, 1, 1, 2, 2, 1, 4, 2, 2]
def baseStart_8368220 : Nat := 118140960795 + 8368220 * 2 ^ 59
def prefixEnd_8368220 : Nat := 4983230072969 + 3 ^ 40 * 8368220 * 2
def baseEnd_8368220 : Nat := 4296919082567354534465263

theorem tailTrace_8368220 : CollatzResearch.WordTrace tailWord_8368220 prefixEnd_8368220 4296919082567354534465263 := by
  unfold tailWord_8368220
  simp only [CollatzResearch.WordTrace]
  refine ⟨152607028871687796519211057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203476038495583728692281409 152607028871687796519211057)
  ·
    refine ⟨114455271653765847389408293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152607028871687796519211057 114455271653765847389408293)
    ·
      refine ⟨21460363435081096385514055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114455271653765847389408293 21460363435081096385514055)
      ·
        refine ⟨32190545152621644578271083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21460363435081096385514055 32190545152621644578271083)
        ·
          refine ⟨48285817728932466867406625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32190545152621644578271083 48285817728932466867406625)
          ·
            refine ⟨36214363296699350150554969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48285817728932466867406625 36214363296699350150554969)
            ·
              refine ⟨27160772472524512612916227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36214363296699350150554969 27160772472524512612916227)
              ·
                refine ⟨40741158708786768919374341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27160772472524512612916227 40741158708786768919374341)
                ·
                  refine ⟨7638967257897519172382689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40741158708786768919374341 7638967257897519172382689)
                  ·
                    refine ⟨5729225443423139379287017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7638967257897519172382689 5729225443423139379287017)
                    ·
                      refine ⟨4296919082567354534465263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5729225443423139379287017 4296919082567354534465263)
                      ·
                        rfl

theorem cell23_8368220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_8368220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368220 prefixEnd_8368220 := by exact prefixLift 8368220
  have htrace : WordTrace (prefixWord ++ tailWord_8368220) baseStart_8368220 baseEnd_8368220 := by
    simpa [prefixWord, tailWord_8368220, baseEnd_8368220] using wordTrace_append hprefix tailTrace_8368220
  have hstable : (prefixWord ++ tailWord_8368220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368220).length < 2 ^ (prefixWord ++ tailWord_8368220).sum := by decide
  have hdescent : baseEnd_8368220 < baseStart_8368220 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368266 : List Nat := [3, 1, 2, 3, 1, 2, 1, 2, 1, 2, 5]
def baseStart_8368266 : Nat := 118140960795 + 8368266 * 2 ^ 59
def prefixEnd_8368266 : Nat := 4983230072969 + 3 ^ 40 * 8368266 * 2
def baseEnd_8368266 : Nat := 4296942702677461354490051

theorem tailTrace_8368266 : CollatzResearch.WordTrace tailWord_8368266 prefixEnd_8368266 4296942702677461354490051 := by
  unfold tailWord_8368266
  simp only [CollatzResearch.WordTrace]
  refine ⟨76303933875302235723649163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203477157000805961929731101 76303933875302235723649163)
  ·
    refine ⟨114455900812953353585473745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76303933875302235723649163 114455900812953353585473745)
    ·
      refine ⟨85841925609715015189105309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114455900812953353585473745 85841925609715015189105309)
      ·
        refine ⟨32190722103643130695914491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85841925609715015189105309 32190722103643130695914491)
        ·
          refine ⟨48286083155464696043871737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32190722103643130695914491 48286083155464696043871737)
          ·
            refine ⟨36214562366598522032903803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48286083155464696043871737 36214562366598522032903803)
            ·
              refine ⟨54321843549897783049355705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36214562366598522032903803 54321843549897783049355705)
              ·
                refine ⟨40741382662423337287016779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54321843549897783049355705 40741382662423337287016779)
                ·
                  refine ⟨61112073993635005930525169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40741382662423337287016779 61112073993635005930525169)
                  ·
                    refine ⟨45834055495226254447893877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61112073993635005930525169 45834055495226254447893877)
                    ·
                      refine ⟨4296942702677461354490051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45834055495226254447893877 4296942702677461354490051)
                      ·
                        rfl

theorem cell23_8368266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_8368266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368266 prefixEnd_8368266 := by exact prefixLift 8368266
  have htrace : WordTrace (prefixWord ++ tailWord_8368266) baseStart_8368266 baseEnd_8368266 := by
    simpa [prefixWord, tailWord_8368266, baseEnd_8368266] using wordTrace_append hprefix tailTrace_8368266
  have hstable : (prefixWord ++ tailWord_8368266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368266).length < 2 ^ (prefixWord ++ tailWord_8368266).sum := by decide
  have hdescent : baseEnd_8368266 < baseStart_8368266 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368293 : List Nat := [1, 3, 1, 2, 1, 3, 3, 1, 2, 4, 2]
def baseStart_8368293 : Nat := 118140960795 + 8368293 * 2 ^ 59
def prefixEnd_8368293 : Nat := 4983230072969 + 3 ^ 40 * 8368293 * 2
def baseEnd_8368293 : Nat := 4296956566655132748852427

theorem tailTrace_8368293 : CollatzResearch.WordTrace tailWord_8368293 prefixEnd_8368293 4296956566655132748852427 := by
  unfold tailWord_8368293
  simp only [CollatzResearch.WordTrace]
  refine ⟨305216720272111126505829533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203477813514740751003886355 305216720272111126505829533)
  ·
    refine ⟨114456270102041672439686075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305216720272111126505829533 114456270102041672439686075)
    ·
      refine ⟨171684405153062508659529113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114456270102041672439686075 171684405153062508659529113)
      ·
        refine ⟨128763303864796881494646835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171684405153062508659529113 128763303864796881494646835)
        ·
          refine ⟨193144955797195322241970253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128763303864796881494646835 193144955797195322241970253)
          ·
            refine ⟨72429358423948245840738845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193144955797195322241970253 72429358423948245840738845)
            ·
              refine ⟨27161009408980592190277067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72429358423948245840738845 27161009408980592190277067)
              ·
                refine ⟨40741514113470888285415601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27161009408980592190277067 40741514113470888285415601)
                ·
                  refine ⟨30556135585103166214061701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40741514113470888285415601 30556135585103166214061701)
                  ·
                    refine ⟨5729275422206843665136569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30556135585103166214061701 5729275422206843665136569)
                    ·
                      refine ⟨4296956566655132748852427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5729275422206843665136569 4296956566655132748852427)
                      ·
                        rfl

theorem cell23_8368293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 4, 2].length) (baseStart_8368293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368293 prefixEnd_8368293 := by exact prefixLift 8368293
  have htrace : WordTrace (prefixWord ++ tailWord_8368293) baseStart_8368293 baseEnd_8368293 := by
    simpa [prefixWord, tailWord_8368293, baseEnd_8368293] using wordTrace_append hprefix tailTrace_8368293
  have hstable : (prefixWord ++ tailWord_8368293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368293).length < 2 ^ (prefixWord ++ tailWord_8368293).sum := by decide
  have hdescent : baseEnd_8368293 < baseStart_8368293 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368320 : List Nat := [2, 1, 1, 2, 5, 1, 1, 5, 1, 4]
def baseStart_8368320 : Nat := 118140960795 + 8368320 * 2 ^ 59
def prefixEnd_8368320 : Nat := 4983230072969 + 3 ^ 40 * 8368320 * 2
def baseEnd_8368320 : Nat := 1432323476877601381071601

theorem tailTrace_8368320 : CollatzResearch.WordTrace tailWord_8368320 prefixEnd_8368320 1432323476877601381071601 := by
  unfold tailWord_8368320
  simp only [CollatzResearch.WordTrace]
  refine ⟨152608852521506655058531207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203478470028675540078041609 152608852521506655058531207)
  ·
    refine ⟨228913278782259982587796811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152608852521506655058531207 228913278782259982587796811)
    ·
      refine ⟨343369918173389973881695217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228913278782259982587796811 343369918173389973881695217)
      ·
        refine ⟨257527438630042480411271413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343369918173389973881695217 257527438630042480411271413)
        ·
          refine ⟨24143197371566482538556695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 257527438630042480411271413 24143197371566482538556695)
          ·
            refine ⟨36214796057349723807835043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24143197371566482538556695 36214796057349723807835043)
            ·
              refine ⟨54322194086024585711752565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36214796057349723807835043 54322194086024585711752565)
              ·
                refine ⟨5092705695564804910476803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54322194086024585711752565 5092705695564804910476803)
                ·
                  refine ⟨7639058543347207365715205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5092705695564804910476803 7639058543347207365715205)
                  ·
                    refine ⟨1432323476877601381071601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7639058543347207365715205 1432323476877601381071601)
                    ·
                      rfl

theorem cell23_8368320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 5, 1, 4].length) (baseStart_8368320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368320 prefixEnd_8368320 := by exact prefixLift 8368320
  have htrace : WordTrace (prefixWord ++ tailWord_8368320) baseStart_8368320 baseEnd_8368320 := by
    simpa [prefixWord, tailWord_8368320, baseEnd_8368320] using wordTrace_append hprefix tailTrace_8368320
  have hstable : (prefixWord ++ tailWord_8368320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368320).length < 2 ^ (prefixWord ++ tailWord_8368320).sum := by decide
  have hdescent : baseEnd_8368320 < baseStart_8368320 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368346 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 5, 5]
def baseStart_8368346 : Nat := 118140960795 + 8368346 * 2 ^ 59
def prefixEnd_8368346 : Nat := 4983230072969 + 3 ^ 40 * 8368346 * 2
def baseEnd_8368346 : Nat := 1432327927043273680496561

theorem tailTrace_8368346 : CollatzResearch.WordTrace tailWord_8368346 prefixEnd_8368346 1432327927043273680496561 := by
  unfold tailWord_8368346
  simp only [CollatzResearch.WordTrace]
  refine ⟨76304663335229779139377223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203479102227279411038339261 76304663335229779139377223)
  ·
    refine ⟨114456995002844668709065835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76304663335229779139377223 114456995002844668709065835)
    ·
      refine ⟨171685492504267003063598753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114456995002844668709065835 171685492504267003063598753)
      ·
        refine ⟨128764119378200252297699065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171685492504267003063598753 128764119378200252297699065)
        ·
          refine ⟨96573089533650189223274299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128764119378200252297699065 96573089533650189223274299)
          ·
            refine ⟨144859634300475283834911449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96573089533650189223274299 144859634300475283834911449)
            ·
              refine ⟨108644725725356462876183587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144859634300475283834911449 108644725725356462876183587)
              ·
                refine ⟨162967088588034694314275381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108644725725356462876183587 162967088588034694314275381)
                ·
                  refine ⟨15278164555128252591963317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 162967088588034694314275381 15278164555128252591963317)
                  ·
                    refine ⟨1432327927043273680496561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15278164555128252591963317 1432327927043273680496561)
                    ·
                      rfl

theorem cell23_8368346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 5, 5].length) (baseStart_8368346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368346 prefixEnd_8368346 := by exact prefixLift 8368346
  have htrace : WordTrace (prefixWord ++ tailWord_8368346) baseStart_8368346 baseEnd_8368346 := by
    simpa [prefixWord, tailWord_8368346, baseEnd_8368346] using wordTrace_append hprefix tailTrace_8368346
  have hstable : (prefixWord ++ tailWord_8368346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368346).length < 2 ^ (prefixWord ++ tailWord_8368346).sum := by decide
  have hdescent : baseEnd_8368346 < baseStart_8368346 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368353 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 3, 5, 2]
def baseStart_8368353 : Nat := 118140960795 + 8368353 * 2 ^ 59
def prefixEnd_8368353 : Nat := 4983230072969 + 3 ^ 40 * 8368353 * 2
def baseEnd_8368353 : Nat := 4296987375494402514102151

theorem tailTrace_8368353 : CollatzResearch.WordTrace tailWord_8368353 prefixEnd_8368353 4296987375494402514102151 := by
  unfold tailWord_8368353
  simp only [CollatzResearch.WordTrace]
  refine ⟨305218908651893756753013713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203479272434595837835342475 305218908651893756753013713)
  ·
    refine ⟨228914181488920317564760285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305218908651893756753013713 228914181488920317564760285)
    ·
      refine ⟨85842818058345119086785107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228914181488920317564760285 85842818058345119086785107)
      ·
        refine ⟨128764227087517678630177661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85842818058345119086785107 128764227087517678630177661)
        ·
          refine ⟨48286585157819129486316623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128764227087517678630177661 48286585157819129486316623)
          ·
            refine ⟨72429877736728694229474935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48286585157819129486316623 72429877736728694229474935)
            ·
              refine ⟨108644816605093041344212403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72429877736728694229474935 108644816605093041344212403)
              ·
                refine ⟨162967224907639562016318605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108644816605093041344212403 162967224907639562016318605)
                ·
                  refine ⟨61112709340364835756119477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162967224907639562016318605 61112709340364835756119477)
                  ·
                    refine ⟨5729316500659203352136201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61112709340364835756119477 5729316500659203352136201)
                    ·
                      refine ⟨4296987375494402514102151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5729316500659203352136201 4296987375494402514102151)
                      ·
                        rfl

theorem cell23_8368353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 5, 2].length) (baseStart_8368353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368353 prefixEnd_8368353 := by exact prefixLift 8368353
  have htrace : WordTrace (prefixWord ++ tailWord_8368353) baseStart_8368353 baseEnd_8368353 := by
    simpa [prefixWord, tailWord_8368353, baseEnd_8368353] using wordTrace_append hprefix tailTrace_8368353
  have hstable : (prefixWord ++ tailWord_8368353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368353).length < 2 ^ (prefixWord ++ tailWord_8368353).sum := by decide
  have hdescent : baseEnd_8368353 < baseStart_8368353 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368360 : List Nat := [2, 1, 4, 1, 2, 2, 2, 2, 3, 1, 3]
def baseStart_8368360 : Nat := 118140960795 + 8368360 * 2 ^ 59
def prefixEnd_8368360 : Nat := 4983230072969 + 3 ^ 40 * 8368360 * 2
def baseEnd_8368360 : Nat := 4296990969858983986714619

theorem tailTrace_8368360 : CollatzResearch.WordTrace tailWord_8368360 prefixEnd_8368360 4296990969858983986714619 := by
  unfold tailWord_8368360
  simp only [CollatzResearch.WordTrace]
  refine ⟨152609581981434198474259267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203479442641912264632345689 152609581981434198474259267)
  ·
    refine ⟨228914372972151297711388901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152609581981434198474259267 228914372972151297711388901)
    ·
      refine ⟨42921444932278368320885419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228914372972151297711388901 42921444932278368320885419)
      ·
        refine ⟨64382167398417552481328129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42921444932278368320885419 64382167398417552481328129)
        ·
          refine ⟨48286625548813164360996097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64382167398417552481328129 48286625548813164360996097)
          ·
            refine ⟨36214969161609873270747073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48286625548813164360996097 36214969161609873270747073)
            ·
              refine ⟨27161226871207404953060305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36214969161609873270747073 27161226871207404953060305)
              ·
                refine ⟨20370920153405553714795229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27161226871207404953060305 20370920153405553714795229)
                ·
                  refine ⟨7639095057527082643048211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20370920153405553714795229 7639095057527082643048211)
                  ·
                    refine ⟨11458642586290623964572317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7639095057527082643048211 11458642586290623964572317)
                    ·
                      refine ⟨4296990969858983986714619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11458642586290623964572317 4296990969858983986714619)
                      ·
                        rfl

theorem cell23_8368360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_8368360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368360 prefixEnd_8368360 := by exact prefixLift 8368360
  have htrace : WordTrace (prefixWord ++ tailWord_8368360) baseStart_8368360 baseEnd_8368360 := by
    simpa [prefixWord, tailWord_8368360, baseEnd_8368360] using wordTrace_append hprefix tailTrace_8368360
  have hstable : (prefixWord ++ tailWord_8368360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368360).length < 2 ^ (prefixWord ++ tailWord_8368360).sum := by decide
  have hdescent : baseEnd_8368360 < baseStart_8368360 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368363 : List Nat := [1, 1, 1, 1, 2, 5, 4, 2, 1, 5]
def baseStart_8368363 : Nat := 118140960795 + 8368363 * 2 ^ 59
def prefixEnd_8368363 : Nat := 4983230072969 + 3 ^ 40 * 8368363 * 2
def baseEnd_8368363 : Nat := 1432330836766982491659035

theorem tailTrace_8368363 : CollatzResearch.WordTrace tailWord_8368363 prefixEnd_8368363 1432330836766982491659035 := by
  unfold tailWord_8368363
  simp only [CollatzResearch.WordTrace]
  refine ⟨305219273381857528460877743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203479515587905018973918495 305219273381857528460877743)
  ·
    refine ⟨457828910072786292691316615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305219273381857528460877743 457828910072786292691316615)
    ·
      refine ⟨686743365109179439036974923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457828910072786292691316615 686743365109179439036974923)
      ·
        refine ⟨1030115047663769158555462385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 686743365109179439036974923 1030115047663769158555462385)
        ·
          refine ⟨772586285747826868916596789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1030115047663769158555462385 772586285747826868916596789)
          ·
            refine ⟨72429964288858768960930949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 772586285747826868916596789 72429964288858768960930949)
            ·
              refine ⟨13580618304161019180174553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72429964288858768960930949 13580618304161019180174553)
              ·
                refine ⟨10185463728120764385130915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13580618304161019180174553 10185463728120764385130915)
                ·
                  refine ⟨15278195592181146577696373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10185463728120764385130915 15278195592181146577696373)
                  ·
                    refine ⟨1432330836766982491659035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15278195592181146577696373 1432330836766982491659035)
                    ·
                      rfl

theorem cell23_8368363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 5].length) (baseStart_8368363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368363 prefixEnd_8368363 := by exact prefixLift 8368363
  have htrace : WordTrace (prefixWord ++ tailWord_8368363) baseStart_8368363 baseEnd_8368363 := by
    simpa [prefixWord, tailWord_8368363, baseEnd_8368363] using wordTrace_append hprefix tailTrace_8368363
  have hstable : (prefixWord ++ tailWord_8368363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368363).length < 2 ^ (prefixWord ++ tailWord_8368363).sum := by decide
  have hdescent : baseEnd_8368363 < baseStart_8368363 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368370 : List Nat := [3, 2, 1, 3, 2, 1, 2, 1, 1, 5, 2]
def baseStart_8368370 : Nat := 118140960795 + 8368370 * 2 ^ 59
def prefixEnd_8368370 : Nat := 4983230072969 + 3 ^ 40 * 8368370 * 2
def baseEnd_8368370 : Nat := 4296996104665528947589573

theorem tailTrace_8368370 : CollatzResearch.WordTrace tailWord_8368370 prefixEnd_8368370 4296996104665528947589573 := by
  unfold tailWord_8368370
  simp only [CollatzResearch.WordTrace]
  refine ⟨76304882173208042164095641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203479685795221445770921709 76304882173208042164095641)
  ·
    refine ⟨57228661629906031623071731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76304882173208042164095641 57228661629906031623071731)
    ·
      refine ⟨85842992444859047434607597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57228661629906031623071731 85842992444859047434607597)
      ·
        refine ⟨32191122166822142787977849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85842992444859047434607597 32191122166822142787977849)
        ·
          refine ⟨24143341625116607090983387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32191122166822142787977849 24143341625116607090983387)
          ·
            refine ⟨36215012437674910636475081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24143341625116607090983387 36215012437674910636475081)
            ·
              refine ⟨27161259328256182977356311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36215012437674910636475081 27161259328256182977356311)
              ·
                refine ⟨40741888992384274466034467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27161259328256182977356311 40741888992384274466034467)
                ·
                  refine ⟨61112833488576411699051701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40741888992384274466034467 61112833488576411699051701)
                  ·
                    refine ⟨5729328139554038596786097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61112833488576411699051701 5729328139554038596786097)
                    ·
                      refine ⟨4296996104665528947589573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5729328139554038596786097 4296996104665528947589573)
                      ·
                        rfl

theorem cell23_8368370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_8368370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368370 prefixEnd_8368370 := by exact prefixLift 8368370
  have htrace : WordTrace (prefixWord ++ tailWord_8368370) baseStart_8368370 baseEnd_8368370 := by
    simpa [prefixWord, tailWord_8368370, baseEnd_8368370] using wordTrace_append hprefix tailTrace_8368370
  have hstable : (prefixWord ++ tailWord_8368370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368370).length < 2 ^ (prefixWord ++ tailWord_8368370).sum := by decide
  have hdescent : baseEnd_8368370 < baseStart_8368370 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368376 : List Nat := [2, 1, 2, 1, 1, 2, 1, 6, 1, 6]
def baseStart_8368376 : Nat := 118140960795 + 8368376 * 2 ^ 59
def prefixEnd_8368376 : Nat := 4983230072969 + 3 ^ 40 * 8368376 * 2
def baseEnd_8368376 : Nat := 1432333061849818641371515

theorem tailTrace_8368376 : CollatzResearch.WordTrace tailWord_8368376 prefixEnd_8368376 1432333061849818641371515 := by
  unfold tailWord_8368376
  simp only [CollatzResearch.WordTrace]
  refine ⟨152609873765405215840550491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203479831687206954454067321 152609873765405215840550491)
  ·
    refine ⟨228914810648107823760825737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152609873765405215840550491 228914810648107823760825737)
    ·
      refine ⟨171686107986080867820619303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228914810648107823760825737 171686107986080867820619303)
      ·
        refine ⟨257529161979121301730928955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171686107986080867820619303 257529161979121301730928955)
        ·
          refine ⟨386293742968681952596393433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257529161979121301730928955 386293742968681952596393433)
          ·
            refine ⟨289720307226511464447295075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386293742968681952596393433 289720307226511464447295075)
            ·
              refine ⟨434580460839767196670942613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289720307226511464447295075 434580460839767196670942613)
              ·
                refine ⟨20370959101864087343950435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 434580460839767196670942613 20370959101864087343950435)
                ·
                  refine ⟨30556438652796131015925653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20370959101864087343950435 30556438652796131015925653)
                  ·
                    refine ⟨1432333061849818641371515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30556438652796131015925653 1432333061849818641371515)
                    ·
                      rfl

theorem cell23_8368376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 1, 6].length) (baseStart_8368376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368376 prefixEnd_8368376 := by exact prefixLift 8368376
  have htrace : WordTrace (prefixWord ++ tailWord_8368376) baseStart_8368376 baseEnd_8368376 := by
    simpa [prefixWord, tailWord_8368376, baseEnd_8368376] using wordTrace_append hprefix tailTrace_8368376
  have hstable : (prefixWord ++ tailWord_8368376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368376).length < 2 ^ (prefixWord ++ tailWord_8368376).sum := by decide
  have hdescent : baseEnd_8368376 < baseStart_8368376 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368383 : List Nat := [1, 1, 2, 2, 1, 4, 1, 5, 1, 1, 4]
def baseStart_8368383 : Nat := 118140960795 + 8368383 * 2 ^ 59
def prefixEnd_8368383 : Nat := 4983230072969 + 3 ^ 40 * 8368383 * 2
def baseEnd_8368383 : Nat := 4297002779914037396727013

theorem tailTrace_8368383 : CollatzResearch.WordTrace tailWord_8368383 prefixEnd_8368383 4297002779914037396727013 := by
  unfold tailWord_8368383
  simp only [CollatzResearch.WordTrace]
  refine ⟨305220002841785071876605803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203480001894523381251070535 305220002841785071876605803)
  ·
    refine ⟨457830004262677607814908705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305220002841785071876605803 457830004262677607814908705)
    ·
      refine ⟨343372503197008205861181529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457830004262677607814908705 343372503197008205861181529)
      ·
        refine ⟨257529377397756154395886147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343372503197008205861181529 257529377397756154395886147)
        ·
          refine ⟨386294066096634231593829221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257529377397756154395886147 386294066096634231593829221)
          ·
            refine ⟨72430137393118918423842979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 386294066096634231593829221 72430137393118918423842979)
            ·
              refine ⟨108645206089678377635764469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72430137393118918423842979 108645206089678377635764469)
              ·
                refine ⟨10185488070907347903352919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108645206089678377635764469 10185488070907347903352919)
                ·
                  refine ⟨15278232106361021855029379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10185488070907347903352919 15278232106361021855029379)
                  ·
                    refine ⟨22917348159541532782544069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15278232106361021855029379 22917348159541532782544069)
                    ·
                      refine ⟨4297002779914037396727013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22917348159541532782544069 4297002779914037396727013)
                      ·
                        rfl

theorem cell23_8368383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 1, 4].length) (baseStart_8368383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368383 prefixEnd_8368383 := by exact prefixLift 8368383
  have htrace : WordTrace (prefixWord ++ tailWord_8368383) baseStart_8368383 baseEnd_8368383 := by
    simpa [prefixWord, tailWord_8368383, baseEnd_8368383] using wordTrace_append hprefix tailTrace_8368383
  have hstable : (prefixWord ++ tailWord_8368383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368383).length < 2 ^ (prefixWord ++ tailWord_8368383).sum := by decide
  have hdescent : baseEnd_8368383 < baseStart_8368383 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368393 : List Nat := [1, 2, 1, 1, 3, 4, 2, 1, 4, 4]
def baseStart_8368393 : Nat := 118140960795 + 8368393 * 2 ^ 59
def prefixEnd_8368393 : Nat := 4983230072969 + 3 ^ 40 * 8368393 * 2
def baseEnd_8368393 : Nat := 1432335971573527452533989

theorem tailTrace_8368393 : CollatzResearch.WordTrace tailWord_8368393 prefixEnd_8368393 1432335971573527452533989 := by
  unfold tailWord_8368393
  simp only [CollatzResearch.WordTrace]
  refine ⟨305220367571748843584469833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203480245047832562389646555 305220367571748843584469833)
  ·
    refine ⟨228915275678811632688352375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305220367571748843584469833 228915275678811632688352375)
    ·
      refine ⟨343372913518217449032528563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228915275678811632688352375 343372913518217449032528563)
      ·
        refine ⟨515059370277326173548792845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343372913518217449032528563 515059370277326173548792845)
        ·
          refine ⟨193147263853997315080797317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 515059370277326173548792845 193147263853997315080797317)
          ·
            refine ⟨36215111972624496577649497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 193147263853997315080797317 36215111972624496577649497)
            ·
              refine ⟨27161333979468372433237123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36215111972624496577649497 27161333979468372433237123)
              ·
                refine ⟨40742000969202558649855685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27161333979468372433237123 40742000969202558649855685)
                ·
                  refine ⟨7639125181725479746847941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40742000969202558649855685 7639125181725479746847941)
                  ·
                    refine ⟨1432335971573527452533989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7639125181725479746847941 1432335971573527452533989)
                    ·
                      rfl

theorem cell23_8368393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 4, 4].length) (baseStart_8368393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368393 prefixEnd_8368393 := by exact prefixLift 8368393
  have htrace : WordTrace (prefixWord ++ tailWord_8368393) baseStart_8368393 baseEnd_8368393 := by
    simpa [prefixWord, tailWord_8368393, baseEnd_8368393] using wordTrace_append hprefix tailTrace_8368393
  have hstable : (prefixWord ++ tailWord_8368393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368393).length < 2 ^ (prefixWord ++ tailWord_8368393).sum := by decide
  have hdescent : baseEnd_8368393 < baseStart_8368393 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368396 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 3, 1, 6]
def baseStart_8368396 : Nat := 118140960795 + 8368396 * 2 ^ 59
def prefixEnd_8368396 : Nat := 4983230072969 + 3 ^ 40 * 8368396 * 2
def baseEnd_8368396 : Nat := 4297009455162545845864453

theorem tailTrace_8368396 : CollatzResearch.WordTrace tailWord_8368396 prefixEnd_8368396 4297009455162545845864453 := by
  unfold tailWord_8368396
  simp only [CollatzResearch.WordTrace]
  refine ⟨152610238495368987548414521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203480317993825316731219361 152610238495368987548414521)
  ·
    refine ⟨114457678871526740661310891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152610238495368987548414521 114457678871526740661310891)
    ·
      refine ⟨171686518307290110991966337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114457678871526740661310891 171686518307290110991966337)
      ·
        refine ⟨128764888730467583243974753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171686518307290110991966337 128764888730467583243974753)
        ·
          refine ⟨96573666547850687432981065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128764888730467583243974753 96573666547850687432981065)
          ·
            refine ⟨72430249910888015574735799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96573666547850687432981065 72430249910888015574735799)
            ·
              refine ⟨108645374866332023362103699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72430249910888015574735799 108645374866332023362103699)
              ·
                refine ⟨162968062299498035043155549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108645374866332023362103699 162968062299498035043155549)
                ·
                  refine ⟨61113023362311763141183331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162968062299498035043155549 61113023362311763141183331)
                  ·
                    refine ⟨91669535043467644711774997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61113023362311763141183331 91669535043467644711774997)
                    ·
                      refine ⟨4297009455162545845864453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91669535043467644711774997 4297009455162545845864453)
                      ·
                        rfl

theorem cell23_8368396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_8368396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368396 prefixEnd_8368396 := by exact prefixLift 8368396
  have htrace : WordTrace (prefixWord ++ tailWord_8368396) baseStart_8368396 baseEnd_8368396 := by
    simpa [prefixWord, tailWord_8368396, baseEnd_8368396] using wordTrace_append hprefix tailTrace_8368396
  have hstable : (prefixWord ++ tailWord_8368396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368396).length < 2 ^ (prefixWord ++ tailWord_8368396).sum := by decide
  have hdescent : baseEnd_8368396 < baseStart_8368396 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368414 : List Nat := [4, 3, 2, 1, 1, 3, 1, 2, 1, 5]
def baseStart_8368414 : Nat := 118140960795 + 8368414 * 2 ^ 59
def prefixEnd_8368414 : Nat := 4983230072969 + 3 ^ 40 * 8368414 * 2
def baseEnd_8368414 : Nat := 1432339565938108925146457

theorem tailTrace_8368414 : CollatzResearch.WordTrace tailWord_8368414 prefixEnd_8368414 1432339565938108925146457 := by
  unfold tailWord_8368414
  simp only [CollatzResearch.WordTrace]
  refine ⟨38152641688084095521373037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203480755669781842780656197 38152641688084095521373037)
  ·
    refine ⟨14307240633031535820514889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38152641688084095521373037 14307240633031535820514889)
    ·
      refine ⟨10730430474773651865386167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14307240633031535820514889 10730430474773651865386167)
      ·
        refine ⟨16095645712160477798079251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10730430474773651865386167 16095645712160477798079251)
        ·
          refine ⟨24143468568240716697118877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16095645712160477798079251 24143468568240716697118877)
          ·
            refine ⟨9053800713090268761419579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24143468568240716697118877 9053800713090268761419579)
            ·
              refine ⟨13580701069635403142129369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9053800713090268761419579 13580701069635403142129369)
              ·
                refine ⟨10185525802226552356597027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13580701069635403142129369 10185525802226552356597027)
                ·
                  refine ⟨15278288703339828534895541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10185525802226552356597027 15278288703339828534895541)
                  ·
                    refine ⟨1432339565938108925146457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15278288703339828534895541 1432339565938108925146457)
                    ·
                      rfl

theorem cell23_8368414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_8368414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368414 prefixEnd_8368414 := by exact prefixLift 8368414
  have htrace : WordTrace (prefixWord ++ tailWord_8368414) baseStart_8368414 baseEnd_8368414 := by
    simpa [prefixWord, tailWord_8368414, baseEnd_8368414] using wordTrace_append hprefix tailTrace_8368414
  have hstable : (prefixWord ++ tailWord_8368414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368414).length < 2 ^ (prefixWord ++ tailWord_8368414).sum := by decide
  have hdescent : baseEnd_8368414 < baseStart_8368414 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368420 : List Nat := [2, 3, 1, 3, 1, 3, 1, 1, 3, 2, 3]
def baseStart_8368420 : Nat := 118140960795 + 8368420 * 2 ^ 59
def prefixEnd_8368420 : Nat := 4983230072969 + 3 ^ 40 * 8368420 * 2
def baseEnd_8368420 : Nat := 4297021778698253751964343

theorem tailTrace_8368420 : CollatzResearch.WordTrace tailWord_8368420 prefixEnd_8368420 4297021778698253751964343 := by
  unfold tailWord_8368420
  simp only [CollatzResearch.WordTrace]
  refine ⟨152610676171325513597851357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203480901561767351463801809 152610676171325513597851357)
  ·
    refine ⟨57229003564247067599194259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152610676171325513597851357 57229003564247067599194259)
    ·
      refine ⟨85843505346370601398791389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57229003564247067599194259 85843505346370601398791389)
      ·
        refine ⟨32191314504888975524546771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85843505346370601398791389 32191314504888975524546771)
        ·
          refine ⟨48286971757333463286820157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32191314504888975524546771 48286971757333463286820157)
          ·
            refine ⟨18107614409000048732557559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48286971757333463286820157 18107614409000048732557559)
            ·
              refine ⟨27161421613500073098836339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18107614409000048732557559 27161421613500073098836339)
              ·
                refine ⟨40742132420250109648254509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27161421613500073098836339 40742132420250109648254509)
                ·
                  refine ⟨15278299657593791118095441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40742132420250109648254509 15278299657593791118095441)
                  ·
                    refine ⟨11458724743195343338571581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15278299657593791118095441 11458724743195343338571581)
                    ·
                      refine ⟨4297021778698253751964343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11458724743195343338571581 4297021778698253751964343)
                      ·
                        rfl

theorem cell23_8368420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_8368420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368420 prefixEnd_8368420 := by exact prefixLift 8368420
  have htrace : WordTrace (prefixWord ++ tailWord_8368420) baseStart_8368420 baseEnd_8368420 := by
    simpa [prefixWord, tailWord_8368420, baseEnd_8368420] using wordTrace_append hprefix tailTrace_8368420
  have hstable : (prefixWord ++ tailWord_8368420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368420).length < 2 ^ (prefixWord ++ tailWord_8368420).sum := by decide
  have hdescent : baseEnd_8368420 < baseStart_8368420 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368437 : List Nat := [1, 3, 3, 1, 2, 1, 5, 1, 1, 2, 3]
def baseStart_8368437 : Nat := 118140960795 + 8368437 * 2 ^ 59
def prefixEnd_8368437 : Nat := 4983230072969 + 3 ^ 40 * 8368437 * 2
def baseEnd_8368437 : Nat := 4297030507869380185451765

theorem tailTrace_8368437 : CollatzResearch.WordTrace tailWord_8368437 prefixEnd_8368437 4297030507869380185451765 := by
  unfold tailWord_8368437
  simp only [CollatzResearch.WordTrace]
  refine ⟨305221972383589439099071565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203481314922392959399381043 305221972383589439099071565)
  ·
    refine ⟨114458239643846039662151837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305221972383589439099071565 114458239643846039662151837)
    ·
      refine ⟨42921839866442264873306939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114458239643846039662151837 42921839866442264873306939)
      ·
        refine ⟨64382759799663397309960409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42921839866442264873306939 64382759799663397309960409)
        ·
          refine ⟨48287069849747547982470307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64382759799663397309960409 48287069849747547982470307)
          ·
            refine ⟨72430604774621321973705461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48287069849747547982470307 72430604774621321973705461)
            ·
              refine ⟨6790369197620748935034887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72430604774621321973705461 6790369197620748935034887)
              ·
                refine ⟨10185553796431123402552331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6790369197620748935034887 10185553796431123402552331)
                ·
                  refine ⟨15278330694646685103828497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10185553796431123402552331 15278330694646685103828497)
                  ·
                    refine ⟨11458748020985013827871373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15278330694646685103828497 11458748020985013827871373)
                    ·
                      refine ⟨4297030507869380185451765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11458748020985013827871373 4297030507869380185451765)
                      ·
                        rfl

theorem cell23_8368437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_8368437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368437 prefixEnd_8368437 := by exact prefixLift 8368437
  have htrace : WordTrace (prefixWord ++ tailWord_8368437) baseStart_8368437 baseEnd_8368437 := by
    simpa [prefixWord, tailWord_8368437, baseEnd_8368437] using wordTrace_append hprefix tailTrace_8368437
  have hstable : (prefixWord ++ tailWord_8368437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368437).length < 2 ^ (prefixWord ++ tailWord_8368437).sum := by decide
  have hdescent : baseEnd_8368437 < baseStart_8368437 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368460 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 5, 3, 2]
def baseStart_8368460 : Nat := 118140960795 + 8368460 * 2 ^ 59
def prefixEnd_8368460 : Nat := 4983230072969 + 3 ^ 40 * 8368460 * 2
def baseEnd_8368460 : Nat := 4297042317924433595464159

theorem tailTrace_8368460 : CollatzResearch.WordTrace tailWord_8368460 prefixEnd_8368460 4297042317924433595464159 := by
  unfold tailWord_8368460
  simp only [CollatzResearch.WordTrace]
  refine ⟨152611405631253057013579417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203481874175004076018105889 152611405631253057013579417)
  ·
    refine ⟨114458554223439792760184563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152611405631253057013579417 114458554223439792760184563)
    ·
      refine ⟨171687831335159689140276845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114458554223439792760184563 171687831335159689140276845)
      ·
        refine ⟨64382936750684883427603817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171687831335159689140276845 64382936750684883427603817)
        ·
          refine ⟨48287202563013662570702863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64382936750684883427603817 48287202563013662570702863)
          ·
            refine ⟨72430803844520493856054295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48287202563013662570702863 72430803844520493856054295)
            ·
              refine ⟨108646205766780740784081443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72430803844520493856054295 108646205766780740784081443)
              ·
                refine ⟨162969308650171111176122165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108646205766780740784081443 162969308650171111176122165)
                ·
                  refine ⟨15278372685953541672761453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 162969308650171111176122165 15278372685953541672761453)
                  ·
                    refine ⟨5729389757232578127285545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15278372685953541672761453 5729389757232578127285545)
                    ·
                      refine ⟨4297042317924433595464159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5729389757232578127285545 4297042317924433595464159)
                      ·
                        rfl

theorem cell23_8368460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_8368460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368460 prefixEnd_8368460 := by exact prefixLift 8368460
  have htrace : WordTrace (prefixWord ++ tailWord_8368460) baseStart_8368460 baseEnd_8368460 := by
    simpa [prefixWord, tailWord_8368460, baseEnd_8368460] using wordTrace_append hprefix tailTrace_8368460
  have hstable : (prefixWord ++ tailWord_8368460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368460).length < 2 ^ (prefixWord ++ tailWord_8368460).sum := by decide
  have hdescent : baseEnd_8368460 < baseStart_8368460 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368493 : List Nat := [1, 5, 1, 1, 1, 2, 2, 1, 1, 3, 5]
def baseStart_8368493 : Nat := 118140960795 + 8368493 * 2 ^ 59
def prefixEnd_8368493 : Nat := 4983230072969 + 3 ^ 40 * 8368493 * 2
def baseEnd_8368493 : Nat := 4297059262786031966351507

theorem tailTrace_8368493 : CollatzResearch.WordTrace tailWord_8368493 prefixEnd_8368493 4297059262786031966351507 := by
  unfold tailWord_8368493
  simp only [CollatzResearch.WordTrace]
  refine ⟨305224014871386560663110133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203482676580924373775406755 305224014871386560663110133)
  ·
    refine ⟨28614751394192490062166575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 305224014871386560663110133 28614751394192490062166575)
    ·
      refine ⟨42922127091288735093249863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28614751394192490062166575 42922127091288735093249863)
      ·
        refine ⟨64383190636933102639874795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42922127091288735093249863 64383190636933102639874795)
        ·
          refine ⟨96574785955399653959812193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64383190636933102639874795 96574785955399653959812193)
          ·
            refine ⟨72431089466549740469859145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96574785955399653959812193 72431089466549740469859145)
            ·
              refine ⟨54323317099912305352394359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72431089466549740469859145 54323317099912305352394359)
              ·
                refine ⟨81484975649868458028591539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54323317099912305352394359 81484975649868458028591539)
                ·
                  refine ⟨122227463474802687042887309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81484975649868458028591539 122227463474802687042887309)
                  ·
                    refine ⟨45835298803051007641082741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 122227463474802687042887309 45835298803051007641082741)
                    ·
                      refine ⟨4297059262786031966351507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45835298803051007641082741 4297059262786031966351507)
                      ·
                        rfl

theorem cell23_8368493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_8368493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368493 prefixEnd_8368493 := by exact prefixLift 8368493
  have htrace : WordTrace (prefixWord ++ tailWord_8368493) baseStart_8368493 baseEnd_8368493 := by
    simpa [prefixWord, tailWord_8368493, baseEnd_8368493] using wordTrace_append hprefix tailTrace_8368493
  have hstable : (prefixWord ++ tailWord_8368493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368493).length < 2 ^ (prefixWord ++ tailWord_8368493).sum := by decide
  have hdescent : baseEnd_8368493 < baseStart_8368493 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368507 : List Nat := [1, 1, 1, 1, 1, 8, 1, 1, 4, 2, 2]
def baseStart_8368507 : Nat := 118140960795 + 8368507 * 2 ^ 59
def prefixEnd_8368507 : Nat := 4983230072969 + 3 ^ 40 * 8368507 * 2
def baseEnd_8368507 : Nat := 4297066451515194911576443

theorem tailTrace_8368507 : CollatzResearch.WordTrace tailWord_8368507 prefixEnd_8368507 4297066451515194911576443 := by
  unfold tailWord_8368507
  simp only [CollatzResearch.WordTrace]
  refine ⟨305224525493335841054119775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203483016995557227369413183 305224525493335841054119775)
  ·
    refine ⟨457836788240003761581179663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305224525493335841054119775 457836788240003761581179663)
    ·
      refine ⟨686755182360005642371769495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457836788240003761581179663 686755182360005642371769495)
      ·
        refine ⟨1030132773540008463557654243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 686755182360005642371769495 1030132773540008463557654243)
        ·
          refine ⟨1545199160310012695336481365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1030132773540008463557654243 1545199160310012695336481365)
          ·
            refine ⟨18107802659882961273474391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1545199160310012695336481365 18107802659882961273474391)
            ·
              refine ⟨27161703989824441910211587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18107802659882961273474391 27161703989824441910211587)
              ·
                refine ⟨40742555984736662865317381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27161703989824441910211587 40742555984736662865317381)
                ·
                  refine ⟨7639229247138124287247009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40742555984736662865317381 7639229247138124287247009)
                  ·
                    refine ⟨5729421935353593215435257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7639229247138124287247009 5729421935353593215435257)
                    ·
                      refine ⟨4297066451515194911576443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5729421935353593215435257 4297066451515194911576443)
                      ·
                        rfl

theorem cell23_8368507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 4, 2, 2].length) (baseStart_8368507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368507 prefixEnd_8368507 := by exact prefixLift 8368507
  have htrace : WordTrace (prefixWord ++ tailWord_8368507) baseStart_8368507 baseEnd_8368507 := by
    simpa [prefixWord, tailWord_8368507, baseEnd_8368507] using wordTrace_append hprefix tailTrace_8368507
  have hstable : (prefixWord ++ tailWord_8368507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368507).length < 2 ^ (prefixWord ++ tailWord_8368507).sum := by decide
  have hdescent : baseEnd_8368507 < baseStart_8368507 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368543 : List Nat := [1, 1, 2, 5, 1, 1, 1, 3, 1, 7]
def baseStart_8368543 : Nat := 118140960795 + 8368543 * 2 ^ 59
def prefixEnd_8368543 : Nat := 4983230072969 + 3 ^ 40 * 8368543 * 2
def baseEnd_8368543 : Nat := 1432361645606252256908759

theorem tailTrace_8368543 : CollatzResearch.WordTrace tailWord_8368543 prefixEnd_8368543 1432361645606252256908759 := by
  unfold tailWord_8368543
  simp only [CollatzResearch.WordTrace]
  refine ⟨305225838521205419202430283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203483892347470279468286855 305225838521205419202430283)
  ·
    refine ⟨457838757781808128803645425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305225838521205419202430283 457838757781808128803645425)
    ·
      refine ⟨343379068336356096602734069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457838757781808128803645425 343379068336356096602734069)
      ·
        refine ⟨32191787656533384056506319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 343379068336356096602734069 32191787656533384056506319)
        ·
          refine ⟨48287681484800076084759479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32191787656533384056506319 48287681484800076084759479)
          ·
            refine ⟨72431522227200114127139219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48287681484800076084759479 72431522227200114127139219)
            ·
              refine ⟨108647283340800171190708829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72431522227200114127139219 108647283340800171190708829)
              ·
                refine ⟨40742731252800064196515811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108647283340800171190708829 40742731252800064196515811)
                ·
                  refine ⟨61114096879200096294773717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40742731252800064196515811 61114096879200096294773717)
                  ·
                    refine ⟨1432361645606252256908759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61114096879200096294773717 1432361645606252256908759)
                    ·
                      rfl

theorem cell23_8368543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 7].length) (baseStart_8368543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368543 prefixEnd_8368543 := by exact prefixLift 8368543
  have htrace : WordTrace (prefixWord ++ tailWord_8368543) baseStart_8368543 baseEnd_8368543 := by
    simpa [prefixWord, tailWord_8368543, baseEnd_8368543] using wordTrace_append hprefix tailTrace_8368543
  have hstable : (prefixWord ++ tailWord_8368543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368543).length < 2 ^ (prefixWord ++ tailWord_8368543).sum := by decide
  have hdescent : baseEnd_8368543 < baseStart_8368543 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368547 : List Nat := [1, 1, 1, 4, 1, 6, 1, 3, 5]
def baseStart_8368547 : Nat := 118140960795 + 8368547 * 2 ^ 59
def prefixEnd_8368547 : Nat := 4983230072969 + 3 ^ 40 * 8368547 * 2
def baseEnd_8368547 : Nat := 477454110082374972786251

theorem tailTrace_8368547 : CollatzResearch.WordTrace tailWord_8368547 prefixEnd_8368547 477454110082374972786251 := by
  unfold tailWord_8368547
  simp only [CollatzResearch.WordTrace]
  refine ⟨305225984413190927885575895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203483989608793951923717263 305225984413190927885575895)
  ·
    refine ⟨457838976619786391828363843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305225984413190927885575895 457838976619786391828363843)
    ·
      refine ⟨686758464929679587742545765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457838976619786391828363843 686758464929679587742545765)
      ·
        refine ⟨128767212174314922701727331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 686758464929679587742545765 128767212174314922701727331)
        ·
          refine ⟨193150818261472384052590997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128767212174314922701727331 193150818261472384052590997)
          ·
            refine ⟨9053944606006518002465203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 193150818261472384052590997 9053944606006518002465203)
            ·
              refine ⟨13580916909009777003697805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9053944606006518002465203 13580916909009777003697805)
              ·
                refine ⟨5092843840878666376386677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13580916909009777003697805 5092843840878666376386677)
                ·
                  refine ⟨477454110082374972786251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5092843840878666376386677 477454110082374972786251)
                  ·
                    rfl

theorem cell23_8368547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 3, 5].length) (baseStart_8368547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368547 prefixEnd_8368547 := by exact prefixLift 8368547
  have htrace : WordTrace (prefixWord ++ tailWord_8368547) baseStart_8368547 baseEnd_8368547 := by
    simpa [prefixWord, tailWord_8368547, baseEnd_8368547] using wordTrace_append hprefix tailTrace_8368547
  have hstable : (prefixWord ++ tailWord_8368547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368547).length < 2 ^ (prefixWord ++ tailWord_8368547).sum := by decide
  have hdescent : baseEnd_8368547 < baseStart_8368547 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368590 : List Nat := [4, 1, 1, 1, 2, 1, 1, 3, 5, 4]
def baseStart_8368590 : Nat := 118140960795 + 8368590 * 2 ^ 59
def prefixEnd_8368590 : Nat := 4983230072969 + 3 ^ 40 * 8368590 * 2
def baseEnd_8368590 : Nat := 1432369690136506028946187

theorem tailTrace_8368590 : CollatzResearch.WordTrace tailWord_8368590 prefixEnd_8368590 1432369690136506028946187 := by
  unfold tailWord_8368590
  simp only [CollatzResearch.WordTrace]
  refine ⟨38153444094004393278673903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203485035168023430819594149 38153444094004393278673903)
  ·
    refine ⟨57230166141006589918010855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38153444094004393278673903 57230166141006589918010855)
    ·
      refine ⟨85845249211509884877016283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57230166141006589918010855 85845249211509884877016283)
      ·
        refine ⟨128767873817264827315524425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85845249211509884877016283 128767873817264827315524425)
        ·
          refine ⟨96575905362948620486643319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128767873817264827315524425 96575905362948620486643319)
          ·
            refine ⟨144863858044422930729964979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96575905362948620486643319 144863858044422930729964979)
            ·
              refine ⟨217295787066634396094947469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144863858044422930729964979 217295787066634396094947469)
              ·
                refine ⟨81485920149987898535605301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217295787066634396094947469 81485920149987898535605301)
                ·
                  refine ⟨7639305014061365487712997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81485920149987898535605301 7639305014061365487712997)
                  ·
                    refine ⟨1432369690136506028946187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7639305014061365487712997 1432369690136506028946187)
                    ·
                      rfl

theorem cell23_8368590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 5, 4].length) (baseStart_8368590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368590 prefixEnd_8368590 := by exact prefixLift 8368590
  have htrace : WordTrace (prefixWord ++ tailWord_8368590) baseStart_8368590 baseEnd_8368590 := by
    simpa [prefixWord, tailWord_8368590, baseEnd_8368590] using wordTrace_append hprefix tailTrace_8368590
  have hstable : (prefixWord ++ tailWord_8368590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368590).length < 2 ^ (prefixWord ++ tailWord_8368590).sum := by decide
  have hdescent : baseEnd_8368590 < baseStart_8368590 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368593 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 2, 4, 4]
def baseStart_8368593 : Nat := 118140960795 + 8368593 * 2 ^ 59
def prefixEnd_8368593 : Nat := 4983230072969 + 3 ^ 40 * 8368593 * 2
def baseEnd_8368593 : Nat := 4297110610851481575101047

theorem tailTrace_8368593 : CollatzResearch.WordTrace tailWord_8368593 prefixEnd_8368593 4297110610851481575101047 := by
  unfold tailWord_8368593
  simp only [CollatzResearch.WordTrace]
  refine ⟨305227662171024277741750433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203485108114016185161166955 305227662171024277741750433)
  ·
    refine ⟨228920746628268208306312825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305227662171024277741750433 228920746628268208306312825)
    ·
      refine ⟨171690559971201156229734619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228920746628268208306312825 171690559971201156229734619)
      ·
        refine ⟨257535839956801734344601929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171690559971201156229734619 257535839956801734344601929)
        ·
          refine ⟨193151879967601300758451447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257535839956801734344601929 193151879967601300758451447)
          ·
            refine ⟨289727819951401951137677171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193151879967601300758451447 289727819951401951137677171)
            ·
              refine ⟨434591729927102926706515757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289727819951401951137677171 434591729927102926706515757)
              ·
                refine ⟨162971898722663597514943409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 434591729927102926706515757 162971898722663597514943409)
                ·
                  refine ⟨122228924041997698136207557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162971898722663597514943409 122228924041997698136207557)
                  ·
                    refine ⟨22917923257874568400538917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 122228924041997698136207557 22917923257874568400538917)
                    ·
                      refine ⟨4297110610851481575101047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22917923257874568400538917 4297110610851481575101047)
                      ·
                        rfl

theorem cell23_8368593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 4, 4].length) (baseStart_8368593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368593 prefixEnd_8368593 := by exact prefixLift 8368593
  have htrace : WordTrace (prefixWord ++ tailWord_8368593) baseStart_8368593 baseEnd_8368593 := by
    simpa [prefixWord, tailWord_8368593, baseEnd_8368593] using wordTrace_append hprefix tailTrace_8368593
  have hstable : (prefixWord ++ tailWord_8368593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368593).length < 2 ^ (prefixWord ++ tailWord_8368593).sum := by decide
  have hdescent : baseEnd_8368593 < baseStart_8368593 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368594 : List Nat := [3, 2, 2, 4, 1, 1, 2, 1, 2, 5]
def baseStart_8368594 : Nat := 118140960795 + 8368594 * 2 ^ 59
def prefixEnd_8368594 : Nat := 4983230072969 + 3 ^ 40 * 8368594 * 2
def baseEnd_8368594 : Nat := 1432370374777378690396181

theorem tailTrace_8368594 : CollatzResearch.WordTrace tailWord_8368594 prefixEnd_8368594 1432370374777378690396181 := by
  unfold tailWord_8368594
  simp only [CollatzResearch.WordTrace]
  refine ⟨76306924661005163728134209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203485132429347103275024557 76306924661005163728134209)
  ·
    refine ⟨57230193495753872796100657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76306924661005163728134209 57230193495753872796100657)
    ·
      refine ⟨42922645121815404597075493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57230193495753872796100657 42922645121815404597075493)
      ·
        refine ⟨8047995960340388361951655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42922645121815404597075493 8047995960340388361951655)
        ·
          refine ⟨12071993940510582542927483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8047995960340388361951655 12071993940510582542927483)
          ·
            refine ⟨18107990910765873814391225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12071993940510582542927483 18107990910765873814391225)
            ·
              refine ⟨13580993183074405360793419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18107990910765873814391225 13580993183074405360793419)
              ·
                refine ⟨20371489774611608041190129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13580993183074405360793419 20371489774611608041190129)
                ·
                  refine ⟨15278617330958706030892597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20371489774611608041190129 15278617330958706030892597)
                  ·
                    refine ⟨1432370374777378690396181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15278617330958706030892597 1432370374777378690396181)
                    ·
                      rfl

theorem cell23_8368594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_8368594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368594 prefixEnd_8368594 := by exact prefixLift 8368594
  have htrace : WordTrace (prefixWord ++ tailWord_8368594) baseStart_8368594 baseEnd_8368594 := by
    simpa [prefixWord, tailWord_8368594, baseEnd_8368594] using wordTrace_append hprefix tailTrace_8368594
  have hstable : (prefixWord ++ tailWord_8368594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368594).length < 2 ^ (prefixWord ++ tailWord_8368594).sum := by decide
  have hdescent : baseEnd_8368594 < baseStart_8368594 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368597 : List Nat := [1, 3, 2, 3, 1, 3, 2, 1, 2, 1, 4]
def baseStart_8368597 : Nat := 118140960795 + 8368597 * 2 ^ 59
def prefixEnd_8368597 : Nat := 4983230072969 + 3 ^ 40 * 8368597 * 2
def baseEnd_8368597 : Nat := 4297112664774099559451029

theorem tailTrace_8368597 : CollatzResearch.WordTrace tailWord_8368597 prefixEnd_8368597 4297112664774099559451029 := by
  unfold tailWord_8368597
  simp only [CollatzResearch.WordTrace]
  refine ⟨305227808063009786424896045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203485205375339857616597363 305227808063009786424896045)
  ·
    refine ⟨114460428023628669909336017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305227808063009786424896045 114460428023628669909336017)
    ·
      refine ⟨85845321017721502432002013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114460428023628669909336017 85845321017721502432002013)
      ·
        refine ⟨32191995381645563412000755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85845321017721502432002013 32191995381645563412000755)
        ·
          refine ⟨48287993072468345118001133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32191995381645563412000755 48287993072468345118001133)
          ·
            refine ⟨18107997402175629419250425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48287993072468345118001133 18107997402175629419250425)
            ·
              refine ⟨13580998051631722064437819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18107997402175629419250425 13580998051631722064437819)
              ·
                refine ⟨20371497077447583096656729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13580998051631722064437819 20371497077447583096656729)
                ·
                  refine ⟨15278622808085687322492547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20371497077447583096656729 15278622808085687322492547)
                  ·
                    refine ⟨22917934212128530983738821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15278622808085687322492547 22917934212128530983738821)
                    ·
                      refine ⟨4297112664774099559451029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22917934212128530983738821 4297112664774099559451029)
                      ·
                        rfl

theorem cell23_8368597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_8368597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368597 prefixEnd_8368597 := by exact prefixLift 8368597
  have htrace : WordTrace (prefixWord ++ tailWord_8368597) baseStart_8368597 baseEnd_8368597 := by
    simpa [prefixWord, tailWord_8368597, baseEnd_8368597] using wordTrace_append hprefix tailTrace_8368597
  have hstable : (prefixWord ++ tailWord_8368597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368597).length < 2 ^ (prefixWord ++ tailWord_8368597).sum := by decide
  have hdescent : baseEnd_8368597 < baseStart_8368597 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368620 : List Nat := [2, 2, 1, 1, 2, 1, 6, 2, 6]
def baseStart_8368620 : Nat := 118140960795 + 8368620 * 2 ^ 59
def prefixEnd_8368620 : Nat := 4983230072969 + 3 ^ 40 * 8368620 * 2
def baseEnd_8368620 : Nat := 477458274981016996607047

theorem tailTrace_8368620 : CollatzResearch.WordTrace tailWord_8368620 prefixEnd_8368620 477458274981016996607047 := by
  unfold tailWord_8368620
  simp only [CollatzResearch.WordTrace]
  refine ⟨152614323470963230676491657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203485764627950974235322209 152614323470963230676491657)
  ·
    refine ⟨114460742603222423007368743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152614323470963230676491657 114460742603222423007368743)
    ·
      refine ⟨171691113904833634511053115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114460742603222423007368743 171691113904833634511053115)
      ·
        refine ⟨257536670857250451766579673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171691113904833634511053115 257536670857250451766579673)
        ·
          refine ⟨193152503142937838824934755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257536670857250451766579673 193152503142937838824934755)
          ·
            refine ⟨289728754714406758237402133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193152503142937838824934755 289728754714406758237402133)
            ·
              refine ⟨13581035377237816792378225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 289728754714406758237402133 13581035377237816792378225)
              ·
                refine ⟨10185776532928362594283669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13581035377237816792378225 10185776532928362594283669)
                ·
                  refine ⟨477458274981016996607047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10185776532928362594283669 477458274981016996607047)
                  ·
                    rfl

theorem cell23_8368620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 6].length) (baseStart_8368620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368620 prefixEnd_8368620 := by exact prefixLift 8368620
  have htrace : WordTrace (prefixWord ++ tailWord_8368620) baseStart_8368620 baseEnd_8368620 := by
    simpa [prefixWord, tailWord_8368620, baseEnd_8368620] using wordTrace_append hprefix tailTrace_8368620
  have hstable : (prefixWord ++ tailWord_8368620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368620).length < 2 ^ (prefixWord ++ tailWord_8368620).sum := by decide
  have hdescent : baseEnd_8368620 < baseStart_8368620 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368623 : List Nat := [1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 6]
def baseStart_8368623 : Nat := 118140960795 + 8368623 * 2 ^ 59
def prefixEnd_8368623 : Nat := 4983230072969 + 3 ^ 40 * 8368623 * 2
def baseEnd_8368623 : Nat := 4297126015271116457725909

theorem tailTrace_8368623 : CollatzResearch.WordTrace tailWord_8368623 prefixEnd_8368623 4297126015271116457725909 := by
  unfold tailWord_8368623
  simp only [CollatzResearch.WordTrace]
  refine ⟨305228756360915592865342523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203485837573943728576895015 305228756360915592865342523)
  ·
    refine ⟨457843134541373389298013785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305228756360915592865342523 457843134541373389298013785)
    ·
      refine ⟨343382350906030041973510339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457843134541373389298013785 343382350906030041973510339)
      ·
        refine ⟨515073526359045062960265509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343382350906030041973510339 515073526359045062960265509)
        ·
          refine ⟨96576286192320949305049783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 515073526359045062960265509 96576286192320949305049783)
          ·
            refine ⟨144864429288481423957574675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96576286192320949305049783 144864429288481423957574675)
            ·
              refine ⟨217296643932722135936362013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144864429288481423957574675 217296643932722135936362013)
              ·
                refine ⟨81486241474770800976135755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217296643932722135936362013 81486241474770800976135755)
                ·
                  refine ⟨122229362212156201464203633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81486241474770800976135755 122229362212156201464203633)
                  ·
                    refine ⟨91672021659117151098152725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 122229362212156201464203633 91672021659117151098152725)
                    ·
                      refine ⟨4297126015271116457725909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91672021659117151098152725 4297126015271116457725909)
                      ·
                        rfl

theorem cell23_8368623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 6].length) (baseStart_8368623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368623 prefixEnd_8368623 := by exact prefixLift 8368623
  have htrace : WordTrace (prefixWord ++ tailWord_8368623) baseStart_8368623 baseEnd_8368623 := by
    simpa [prefixWord, tailWord_8368623, baseEnd_8368623] using wordTrace_append hprefix tailTrace_8368623
  have hstable : (prefixWord ++ tailWord_8368623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368623).length < 2 ^ (prefixWord ++ tailWord_8368623).sum := by decide
  have hdescent : baseEnd_8368623 < baseStart_8368623 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368643 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 7]
def baseStart_8368643 : Nat := 118140960795 + 8368643 * 2 ^ 59
def prefixEnd_8368643 : Nat := 4983230072969 + 3 ^ 40 * 8368643 * 2
def baseEnd_8368643 : Nat := 4297136284884206379475817

theorem tailTrace_8368643 : CollatzResearch.WordTrace tailWord_8368643 prefixEnd_8368643 4297136284884206379475817 := by
  unfold tailWord_8368643
  simp only [CollatzResearch.WordTrace]
  refine ⟨305229485820843136281070583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203486323880562090854047055 305229485820843136281070583)
  ·
    refine ⟨457844228731264704421605875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305229485820843136281070583 457844228731264704421605875)
    ·
      refine ⟨686766343096897056632408813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457844228731264704421605875 686766343096897056632408813)
      ·
        refine ⟨257537378661336396237153305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 686766343096897056632408813 257537378661336396237153305)
        ·
          refine ⟨193153033996002297177864979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257537378661336396237153305 193153033996002297177864979)
          ·
            refine ⟨289729550994003445766797469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193153033996002297177864979 289729550994003445766797469)
            ·
              refine ⟨108648581622751292162549051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 289729550994003445766797469 108648581622751292162549051)
              ·
                refine ⟨162972872434126938243823577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108648581622751292162549051 162972872434126938243823577)
                ·
                  refine ⟨122229654325595203682867683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162972872434126938243823577 122229654325595203682867683)
                  ·
                    refine ⟨183344481488392805524301525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 122229654325595203682867683 183344481488392805524301525)
                    ·
                      refine ⟨4297136284884206379475817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 183344481488392805524301525 4297136284884206379475817)
                      ·
                        rfl

theorem cell23_8368643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_8368643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368643 prefixEnd_8368643 := by exact prefixLift 8368643
  have htrace : WordTrace (prefixWord ++ tailWord_8368643) baseStart_8368643 baseEnd_8368643 := by
    simpa [prefixWord, tailWord_8368643, baseEnd_8368643] using wordTrace_append hprefix tailTrace_8368643
  have hstable : (prefixWord ++ tailWord_8368643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368643).length < 2 ^ (prefixWord ++ tailWord_8368643).sum := by decide
  have hdescent : baseEnd_8368643 < baseStart_8368643 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368650 : List Nat := [3, 1, 2, 2, 2, 1, 1, 3, 3, 5]
def baseStart_8368650 : Nat := 118140960795 + 8368650 * 2 ^ 59
def prefixEnd_8368650 : Nat := 4983230072969 + 3 ^ 40 * 8368650 * 2
def baseEnd_8368650 : Nat := 1432379959749595950696095

theorem tailTrace_8368650 : CollatzResearch.WordTrace tailWord_8368650 prefixEnd_8368650 1432379959749595950696095 := by
  unfold tailWord_8368650
  simp only [CollatzResearch.WordTrace]
  refine ⟨76307435282954444119143851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203486494087878517651050269 76307435282954444119143851)
  ·
    refine ⟨114461152924431666178715777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76307435282954444119143851 114461152924431666178715777)
    ·
      refine ⟨85845864693323749634036833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114461152924431666178715777 85845864693323749634036833)
      ·
        refine ⟨64384398519992812225527625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85845864693323749634036833 64384398519992812225527625)
        ·
          refine ⟨48288298889994609169145719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64384398519992812225527625 48288298889994609169145719)
          ·
            refine ⟨72432448334991913753718579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48288298889994609169145719 72432448334991913753718579)
            ·
              refine ⟨108648672502487870630577869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72432448334991913753718579 108648672502487870630577869)
              ·
                refine ⟨40743252188432951486466701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108648672502487870630577869 40743252188432951486466701)
                ·
                  refine ⟨15278719570662356807425013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40743252188432951486466701 15278719570662356807425013)
                  ·
                    refine ⟨1432379959749595950696095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15278719570662356807425013 1432379959749595950696095)
                    ·
                      rfl

theorem cell23_8368650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_8368650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368650 prefixEnd_8368650 := by exact prefixLift 8368650
  have htrace : WordTrace (prefixWord ++ tailWord_8368650) baseStart_8368650 baseEnd_8368650 := by
    simpa [prefixWord, tailWord_8368650, baseEnd_8368650] using wordTrace_append hprefix tailTrace_8368650
  have hstable : (prefixWord ++ tailWord_8368650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368650).length < 2 ^ (prefixWord ++ tailWord_8368650).sum := by decide
  have hdescent : baseEnd_8368650 < baseStart_8368650 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368657 : List Nat := [1, 2, 2, 1, 1, 2, 2, 5, 2, 3, 2]
def baseStart_8368657 : Nat := 118140960795 + 8368657 * 2 ^ 59
def prefixEnd_8368657 : Nat := 4983230072969 + 3 ^ 40 * 8368657 * 2
def baseEnd_8368657 : Nat := 4297143473613369324700753

theorem tailTrace_8368657 : CollatzResearch.WordTrace tailWord_8368657 prefixEnd_8368657 4297143473613369324700753 := by
  unfold tailWord_8368657
  simp only [CollatzResearch.WordTrace]
  refine ⟨305229996442792416672080225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203486664295194944448053483 305229996442792416672080225)
  ·
    refine ⟨228922497332094312504060169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305229996442792416672080225 228922497332094312504060169)
    ·
      refine ⟨171691872999070734378045127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228922497332094312504060169 171691872999070734378045127)
      ·
        refine ⟨257537809498606101567067691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171691872999070734378045127 257537809498606101567067691)
        ·
          refine ⟨386306714247909152350601537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257537809498606101567067691 386306714247909152350601537)
          ·
            refine ⟨289730035685931864262951153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386306714247909152350601537 289730035685931864262951153)
            ·
              refine ⟨217297526764448898197213365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289730035685931864262951153 217297526764448898197213365)
              ·
                refine ⟨20371643134167084205988753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 217297526764448898197213365 20371643134167084205988753)
                ·
                  refine ⟨15278732350625313154491565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20371643134167084205988753 15278732350625313154491565)
                  ·
                    refine ⟨5729524631484492432934337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15278732350625313154491565 5729524631484492432934337)
                    ·
                      refine ⟨4297143473613369324700753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5729524631484492432934337 4297143473613369324700753)
                      ·
                        rfl

theorem cell23_8368657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 3, 2].length) (baseStart_8368657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368657 prefixEnd_8368657 := by exact prefixLift 8368657
  have htrace : WordTrace (prefixWord ++ tailWord_8368657) baseStart_8368657 baseEnd_8368657 := by
    simpa [prefixWord, tailWord_8368657, baseEnd_8368657] using wordTrace_append hprefix tailTrace_8368657
  have hstable : (prefixWord ++ tailWord_8368657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368657).length < 2 ^ (prefixWord ++ tailWord_8368657).sum := by decide
  have hdescent : baseEnd_8368657 < baseStart_8368657 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368690 : List Nat := [3, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5]
def baseStart_8368690 : Nat := 118140960795 + 8368690 * 2 ^ 59
def prefixEnd_8368690 : Nat := 4983230072969 + 3 ^ 40 * 8368690 * 2
def baseEnd_8368690 : Nat := 4297160418474967695588101

theorem tailTrace_8368690 : CollatzResearch.WordTrace tailWord_8368690 prefixEnd_8368690 4297160418474967695588101 := by
  unfold tailWord_8368690
  simp only [CollatzResearch.WordTrace]
  refine ⟨76307800012918215827007881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203487466701115242205354349 76307800012918215827007881)
  ·
    refine ⟨57230850009688661870255911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76307800012918215827007881 57230850009688661870255911)
    ·
      refine ⟨85846275014532992805383867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57230850009688661870255911 85846275014532992805383867)
      ·
        refine ⟨128769412521799489208075801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85846275014532992805383867 128769412521799489208075801)
        ·
          refine ⟨96577059391349616906056851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128769412521799489208075801 96577059391349616906056851)
          ·
            refine ⟨144865589087024425359085277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96577059391349616906056851 144865589087024425359085277)
            ·
              refine ⟨54324595907634159509656979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144865589087024425359085277 54324595907634159509656979)
              ·
                refine ⟨81486893861451239264485469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54324595907634159509656979 81486893861451239264485469)
                ·
                  refine ⟨30557585198044214724182051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81486893861451239264485469 30557585198044214724182051)
                  ·
                    refine ⟨45836377797066322086273077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30557585198044214724182051 45836377797066322086273077)
                    ·
                      refine ⟨4297160418474967695588101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45836377797066322086273077 4297160418474967695588101)
                      ·
                        rfl

theorem cell23_8368690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_8368690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368690 prefixEnd_8368690 := by exact prefixLift 8368690
  have htrace : WordTrace (prefixWord ++ tailWord_8368690) baseStart_8368690 baseEnd_8368690 := by
    simpa [prefixWord, tailWord_8368690, baseEnd_8368690] using wordTrace_append hprefix tailTrace_8368690
  have hstable : (prefixWord ++ tailWord_8368690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368690).length < 2 ^ (prefixWord ++ tailWord_8368690).sum := by decide
  have hdescent : baseEnd_8368690 < baseStart_8368690 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368704 : List Nat := [2, 1, 1, 2, 2, 2, 4, 2, 3, 2, 2]
def baseStart_8368704 : Nat := 118140960795 + 8368704 * 2 ^ 59
def prefixEnd_8368704 : Nat := 4983230072969 + 3 ^ 40 * 8368704 * 2
def baseEnd_8368704 : Nat := 4297167607204130640813037

theorem tailTrace_8368704 : CollatzResearch.WordTrace tailWord_8368704 prefixEnd_8368704 4297167607204130640813037 := by
  unfold tailWord_8368704
  simp only [CollatzResearch.WordTrace]
  refine ⟨152615855336811071849520583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203487807115748095799360777 152615855336811071849520583)
  ·
    refine ⟨228923783005216607774280875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152615855336811071849520583 228923783005216607774280875)
    ·
      refine ⟨343385674507824911661421313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228923783005216607774280875 343385674507824911661421313)
      ·
        refine ⟨257539255880868683746065985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343385674507824911661421313 257539255880868683746065985)
        ·
          refine ⟨193154441910651512809549489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257539255880868683746065985 193154441910651512809549489)
          ·
            refine ⟨144865831432988634607162117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193154441910651512809549489 144865831432988634607162117)
            ·
              refine ⟨27162343393685368988842897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144865831432988634607162117 27162343393685368988842897)
              ·
                refine ⟨20371757545264026741632173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27162343393685368988842897 20371757545264026741632173)
                ·
                  refine ⟨7639409079474010028112065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20371757545264026741632173 7639409079474010028112065)
                  ·
                    refine ⟨5729556809605507521084049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7639409079474010028112065 5729556809605507521084049)
                    ·
                      refine ⟨4297167607204130640813037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5729556809605507521084049 4297167607204130640813037)
                      ·
                        rfl

theorem cell23_8368704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 3, 2, 2].length) (baseStart_8368704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368704 prefixEnd_8368704 := by exact prefixLift 8368704
  have htrace : WordTrace (prefixWord ++ tailWord_8368704) baseStart_8368704 baseEnd_8368704 := by
    simpa [prefixWord, tailWord_8368704, baseEnd_8368704] using wordTrace_append hprefix tailTrace_8368704
  have hstable : (prefixWord ++ tailWord_8368704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368704).length < 2 ^ (prefixWord ++ tailWord_8368704).sum := by decide
  have hdescent : baseEnd_8368704 < baseStart_8368704 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368724 : List Nat := [2, 4, 1, 1, 1, 3, 2, 3, 1, 2, 3]
def baseStart_8368724 : Nat := 118140960795 + 8368724 * 2 ^ 59
def prefixEnd_8368724 : Nat := 4983230072969 + 3 ^ 40 * 8368724 * 2
def baseEnd_8368724 : Nat := 4297177876817220562562945

theorem tailTrace_8368724 : CollatzResearch.WordTrace tailWord_8368724 prefixEnd_8368724 4297177876817220562562945 := by
  unfold tailWord_8368724
  simp only [CollatzResearch.WordTrace]
  refine ⟨152616220066774843557384613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203488293422366458076512817 152616220066774843557384613)
  ·
    refine ⟨28615541262520283167009615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152616220066774843557384613 28615541262520283167009615)
    ·
      refine ⟨42923311893780424750514423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28615541262520283167009615 42923311893780424750514423)
      ·
        refine ⟨64384967840670637125771635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42923311893780424750514423 64384967840670637125771635)
        ·
          refine ⟨96577451761005955688657453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64384967840670637125771635 96577451761005955688657453)
          ·
            refine ⟨36216544410377233383246545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96577451761005955688657453 36216544410377233383246545)
            ·
              refine ⟨27162408307782925037434909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36216544410377233383246545 27162408307782925037434909)
              ·
                refine ⟨10185903115418596889038091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27162408307782925037434909 10185903115418596889038091)
                ·
                  refine ⟨15278854673127895333557137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10185903115418596889038091 15278854673127895333557137)
                  ·
                    refine ⟨11459141004845921500167853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15278854673127895333557137 11459141004845921500167853)
                    ·
                      refine ⟨4297177876817220562562945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11459141004845921500167853 4297177876817220562562945)
                      ·
                        rfl

theorem cell23_8368724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_8368724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368724 prefixEnd_8368724 := by exact prefixLift 8368724
  have htrace : WordTrace (prefixWord ++ tailWord_8368724) baseStart_8368724 baseEnd_8368724 := by
    simpa [prefixWord, tailWord_8368724, baseEnd_8368724] using wordTrace_append hprefix tailTrace_8368724
  have hstable : (prefixWord ++ tailWord_8368724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368724).length < 2 ^ (prefixWord ++ tailWord_8368724).sum := by decide
  have hdescent : baseEnd_8368724 < baseStart_8368724 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368740 : List Nat := [2, 3, 1, 1, 2, 2, 2, 1, 2, 7]
def baseStart_8368740 : Nat := 118140960795 + 8368740 * 2 ^ 59
def prefixEnd_8368740 : Nat := 4983230072969 + 3 ^ 40 * 8368740 * 2
def baseEnd_8368740 : Nat := 1432395364169230833320957

theorem tailTrace_8368740 : CollatzResearch.WordTrace tailWord_8368740 prefixEnd_8368740 1432395364169230833320957 := by
  unfold tailWord_8368740
  simp only [CollatzResearch.WordTrace]
  refine ⟨152616511850745860923675837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203488682467661147898234449 152616511850745860923675837)
  ·
    refine ⟨57231191944029697846378439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152616511850745860923675837 57231191944029697846378439)
    ·
      refine ⟨85846787916044546769567659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57231191944029697846378439 85846787916044546769567659)
      ·
        refine ⟨128770181874066820154351489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85846787916044546769567659 128770181874066820154351489)
        ·
          refine ⟨96577636405550115115763617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128770181874066820154351489 96577636405550115115763617)
          ·
            refine ⟨72433227304162586336822713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96577636405550115115763617 72433227304162586336822713)
            ·
              refine ⟨54324920478121939752617035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72433227304162586336822713 54324920478121939752617035)
              ·
                refine ⟨81487380717182909628925553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54324920478121939752617035 81487380717182909628925553)
                ·
                  refine ⟨61115535537887182221694165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81487380717182909628925553 61115535537887182221694165)
                  ·
                    refine ⟨1432395364169230833320957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61115535537887182221694165 1432395364169230833320957)
                    ·
                      rfl

theorem cell23_8368740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_8368740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368740 prefixEnd_8368740 := by exact prefixLift 8368740
  have htrace : WordTrace (prefixWord ++ tailWord_8368740) baseStart_8368740 baseEnd_8368740 := by
    simpa [prefixWord, tailWord_8368740, baseEnd_8368740] using wordTrace_append hprefix tailTrace_8368740
  have hstable : (prefixWord ++ tailWord_8368740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368740).length < 2 ^ (prefixWord ++ tailWord_8368740).sum := by decide
  have hdescent : baseEnd_8368740 < baseStart_8368740 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368758 : List Nat := [5, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3]
def baseStart_8368758 : Nat := 118140960795 + 8368758 * 2 ^ 59
def prefixEnd_8368758 : Nat := 4983230072969 + 3 ^ 40 * 8368758 * 2
def baseEnd_8368758 : Nat := 4297195335159473429537789

theorem tailTrace_8368758 : CollatzResearch.WordTrace tailWord_8368758 prefixEnd_8368758 4297195335159473429537789 := by
  unfold tailWord_8368758
  simp only [CollatzResearch.WordTrace]
  refine ⟨19077105013464156932594183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203489120143617673947671285 19077105013464156932594183)
  ·
    refine ⟨28615657520196235398891275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19077105013464156932594183 28615657520196235398891275)
    ·
      refine ⟨42923486280294353098336913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28615657520196235398891275 42923486280294353098336913)
      ·
        refine ⟨32192614710220764823752685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42923486280294353098336913 32192614710220764823752685)
        ·
          refine ⟨12072230516332786808907257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32192614710220764823752685 12072230516332786808907257)
          ·
            refine ⟨9054172887249590106680443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12072230516332786808907257 9054172887249590106680443)
            ·
              refine ⟨13581259330874385160020665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9054172887249590106680443 13581259330874385160020665)
              ·
                refine ⟨10185944498155788870015499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13581259330874385160020665 10185944498155788870015499)
                ·
                  refine ⟨15278916747233683305023249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10185944498155788870015499 15278916747233683305023249)
                  ·
                    refine ⟨11459187560425262478767437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15278916747233683305023249 11459187560425262478767437)
                    ·
                      refine ⟨4297195335159473429537789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11459187560425262478767437 4297195335159473429537789)
                      ·
                        rfl

theorem cell23_8368758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_8368758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368758 prefixEnd_8368758 := by exact prefixLift 8368758
  have htrace : WordTrace (prefixWord ++ tailWord_8368758) baseStart_8368758 baseEnd_8368758 := by
    simpa [prefixWord, tailWord_8368758, baseEnd_8368758] using wordTrace_append hprefix tailTrace_8368758
  have hstable : (prefixWord ++ tailWord_8368758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368758).length < 2 ^ (prefixWord ++ tailWord_8368758).sum := by decide
  have hdescent : baseEnd_8368758 < baseStart_8368758 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368760 : List Nat := [2, 1, 2, 1, 1, 1, 2, 4, 2, 3, 4]
def baseStart_8368760 : Nat := 118140960795 + 8368760 * 2 ^ 59
def prefixEnd_8368760 : Nat := 4983230072969 + 3 ^ 40 * 8368760 * 2
def baseEnd_8368760 : Nat := 4297196362120782421712779

theorem tailTrace_8368760 : CollatzResearch.WordTrace tailWord_8368760 prefixEnd_8368760 4297196362120782421712779 := by
  unfold tailWord_8368760
  simp only [CollatzResearch.WordTrace]
  refine ⟨152616876580709632631539867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203489168774279510175386489 152616876580709632631539867)
  ·
    refine ⟨228925314871064448947309801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152616876580709632631539867 228925314871064448947309801)
    ·
      refine ⟨171693986153298336710482351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228925314871064448947309801 171693986153298336710482351)
      ·
        refine ⟨257540979229947505065723527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171693986153298336710482351 257540979229947505065723527)
        ·
          refine ⟨386311468844921257598585291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257540979229947505065723527 386311468844921257598585291)
          ·
            refine ⟨579467203267381886397877937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386311468844921257598585291 579467203267381886397877937)
            ·
              refine ⟨434600402450536414798408453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 579467203267381886397877937 434600402450536414798408453)
              ·
                refine ⟨81487575459475577774701585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 434600402450536414798408453 81487575459475577774701585)
                ·
                  refine ⟨61115681594606683331026189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81487575459475577774701585 61115681594606683331026189)
                  ·
                    refine ⟨22918380597977506249134821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61115681594606683331026189 22918380597977506249134821)
                    ·
                      refine ⟨4297196362120782421712779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22918380597977506249134821 4297196362120782421712779)
                      ·
                        rfl

theorem cell23_8368760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 2, 3, 4].length) (baseStart_8368760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368760 prefixEnd_8368760 := by exact prefixLift 8368760
  have htrace : WordTrace (prefixWord ++ tailWord_8368760) baseStart_8368760 baseEnd_8368760 := by
    simpa [prefixWord, tailWord_8368760, baseEnd_8368760] using wordTrace_append hprefix tailTrace_8368760
  have hstable : (prefixWord ++ tailWord_8368760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368760).length < 2 ^ (prefixWord ++ tailWord_8368760).sum := by decide
  have hdescent : baseEnd_8368760 < baseStart_8368760 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368780 : List Nat := [2, 2, 1, 2, 1, 1, 2, 3, 1, 3, 5]
def baseStart_8368780 : Nat := 118140960795 + 8368780 * 2 ^ 59
def prefixEnd_8368780 : Nat := 4983230072969 + 3 ^ 40 * 8368780 * 2
def baseEnd_8368780 : Nat := 4297206631733872343462687

theorem tailTrace_8368780 : CollatzResearch.WordTrace tailWord_8368780 prefixEnd_8368780 4297206631733872343462687 := by
  unfold tailWord_8368780
  simp only [CollatzResearch.WordTrace]
  refine ⟨152617241310673404339403897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203489655080897872452538529 152617241310673404339403897)
  ·
    refine ⟨114462930983005053254552923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152617241310673404339403897 114462930983005053254552923)
    ·
      refine ⟨171694396474507579881829385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114462930983005053254552923 171694396474507579881829385)
      ·
        refine ⟨128770797355880684911372039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171694396474507579881829385 128770797355880684911372039)
        ·
          refine ⟨193156196033821027367058059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128770797355880684911372039 193156196033821027367058059)
          ·
            refine ⟨289734294050731541050587089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193156196033821027367058059 289734294050731541050587089)
            ·
              refine ⟨217300720538048655787940317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289734294050731541050587089 217300720538048655787940317)
              ·
                refine ⟨81487770201768245920477619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217300720538048655787940317 81487770201768245920477619)
                ·
                  refine ⟨122231655302652368880716429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81487770201768245920477619 122231655302652368880716429)
                  ·
                    refine ⟨45836870738494638330268661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 122231655302652368880716429 45836870738494638330268661)
                    ·
                      refine ⟨4297206631733872343462687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45836870738494638330268661 4297206631733872343462687)
                      ·
                        rfl

theorem cell23_8368780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_8368780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368780 prefixEnd_8368780 := by exact prefixLift 8368780
  have htrace : WordTrace (prefixWord ++ tailWord_8368780) baseStart_8368780 baseEnd_8368780 := by
    simpa [prefixWord, tailWord_8368780, baseEnd_8368780] using wordTrace_append hprefix tailTrace_8368780
  have hstable : (prefixWord ++ tailWord_8368780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368780).length < 2 ^ (prefixWord ++ tailWord_8368780).sum := by decide
  have hdescent : baseEnd_8368780 < baseStart_8368780 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368788 : List Nat := [2, 4, 2, 2, 1, 2, 2, 2, 2, 1, 3]
def baseStart_8368788 : Nat := 118140960795 + 8368788 * 2 ^ 59
def prefixEnd_8368788 : Nat := 4983230072969 + 3 ^ 40 * 8368788 * 2
def baseEnd_8368788 : Nat := 4297210739579108312162651

theorem tailTrace_8368788 : CollatzResearch.WordTrace tailWord_8368788 prefixEnd_8368788 4297210739579108312162651 := by
  unfold tailWord_8368788
  simp only [CollatzResearch.WordTrace]
  refine ⟨152617387202658913022549509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203489849603545217363399345 152617387202658913022549509)
  ·
    refine ⟨28615760100498546191728033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152617387202658913022549509 28615760100498546191728033)
    ·
      refine ⟨21461820075373909643796025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28615760100498546191728033 21461820075373909643796025)
      ·
        refine ⟨16096365056530432232847019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21461820075373909643796025 16096365056530432232847019)
        ·
          refine ⟨24144547584795648349270529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16096365056530432232847019 24144547584795648349270529)
          ·
            refine ⟨18108410688596736261952897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24144547584795648349270529 18108410688596736261952897)
            ·
              refine ⟨13581308016447552196464673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18108410688596736261952897 13581308016447552196464673)
              ·
                refine ⟨10185981012335664147348505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13581308016447552196464673 10185981012335664147348505)
                ·
                  refine ⟨7639485759251748110511379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10185981012335664147348505 7639485759251748110511379)
                  ·
                    refine ⟨11459228638877622165767069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7639485759251748110511379 11459228638877622165767069)
                    ·
                      refine ⟨4297210739579108312162651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11459228638877622165767069 4297210739579108312162651)
                      ·
                        rfl

theorem cell23_8368788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_8368788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368788 prefixEnd_8368788 := by exact prefixLift 8368788
  have htrace : WordTrace (prefixWord ++ tailWord_8368788) baseStart_8368788 baseEnd_8368788 := by
    simpa [prefixWord, tailWord_8368788, baseEnd_8368788] using wordTrace_append hprefix tailTrace_8368788
  have hstable : (prefixWord ++ tailWord_8368788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368788).length < 2 ^ (prefixWord ++ tailWord_8368788).sum := by decide
  have hdescent : baseEnd_8368788 < baseStart_8368788 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368797 : List Nat := [1, 4, 2, 1, 1, 1, 3, 1, 2, 4, 3]
def baseStart_8368797 : Nat := 118140960795 + 8368797 * 2 ^ 59
def prefixEnd_8368797 : Nat := 4983230072969 + 3 ^ 40 * 8368797 * 2
def baseEnd_8368797 : Nat := 4297215360904998776950109

theorem tailTrace_8368797 : CollatzResearch.WordTrace tailWord_8368797 prefixEnd_8368797 4297215360904998776950109 := by
  unfold tailWord_8368797
  simp only [CollatzResearch.WordTrace]
  refine ⟨305235102662285220582176645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203490068441523480388117763 305235102662285220582176645)
  ·
    refine ⟨57231581749178478859158121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305235102662285220582176645 57231581749178478859158121)
    ·
      refine ⟨42923686311883859144368591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57231581749178478859158121 42923686311883859144368591)
      ·
        refine ⟨64385529467825788716552887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42923686311883859144368591 64385529467825788716552887)
        ·
          refine ⟨96578294201738683074829331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64385529467825788716552887 96578294201738683074829331)
          ·
            refine ⟨144867441302608024612243997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96578294201738683074829331 144867441302608024612243997)
            ·
              refine ⟨54325290488478009229591499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144867441302608024612243997 54325290488478009229591499)
              ·
                refine ⟨81487935732717013844387249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54325290488478009229591499 81487935732717013844387249)
                ·
                  refine ⟨61115951799537760383290437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81487935732717013844387249 61115951799537760383290437)
                  ·
                    refine ⟨11459240962413330071866957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61115951799537760383290437 11459240962413330071866957)
                    ·
                      refine ⟨4297215360904998776950109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11459240962413330071866957 4297215360904998776950109)
                      ·
                        rfl

theorem cell23_8368797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_8368797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368797 prefixEnd_8368797 := by exact prefixLift 8368797
  have htrace : WordTrace (prefixWord ++ tailWord_8368797) baseStart_8368797 baseEnd_8368797 := by
    simpa [prefixWord, tailWord_8368797, baseEnd_8368797] using wordTrace_append hprefix tailTrace_8368797
  have hstable : (prefixWord ++ tailWord_8368797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368797).length < 2 ^ (prefixWord ++ tailWord_8368797).sum := by decide
  have hdescent : baseEnd_8368797 < baseStart_8368797 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368844 : List Nat := [2, 2, 1, 5, 1, 1, 1, 2, 2, 3, 3]
def baseStart_8368844 : Nat := 118140960795 + 8368844 * 2 ^ 59
def prefixEnd_8368844 : Nat := 4983230072969 + 3 ^ 40 * 8368844 * 2
def baseEnd_8368844 : Nat := 4297239494495760093062393

theorem tailTrace_8368844 : CollatzResearch.WordTrace tailWord_8368844 prefixEnd_8368844 4297239494495760093062393 := by
  unfold tailWord_8368844
  simp only [CollatzResearch.WordTrace]
  refine ⟨152618408446557473804568793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203491211262076631739425057 152618408446557473804568793)
  ·
    refine ⟨114463806334918105353426595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152618408446557473804568793 114463806334918105353426595)
    ·
      refine ⟨171695709502377158030139893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114463806334918105353426595 171695709502377158030139893)
      ·
        refine ⟨16096472765847858565325615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 171695709502377158030139893 16096472765847858565325615)
        ·
          refine ⟨24144709148771787847988423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16096472765847858565325615 24144709148771787847988423)
          ·
            refine ⟨36217063723157681771982635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24144709148771787847988423 36217063723157681771982635)
            ·
              refine ⟨54325595584736522657973953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36217063723157681771982635 54325595584736522657973953)
              ·
                refine ⟨40744196688552391993480465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54325595584736522657973953 40744196688552391993480465)
                ·
                  refine ⟨30558147516414293995110349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40744196688552391993480465 30558147516414293995110349)
                  ·
                    refine ⟨11459305318655360248166381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30558147516414293995110349 11459305318655360248166381)
                    ·
                      refine ⟨4297239494495760093062393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11459305318655360248166381 4297239494495760093062393)
                      ·
                        rfl

theorem cell23_8368844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_8368844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368844 prefixEnd_8368844 := by exact prefixLift 8368844
  have htrace : WordTrace (prefixWord ++ tailWord_8368844) baseStart_8368844 baseEnd_8368844 := by
    simpa [prefixWord, tailWord_8368844, baseEnd_8368844] using wordTrace_append hprefix tailTrace_8368844
  have hstable : (prefixWord ++ tailWord_8368844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368844).length < 2 ^ (prefixWord ++ tailWord_8368844).sum := by decide
  have hdescent : baseEnd_8368844 < baseStart_8368844 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368845 : List Nat := [1, 6, 2, 1, 2, 1, 1, 1, 4, 2, 2]
def baseStart_8368845 : Nat := 118140960795 + 8368845 * 2 ^ 59
def prefixEnd_8368845 : Nat := 4983230072969 + 3 ^ 40 * 8368845 * 2
def baseEnd_8368845 : Nat := 4297240007976414589149889

theorem tailTrace_8368845 : CollatzResearch.WordTrace tailWord_8368845 prefixEnd_8368845 4297240007976414589149889 := by
  unfold tailWord_8368845
  simp only [CollatzResearch.WordTrace]
  refine ⟨305236853366111324779923989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203491235577407549853282659 305236853366111324779923989)
  ·
    refine ⟨14307977501536468349058937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 305236853366111324779923989 14307977501536468349058937)
    ·
      refine ⟨10730983126152351261794203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14307977501536468349058937 10730983126152351261794203)
      ·
        refine ⟨16096474689228526892691305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10730983126152351261794203 16096474689228526892691305)
        ·
          refine ⟨12072356016921395169518479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16096474689228526892691305 12072356016921395169518479)
          ·
            refine ⟨18108534025382092754277719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12072356016921395169518479 18108534025382092754277719)
            ·
              refine ⟨27162801038073139131416579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18108534025382092754277719 27162801038073139131416579)
              ·
                refine ⟨40744201557109708697124869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27162801038073139131416579 40744201557109708697124869)
                ·
                  refine ⟨7639537791958070380710913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40744201557109708697124869 7639537791958070380710913)
                  ·
                    refine ⟨5729653343968552785533185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7639537791958070380710913 5729653343968552785533185)
                    ·
                      refine ⟨4297240007976414589149889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5729653343968552785533185 4297240007976414589149889)
                      ·
                        rfl

theorem cell23_8368845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_8368845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368845 prefixEnd_8368845 := by exact prefixLift 8368845
  have htrace : WordTrace (prefixWord ++ tailWord_8368845) baseStart_8368845 baseEnd_8368845 := by
    simpa [prefixWord, tailWord_8368845, baseEnd_8368845] using wordTrace_append hprefix tailTrace_8368845
  have hstable : (prefixWord ++ tailWord_8368845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368845).length < 2 ^ (prefixWord ++ tailWord_8368845).sum := by decide
  have hdescent : baseEnd_8368845 < baseStart_8368845 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368877 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 2, 8]
def baseStart_8368877 : Nat := 118140960795 + 8368877 * 2 ^ 59
def prefixEnd_8368877 : Nat := 4983230072969 + 3 ^ 40 * 8368877 * 2
def baseEnd_8368877 : Nat := 1432418813119119487983247

theorem tailTrace_8368877 : CollatzResearch.WordTrace tailWord_8368877 prefixEnd_8368877 1432418813119119487983247 := by
  unfold tailWord_8368877
  simp only [CollatzResearch.WordTrace]
  refine ⟨305238020501995394245088885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203492013667996929496725923 305238020501995394245088885)
  ·
    refine ⟨28616064422062068210477083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 305238020501995394245088885 28616064422062068210477083)
    ·
      refine ⟨42924096633093102315715625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28616064422062068210477083 42924096633093102315715625)
      ·
        refine ⟨32193072474819826736786719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42924096633093102315715625 32193072474819826736786719)
        ·
          refine ⟨48289608712229740105180079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32193072474819826736786719 48289608712229740105180079)
          ·
            refine ⟨72434413068344610157770119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48289608712229740105180079 72434413068344610157770119)
            ·
              refine ⟨108651619602516915236655179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72434413068344610157770119 108651619602516915236655179)
              ·
                refine ⟨162977429403775372854982769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108651619602516915236655179 162977429403775372854982769)
                ·
                  refine ⟨122233072052831529641237077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162977429403775372854982769 122233072052831529641237077)
                  ·
                    refine ⟨1432418813119119487983247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 122233072052831529641237077 1432418813119119487983247)
                    ·
                      rfl

theorem cell23_8368877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_8368877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368877 prefixEnd_8368877 := by exact prefixLift 8368877
  have htrace : WordTrace (prefixWord ++ tailWord_8368877) baseStart_8368877 baseEnd_8368877 := by
    simpa [prefixWord, tailWord_8368877, baseEnd_8368877] using wordTrace_append hprefix tailTrace_8368877
  have hstable : (prefixWord ++ tailWord_8368877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368877).length < 2 ^ (prefixWord ++ tailWord_8368877).sum := by decide
  have hdescent : baseEnd_8368877 < baseStart_8368877 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368904 : List Nat := [2, 1, 3, 2, 2, 2, 1, 1, 4, 2, 3]
def baseStart_8368904 : Nat := 118140960795 + 8368904 * 2 ^ 59
def prefixEnd_8368904 : Nat := 4983230072969 + 3 ^ 40 * 8368904 * 2
def baseEnd_8368904 : Nat := 4297270303335029858312117

theorem tailTrace_8368904 : CollatzResearch.WordTrace tailWord_8368904 prefixEnd_8368904 4297270303335029858312117 := by
  unfold tailWord_8368904
  simp only [CollatzResearch.WordTrace]
  refine ⟨152619502636448788928160883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203492670181931718570881177 152619502636448788928160883)
  ·
    refine ⟨228929253954673183392241325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152619502636448788928160883 228929253954673183392241325)
    ·
      refine ⟨85848470233002443772090497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228929253954673183392241325 85848470233002443772090497)
      ·
        refine ⟨64386352674751832829067873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85848470233002443772090497 64386352674751832829067873)
        ·
          refine ⟨48289764506063874621800905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64386352674751832829067873 48289764506063874621800905)
          ·
            refine ⟨36217323379547905966350679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48289764506063874621800905 36217323379547905966350679)
            ·
              refine ⟨54325985069321858949526019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36217323379547905966350679 54325985069321858949526019)
              ·
                refine ⟨81488977603982788424289029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54325985069321858949526019 81488977603982788424289029)
                ·
                  refine ⟨15279183300746772829554193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81488977603982788424289029 15279183300746772829554193)
                  ·
                    refine ⟨11459387475560079622165645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15279183300746772829554193 11459387475560079622165645)
                    ·
                      refine ⟨4297270303335029858312117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11459387475560079622165645 4297270303335029858312117)
                      ·
                        rfl

theorem cell23_8368904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_8368904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368904 prefixEnd_8368904 := by exact prefixLift 8368904
  have htrace : WordTrace (prefixWord ++ tailWord_8368904) baseStart_8368904 baseEnd_8368904 := by
    simpa [prefixWord, tailWord_8368904, baseEnd_8368904] using wordTrace_append hprefix tailTrace_8368904
  have hstable : (prefixWord ++ tailWord_8368904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368904).length < 2 ^ (prefixWord ++ tailWord_8368904).sum := by decide
  have hdescent : baseEnd_8368904 < baseStart_8368904 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368907 : List Nat := [1, 1, 1, 1, 5, 1, 1, 6, 6]
def baseStart_8368907 : Nat := 118140960795 + 8368907 * 2 ^ 59
def prefixEnd_8368907 : Nat := 4983230072969 + 3 ^ 40 * 8368907 * 2
def baseEnd_8368907 : Nat := 477474649308554816286067

theorem tailTrace_8368907 : CollatzResearch.WordTrace tailWord_8368907 prefixEnd_8368907 477474649308554816286067 := by
  unfold tailWord_8368907
  simp only [CollatzResearch.WordTrace]
  refine ⟨305239114691886709368680975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203492743127924472912453983 305239114691886709368680975)
  ·
    refine ⟨457858672037830064053021463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305239114691886709368680975 457858672037830064053021463)
    ·
      refine ⟨686788008056745096079532195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457858672037830064053021463 686788008056745096079532195)
      ·
        refine ⟨1030182012085117644119298293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 686788008056745096079532195 1030182012085117644119298293)
        ·
          refine ⟨96579563632979779136184215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1030182012085117644119298293 96579563632979779136184215)
          ·
            refine ⟨144869345449469668704276323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96579563632979779136184215 144869345449469668704276323)
            ·
              refine ⟨217304018174204503056414485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144869345449469668704276323 217304018174204503056414485)
              ·
                refine ⟨10186125851915836080769429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 217304018174204503056414485 10186125851915836080769429)
                ·
                  refine ⟨477474649308554816286067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10186125851915836080769429 477474649308554816286067)
                  ·
                    rfl

theorem cell23_8368907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 6].length) (baseStart_8368907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368907 prefixEnd_8368907 := by exact prefixLift 8368907
  have htrace : WordTrace (prefixWord ++ tailWord_8368907) baseStart_8368907 baseEnd_8368907 := by
    simpa [prefixWord, tailWord_8368907, baseEnd_8368907] using wordTrace_append hprefix tailTrace_8368907
  have hstable : (prefixWord ++ tailWord_8368907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368907).length < 2 ^ (prefixWord ++ tailWord_8368907).sum := by decide
  have hdescent : baseEnd_8368907 < baseStart_8368907 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368924 : List Nat := [2, 2, 3, 1, 1, 4, 1, 3, 6]
def baseStart_8368924 : Nat := 118140960795 + 8368924 * 2 ^ 59
def prefixEnd_8368924 : Nat := 4983230072969 + 3 ^ 40 * 8368924 * 2
def baseEnd_8368924 : Nat := 477475619216457753340225

theorem tailTrace_8368924 : CollatzResearch.WordTrace tailWord_8368924 prefixEnd_8368924 477475619216457753340225 := by
  unfold tailWord_8368924
  simp only [CollatzResearch.WordTrace]
  refine ⟨152619867366412560636024913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203493156488550080848033217 152619867366412560636024913)
  ·
    refine ⟨114464900524809420477018685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152619867366412560636024913 114464900524809420477018685)
    ·
      refine ⟨42924337696803532678882007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114464900524809420477018685 42924337696803532678882007)
      ·
        refine ⟨64386506545205299018323011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42924337696803532678882007 64386506545205299018323011)
        ·
          refine ⟨96579759817807948527484517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64386506545205299018323011 96579759817807948527484517)
          ·
            refine ⟨18108704965838990348903347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96579759817807948527484517 18108704965838990348903347)
            ·
              refine ⟨27163057448758485523355021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18108704965838990348903347 27163057448758485523355021)
              ·
                refine ⟨10186146543284432071258133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27163057448758485523355021 10186146543284432071258133)
                ·
                  refine ⟨477475619216457753340225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10186146543284432071258133 477475619216457753340225)
                  ·
                    rfl

theorem cell23_8368924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 6].length) (baseStart_8368924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368924 prefixEnd_8368924 := by exact prefixLift 8368924
  have htrace : WordTrace (prefixWord ++ tailWord_8368924) baseStart_8368924 baseEnd_8368924 := by
    simpa [prefixWord, tailWord_8368924, baseEnd_8368924] using wordTrace_append hprefix tailTrace_8368924
  have hstable : (prefixWord ++ tailWord_8368924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368924).length < 2 ^ (prefixWord ++ tailWord_8368924).sum := by decide
  have hdescent : baseEnd_8368924 < baseStart_8368924 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368937 : List Nat := [1, 2, 1, 1, 1, 1, 1, 7, 3, 5]
def baseStart_8368937 : Nat := 118140960795 + 8368937 * 2 ^ 59
def prefixEnd_8368937 : Nat := 4983230072969 + 3 ^ 40 * 8368937 * 2
def baseEnd_8368937 : Nat := 1432429082732209409733155

theorem tailTrace_8368937 : CollatzResearch.WordTrace tailWord_8368937 prefixEnd_8368937 1432429082732209409733155 := by
  unfold tailWord_8368937
  simp only [CollatzResearch.WordTrace]
  refine ⟨305240208881778024492273065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203493472587852016328182043 305240208881778024492273065)
  ·
    refine ⟨228930156661333518369204799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305240208881778024492273065 228930156661333518369204799)
    ·
      refine ⟨343395234992000277553807199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228930156661333518369204799 343395234992000277553807199)
      ·
        refine ⟨515092852488000416330710799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343395234992000277553807199 515092852488000416330710799)
        ·
          refine ⟨772639278732000624496066199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515092852488000416330710799 772639278732000624496066199)
          ·
            refine ⟨1158958918098000936744099299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 772639278732000624496066199 1158958918098000936744099299)
            ·
              refine ⟨1738438377147001405116148949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1158958918098000936744099299 1738438377147001405116148949)
              ·
                refine ⟨40744649464382845432409741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1738438377147001405116148949 40744649464382845432409741)
                ·
                  refine ⟨15279243549143567037153653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40744649464382845432409741 15279243549143567037153653)
                  ·
                    refine ⟨1432429082732209409733155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15279243549143567037153653 1432429082732209409733155)
                    ·
                      rfl

theorem cell23_8368937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 5].length) (baseStart_8368937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368937 prefixEnd_8368937 := by exact prefixLift 8368937
  have htrace : WordTrace (prefixWord ++ tailWord_8368937) baseStart_8368937 baseEnd_8368937 := by
    simpa [prefixWord, tailWord_8368937, baseEnd_8368937] using wordTrace_append hprefix tailTrace_8368937
  have hstable : (prefixWord ++ tailWord_8368937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368937).length < 2 ^ (prefixWord ++ tailWord_8368937).sum := by decide
  have hdescent : baseEnd_8368937 < baseStart_8368937 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368944 : List Nat := [2, 1, 1, 1, 2, 2, 1, 5, 1, 5, 2]
def baseStart_8368944 : Nat := 118140960795 + 8368944 * 2 ^ 59
def prefixEnd_8368944 : Nat := 4983230072969 + 3 ^ 40 * 8368944 * 2
def baseEnd_8368944 : Nat := 4297290842561209701811933

theorem tailTrace_8368944 : CollatzResearch.WordTrace tailWord_8368944 prefixEnd_8368944 4297290842561209701811933 := by
  unfold tailWord_8368944
  simp only [CollatzResearch.WordTrace]
  refine ⟨152620232096376332343888943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203493642795168443125185257 152620232096376332343888943)
  ·
    refine ⟨228930348144564498515833415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152620232096376332343888943 228930348144564498515833415)
    ·
      refine ⟨343395522216846747773750123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228930348144564498515833415 343395522216846747773750123)
      ·
        refine ⟨515093283325270121660625185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343395522216846747773750123 515093283325270121660625185)
        ·
          refine ⟨386319962493952591245468889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515093283325270121660625185 386319962493952591245468889)
          ·
            refine ⟨289739971870464443434101667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386319962493952591245468889 289739971870464443434101667)
            ·
              refine ⟨434609957805696665151152501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289739971870464443434101667 434609957805696665151152501)
              ·
                refine ⟨40744683544284062357920547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 434609957805696665151152501 40744683544284062357920547)
                ·
                  refine ⟨61117025316426093536880821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40744683544284062357920547 61117025316426093536880821)
                  ·
                    refine ⟨5729721123414946269082577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61117025316426093536880821 5729721123414946269082577)
                    ·
                      refine ⟨4297290842561209701811933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5729721123414946269082577 4297290842561209701811933)
                      ·
                        rfl

theorem cell23_8368944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 1, 5, 2].length) (baseStart_8368944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368944 prefixEnd_8368944 := by exact prefixLift 8368944
  have htrace : WordTrace (prefixWord ++ tailWord_8368944) baseStart_8368944 baseEnd_8368944 := by
    simpa [prefixWord, tailWord_8368944, baseEnd_8368944] using wordTrace_append hprefix tailTrace_8368944
  have hstable : (prefixWord ++ tailWord_8368944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368944).length < 2 ^ (prefixWord ++ tailWord_8368944).sum := by decide
  have hdescent : baseEnd_8368944 < baseStart_8368944 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368967 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 5, 6]
def baseStart_8368967 : Nat := 118140960795 + 8368967 * 2 ^ 59
def prefixEnd_8368967 : Nat := 4983230072969 + 3 ^ 40 * 8368967 * 2
def baseEnd_8368967 : Nat := 1432434217538754370608109

theorem tailTrace_8368967 : CollatzResearch.WordTrace tailWord_8368967 prefixEnd_8368967 1432434217538754370608109 := by
  unfold tailWord_8368967
  simp only [CollatzResearch.WordTrace]
  refine ⟨305241303071669339615865155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203494202047779559743910103 305241303071669339615865155)
  ·
    refine ⟨457861954607504009423797733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305241303071669339615865155 457861954607504009423797733)
    ·
      refine ⟨85849116488907001766962075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 457861954607504009423797733 85849116488907001766962075)
      ·
        refine ⟨128773674733360502650443113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85849116488907001766962075 128773674733360502650443113)
        ·
          refine ⟨96580256050020376987832335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128773674733360502650443113 96580256050020376987832335)
          ·
            refine ⟨144870384075030565481748503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96580256050020376987832335 144870384075030565481748503)
            ·
              refine ⟨217305576112545848222622755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144870384075030565481748503 217305576112545848222622755)
              ·
                refine ⟨325958364168818772333934133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217305576112545848222622755 325958364168818772333934133)
                ·
                  refine ⟨30558596640826759906306325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 325958364168818772333934133 30558596640826759906306325)
                  ·
                    refine ⟨1432434217538754370608109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30558596640826759906306325 1432434217538754370608109)
                    ·
                      rfl

theorem cell23_8368967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_8368967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368967 prefixEnd_8368967 := by exact prefixLift 8368967
  have htrace : WordTrace (prefixWord ++ tailWord_8368967) baseStart_8368967 baseEnd_8368967 := by
    simpa [prefixWord, tailWord_8368967, baseEnd_8368967] using wordTrace_append hprefix tailTrace_8368967
  have hstable : (prefixWord ++ tailWord_8368967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368967).length < 2 ^ (prefixWord ++ tailWord_8368967).sum := by decide
  have hdescent : baseEnd_8368967 < baseStart_8368967 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368968 : List Nat := [2, 1, 3, 1, 1, 3, 3, 4, 1, 1, 3]
def baseStart_8368968 : Nat := 118140960795 + 8368968 * 2 ^ 59
def prefixEnd_8368968 : Nat := 4983230072969 + 3 ^ 40 * 8368968 * 2
def baseEnd_8368968 : Nat := 4297303166096917607911823

theorem tailTrace_8368968 : CollatzResearch.WordTrace tailWord_8368968 prefixEnd_8368968 4297303166096917607911823 := by
  unfold tailWord_8368968
  simp only [CollatzResearch.WordTrace]
  refine ⟨152620669772332858393325779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203494226363110477857767705 152620669772332858393325779)
  ·
    refine ⟨228931004658499287589988669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152620669772332858393325779 228931004658499287589988669)
    ·
      refine ⟨85849126746937232846245751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228931004658499287589988669 85849126746937232846245751)
      ·
        refine ⟨128773690120405849269368627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85849126746937232846245751 128773690120405849269368627)
        ·
          refine ⟨193160535180608773904052941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128773690120405849269368627 193160535180608773904052941)
          ·
            refine ⟨72435200692728290214019853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193160535180608773904052941 72435200692728290214019853)
            ·
              refine ⟨27163200259773108830257445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72435200692728290214019853 27163200259773108830257445)
              ·
                refine ⟨5093100048707457905673271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27163200259773108830257445 5093100048707457905673271)
                ·
                  refine ⟨7639650073061186858509907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5093100048707457905673271 7639650073061186858509907)
                  ·
                    refine ⟨11459475109591780287764861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7639650073061186858509907 11459475109591780287764861)
                    ·
                      refine ⟨4297303166096917607911823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11459475109591780287764861 4297303166096917607911823)
                      ·
                        rfl

theorem cell23_8368968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 4, 1, 1, 3].length) (baseStart_8368968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368968 prefixEnd_8368968 := by exact prefixLift 8368968
  have htrace : WordTrace (prefixWord ++ tailWord_8368968) baseStart_8368968 baseEnd_8368968 := by
    simpa [prefixWord, tailWord_8368968, baseEnd_8368968] using wordTrace_append hprefix tailTrace_8368968
  have hstable : (prefixWord ++ tailWord_8368968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368968).length < 2 ^ (prefixWord ++ tailWord_8368968).sum := by decide
  have hdescent : baseEnd_8368968 < baseStart_8368968 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8368997 : List Nat := [1, 3, 1, 3, 1, 1, 2, 11]
def baseStart_8368997 : Nat := 118140960795 + 8368997 * 2 ^ 59
def prefixEnd_8368997 : Nat := 4983230072969 + 3 ^ 40 * 8368997 * 2
def baseEnd_8368997 : Nat := 159159928038366592387007

theorem tailTrace_8368997 : CollatzResearch.WordTrace tailWord_8368997 prefixEnd_8368997 159159928038366592387007 := by
  unfold tailWord_8368997
  simp only [CollatzResearch.WordTrace]
  refine ⟨305242397261560654739457245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203494931507707103159638163 305242397261560654739457245)
  ·
    refine ⟨114465898973085245527296467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305242397261560654739457245 114465898973085245527296467)
    ·
      refine ⟨171698848459627868290944701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114465898973085245527296467 171698848459627868290944701)
      ·
        refine ⟨64387068172360450609104263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171698848459627868290944701 64387068172360450609104263)
        ·
          refine ⟨96580602258540675913656395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64387068172360450609104263 96580602258540675913656395)
          ·
            refine ⟨144870903387811013870484593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96580602258540675913656395 144870903387811013870484593)
            ·
              refine ⟨108653177540858260402863445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144870903387811013870484593 108653177540858260402863445)
              ·
                refine ⟨159159928038366592387007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 108653177540858260402863445 159159928038366592387007)
                ·
                  rfl

theorem cell23_8368997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 11].length) (baseStart_8368997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8368997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8368997 prefixEnd_8368997 := by exact prefixLift 8368997
  have htrace : WordTrace (prefixWord ++ tailWord_8368997) baseStart_8368997 baseEnd_8368997 := by
    simpa [prefixWord, tailWord_8368997, baseEnd_8368997] using wordTrace_append hprefix tailTrace_8368997
  have hstable : (prefixWord ++ tailWord_8368997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8368997).length < 2 ^ (prefixWord ++ tailWord_8368997).sum := by decide
  have hdescent : baseEnd_8368997 < baseStart_8368997 := by decide
  rcases family_descends (prefixWord ++ tailWord_8368997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369004 : List Nat := [2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 4]
def baseStart_8369004 : Nat := 118140960795 + 8369004 * 2 ^ 59
def prefixEnd_8369004 : Nat := 4983230072969 + 3 ^ 40 * 8369004 * 2
def baseEnd_8369004 : Nat := 4297321651400479467061657

theorem tailTrace_8369004 : CollatzResearch.WordTrace tailWord_8369004 prefixEnd_8369004 4297321651400479467061657 := by
  unfold tailWord_8369004
  simp only [CollatzResearch.WordTrace]
  refine ⟨152621326286267647467481033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203495101715023529956641377 152621326286267647467481033)
  ·
    refine ⟨114465994714700735600610775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152621326286267647467481033 114465994714700735600610775)
    ·
      refine ⟨171698992072051103400916163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114465994714700735600610775 171698992072051103400916163)
      ·
        refine ⟨257548488108076655101374245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171698992072051103400916163 257548488108076655101374245)
        ·
          refine ⟨48290341520264372831507671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 257548488108076655101374245 48290341520264372831507671)
          ·
            refine ⟨72435512280396559247261507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48290341520264372831507671 72435512280396559247261507)
            ·
              refine ⟨108653268420594838870892261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72435512280396559247261507 108653268420594838870892261)
              ·
                refine ⟨20372487828861532288292299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108653268420594838870892261 20372487828861532288292299)
                ·
                  refine ⟨30558731743292298432438449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20372487828861532288292299 30558731743292298432438449)
                  ·
                    refine ⟨22919048807469223824328837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30558731743292298432438449 22919048807469223824328837)
                    ·
                      refine ⟨4297321651400479467061657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22919048807469223824328837 4297321651400479467061657)
                      ·
                        rfl

theorem cell23_8369004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 4].length) (baseStart_8369004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369004 prefixEnd_8369004 := by exact prefixLift 8369004
  have htrace : WordTrace (prefixWord ++ tailWord_8369004) baseStart_8369004 baseEnd_8369004 := by
    simpa [prefixWord, tailWord_8369004, baseEnd_8369004] using wordTrace_append hprefix tailTrace_8369004
  have hstable : (prefixWord ++ tailWord_8369004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369004).length < 2 ^ (prefixWord ++ tailWord_8369004).sum := by decide
  have hdescent : baseEnd_8369004 < baseStart_8369004 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369058 : List Nat := [3, 3, 1, 2, 2, 1, 1, 2, 4, 1, 3]
def baseStart_8369058 : Nat := 118140960795 + 8369058 * 2 ^ 59
def prefixEnd_8369058 : Nat := 4983230072969 + 3 ^ 40 * 8369058 * 2
def baseEnd_8369058 : Nat := 4297349379355822255786409

theorem tailTrace_8369058 : CollatzResearch.WordTrace tailWord_8369058 prefixEnd_8369058 4297349379355822255786409 := by
  unfold tailWord_8369058
  simp only [CollatzResearch.WordTrace]
  refine ⟨76311155528584915539356957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203496414742893108104951885 76311155528584915539356957)
  ·
    refine ⟨28616683323219343327258859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76311155528584915539356957 28616683323219343327258859)
    ·
      refine ⟨42925024984829014990888289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28616683323219343327258859 42925024984829014990888289)
      ·
        refine ⟨32193768738621761243166217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42925024984829014990888289 32193768738621761243166217)
        ·
          refine ⟨24145326553966320932374663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32193768738621761243166217 24145326553966320932374663)
          ·
            refine ⟨36217989830949481398561995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24145326553966320932374663 36217989830949481398561995)
            ·
              refine ⟨54326984746424222097842993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36217989830949481398561995 54326984746424222097842993)
              ·
                refine ⟨40745238559818166573382245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54326984746424222097842993 40745238559818166573382245)
                ·
                  refine ⟨7639732229965906232509171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40745238559818166573382245 7639732229965906232509171)
                  ·
                    refine ⟨11459598344948859348763757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7639732229965906232509171 11459598344948859348763757)
                    ·
                      refine ⟨4297349379355822255786409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11459598344948859348763757 4297349379355822255786409)
                      ·
                        rfl

theorem cell23_8369058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_8369058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369058 prefixEnd_8369058 := by exact prefixLift 8369058
  have htrace : WordTrace (prefixWord ++ tailWord_8369058) baseStart_8369058 baseEnd_8369058 := by
    simpa [prefixWord, tailWord_8369058, baseEnd_8369058] using wordTrace_append hprefix tailTrace_8369058
  have hstable : (prefixWord ++ tailWord_8369058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369058).length < 2 ^ (prefixWord ++ tailWord_8369058).sum := by decide
  have hdescent : baseEnd_8369058 < baseStart_8369058 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369076 : List Nat := [2, 5, 2, 1, 1, 2, 3, 2, 1, 2, 2]
def baseStart_8369076 : Nat := 118140960795 + 8369076 * 2 ^ 59
def prefixEnd_8369076 : Nat := 4983230072969 + 3 ^ 40 * 8369076 * 2
def baseEnd_8369076 : Nat := 4297358622007603185361327

theorem tailTrace_8369076 : CollatzResearch.WordTrace tailWord_8369076 prefixEnd_8369076 4297358622007603185361327 := by
  unfold tailWord_8369076
  simp only [CollatzResearch.WordTrace]
  refine ⟨152622639314137225615791541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203496852418849634154388721 152622639314137225615791541)
  ·
    refine ⟨14308372435700364901480457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152622639314137225615791541 14308372435700364901480457)
    ·
      refine ⟨10731279326775273676110343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14308372435700364901480457 10731279326775273676110343)
      ·
        refine ⟨16096918990162910514165515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10731279326775273676110343 16096918990162910514165515)
        ·
          refine ⟨24145378485244365771248273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16096918990162910514165515 24145378485244365771248273)
          ·
            refine ⟨18109033863933274328436205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24145378485244365771248273 18109033863933274328436205)
            ·
              refine ⟨6790887698974977873163577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18109033863933274328436205 6790887698974977873163577)
              ·
                refine ⟨5093165774231233404872683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6790887698974977873163577 5093165774231233404872683)
                ·
                  refine ⟨7639748661346850107309025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5093165774231233404872683 7639748661346850107309025)
                  ·
                    refine ⟨5729811496010137580481769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7639748661346850107309025 5729811496010137580481769)
                    ·
                      refine ⟨4297358622007603185361327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5729811496010137580481769 4297358622007603185361327)
                      ·
                        rfl

theorem cell23_8369076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_8369076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369076 prefixEnd_8369076 := by exact prefixLift 8369076
  have htrace : WordTrace (prefixWord ++ tailWord_8369076) baseStart_8369076 baseEnd_8369076 := by
    simpa [prefixWord, tailWord_8369076, baseEnd_8369076] using wordTrace_append hprefix tailTrace_8369076
  have hstable : (prefixWord ++ tailWord_8369076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369076).length < 2 ^ (prefixWord ++ tailWord_8369076).sum := by decide
  have hdescent : baseEnd_8369076 < baseStart_8369076 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369092 : List Nat := [2, 3, 3, 3, 1, 1, 1, 3, 2, 1, 3]
def baseStart_8369092 : Nat := 118140960795 + 8369092 * 2 ^ 59
def prefixEnd_8369092 : Nat := 4983230072969 + 3 ^ 40 * 8369092 * 2
def baseEnd_8369092 : Nat := 4297366837698075122761253

theorem tailTrace_8369092 : CollatzResearch.WordTrace tailWord_8369092 prefixEnd_8369092 4297366837698075122761253 := by
  unfold tailWord_8369092
  simp only [CollatzResearch.WordTrace]
  refine ⟨152622931098108242982082765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203497241464144323976110353 152622931098108242982082765)
  ·
    refine ⟨57233599161790591118281037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152622931098108242982082765 57233599161790591118281037)
    ·
      refine ⟨21462599685671471669355389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57233599161790591118281037 21462599685671471669355389)
      ·
        refine ⟨8048474882126801876008271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21462599685671471669355389 8048474882126801876008271)
        ·
          refine ⟨12072712323190202814012407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8048474882126801876008271 12072712323190202814012407)
          ·
            refine ⟨18109068484785304221018611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12072712323190202814012407 18109068484785304221018611)
            ·
              refine ⟨27163602727177956331527917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18109068484785304221018611 27163602727177956331527917)
              ·
                refine ⟨10186351022691733624322969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27163602727177956331527917 10186351022691733624322969)
                ·
                  refine ⟨7639763267018800218242227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10186351022691733624322969 7639763267018800218242227)
                  ·
                    refine ⟨11459644900528200327363341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7639763267018800218242227 11459644900528200327363341)
                    ·
                      refine ⟨4297366837698075122761253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11459644900528200327363341 4297366837698075122761253)
                      ·
                        rfl

theorem cell23_8369092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_8369092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369092 prefixEnd_8369092 := by exact prefixLift 8369092
  have htrace : WordTrace (prefixWord ++ tailWord_8369092) baseStart_8369092 baseEnd_8369092 := by
    simpa [prefixWord, tailWord_8369092, baseEnd_8369092] using wordTrace_append hprefix tailTrace_8369092
  have hstable : (prefixWord ++ tailWord_8369092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369092).length < 2 ^ (prefixWord ++ tailWord_8369092).sum := by decide
  have hdescent : baseEnd_8369092 < baseStart_8369092 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369121 : List Nat := [1, 2, 3, 1, 2, 1, 1, 7, 5]
def baseStart_8369121 : Nat := 118140960795 + 8369121 * 2 ^ 59
def prefixEnd_8369121 : Nat := 4983230072969 + 3 ^ 40 * 8369121 * 2
def baseEnd_8369121 : Nat := 477486858737450612144291

theorem tailTrace_8369121 : CollatzResearch.WordTrace tailWord_8369121 prefixEnd_8369121 477486858737450612144291 := by
  unfold tailWord_8369121
  simp only [CollatzResearch.WordTrace]
  refine ⟨305246919913111423916971217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203497946608740949277980811 305246919913111423916971217)
  ·
    refine ⟨228935189934833567937728413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305246919913111423916971217 228935189934833567937728413)
    ·
      refine ⟨85850696225562587976648155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228935189934833567937728413 85850696225562587976648155)
      ·
        refine ⟨128776044338343881964972233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85850696225562587976648155 128776044338343881964972233)
        ·
          refine ⟨96582033253757911473729175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128776044338343881964972233 96582033253757911473729175)
          ·
            refine ⟨144873049880636867210593763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96582033253757911473729175 144873049880636867210593763)
            ·
              refine ⟨217309574820955300815890645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144873049880636867210593763 217309574820955300815890645)
              ·
                refine ⟨5093193159866139862872437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 217309574820955300815890645 5093193159866139862872437)
                ·
                  refine ⟨477486858737450612144291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5093193159866139862872437 477486858737450612144291)
                  ·
                    rfl

theorem cell23_8369121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 7, 5].length) (baseStart_8369121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369121 prefixEnd_8369121 := by exact prefixLift 8369121
  have htrace : WordTrace (prefixWord ++ tailWord_8369121) baseStart_8369121 baseEnd_8369121 := by
    simpa [prefixWord, tailWord_8369121, baseEnd_8369121] using wordTrace_append hprefix tailTrace_8369121
  have hstable : (prefixWord ++ tailWord_8369121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369121).length < 2 ^ (prefixWord ++ tailWord_8369121).sum := by decide
  have hdescent : baseEnd_8369121 < baseStart_8369121 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369171 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 3, 6, 2]
def baseStart_8369171 : Nat := 118140960795 + 8369171 * 2 ^ 59
def prefixEnd_8369171 : Nat := 4983230072969 + 3 ^ 40 * 8369171 * 2
def baseEnd_8369171 : Nat := 4297407402669780313673389

theorem tailTrace_8369171 : CollatzResearch.WordTrace tailWord_8369171 prefixEnd_8369171 4297407402669780313673389 := by
  unfold tailWord_8369171
  simp only [CollatzResearch.WordTrace]
  refine ⟨305248743562930282456291367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203499162375286854970860911 305248743562930282456291367)
  ·
    refine ⟨457873115344395423684437051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305248743562930282456291367 457873115344395423684437051)
    ·
      refine ⟨686809673016593135526655577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457873115344395423684437051 686809673016593135526655577)
      ·
        refine ⟨515107254762444851644991683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 686809673016593135526655577 515107254762444851644991683)
        ·
          refine ⟨772660882143667277467487525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515107254762444851644991683 772660882143667277467487525)
          ·
            refine ⟨144873915401937614525153911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 772660882143667277467487525 144873915401937614525153911)
            ·
              refine ⟨217310873102906421787730867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144873915401937614525153911 217310873102906421787730867)
              ·
                refine ⟨325966309654359632681596301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217310873102906421787730867 325966309654359632681596301)
                ·
                  refine ⟨122237366120384862255598613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 325966309654359632681596301 122237366120384862255598613)
                  ·
                    refine ⟨5729876536893040418231185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 122237366120384862255598613 5729876536893040418231185)
                    ·
                      refine ⟨4297407402669780313673389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5729876536893040418231185 4297407402669780313673389)
                      ·
                        rfl

theorem cell23_8369171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 6, 2].length) (baseStart_8369171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369171 prefixEnd_8369171 := by exact prefixLift 8369171
  have htrace : WordTrace (prefixWord ++ tailWord_8369171) baseStart_8369171 baseEnd_8369171 := by
    simpa [prefixWord, tailWord_8369171, baseEnd_8369171] using wordTrace_append hprefix tailTrace_8369171
  have hstable : (prefixWord ++ tailWord_8369171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369171).length < 2 ^ (prefixWord ++ tailWord_8369171).sum := by decide
  have hdescent : baseEnd_8369171 < baseStart_8369171 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369255 : List Nat := [1, 1, 5, 1, 1, 3, 3, 1, 3, 1, 3]
def baseStart_8369255 : Nat := 118140960795 + 8369255 * 2 ^ 59
def prefixEnd_8369255 : Nat := 4983230072969 + 3 ^ 40 * 8369255 * 2
def baseEnd_8369255 : Nat := 4297450535044757985023003

theorem tailTrace_8369255 : CollatzResearch.WordTrace tailWord_8369255 prefixEnd_8369255 4297450535044757985023003 := by
  unfold tailWord_8369255
  simp only [CollatzResearch.WordTrace]
  refine ⟨305251807294625964802349219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203501204863083976534899479 305251807294625964802349219)
  ·
    refine ⟨457877710941938947203523829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305251807294625964802349219 457877710941938947203523829)
    ·
      refine ⟨42926035400806776300330359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 457877710941938947203523829 42926035400806776300330359)
      ·
        refine ⟨64389053101210164450495539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42926035400806776300330359 64389053101210164450495539)
        ·
          refine ⟨96583579651815246675743309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64389053101210164450495539 96583579651815246675743309)
          ·
            refine ⟨36218842369430717503403741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96583579651815246675743309 36218842369430717503403741)
            ·
              refine ⟨13582065888536519063776403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36218842369430717503403741 13582065888536519063776403)
              ·
                refine ⟨20373098832804778595664605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13582065888536519063776403 20373098832804778595664605)
                ·
                  refine ⟨7639912062301791973374227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20373098832804778595664605 7639912062301791973374227)
                  ·
                    refine ⟨11459868093452687960061341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7639912062301791973374227 11459868093452687960061341)
                    ·
                      refine ⟨4297450535044757985023003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11459868093452687960061341 4297450535044757985023003)
                      ·
                        rfl

theorem cell23_8369255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_8369255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369255 prefixEnd_8369255 := by exact prefixLift 8369255
  have htrace : WordTrace (prefixWord ++ tailWord_8369255) baseStart_8369255 baseEnd_8369255 := by
    simpa [prefixWord, tailWord_8369255, baseEnd_8369255] using wordTrace_append hprefix tailTrace_8369255
  have hstable : (prefixWord ++ tailWord_8369255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369255).length < 2 ^ (prefixWord ++ tailWord_8369255).sum := by decide
  have hdescent : baseEnd_8369255 < baseStart_8369255 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369271 : List Nat := [1, 1, 3, 1, 1, 4, 2, 3, 1, 6]
def baseStart_8369271 : Nat := 118140960795 + 8369271 * 2 ^ 59
def prefixEnd_8369271 : Nat := 4983230072969 + 3 ^ 40 * 8369271 * 2
def baseEnd_8369271 : Nat := 1432486250245076640807643

theorem tailTrace_8369271 : CollatzResearch.WordTrace tailWord_8369271 prefixEnd_8369271 1432486250245076640807643 := by
  unfold tailWord_8369271
  simp only [CollatzResearch.WordTrace]
  refine ⟨305252390862567999534931667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203501593908378666356621111 305252390862567999534931667)
  ·
    refine ⟨457878586293851999302397501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305252390862567999534931667 457878586293851999302397501)
    ·
      refine ⟨171704469860194499738399063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 457878586293851999302397501 171704469860194499738399063)
      ·
        refine ⟨257556704790291749607598595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171704469860194499738399063 257556704790291749607598595)
        ·
          refine ⟨386335057185437624411397893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257556704790291749607598595 386335057185437624411397893)
          ·
            refine ⟨72437823222269554577137105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 386335057185437624411397893 72437823222269554577137105)
            ·
              refine ⟨54328367416702165932852829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72437823222269554577137105 54328367416702165932852829)
              ·
                refine ⟨20373137781263312224819811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54328367416702165932852829 20373137781263312224819811)
                ·
                  refine ⟨30559706671894968337229717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20373137781263312224819811 30559706671894968337229717)
                  ·
                    refine ⟨1432486250245076640807643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30559706671894968337229717 1432486250245076640807643)
                    ·
                      rfl

theorem cell23_8369271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 6].length) (baseStart_8369271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369271 prefixEnd_8369271 := by exact prefixLift 8369271
  have htrace : WordTrace (prefixWord ++ tailWord_8369271) baseStart_8369271 baseEnd_8369271 := by
    simpa [prefixWord, tailWord_8369271, baseEnd_8369271] using wordTrace_append hprefix tailTrace_8369271
  have hstable : (prefixWord ++ tailWord_8369271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369271).length < 2 ^ (prefixWord ++ tailWord_8369271).sum := by decide
  have hdescent : baseEnd_8369271 < baseStart_8369271 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369306 : List Nat := [3, 1, 1, 5, 1, 3, 2, 2, 1, 1, 3]
def baseStart_8369306 : Nat := 118140960795 + 8369306 * 2 ^ 59
def prefixEnd_8369306 : Nat := 4983230072969 + 3 ^ 40 * 8369306 * 2
def baseEnd_8369306 : Nat := 4297476722558137285485269

theorem tailTrace_8369306 : CollatzResearch.WordTrace tailWord_8369306 prefixEnd_8369306 4297476722558137285485269 := by
  unfold tailWord_8369306
  simp only [CollatzResearch.WordTrace]
  refine ⟨76313416854360300128113943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203502444944960800341637181 76313416854360300128113943)
  ·
    refine ⟨114470125281540450192170915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76313416854360300128113943 114470125281540450192170915)
    ·
      refine ⟨171705187922310675288256373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114470125281540450192170915 171705187922310675288256373)
      ·
        refine ⟨16097361367716625808274035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 171705187922310675288256373 16097361367716625808274035)
        ·
          refine ⟨24146042051574938712411053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16097361367716625808274035 24146042051574938712411053)
          ·
            refine ⟨9054765769340602017154145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24146042051574938712411053 9054765769340602017154145)
            ·
              refine ⟨6791074327005451512865609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9054765769340602017154145 6791074327005451512865609)
              ·
                refine ⟨5093305745254088634649207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6791074327005451512865609 5093305745254088634649207)
                ·
                  refine ⟨7639958617881132951973811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5093305745254088634649207 7639958617881132951973811)
                  ·
                    refine ⟨11459937926821699427960717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7639958617881132951973811 11459937926821699427960717)
                    ·
                      refine ⟨4297476722558137285485269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11459937926821699427960717 4297476722558137285485269)
                      ·
                        rfl

theorem cell23_8369306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_8369306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369306 prefixEnd_8369306 := by exact prefixLift 8369306
  have htrace : WordTrace (prefixWord ++ tailWord_8369306) baseStart_8369306 baseEnd_8369306 := by
    simpa [prefixWord, tailWord_8369306, baseEnd_8369306] using wordTrace_append hprefix tailTrace_8369306
  have hstable : (prefixWord ++ tailWord_8369306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369306).length < 2 ^ (prefixWord ++ tailWord_8369306).sum := by decide
  have hdescent : baseEnd_8369306 < baseStart_8369306 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369322 : List Nat := [3, 1, 5, 1, 1, 1, 2, 3, 2, 4]
def baseStart_8369322 : Nat := 118140960795 + 8369322 * 2 ^ 59
def prefixEnd_8369322 : Nat := 4983230072969 + 3 ^ 40 * 8369322 * 2
def baseEnd_8369322 : Nat := 1432494979416203074295065

theorem tailTrace_8369322 : CollatzResearch.WordTrace tailWord_8369322 prefixEnd_8369322 1432494979416203074295065 := by
  unfold tailWord_8369322
  simp only [CollatzResearch.WordTrace]
  refine ⟨76313562746345808811259555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203502833990255490163358813 76313562746345808811259555)
  ·
    refine ⟨114470344119518713216889333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76313562746345808811259555 114470344119518713216889333)
    ·
      refine ⟨10731594761204879364083375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114470344119518713216889333 10731594761204879364083375)
      ·
        refine ⟨16097392141807319046125063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10731594761204879364083375 16097392141807319046125063)
        ·
          refine ⟨24146088212710978569187595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16097392141807319046125063 24146088212710978569187595)
          ·
            refine ⟨36219132319066467853781393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24146088212710978569187595 36219132319066467853781393)
            ·
              refine ⟨27164349239299850890336045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36219132319066467853781393 27164349239299850890336045)
              ·
                refine ⟨10186630964737444083876017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27164349239299850890336045 10186630964737444083876017)
                ·
                  refine ⟨7639973223553083062907013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10186630964737444083876017 7639973223553083062907013)
                  ·
                    refine ⟨1432494979416203074295065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7639973223553083062907013 1432494979416203074295065)
                    ·
                      rfl

theorem cell23_8369322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_8369322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369322 prefixEnd_8369322 := by exact prefixLift 8369322
  have htrace : WordTrace (prefixWord ++ tailWord_8369322) baseStart_8369322 baseEnd_8369322 := by
    simpa [prefixWord, tailWord_8369322, baseEnd_8369322] using wordTrace_append hprefix tailTrace_8369322
  have hstable : (prefixWord ++ tailWord_8369322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369322).length < 2 ^ (prefixWord ++ tailWord_8369322).sum := by decide
  have hdescent : baseEnd_8369322 < baseStart_8369322 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369385 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 8, 2, 2]
def baseStart_8369385 : Nat := 118140960795 + 8369385 * 2 ^ 59
def prefixEnd_8369385 : Nat := 4983230072969 + 3 ^ 40 * 8369385 * 2
def baseEnd_8369385 : Nat := 4297517287529842476397405

theorem tailTrace_8369385 : CollatzResearch.WordTrace tailWord_8369385 prefixEnd_8369385 4297517287529842476397405 := by
  unfold tailWord_8369385
  simp only [CollatzResearch.WordTrace]
  refine ⟨305256548784154997004581609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203504365856103331336387739 305256548784154997004581609)
  ·
    refine ⟨228942411588116247753436207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305256548784154997004581609 228942411588116247753436207)
    ·
      refine ⟨343413617382174371630154311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228942411588116247753436207 343413617382174371630154311)
      ·
        refine ⟨515120426073261557445231467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343413617382174371630154311 515120426073261557445231467)
        ·
          refine ⟨772680639109892336167847201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515120426073261557445231467 772680639109892336167847201)
          ·
            refine ⟨579510479332419252125885401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 772680639109892336167847201 579510479332419252125885401)
            ·
              refine ⟨434632859499314439094414051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 579510479332419252125885401 434632859499314439094414051)
              ·
                refine ⟨651949289248971658641621077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434632859499314439094414051 651949289248971658641621077)
                ·
                  refine ⟨7640030733386386624706497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 651949289248971658641621077 7640030733386386624706497)
                  ·
                    refine ⟨5730023050039789968529873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7640030733386386624706497 5730023050039789968529873)
                    ·
                      refine ⟨4297517287529842476397405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5730023050039789968529873 4297517287529842476397405)
                      ·
                        rfl

theorem cell23_8369385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 8, 2, 2].length) (baseStart_8369385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369385 prefixEnd_8369385 := by exact prefixLift 8369385
  have htrace : WordTrace (prefixWord ++ tailWord_8369385) baseStart_8369385 baseEnd_8369385 := by
    simpa [prefixWord, tailWord_8369385, baseEnd_8369385] using wordTrace_append hprefix tailTrace_8369385
  have hstable : (prefixWord ++ tailWord_8369385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369385).length < 2 ^ (prefixWord ++ tailWord_8369385).sum := by decide
  have hdescent : baseEnd_8369385 < baseStart_8369385 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369389 : List Nat := [1, 5, 1, 2, 2, 2, 2, 2, 1, 3, 2]
def baseStart_8369389 : Nat := 118140960795 + 8369389 * 2 ^ 59
def prefixEnd_8369389 : Nat := 4983230072969 + 3 ^ 40 * 8369389 * 2
def baseEnd_8369389 : Nat := 4297519341452460460747387

theorem tailTrace_8369389 : CollatzResearch.WordTrace tailWord_8369389 prefixEnd_8369389 4297519341452460460747387 := by
  unfold tailWord_8369389
  simp only [CollatzResearch.WordTrace]
  refine ⟨305256694676140505687727221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203504463117427003791818147 305256694676140505687727221)
  ·
    refine ⟨28617815125888172408224427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 305256694676140505687727221 28617815125888172408224427)
    ·
      refine ⟨42926722688832258612336641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28617815125888172408224427 42926722688832258612336641)
      ·
        refine ⟨32195042016624193959252481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42926722688832258612336641 32195042016624193959252481)
        ·
          refine ⟨24146281512468145469439361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32195042016624193959252481 24146281512468145469439361)
          ·
            refine ⟨18109711134351109102079521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24146281512468145469439361 18109711134351109102079521)
            ·
              refine ⟨13582283350763331826559641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18109711134351109102079521 13582283350763331826559641)
              ·
                refine ⟨10186712513072498869919731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13582283350763331826559641 10186712513072498869919731)
                ·
                  refine ⟨15280068769608748304879597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10186712513072498869919731 15280068769608748304879597)
                  ·
                    refine ⟨5730025788603280614329849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15280068769608748304879597 5730025788603280614329849)
                    ·
                      refine ⟨4297519341452460460747387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5730025788603280614329849 4297519341452460460747387)
                      ·
                        rfl

theorem cell23_8369389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_8369389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369389 prefixEnd_8369389 := by exact prefixLift 8369389
  have htrace : WordTrace (prefixWord ++ tailWord_8369389) baseStart_8369389 baseEnd_8369389 := by
    simpa [prefixWord, tailWord_8369389, baseEnd_8369389] using wordTrace_append hprefix tailTrace_8369389
  have hstable : (prefixWord ++ tailWord_8369389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369389).length < 2 ^ (prefixWord ++ tailWord_8369389).sum := by decide
  have hdescent : baseEnd_8369389 < baseStart_8369389 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369475 : List Nat := [1, 1, 1, 3, 1, 3, 1, 4, 2, 4, 2]
def baseStart_8369475 : Nat := 118140960795 + 8369475 * 2 ^ 59
def prefixEnd_8369475 : Nat := 4983230072969 + 3 ^ 40 * 8369475 * 2
def baseEnd_8369475 : Nat := 4297563500788747124271991

theorem tailTrace_8369475 : CollatzResearch.WordTrace tailWord_8369475 prefixEnd_8369475 4297563500788747124271991 := by
  unfold tailWord_8369475
  simp only [CollatzResearch.WordTrace]
  refine ⟨305259831353828942375357879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203506554235885961583571919 305259831353828942375357879)
  ·
    refine ⟨457889747030743413563036819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305259831353828942375357879 457889747030743413563036819)
    ·
      refine ⟨686834620546115120344555229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457889747030743413563036819 686834620546115120344555229)
      ·
        refine ⟨257562982704793170129208211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 686834620546115120344555229 257562982704793170129208211)
        ·
          refine ⟨386344474057189755193812317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257562982704793170129208211 386344474057189755193812317)
          ·
            refine ⟨144879177771446158197679619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 386344474057189755193812317 144879177771446158197679619)
            ·
              refine ⟨217318766657169237296519429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144879177771446158197679619 217318766657169237296519429)
              ·
                refine ⟨40747268748219231993097393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 217318766657169237296519429 40747268748219231993097393)
                ·
                  refine ⟨30560451561164423994823045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40747268748219231993097393 30560451561164423994823045)
                  ·
                    refine ⟨5730084667718329499029321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30560451561164423994823045 5730084667718329499029321)
                    ·
                      refine ⟨4297563500788747124271991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5730084667718329499029321 4297563500788747124271991)
                      ·
                        rfl

theorem cell23_8369475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 4, 2].length) (baseStart_8369475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369475 prefixEnd_8369475 := by exact prefixLift 8369475
  have htrace : WordTrace (prefixWord ++ tailWord_8369475) baseStart_8369475 baseEnd_8369475 := by
    simpa [prefixWord, tailWord_8369475, baseEnd_8369475] using wordTrace_append hprefix tailTrace_8369475
  have hstable : (prefixWord ++ tailWord_8369475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369475).length < 2 ^ (prefixWord ++ tailWord_8369475).sum := by decide
  have hdescent : baseEnd_8369475 < baseStart_8369475 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369476 : List Nat := [2, 3, 4, 1, 1, 3, 2, 2, 5]
def baseStart_8369476 : Nat := 118140960795 + 8369476 * 2 ^ 59
def prefixEnd_8369476 : Nat := 4983230072969 + 3 ^ 40 * 8369476 * 2
def baseEnd_8369476 : Nat := 477507112696600180039943

theorem tailTrace_8369476 : CollatzResearch.WordTrace tailWord_8369476 prefixEnd_8369476 477507112696600180039943 := by
  unfold tailWord_8369476
  simp only [CollatzResearch.WordTrace]
  refine ⟨152629933913412659773072141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203506578551216879697429521 152629933913412659773072141)
  ·
    refine ⟨57236225217529747414902053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152629933913412659773072141 57236225217529747414902053)
    ·
      refine ⟨10731792228286827640294135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57236225217529747414902053 10731792228286827640294135)
      ·
        refine ⟨16097688342430241460441203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10731792228286827640294135 16097688342430241460441203)
        ·
          refine ⟨24146532513645362190661805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16097688342430241460441203 24146532513645362190661805)
          ·
            refine ⟨9054949692617010821498177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24146532513645362190661805 9054949692617010821498177)
            ·
              refine ⟨6791212269462758116123633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9054949692617010821498177 6791212269462758116123633)
              ·
                refine ⟨5093409202097068587092725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6791212269462758116123633 5093409202097068587092725)
                ·
                  refine ⟨477507112696600180039943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5093409202097068587092725 477507112696600180039943)
                  ·
                    rfl

theorem cell23_8369476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 2, 5].length) (baseStart_8369476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369476 prefixEnd_8369476 := by exact prefixLift 8369476
  have htrace : WordTrace (prefixWord ++ tailWord_8369476) baseStart_8369476 baseEnd_8369476 := by
    simpa [prefixWord, tailWord_8369476, baseEnd_8369476] using wordTrace_append hprefix tailTrace_8369476
  have hstable : (prefixWord ++ tailWord_8369476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369476).length < 2 ^ (prefixWord ++ tailWord_8369476).sum := by decide
  have hdescent : baseEnd_8369476 < baseStart_8369476 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369492 : List Nat := [2, 4, 1, 1, 2, 1, 3, 1, 2, 4, 2]
def baseStart_8369492 : Nat := 118140960795 + 8369492 * 2 ^ 59
def prefixEnd_8369492 : Nat := 4983230072969 + 3 ^ 40 * 8369492 * 2
def baseEnd_8369492 : Nat := 4297572229959873557759413

theorem tailTrace_8369492 : CollatzResearch.WordTrace tailWord_8369492 prefixEnd_8369492 4297572229959873557759413 := by
  unfold tailWord_8369492
  simp only [CollatzResearch.WordTrace]
  refine ⟨152630225697383677139363365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203506967596511569519151153 152630225697383677139363365)
  ·
    refine ⟨28618167318259439463630631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152630225697383677139363365 28618167318259439463630631)
    ·
      refine ⟨42927250977389159195445947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28618167318259439463630631 42927250977389159195445947)
      ·
        refine ⟨64390876466083738793168921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42927250977389159195445947 64390876466083738793168921)
        ·
          refine ⟨48293157349562804094876691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64390876466083738793168921 48293157349562804094876691)
          ·
            refine ⟨72439736024344206142315037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48293157349562804094876691 72439736024344206142315037)
            ·
              refine ⟨27164901009129077303368139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72439736024344206142315037 27164901009129077303368139)
              ·
                refine ⟨40747351513693615955052209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27164901009129077303368139 40747351513693615955052209)
                ·
                  refine ⟨30560513635270211966289157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40747351513693615955052209 30560513635270211966289157)
                  ·
                    refine ⟨5730096306613164743679217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30560513635270211966289157 5730096306613164743679217)
                    ·
                      refine ⟨4297572229959873557759413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5730096306613164743679217 4297572229959873557759413)
                      ·
                        rfl

theorem cell23_8369492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_8369492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369492 prefixEnd_8369492 := by exact prefixLift 8369492
  have htrace : WordTrace (prefixWord ++ tailWord_8369492) baseStart_8369492 baseEnd_8369492 := by
    simpa [prefixWord, tailWord_8369492, baseEnd_8369492] using wordTrace_append hprefix tailTrace_8369492
  have hstable : (prefixWord ++ tailWord_8369492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369492).length < 2 ^ (prefixWord ++ tailWord_8369492).sum := by decide
  have hdescent : baseEnd_8369492 < baseStart_8369492 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369512 : List Nat := [2, 1, 4, 2, 3, 1, 1, 1, 1, 4, 3]
def baseStart_8369512 : Nat := 118140960795 + 8369512 * 2 ^ 59
def prefixEnd_8369512 : Nat := 4983230072969 + 3 ^ 40 * 8369512 * 2
def baseEnd_8369512 : Nat := 4297582499572963479509321

theorem tailTrace_8369512 : CollatzResearch.WordTrace tailWord_8369512 prefixEnd_8369512 4297582499572963479509321 := by
  unfold tailWord_8369512
  simp only [CollatzResearch.WordTrace]
  refine ⟨152630590427347448847227395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203507453903129931796303193 152630590427347448847227395)
  ·
    refine ⟨228945885641021173270841093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152630590427347448847227395 228945885641021173270841093)
    ·
      refine ⟨42927353557691469988282705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228945885641021173270841093 42927353557691469988282705)
      ·
        refine ⟨32195515168268602491212029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42927353557691469988282705 32195515168268602491212029)
        ·
          refine ⟨12073318188100725934204511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32195515168268602491212029 12073318188100725934204511)
          ·
            refine ⟨18109977282151088901306767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12073318188100725934204511 18109977282151088901306767)
            ·
              refine ⟨27164965923226633351960151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18109977282151088901306767 27164965923226633351960151)
              ·
                refine ⟨40747448884839950027940227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27164965923226633351960151 40747448884839950027940227)
                ·
                  refine ⟨61121173327259925041910341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40747448884839950027940227 61121173327259925041910341)
                  ·
                    refine ⟨11460219998861235945358189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61121173327259925041910341 11460219998861235945358189)
                    ·
                      refine ⟨4297582499572963479509321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11460219998861235945358189 4297582499572963479509321)
                      ·
                        rfl

theorem cell23_8369512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_8369512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369512 prefixEnd_8369512 := by exact prefixLift 8369512
  have htrace : WordTrace (prefixWord ++ tailWord_8369512) baseStart_8369512 baseEnd_8369512 := by
    simpa [prefixWord, tailWord_8369512, baseEnd_8369512] using wordTrace_append hprefix tailTrace_8369512
  have hstable : (prefixWord ++ tailWord_8369512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369512).length < 2 ^ (prefixWord ++ tailWord_8369512).sum := by decide
  have hdescent : baseEnd_8369512 < baseStart_8369512 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369535 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 5, 5, 2]
def baseStart_8369535 : Nat := 118140960795 + 8369535 * 2 ^ 59
def prefixEnd_8369535 : Nat := 4983230072969 + 3 ^ 40 * 8369535 * 2
def baseEnd_8369535 : Nat := 4297594309628016889521715

theorem tailTrace_8369535 : CollatzResearch.WordTrace tailWord_8369535 prefixEnd_8369535 4297594309628016889521715 := by
  unfold tailWord_8369535
  simp only [CollatzResearch.WordTrace]
  refine ⟨305262019733611572622542059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203508013155741048415028039 305262019733611572622542059)
  ·
    refine ⟨457893029600417358933813089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305262019733611572622542059 457893029600417358933813089)
    ·
      refine ⟨343419772200313019200359817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457893029600417358933813089 343419772200313019200359817)
      ·
        refine ⟨257564829150234764400269863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343419772200313019200359817 257564829150234764400269863)
        ·
          refine ⟨386347243725352146600404795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257564829150234764400269863 386347243725352146600404795)
          ·
            refine ⟨579520865588028219900607193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386347243725352146600404795 579520865588028219900607193)
            ·
              refine ⟨434640649191021164925455395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 579520865588028219900607193 434640649191021164925455395)
              ·
                refine ⟨651960973786531747388183093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434640649191021164925455395 651960973786531747388183093)
                ·
                  refine ⟨61121341292487351317642165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 651960973786531747388183093 61121341292487351317642165)
                  ·
                    refine ⟨5730125746170689186028953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61121341292487351317642165 5730125746170689186028953)
                    ·
                      refine ⟨4297594309628016889521715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5730125746170689186028953 4297594309628016889521715)
                      ·
                        rfl

theorem cell23_8369535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 5, 2].length) (baseStart_8369535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369535 prefixEnd_8369535 := by exact prefixLift 8369535
  have htrace : WordTrace (prefixWord ++ tailWord_8369535) baseStart_8369535 baseEnd_8369535 := by
    simpa [prefixWord, tailWord_8369535, baseEnd_8369535] using wordTrace_append hprefix tailTrace_8369535
  have hstable : (prefixWord ++ tailWord_8369535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369535).length < 2 ^ (prefixWord ++ tailWord_8369535).sum := by decide
  have hdescent : baseEnd_8369535 < baseStart_8369535 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369562 : List Nat := [3, 1, 1, 4, 1, 1, 4, 2, 1, 5]
def baseStart_8369562 : Nat := 118140960795 + 8369562 * 2 ^ 59
def prefixEnd_8369562 : Nat := 4983230072969 + 3 ^ 40 * 8369562 * 2
def baseEnd_8369562 : Nat := 1432536057868562761294697

theorem tailTrace_8369562 : CollatzResearch.WordTrace tailWord_8369562 prefixEnd_8369562 1432536057868562761294697 := by
  unfold tailWord_8369562
  simp only [CollatzResearch.WordTrace]
  refine ⟨76315751126128439058443735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203508669669675837489183293 76315751126128439058443735)
  ·
    refine ⟨114473626689192658587665603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76315751126128439058443735 114473626689192658587665603)
    ·
      refine ⟨171710440033788987881498405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114473626689192658587665603 171710440033788987881498405)
      ·
        refine ⟨32195707506335435227780951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171710440033788987881498405 32195707506335435227780951)
        ·
          refine ⟨48293561259503152841671427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32195707506335435227780951 48293561259503152841671427)
          ·
            refine ⟨72440341889254729262507141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48293561259503152841671427 72440341889254729262507141)
            ·
              refine ⟨13582564104235261736720089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72440341889254729262507141 13582564104235261736720089)
              ·
                refine ⟨10186923078176446302540067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13582564104235261736720089 10186923078176446302540067)
                ·
                  refine ⟨15280384617264669453810101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10186923078176446302540067 15280384617264669453810101)
                  ·
                    refine ⟨1432536057868562761294697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15280384617264669453810101 1432536057868562761294697)
                    ·
                      rfl

theorem cell23_8369562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 1, 5].length) (baseStart_8369562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369562 prefixEnd_8369562 := by exact prefixLift 8369562
  have htrace : WordTrace (prefixWord ++ tailWord_8369562) baseStart_8369562 baseEnd_8369562 := by
    simpa [prefixWord, tailWord_8369562, baseEnd_8369562] using wordTrace_append hprefix tailTrace_8369562
  have hstable : (prefixWord ++ tailWord_8369562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369562).length < 2 ^ (prefixWord ++ tailWord_8369562).sum := by decide
  have hdescent : baseEnd_8369562 < baseStart_8369562 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369575 : List Nat := [1, 1, 6, 1, 1, 1, 2, 1, 3, 6]
def baseStart_8369575 : Nat := 118140960795 + 8369575 * 2 ^ 59
def prefixEnd_8369575 : Nat := 4983230072969 + 3 ^ 40 * 8369575 * 2
def baseEnd_8369575 : Nat := 1432538282951398911007177

theorem tailTrace_8369575 : CollatzResearch.WordTrace tailWord_8369575 prefixEnd_8369575 1432538282951398911007177 := by
  unfold tailWord_8369575
  simp only [CollatzResearch.WordTrace]
  refine ⟨305263478653466659453998179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203508985768977772969332119 305263478653466659453998179)
  ·
    refine ⟨457895217980199989180997269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305263478653466659453998179 457895217980199989180997269)
    ·
      refine ⟨21463838342821874492859247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 457895217980199989180997269 21463838342821874492859247)
      ·
        refine ⟨32195757514232811739288871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21463838342821874492859247 32195757514232811739288871)
        ·
          refine ⟨48293636271349217608933307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32195757514232811739288871 48293636271349217608933307)
          ·
            refine ⟨72440454407023826413399961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48293636271349217608933307 72440454407023826413399961)
            ·
              refine ⟨54330340805267869810049971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72440454407023826413399961 54330340805267869810049971)
              ·
                refine ⟨81495511207901804715074957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54330340805267869810049971 81495511207901804715074957)
                ·
                  refine ⟨30560816702963176768153109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81495511207901804715074957 30560816702963176768153109)
                  ·
                    refine ⟨1432538282951398911007177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30560816702963176768153109 1432538282951398911007177)
                    ·
                      rfl

theorem cell23_8369575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_8369575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369575 prefixEnd_8369575 := by exact prefixLift 8369575
  have htrace : WordTrace (prefixWord ++ tailWord_8369575) baseStart_8369575 baseEnd_8369575 := by
    simpa [prefixWord, tailWord_8369575, baseEnd_8369575] using wordTrace_append hprefix tailTrace_8369575
  have hstable : (prefixWord ++ tailWord_8369575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369575).length < 2 ^ (prefixWord ++ tailWord_8369575).sum := by decide
  have hdescent : baseEnd_8369575 < baseStart_8369575 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369593 : List Nat := [1, 2, 1, 4, 4, 1, 3, 2, 1, 1, 3]
def baseStart_8369593 : Nat := 118140960795 + 8369593 * 2 ^ 59
def prefixEnd_8369593 : Nat := 4983230072969 + 3 ^ 40 * 8369593 * 2
def baseEnd_8369593 : Nat := 4297624091505977662596449

theorem tailTrace_8369593 : CollatzResearch.WordTrace tailWord_8369593 prefixEnd_8369593 4297624091505977662596449 := by
  unfold tailWord_8369593
  simp only [CollatzResearch.WordTrace]
  refine ⟨305264135167401448528153433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203509423444934299018768955 305264135167401448528153433)
  ·
    refine ⟨228948101375551086396115075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305264135167401448528153433 228948101375551086396115075)
    ·
      refine ⟨343422152063326629594172613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228948101375551086396115075 343422152063326629594172613)
      ·
        refine ⟨64391653511873743048907365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 343422152063326629594172613 64391653511873743048907365)
        ·
          refine ⟨12073435033476326821670131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64391653511873743048907365 12073435033476326821670131)
          ·
            refine ⟨18110152550214490232505197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12073435033476326821670131 18110152550214490232505197)
            ·
              refine ⟨6791307206330433837189449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18110152550214490232505197 6791307206330433837189449)
              ·
                refine ⟨5093480404747825377892087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6791307206330433837189449 5093480404747825377892087)
                ·
                  refine ⟨7640220607121738066838131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5093480404747825377892087 7640220607121738066838131)
                  ·
                    refine ⟨11460330910682607100257197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7640220607121738066838131 11460330910682607100257197)
                    ·
                      refine ⟨4297624091505977662596449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11460330910682607100257197 4297624091505977662596449)
                      ·
                        rfl

theorem cell23_8369593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 2, 1, 1, 3].length) (baseStart_8369593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369593 prefixEnd_8369593 := by exact prefixLift 8369593
  have htrace : WordTrace (prefixWord ++ tailWord_8369593) baseStart_8369593 baseEnd_8369593 := by
    simpa [prefixWord, tailWord_8369593, baseEnd_8369593] using wordTrace_append hprefix tailTrace_8369593
  have hstable : (prefixWord ++ tailWord_8369593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369593).length < 2 ^ (prefixWord ++ tailWord_8369593).sum := by decide
  have hdescent : baseEnd_8369593 < baseStart_8369593 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369622 : List Nat := [5, 2, 1, 1, 1, 2, 2, 9]
def baseStart_8369622 : Nat := 118140960795 + 8369622 * 2 ^ 59
def prefixEnd_8369622 : Nat := 4983230072969 + 3 ^ 40 * 8369622 * 2
def baseEnd_8369622 : Nat := 159171814164628075893845

theorem tailTrace_8369622 : CollatzResearch.WordTrace tailWord_8369622 prefixEnd_8369622 159171814164628075893845 := by
  unfold tailWord_8369622
  simp only [CollatzResearch.WordTrace]
  refine ⟨19079074555268524155059945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203510128589530924320639413 19079074555268524155059945)
  ·
    refine ⟨14309305916451393116294959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19079074555268524155059945 14309305916451393116294959)
    ·
      refine ⟨21463958874677089674442439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14309305916451393116294959 21463958874677089674442439)
      ·
        refine ⟨32195938312015634511663659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21463958874677089674442439 32195938312015634511663659)
        ·
          refine ⟨48293907468023451767495489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32195938312015634511663659 48293907468023451767495489)
          ·
            refine ⟨36220430601017588825621617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48293907468023451767495489 36220430601017588825621617)
            ·
              refine ⟨27165322950763191619216213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36220430601017588825621617 27165322950763191619216213)
              ·
                refine ⟨159171814164628075893845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 27165322950763191619216213 159171814164628075893845)
                ·
                  rfl

theorem cell23_8369622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 9].length) (baseStart_8369622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369622 prefixEnd_8369622 := by exact prefixLift 8369622
  have htrace : WordTrace (prefixWord ++ tailWord_8369622) baseStart_8369622 baseEnd_8369622 := by
    simpa [prefixWord, tailWord_8369622, baseEnd_8369622] using wordTrace_append hprefix tailTrace_8369622
  have hstable : (prefixWord ++ tailWord_8369622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369622).length < 2 ^ (prefixWord ++ tailWord_8369622).sum := by decide
  have hdescent : baseEnd_8369622 < baseStart_8369622 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369632 : List Nat := [2, 1, 1, 3, 1, 1, 2, 4, 4, 1, 3]
def baseStart_8369632 : Nat := 118140960795 + 8369632 * 2 ^ 59
def prefixEnd_8369632 : Nat := 4983230072969 + 3 ^ 40 * 8369632 * 2
def baseEnd_8369632 : Nat := 4297644117251503010008769

theorem tailTrace_8369632 : CollatzResearch.WordTrace tailWord_8369632 prefixEnd_8369632 4297644117251503010008769 := by
  unfold tailWord_8369632
  simp only [CollatzResearch.WordTrace]
  refine ⟨152632778807130079094411575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203510371742840105459215433 152632778807130079094411575)
  ·
    refine ⟨228949168210695118641617363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152632778807130079094411575 228949168210695118641617363)
    ·
      refine ⟨343423752316042677962426045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228949168210695118641617363 343423752316042677962426045)
      ·
        refine ⟨128783907118516004235909767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343423752316042677962426045 128783907118516004235909767)
        ·
          refine ⟨193175860677774006353864651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128783907118516004235909767 193175860677774006353864651)
          ·
            refine ⟨289763791016661009530796977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193175860677774006353864651 289763791016661009530796977)
            ·
              refine ⟨217322843262495757148097733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289763791016661009530796977 217322843262495757148097733)
              ·
                refine ⟨40748033111717954465268325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 217322843262495757148097733 40748033111717954465268325)
                ·
                  refine ⟨7640256208447116462237811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40748033111717954465268325 7640256208447116462237811)
                  ·
                    refine ⟨11460384312670674693356717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7640256208447116462237811 11460384312670674693356717)
                    ·
                      refine ⟨4297644117251503010008769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11460384312670674693356717 4297644117251503010008769)
                      ·
                        rfl

theorem cell23_8369632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 4, 1, 3].length) (baseStart_8369632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369632 prefixEnd_8369632 := by exact prefixLift 8369632
  have htrace : WordTrace (prefixWord ++ tailWord_8369632) baseStart_8369632 baseEnd_8369632 := by
    simpa [prefixWord, tailWord_8369632, baseEnd_8369632] using wordTrace_append hprefix tailTrace_8369632
  have hstable : (prefixWord ++ tailWord_8369632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369632).length < 2 ^ (prefixWord ++ tailWord_8369632).sum := by decide
  have hdescent : baseEnd_8369632 < baseStart_8369632 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369649 : List Nat := [1, 2, 2, 2, 3, 2, 1, 4, 2, 1, 3]
def baseStart_8369649 : Nat := 118140960795 + 8369649 * 2 ^ 59
def prefixEnd_8369649 : Nat := 4983230072969 + 3 ^ 40 * 8369649 * 2
def baseEnd_8369649 : Nat := 4297652846422629443496191

theorem tailTrace_8369649 : CollatzResearch.WordTrace tailWord_8369649 prefixEnd_8369649 4297652846422629443496191 := by
  unfold tailWord_8369649
  simp only [CollatzResearch.WordTrace]
  refine ⟨305266177655198570092192001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203510785103465713394794667 305266177655198570092192001)
  ·
    refine ⟨228949633241398927569144001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305266177655198570092192001 228949633241398927569144001)
    ·
      refine ⟨171712224931049195676858001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228949633241398927569144001 171712224931049195676858001)
      ·
        refine ⟨128784168698286896757643501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171712224931049195676858001 128784168698286896757643501)
        ·
          refine ⟨48294063261857586284116313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128784168698286896757643501 48294063261857586284116313)
          ·
            refine ⟨36220547446393189713087235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48294063261857586284116313 36220547446393189713087235)
            ·
              refine ⟨54330821169589784569630853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36220547446393189713087235 54330821169589784569630853)
              ·
                refine ⟨10187028969298084606805785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54330821169589784569630853 10187028969298084606805785)
                ·
                  refine ⟨7640271726973563455104339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10187028969298084606805785 7640271726973563455104339)
                  ·
                    refine ⟨11460407590460345182656509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7640271726973563455104339 11460407590460345182656509)
                    ·
                      refine ⟨4297652846422629443496191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11460407590460345182656509 4297652846422629443496191)
                      ·
                        rfl

theorem cell23_8369649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 2, 1, 3].length) (baseStart_8369649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369649 prefixEnd_8369649 := by exact prefixLift 8369649
  have htrace : WordTrace (prefixWord ++ tailWord_8369649) baseStart_8369649 baseEnd_8369649 := by
    simpa [prefixWord, tailWord_8369649, baseEnd_8369649] using wordTrace_append hprefix tailTrace_8369649
  have hstable : (prefixWord ++ tailWord_8369649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369649).length < 2 ^ (prefixWord ++ tailWord_8369649).sum := by decide
  have hdescent : baseEnd_8369649 < baseStart_8369649 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369650 : List Nat := [3, 2, 1, 4, 1, 1, 4, 2, 1, 2, 2]
def baseStart_8369650 : Nat := 118140960795 + 8369650 * 2 ^ 59
def prefixEnd_8369650 : Nat := 4983230072969 + 3 ^ 40 * 8369650 * 2
def baseEnd_8369650 : Nat := 4297653359903283939583687

theorem tailTrace_8369650 : CollatzResearch.WordTrace tailWord_8369650 prefixEnd_8369650 4297653359903283939583687 := by
  unfold tailWord_8369650
  simp only [CollatzResearch.WordTrace]
  refine ⟨76316553532048736815744601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203510809418796631508652269 76316553532048736815744601)
  ·
    refine ⟨57237415149036552611808451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76316553532048736815744601 57237415149036552611808451)
    ·
      refine ⟨85856122723554828917712677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57237415149036552611808451 85856122723554828917712677)
      ·
        refine ⟨16098023010666530422071127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85856122723554828917712677 16098023010666530422071127)
        ·
          refine ⟨24147034515999795633106691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16098023010666530422071127 24147034515999795633106691)
          ·
            refine ⟨36220551773999693449660037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24147034515999795633106691 36220551773999693449660037)
            ·
              refine ⟨6791353457624942521811257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36220551773999693449660037 6791353457624942521811257)
              ·
                refine ⟨5093515093218706891358443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6791353457624942521811257 5093515093218706891358443)
                ·
                  refine ⟨7640272639828060337037665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5093515093218706891358443 7640272639828060337037665)
                  ·
                    refine ⟨5730204479871045252778249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7640272639828060337037665 5730204479871045252778249)
                    ·
                      refine ⟨4297653359903283939583687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5730204479871045252778249 4297653359903283939583687)
                      ·
                        rfl

theorem cell23_8369650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_8369650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369650 prefixEnd_8369650 := by exact prefixLift 8369650
  have htrace : WordTrace (prefixWord ++ tailWord_8369650) baseStart_8369650 baseEnd_8369650 := by
    simpa [prefixWord, tailWord_8369650, baseEnd_8369650] using wordTrace_append hprefix tailTrace_8369650
  have hstable : (prefixWord ++ tailWord_8369650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369650).length < 2 ^ (prefixWord ++ tailWord_8369650).sum := by decide
  have hdescent : baseEnd_8369650 < baseStart_8369650 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369666 : List Nat := [3, 4, 1, 2, 1, 2, 2, 1, 1, 3, 3]
def baseStart_8369666 : Nat := 118140960795 + 8369666 * 2 ^ 59
def prefixEnd_8369666 : Nat := 4983230072969 + 3 ^ 40 * 8369666 * 2
def baseEnd_8369666 : Nat := 4297661575593755876983613

theorem tailTrace_8369666 : CollatzResearch.WordTrace tailWord_8369666 prefixEnd_8369666 4297661575593755876983613 := by
  unfold tailWord_8369666
  simp only [CollatzResearch.WordTrace]
  refine ⟨76316699424034245498890213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203511198464091321330373901 76316699424034245498890213)
  ·
    refine ⟨14309381142006421031041915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76316699424034245498890213 14309381142006421031041915)
    ·
      refine ⟨21464071713009631546562873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14309381142006421031041915 21464071713009631546562873)
      ·
        refine ⟨16098053784757223659922155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21464071713009631546562873 16098053784757223659922155)
        ·
          refine ⟨24147080677135835489883233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16098053784757223659922155 24147080677135835489883233)
          ·
            refine ⟨18110310507851876617412425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24147080677135835489883233 18110310507851876617412425)
            ·
              refine ⟨13582732880888907463059319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18110310507851876617412425 13582732880888907463059319)
              ·
                refine ⟨20374099321333361194588979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13582732880888907463059319 20374099321333361194588979)
                ·
                  refine ⟨30561148982000041791883469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20374099321333361194588979 30561148982000041791883469)
                  ·
                    refine ⟨11460430868250015671956301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30561148982000041791883469 11460430868250015671956301)
                    ·
                      refine ⟨4297661575593755876983613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11460430868250015671956301 4297661575593755876983613)
                      ·
                        rfl

theorem cell23_8369666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_8369666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369666 prefixEnd_8369666 := by exact prefixLift 8369666
  have htrace : WordTrace (prefixWord ++ tailWord_8369666) baseStart_8369666 baseEnd_8369666 := by
    simpa [prefixWord, tailWord_8369666, baseEnd_8369666] using wordTrace_append hprefix tailTrace_8369666
  have hstable : (prefixWord ++ tailWord_8369666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369666).length < 2 ^ (prefixWord ++ tailWord_8369666).sum := by decide
  have hdescent : baseEnd_8369666 < baseStart_8369666 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369706 : List Nat := [3, 1, 4, 1, 1, 1, 3, 1, 4, 2, 2]
def baseStart_8369706 : Nat := 118140960795 + 8369706 * 2 ^ 59
def prefixEnd_8369706 : Nat := 4983230072969 + 3 ^ 40 * 8369706 * 2
def baseEnd_8369706 : Nat := 4297682114819935720483429

theorem tailTrace_8369706 : CollatzResearch.WordTrace tailWord_8369706 prefixEnd_8369706 4297682114819935720483429 := by
  unfold tailWord_8369706
  simp only [CollatzResearch.WordTrace]
  refine ⟨76317064153998017206754243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203512171077328045884677981 76317064153998017206754243)
  ·
    refine ⟨114475596230997025810131365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76317064153998017206754243 114475596230997025810131365)
    ·
      refine ⟨21464174293311942339399631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114475596230997025810131365 21464174293311942339399631)
      ·
        refine ⟨32196261439967913509099447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21464174293311942339399631 32196261439967913509099447)
        ·
          refine ⟨48294392159951870263649171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32196261439967913509099447 48294392159951870263649171)
          ·
            refine ⟨72441588239927805395473757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48294392159951870263649171 72441588239927805395473757)
            ·
              refine ⟨27165595589972927023302659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72441588239927805395473757 27165595589972927023302659)
              ·
                refine ⟨40748393384959390534953989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27165595589972927023302659 40748393384959390534953989)
                ·
                  refine ⟨7640323759679885725303873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40748393384959390534953989 7640323759679885725303873)
                  ·
                    refine ⟨5730242819759914293977905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7640323759679885725303873 5730242819759914293977905)
                    ·
                      refine ⟨4297682114819935720483429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5730242819759914293977905 4297682114819935720483429)
                      ·
                        rfl

theorem cell23_8369706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_8369706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369706 prefixEnd_8369706 := by exact prefixLift 8369706
  have htrace : WordTrace (prefixWord ++ tailWord_8369706) baseStart_8369706 baseEnd_8369706 := by
    simpa [prefixWord, tailWord_8369706, baseEnd_8369706] using wordTrace_append hprefix tailTrace_8369706
  have hstable : (prefixWord ++ tailWord_8369706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369706).length < 2 ^ (prefixWord ++ tailWord_8369706).sum := by decide
  have hdescent : baseEnd_8369706 < baseStart_8369706 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369722 : List Nat := [3, 1, 1, 1, 3, 2, 1, 3, 2, 3, 3]
def baseStart_8369722 : Nat := 118140960795 + 8369722 * 2 ^ 59
def prefixEnd_8369722 : Nat := 4983230072969 + 3 ^ 40 * 8369722 * 2
def baseEnd_8369722 : Nat := 4297690330510407657883355

theorem tailTrace_8369722 : CollatzResearch.WordTrace tailWord_8369722 prefixEnd_8369722 4297690330510407657883355 := by
  unfold tailWord_8369722
  simp only [CollatzResearch.WordTrace]
  refine ⟨76317210045983525889899855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203512560122622735706399613 76317210045983525889899855)
  ·
    refine ⟨114475815068975288834849783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76317210045983525889899855 114475815068975288834849783)
    ·
      refine ⟨171713722603462933252274675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114475815068975288834849783 171713722603462933252274675)
      ·
        refine ⟨257570583905194399878412013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171713722603462933252274675 257570583905194399878412013)
        ·
          refine ⟨96588968964447899954404505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257570583905194399878412013 96588968964447899954404505)
          ·
            refine ⟨72441726723335924965803379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96588968964447899954404505 72441726723335924965803379)
            ·
              refine ⟨108662590085003887448705069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72441726723335924965803379 108662590085003887448705069)
              ·
                refine ⟨40748471281876457793264401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108662590085003887448705069 40748471281876457793264401)
                ·
                  refine ⟨30561353461407343344948301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40748471281876457793264401 30561353461407343344948301)
                  ·
                    refine ⟨11460507548027753754355613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30561353461407343344948301 11460507548027753754355613)
                    ·
                      refine ⟨4297690330510407657883355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11460507548027753754355613 4297690330510407657883355)
                      ·
                        rfl

theorem cell23_8369722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 2, 3, 3].length) (baseStart_8369722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369722 prefixEnd_8369722 := by exact prefixLift 8369722
  have htrace : WordTrace (prefixWord ++ tailWord_8369722) baseStart_8369722 baseEnd_8369722 := by
    simpa [prefixWord, tailWord_8369722, baseEnd_8369722] using wordTrace_append hprefix tailTrace_8369722
  have hstable : (prefixWord ++ tailWord_8369722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369722).length < 2 ^ (prefixWord ++ tailWord_8369722).sum := by decide
  have hdescent : baseEnd_8369722 < baseStart_8369722 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369742 : List Nat := [4, 1, 1, 1, 1, 2, 1, 5, 2, 5]
def baseStart_8369742 : Nat := 118140960795 + 8369742 * 2 ^ 59
def prefixEnd_8369742 : Nat := 4983230072969 + 3 ^ 40 * 8369742 * 2
def baseEnd_8369742 : Nat := 1432566866707832526544421

theorem tailTrace_8369742 : CollatzResearch.WordTrace tailWord_8369742 prefixEnd_8369742 1432566866707832526544421 := by
  unfold tailWord_8369742
  simp only [CollatzResearch.WordTrace]
  refine ⟨38158696205482705871915935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203513046429241097983551653 38158696205482705871915935)
  ·
    refine ⟨57238044308224058807873903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38158696205482705871915935 57238044308224058807873903)
    ·
      refine ⟨85857066462336088211810855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57238044308224058807873903 85857066462336088211810855)
      ·
        refine ⟨128785599693504132317716283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85857066462336088211810855 128785599693504132317716283)
        ·
          refine ⟨193178399540256198476574425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128785599693504132317716283 193178399540256198476574425)
          ·
            refine ⟨144883799655192148857430819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193178399540256198476574425 144883799655192148857430819)
            ·
              refine ⟨217325699482788223286146229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144883799655192148857430819 217325699482788223286146229)
              ·
                refine ⟨20374284326511395933076209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 217325699482788223286146229 20374284326511395933076209)
                ·
                  refine ⟨15280713244883546949807157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20374284326511395933076209 15280713244883546949807157)
                  ·
                    refine ⟨1432566866707832526544421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15280713244883546949807157 1432566866707832526544421)
                    ·
                      rfl

theorem cell23_8369742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_8369742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369742 prefixEnd_8369742 := by exact prefixLift 8369742
  have htrace : WordTrace (prefixWord ++ tailWord_8369742) baseStart_8369742 baseEnd_8369742 := by
    simpa [prefixWord, tailWord_8369742, baseEnd_8369742] using wordTrace_append hprefix tailTrace_8369742
  have hstable : (prefixWord ++ tailWord_8369742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369742).length < 2 ^ (prefixWord ++ tailWord_8369742).sum := by decide
  have hdescent : baseEnd_8369742 < baseStart_8369742 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369746 : List Nat := [3, 2, 2, 1, 2, 4, 1, 3, 5]
def baseStart_8369746 : Nat := 118140960795 + 8369746 * 2 ^ 59
def prefixEnd_8369746 : Nat := 4983230072969 + 3 ^ 40 * 8369746 * 2
def baseEnd_8369746 : Nat := 477522517116235062664805

theorem tailTrace_8369746 : CollatzResearch.WordTrace tailWord_8369746 prefixEnd_8369746 477522517116235062664805 := by
  unfold tailWord_8369746
  simp only [CollatzResearch.WordTrace]
  refine ⟨76317428883961788914618273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203513143690564770438982061 76317428883961788914618273)
  ·
    refine ⟨57238071662971341685963705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76317428883961788914618273 57238071662971341685963705)
    ·
      refine ⟨42928553747228506264472779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57238071662971341685963705 42928553747228506264472779)
      ·
        refine ⟨64392830620842759396709169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42928553747228506264472779 64392830620842759396709169)
        ·
          refine ⟨48294622965632069547531877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64392830620842759396709169 48294622965632069547531877)
          ·
            refine ⟨9055241806056013040162227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48294622965632069547531877 9055241806056013040162227)
            ·
              refine ⟨13582862709084019560243341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9055241806056013040162227 13582862709084019560243341)
              ·
                refine ⟨5093573515906507335091253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13582862709084019560243341 5093573515906507335091253)
                ·
                  refine ⟨477522517116235062664805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5093573515906507335091253 477522517116235062664805)
                  ·
                    rfl

theorem cell23_8369746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 3, 5].length) (baseStart_8369746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369746 prefixEnd_8369746 := by exact prefixLift 8369746
  have htrace : WordTrace (prefixWord ++ tailWord_8369746) baseStart_8369746 baseEnd_8369746 := by
    simpa [prefixWord, tailWord_8369746, baseEnd_8369746] using wordTrace_append hprefix tailTrace_8369746
  have hstable : (prefixWord ++ tailWord_8369746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369746).length < 2 ^ (prefixWord ++ tailWord_8369746).sum := by decide
  have hdescent : baseEnd_8369746 < baseStart_8369746 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369796 : List Nat := [2, 3, 2, 1, 4, 1, 2, 1, 2, 1, 4]
def baseStart_8369796 : Nat := 118140960795 + 8369796 * 2 ^ 59
def prefixEnd_8369796 : Nat := 4983230072969 + 3 ^ 40 * 8369796 * 2
def baseEnd_8369796 : Nat := 4297728328078840368358015

theorem tailTrace_8369796 : CollatzResearch.WordTrace tailWord_8369796 prefixEnd_8369796 4297728328078840368358015 := by
  unfold tailWord_8369796
  simp only [CollatzResearch.WordTrace]
  refine ⟨152635769592833007098896621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203514359457110676131862161 152635769592833007098896621)
  ·
    refine ⟨57238413597312377662086233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152635769592833007098896621 57238413597312377662086233)
    ·
      refine ⟨42928810197984283246564675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57238413597312377662086233 42928810197984283246564675)
      ·
        refine ⟨64393215296976424869847013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42928810197984283246564675 64393215296976424869847013)
        ·
          refine ⟨12073727868183079663096315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64393215296976424869847013 12073727868183079663096315)
          ·
            refine ⟨18110591802274619494644473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12073727868183079663096315 18110591802274619494644473)
            ·
              refine ⟨13582943851705964620983355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18110591802274619494644473 13582943851705964620983355)
              ·
                refine ⟨20374415777558946931475033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13582943851705964620983355 20374415777558946931475033)
                ·
                  refine ⟨15280811833169210198606275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20374415777558946931475033 15280811833169210198606275)
                  ·
                    refine ⟨22921217749753815297909413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15280811833169210198606275 22921217749753815297909413)
                    ·
                      refine ⟨4297728328078840368358015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22921217749753815297909413 4297728328078840368358015)
                      ·
                        rfl

theorem cell23_8369796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_8369796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369796 prefixEnd_8369796 := by exact prefixLift 8369796
  have htrace : WordTrace (prefixWord ++ tailWord_8369796) baseStart_8369796 baseEnd_8369796 := by
    simpa [prefixWord, tailWord_8369796, baseEnd_8369796] using wordTrace_append hprefix tailTrace_8369796
  have hstable : (prefixWord ++ tailWord_8369796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369796).length < 2 ^ (prefixWord ++ tailWord_8369796).sum := by decide
  have hdescent : baseEnd_8369796 < baseStart_8369796 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369799 : List Nat := [1, 1, 4, 2, 1, 3, 1, 3, 2, 2, 3]
def baseStart_8369799 : Nat := 118140960795 + 8369799 * 2 ^ 59
def prefixEnd_8369799 : Nat := 4983230072969 + 3 ^ 40 * 8369799 * 2
def baseEnd_8369799 : Nat := 4297729868520803856620501

theorem tailTrace_8369799 : CollatzResearch.WordTrace tailWord_8369799 prefixEnd_8369799 4297729868520803856620501 := by
  unfold tailWord_8369799
  simp only [CollatzResearch.WordTrace]
  refine ⟨305271648604655145710152451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203514432403103430473434967 305271648604655145710152451)
  ·
    refine ⟨457907472906982718565228677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305271648604655145710152451 457907472906982718565228677)
    ·
      refine ⟨85857651170059259730980377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 457907472906982718565228677 85857651170059259730980377)
      ·
        refine ⟨64393238377544444798235283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85857651170059259730980377 64393238377544444798235283)
        ·
          refine ⟨96589857566316667197352925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64393238377544444798235283 96589857566316667197352925)
          ·
            refine ⟨36221196587368750199007347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96589857566316667197352925 36221196587368750199007347)
            ·
              refine ⟨54331794881053125298511021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36221196587368750199007347 54331794881053125298511021)
              ·
                refine ⟨20374423080394921986941633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54331794881053125298511021 20374423080394921986941633)
                ·
                  refine ⟨15280817310296191490206225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20374423080394921986941633 15280817310296191490206225)
                  ·
                    refine ⟨11460612982722143617654669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15280817310296191490206225 11460612982722143617654669)
                    ·
                      refine ⟨4297729868520803856620501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11460612982722143617654669 4297729868520803856620501)
                      ·
                        rfl

theorem cell23_8369799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_8369799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369799 prefixEnd_8369799 := by exact prefixLift 8369799
  have htrace : WordTrace (prefixWord ++ tailWord_8369799) baseStart_8369799 baseEnd_8369799 := by
    simpa [prefixWord, tailWord_8369799, baseEnd_8369799] using wordTrace_append hprefix tailTrace_8369799
  have hstable : (prefixWord ++ tailWord_8369799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369799).length < 2 ^ (prefixWord ++ tailWord_8369799).sum := by decide
  have hdescent : baseEnd_8369799 < baseStart_8369799 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369839 : List Nat := [1, 1, 2, 1, 2, 4, 2, 2, 1, 5, 2]
def baseStart_8369839 : Nat := 118140960795 + 8369839 * 2 ^ 59
def prefixEnd_8369839 : Nat := 4983230072969 + 3 ^ 40 * 8369839 * 2
def baseEnd_8369839 : Nat := 4297750407746983700120317

theorem tailTrace_8369839 : CollatzResearch.WordTrace tailWord_8369839 prefixEnd_8369839 4297750407746983700120317 := by
  unfold tailWord_8369839
  simp only [CollatzResearch.WordTrace]
  refine ⟨305273107524510232541608571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203515405016340155027739047 305273107524510232541608571)
  ·
    refine ⟨457909661286765348812412857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305273107524510232541608571 457909661286765348812412857)
    ·
      refine ⟨343432245965074011609309643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457909661286765348812412857 343432245965074011609309643)
      ·
        refine ⟨515148368947611017413964465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343432245965074011609309643 515148368947611017413964465)
        ·
          refine ⟨386361276710708263060473349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515148368947611017413964465 386361276710708263060473349)
          ·
            refine ⟨72442739383257799323838753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 386361276710708263060473349 72442739383257799323838753)
            ·
              refine ⟨54332054537443349492879065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72442739383257799323838753 54332054537443349492879065)
              ·
                refine ⟨40749040903082512119659299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54332054537443349492879065 40749040903082512119659299)
                ·
                  refine ⟨61123561354623768179488949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40749040903082512119659299 61123561354623768179488949)
                  ·
                    refine ⟨5730333876995978266827089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61123561354623768179488949 5730333876995978266827089)
                    ·
                      refine ⟨4297750407746983700120317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5730333876995978266827089 4297750407746983700120317)
                      ·
                        rfl

theorem cell23_8369839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 5, 2].length) (baseStart_8369839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369839 prefixEnd_8369839 := by exact prefixLift 8369839
  have htrace : WordTrace (prefixWord ++ tailWord_8369839) baseStart_8369839 baseEnd_8369839 := by
    simpa [prefixWord, tailWord_8369839, baseEnd_8369839] using wordTrace_append hprefix tailTrace_8369839
  have hstable : (prefixWord ++ tailWord_8369839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369839).length < 2 ^ (prefixWord ++ tailWord_8369839).sum := by decide
  have hdescent : baseEnd_8369839 < baseStart_8369839 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369863 : List Nat := [1, 1, 4, 1, 1, 1, 6, 3, 1, 1, 3]
def baseStart_8369863 : Nat := 118140960795 + 8369863 * 2 ^ 59
def prefixEnd_8369863 : Nat := 4983230072969 + 3 ^ 40 * 8369863 * 2
def baseEnd_8369863 : Nat := 4297762731282691606220207

theorem tailTrace_8369863 : CollatzResearch.WordTrace tailWord_8369863 prefixEnd_8369863 4297762731282691606220207 := by
  unfold tailWord_8369863
  simp only [CollatzResearch.WordTrace]
  refine ⟨305273982876423284640482243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203515988584282189760321495 305273982876423284640482243)
  ·
    refine ⟨457910974314634926960723365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305273982876423284640482243 457910974314634926960723365)
    ·
      refine ⟨85858307683994048805135631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 457910974314634926960723365 85858307683994048805135631)
      ·
        refine ⟨128787461525991073207703447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85858307683994048805135631 128787461525991073207703447)
        ·
          refine ⟨193181192288986609811555171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128787461525991073207703447 193181192288986609811555171)
          ·
            refine ⟨289771788433479914717332757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193181192288986609811555171 289771788433479914717332757)
            ·
              refine ⟨13583052582819371002374973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 289771788433479914717332757 13583052582819371002374973)
              ·
                refine ⟨5093644718557264125890615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13583052582819371002374973 5093644718557264125890615)
                ·
                  refine ⟨7640467077835896188835923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5093644718557264125890615 7640467077835896188835923)
                  ·
                    refine ⟨11460700616753844283253885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7640467077835896188835923 11460700616753844283253885)
                    ·
                      refine ⟨4297762731282691606220207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11460700616753844283253885 4297762731282691606220207)
                      ·
                        rfl

theorem cell23_8369863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 3, 1, 1, 3].length) (baseStart_8369863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369863 prefixEnd_8369863 := by exact prefixLift 8369863
  have htrace : WordTrace (prefixWord ++ tailWord_8369863) baseStart_8369863 baseEnd_8369863 := by
    simpa [prefixWord, tailWord_8369863, baseEnd_8369863] using wordTrace_append hprefix tailTrace_8369863
  have hstable : (prefixWord ++ tailWord_8369863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369863).length < 2 ^ (prefixWord ++ tailWord_8369863).sum := by decide
  have hdescent : baseEnd_8369863 < baseStart_8369863 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369866 : List Nat := [3, 1, 2, 1, 5, 1, 1, 3, 1, 5]
def baseStart_8369866 : Nat := 118140960795 + 8369866 * 2 ^ 59
def prefixEnd_8369866 : Nat := 4983230072969 + 3 ^ 40 * 8369866 * 2
def baseEnd_8369866 : Nat := 1432588090574885031494231

theorem tailTrace_8369866 : CollatzResearch.WordTrace tailWord_8369866 prefixEnd_8369866 1432588090574885031494231 := by
  unfold tailWord_8369866
  simp only [CollatzResearch.WordTrace]
  refine ⟨76318523073853104038210363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203516061530274944101894301 76318523073853104038210363)
  ·
    refine ⟨114477784610779656057315545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76318523073853104038210363 114477784610779656057315545)
    ·
      refine ⟨85858338458084742042986659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114477784610779656057315545 85858338458084742042986659)
      ·
        refine ⟨128787507687127113064479989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85858338458084742042986659 128787507687127113064479989)
        ·
          refine ⟨12073828845668166849794999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128787507687127113064479989 12073828845668166849794999)
          ·
            refine ⟨18110743268502250274692499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12073828845668166849794999 18110743268502250274692499)
            ·
              refine ⟨27166114902753375412038749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18110743268502250274692499 27166114902753375412038749)
              ·
                refine ⟨10187293088532515779514531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27166114902753375412038749 10187293088532515779514531)
                ·
                  refine ⟨15280939632798773669271797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10187293088532515779514531 15280939632798773669271797)
                  ·
                    refine ⟨1432588090574885031494231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15280939632798773669271797 1432588090574885031494231)
                    ·
                      rfl

theorem cell23_8369866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 1, 5].length) (baseStart_8369866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369866 prefixEnd_8369866 := by exact prefixLift 8369866
  have htrace : WordTrace (prefixWord ++ tailWord_8369866) baseStart_8369866 baseEnd_8369866 := by
    simpa [prefixWord, tailWord_8369866, baseEnd_8369866] using wordTrace_append hprefix tailTrace_8369866
  have hstable : (prefixWord ++ tailWord_8369866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369866).length < 2 ^ (prefixWord ++ tailWord_8369866).sum := by decide
  have hdescent : baseEnd_8369866 < baseStart_8369866 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369879 : List Nat := [1, 1, 3, 2, 1, 3, 3, 1, 4, 4]
def baseStart_8369879 : Nat := 118140960795 + 8369879 * 2 ^ 59
def prefixEnd_8369879 : Nat := 4983230072969 + 3 ^ 40 * 8369879 * 2
def baseEnd_8369879 : Nat := 1432590315657721181206711

theorem tailTrace_8369879 : CollatzResearch.WordTrace tailWord_8369879 prefixEnd_8369879 1432590315657721181206711 := by
  unfold tailWord_8369879
  simp only [CollatzResearch.WordTrace]
  refine ⟨305274566444365319373064691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203516377629576879582043127 305274566444365319373064691)
  ·
    refine ⟨457911849666547979059597037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305274566444365319373064691 457911849666547979059597037)
    ·
      refine ⟨171716943624955492147348889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 457911849666547979059597037 171716943624955492147348889)
      ·
        refine ⟨128787707718716619110511667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171716943624955492147348889 128787707718716619110511667)
        ·
          refine ⟨193181561578074928665767501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128787707718716619110511667 193181561578074928665767501)
          ·
            refine ⟨72443085591778098249662813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193181561578074928665767501 72443085591778098249662813)
            ·
              refine ⟨27166157096916786843623555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72443085591778098249662813 27166157096916786843623555)
              ·
                refine ⟨40749235645375180265435333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27166157096916786843623555 40749235645375180265435333)
                ·
                  refine ⟨7640481683507846299769125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40749235645375180265435333 7640481683507846299769125)
                  ·
                    refine ⟨1432590315657721181206711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7640481683507846299769125 1432590315657721181206711)
                    ·
                      rfl

theorem cell23_8369879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 4, 4].length) (baseStart_8369879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369879 prefixEnd_8369879 := by exact prefixLift 8369879
  have htrace : WordTrace (prefixWord ++ tailWord_8369879) baseStart_8369879 baseEnd_8369879 := by
    simpa [prefixWord, tailWord_8369879, baseEnd_8369879] using wordTrace_append hprefix tailTrace_8369879
  have hstable : (prefixWord ++ tailWord_8369879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369879).length < 2 ^ (prefixWord ++ tailWord_8369879).sum := by decide
  have hdescent : baseEnd_8369879 < baseStart_8369879 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369892 : List Nat := [2, 3, 1, 1, 1, 3, 2, 10]
def baseStart_8369892 : Nat := 118140960795 + 8369892 * 2 ^ 59
def prefixEnd_8369892 : Nat := 4983230072969 + 3 ^ 40 * 8369892 * 2
def baseEnd_8369892 : Nat := 159176948971173036768799

theorem tailTrace_8369892 : CollatzResearch.WordTrace tailWord_8369892 prefixEnd_8369892 159176948971173036768799 := by
  unfold tailWord_8369892
  simp only [CollatzResearch.WordTrace]
  refine ⟨152637520296659111296643965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203516693728878815062191953 152637520296659111296643965)
  ·
    refine ⟨57239070111247166736241487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152637520296659111296643965 57239070111247166736241487)
    ·
      refine ⟨85858605166870750104362231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57239070111247166736241487 85858605166870750104362231)
      ·
        refine ⟨128787907750306125156543347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85858605166870750104362231 128787907750306125156543347)
        ·
          refine ⟨193181861625459187734815021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128787907750306125156543347 193181861625459187734815021)
          ·
            refine ⟨72443198109547195400555633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193181861625459187734815021 72443198109547195400555633)
            ·
              refine ⟨54332398582160396550416725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72443198109547195400555633 54332398582160396550416725)
              ·
                refine ⟨159176948971173036768799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 54332398582160396550416725 159176948971173036768799)
                ·
                  rfl

theorem cell23_8369892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 10].length) (baseStart_8369892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369892 prefixEnd_8369892 := by exact prefixLift 8369892
  have htrace : WordTrace (prefixWord ++ tailWord_8369892) baseStart_8369892 baseEnd_8369892 := by
    simpa [prefixWord, tailWord_8369892, baseEnd_8369892] using wordTrace_append hprefix tailTrace_8369892
  have hstable : (prefixWord ++ tailWord_8369892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369892).length < 2 ^ (prefixWord ++ tailWord_8369892).sum := by decide
  have hdescent : baseEnd_8369892 < baseStart_8369892 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369896 : List Nat := [2, 1, 4, 1, 3, 3, 1, 1, 1, 6]
def baseStart_8369896 : Nat := 118140960795 + 8369896 * 2 ^ 59
def prefixEnd_8369896 : Nat := 4983230072969 + 3 ^ 40 * 8369896 * 2
def baseEnd_8369896 : Nat := 1432593225381429992369185

theorem tailTrace_8369896 : CollatzResearch.WordTrace tailWord_8369896 prefixEnd_8369896 1432593225381429992369185 := by
  unfold tailWord_8369896
  simp only [CollatzResearch.WordTrace]
  refine ⟨152637593242651865638216771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203516790990202487517622361 152637593242651865638216771)
  ·
    refine ⟨228956389863977798457325157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152637593242651865638216771 228956389863977798457325157)
    ·
      refine ⟨42929323099495837210748467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228956389863977798457325157 42929323099495837210748467)
      ·
        refine ⟨64393984649243755816122701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42929323099495837210748467 64393984649243755816122701)
        ·
          refine ⟨24147744243466408431046013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64393984649243755816122701 24147744243466408431046013)
          ·
            refine ⟨9055404091299903161642255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24147744243466408431046013 9055404091299903161642255)
            ·
              refine ⟨13583106136949854742463383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9055404091299903161642255 13583106136949854742463383)
              ·
                refine ⟨20374659205424782113695075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13583106136949854742463383 20374659205424782113695075)
                ·
                  refine ⟨30561988808137173170542613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20374659205424782113695075 30561988808137173170542613)
                  ·
                    refine ⟨1432593225381429992369185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30561988808137173170542613 1432593225381429992369185)
                    ·
                      rfl

theorem cell23_8369896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_8369896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369896 prefixEnd_8369896 := by exact prefixLift 8369896
  have htrace : WordTrace (prefixWord ++ tailWord_8369896) baseStart_8369896 baseEnd_8369896 := by
    simpa [prefixWord, tailWord_8369896, baseEnd_8369896] using wordTrace_append hprefix tailTrace_8369896
  have hstable : (prefixWord ++ tailWord_8369896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369896).length < 2 ^ (prefixWord ++ tailWord_8369896).sum := by decide
  have hdescent : baseEnd_8369896 < baseStart_8369896 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369899 : List Nat := [1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 4]
def baseStart_8369899 : Nat := 118140960795 + 8369899 * 2 ^ 59
def prefixEnd_8369899 : Nat := 4983230072969 + 3 ^ 40 * 8369899 * 2
def baseEnd_8369899 : Nat := 4297781216586253465370041

theorem tailTrace_8369899 : CollatzResearch.WordTrace tailWord_8369899 prefixEnd_8369899 4297781216586253465370041 := by
  unfold tailWord_8369899
  simp only [CollatzResearch.WordTrace]
  refine ⟨305275295904292862788792751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203516863936195241859195167 305275295904292862788792751)
  ·
    refine ⟨457912943856439294183189127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305275295904292862788792751 457912943856439294183189127)
    ·
      refine ⟨686869415784658941274783691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457912943856439294183189127 686869415784658941274783691)
      ·
        refine ⟨1030304123676988411912175537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 686869415784658941274783691 1030304123676988411912175537)
        ·
          refine ⟨772728092757741308934131653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1030304123676988411912175537 772728092757741308934131653)
          ·
            refine ⟨144886517392076495425149685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 772728092757741308934131653 144886517392076495425149685)
            ·
              refine ⟨13583111005507171446107783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 144886517392076495425149685 13583111005507171446107783)
              ·
                refine ⟨20374666508260757169161675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13583111005507171446107783 20374666508260757169161675)
                ·
                  refine ⟨30561999762391135753742513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20374666508260757169161675 30561999762391135753742513)
                  ·
                    refine ⟨22921499821793351815306885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30561999762391135753742513 22921499821793351815306885)
                    ·
                      refine ⟨4297781216586253465370041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22921499821793351815306885 4297781216586253465370041)
                      ·
                        rfl

theorem cell23_8369899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 4].length) (baseStart_8369899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369899 prefixEnd_8369899 := by exact prefixLift 8369899
  have htrace : WordTrace (prefixWord ++ tailWord_8369899) baseStart_8369899 baseEnd_8369899 := by
    simpa [prefixWord, tailWord_8369899, baseEnd_8369899] using wordTrace_append hprefix tailTrace_8369899
  have hstable : (prefixWord ++ tailWord_8369899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369899).length < 2 ^ (prefixWord ++ tailWord_8369899).sum := by decide
  have hdescent : baseEnd_8369899 < baseStart_8369899 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369919 : List Nat := [1, 1, 2, 2, 1, 3, 2, 4, 1, 3, 3]
def baseStart_8369919 : Nat := 118140960795 + 8369919 * 2 ^ 59
def prefixEnd_8369919 : Nat := 4983230072969 + 3 ^ 40 * 8369919 * 2
def baseEnd_8369919 : Nat := 4297791486199343387119949

theorem tailTrace_8369919 : CollatzResearch.WordTrace tailWord_8369919 prefixEnd_8369919 4297791486199343387119949 := by
  unfold tailWord_8369919
  simp only [CollatzResearch.WordTrace]
  refine ⟨305276025364220406204520811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203517350242813604136347207 305276025364220406204520811)
  ·
    refine ⟨457914038046330609306781217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305276025364220406204520811 457914038046330609306781217)
    ·
      refine ⟨343435528534747956980085913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457914038046330609306781217 343435528534747956980085913)
      ·
        refine ⟨257576646401060967735064435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343435528534747956980085913 257576646401060967735064435)
        ·
          refine ⟨386364969601591451602596653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257576646401060967735064435 386364969601591451602596653)
          ·
            refine ⟨144886863600596794350973745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 386364969601591451602596653 144886863600596794350973745)
            ·
              refine ⟨108665147700447595763230309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144886863600596794350973745 108665147700447595763230309)
              ·
                refine ⟨20374715193833924205605683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108665147700447595763230309 20374715193833924205605683)
                ·
                  refine ⟨30562072790750886308408525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20374715193833924205605683 30562072790750886308408525)
                  ·
                    refine ⟨11460777296531582365653197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30562072790750886308408525 11460777296531582365653197)
                    ·
                      refine ⟨4297791486199343387119949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11460777296531582365653197 4297791486199343387119949)
                      ·
                        rfl

theorem cell23_8369919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 3, 3].length) (baseStart_8369919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369919 prefixEnd_8369919 := by exact prefixLift 8369919
  have htrace : WordTrace (prefixWord ++ tailWord_8369919) baseStart_8369919 baseEnd_8369919 := by
    simpa [prefixWord, tailWord_8369919, baseEnd_8369919] using wordTrace_append hprefix tailTrace_8369919
  have hstable : (prefixWord ++ tailWord_8369919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369919).length < 2 ^ (prefixWord ++ tailWord_8369919).sum := by decide
  have hdescent : baseEnd_8369919 < baseStart_8369919 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369953 : List Nat := [1, 2, 3, 2, 1, 4, 1, 3, 2, 1, 3]
def baseStart_8369953 : Nat := 118140960795 + 8369953 * 2 ^ 59
def prefixEnd_8369953 : Nat := 4983230072969 + 3 ^ 40 * 8369953 * 2
def baseEnd_8369953 : Nat := 4297808944541596254094793

theorem tailTrace_8369953 : CollatzResearch.WordTrace tailWord_8369953 prefixEnd_8369953 4297808944541596254094793 := by
  unfold tailWord_8369953
  simp only [CollatzResearch.WordTrace]
  refine ⟨305277265446097230011258513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203518176964064820007505675 305277265446097230011258513)
  ·
    refine ⟨228957949084572922508443885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305277265446097230011258513 228957949084572922508443885)
    ·
      refine ⟨85859230906714845940666457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228957949084572922508443885 85859230906714845940666457)
      ·
        refine ⟨64394423180036134455499843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85859230906714845940666457 64394423180036134455499843)
        ·
          refine ⟨96591634770054201683249765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64394423180036134455499843 96591634770054201683249765)
          ·
            refine ⟨18110931519385162815609331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96591634770054201683249765 18110931519385162815609331)
            ·
              refine ⟨27166397279077744223413997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18110931519385162815609331 27166397279077744223413997)
              ·
                refine ⟨10187398979654154083780249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27166397279077744223413997 10187398979654154083780249)
                ·
                  refine ⟨7640549234740615562835187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10187398979654154083780249 7640549234740615562835187)
                  ·
                    refine ⟨11460823852110923344252781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7640549234740615562835187 11460823852110923344252781)
                    ·
                      refine ⟨4297808944541596254094793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11460823852110923344252781 4297808944541596254094793)
                      ·
                        rfl

theorem cell23_8369953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_8369953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369953 prefixEnd_8369953 := by exact prefixLift 8369953
  have htrace : WordTrace (prefixWord ++ tailWord_8369953) baseStart_8369953 baseEnd_8369953 := by
    simpa [prefixWord, tailWord_8369953, baseEnd_8369953] using wordTrace_append hprefix tailTrace_8369953
  have hstable : (prefixWord ++ tailWord_8369953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369953).length < 2 ^ (prefixWord ++ tailWord_8369953).sum := by decide
  have hdescent : baseEnd_8369953 < baseStart_8369953 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369976 : List Nat := [2, 1, 2, 1, 3, 3, 1, 1, 3, 4, 2]
def baseStart_8369976 : Nat := 118140960795 + 8369976 * 2 ^ 59
def prefixEnd_8369976 : Nat := 4983230072969 + 3 ^ 40 * 8369976 * 2
def baseEnd_8369976 : Nat := 4297820754596649664107187

theorem tailTrace_8369976 : CollatzResearch.WordTrace tailWord_8369976 prefixEnd_8369976 4297820754596649664107187 := by
  unfold tailWord_8369976
  simp only [CollatzResearch.WordTrace]
  refine ⟨152639052162506952469672891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203518736216675936626230521 152639052162506952469672891)
  ·
    refine ⟨228958578243760428704509337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152639052162506952469672891 228958578243760428704509337)
    ·
      refine ⟨171718933682820321528382003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228958578243760428704509337 171718933682820321528382003)
      ·
        refine ⟨257578400524230482292573005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171718933682820321528382003 257578400524230482292573005)
        ·
          refine ⟨96591900196586430859714877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257578400524230482292573005 96591900196586430859714877)
          ·
            refine ⟨36221962573719911572393079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96591900196586430859714877 36221962573719911572393079)
            ·
              refine ⟨54332943860579867358589619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36221962573719911572393079 54332943860579867358589619)
              ·
                refine ⟨81499415790869801037884429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54332943860579867358589619 81499415790869801037884429)
                ·
                  refine ⟨30562280921576175389206661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81499415790869801037884429 30562280921576175389206661)
                  ·
                    refine ⟨5730427672795532885476249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30562280921576175389206661 5730427672795532885476249)
                    ·
                      refine ⟨4297820754596649664107187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5730427672795532885476249 4297820754596649664107187)
                      ·
                        rfl

theorem cell23_8369976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 3, 4, 2].length) (baseStart_8369976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369976 prefixEnd_8369976 := by exact prefixLift 8369976
  have htrace : WordTrace (prefixWord ++ tailWord_8369976) baseStart_8369976 baseEnd_8369976 := by
    simpa [prefixWord, tailWord_8369976, baseEnd_8369976] using wordTrace_append hprefix tailTrace_8369976
  have hstable : (prefixWord ++ tailWord_8369976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369976).length < 2 ^ (prefixWord ++ tailWord_8369976).sum := by decide
  have hdescent : baseEnd_8369976 < baseStart_8369976 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8369989 : List Nat := [1, 3, 1, 1, 1, 2, 4, 2, 2, 2, 4]
def baseStart_8369989 : Nat := 118140960795 + 8369989 * 2 ^ 59
def prefixEnd_8369989 : Nat := 4983230072969 + 3 ^ 40 * 8369989 * 2
def baseEnd_8369989 : Nat := 4297827429845158113244627

theorem tailTrace_8369989 : CollatzResearch.WordTrace tailWord_8369989 prefixEnd_8369989 4297827429845158113244627 := by
  unfold tailWord_8369989
  simp only [CollatzResearch.WordTrace]
  refine ⟨305278578473966808159569021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203519052315977872106379347 305278578473966808159569021)
  ·
    refine ⟨114479466927737553059838383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305278578473966808159569021 114479466927737553059838383)
    ·
      refine ⟨171719200391606329589757575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114479466927737553059838383 171719200391606329589757575)
      ·
        refine ⟨257578800587409494384636363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171719200391606329589757575 257578800587409494384636363)
        ·
          refine ⟨386368200881114241576954545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257578800587409494384636363 386368200881114241576954545)
          ·
            refine ⟨289776150660835681182715909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386368200881114241576954545 289776150660835681182715909)
            ·
              refine ⟨54333028248906690221759233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 289776150660835681182715909 54333028248906690221759233)
              ·
                refine ⟨40749771186680017666319425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54333028248906690221759233 40749771186680017666319425)
                ·
                  refine ⟨30562328390010013249739569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40749771186680017666319425 30562328390010013249739569)
                  ·
                    refine ⟨22921746292507509937304677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30562328390010013249739569 22921746292507509937304677)
                    ·
                      refine ⟨4297827429845158113244627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22921746292507509937304677 4297827429845158113244627)
                      ·
                        rfl

theorem cell23_8369989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 2, 4].length) (baseStart_8369989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8369989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8369989 prefixEnd_8369989 := by exact prefixLift 8369989
  have htrace : WordTrace (prefixWord ++ tailWord_8369989) baseStart_8369989 baseEnd_8369989 := by
    simpa [prefixWord, tailWord_8369989, baseEnd_8369989] using wordTrace_append hprefix tailTrace_8369989
  have hstable : (prefixWord ++ tailWord_8369989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8369989).length < 2 ^ (prefixWord ++ tailWord_8369989).sum := by decide
  have hdescent : baseEnd_8369989 < baseStart_8369989 := by decide
  rcases family_descends (prefixWord ++ tailWord_8369989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8370110 : List Nat := [4, 2, 1, 1, 1, 5, 1, 1, 3, 4]
def baseStart_8370110 : Nat := 118140960795 + 8370110 * 2 ^ 59
def prefixEnd_8370110 : Nat := 4983230072969 + 3 ^ 40 * 8370110 * 2
def baseEnd_8370110 : Nat := 1432629853668117379943857

theorem tailTrace_8370110 : CollatzResearch.WordTrace tailWord_8370110 prefixEnd_8370110 1432629853668117379943857 := by
  unfold tailWord_8370110
  simp only [CollatzResearch.WordTrace]
  refine ⟨38160373963316055728090473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203521994471018963883149189 38160373963316055728090473)
  ·
    refine ⟨28620280472487041796067855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38160373963316055728090473 28620280472487041796067855)
    ·
      refine ⟨42930420708730562694101783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28620280472487041796067855 42930420708730562694101783)
      ·
        refine ⟨64395631063095844041152675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42930420708730562694101783 64395631063095844041152675)
        ·
          refine ⟨96593446594643766061729013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64395631063095844041152675 96593446594643766061729013)
          ·
            refine ⟨9055635618247853068287095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96593446594643766061729013 9055635618247853068287095)
            ·
              refine ⟨13583453427371779602430643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9055635618247853068287095 13583453427371779602430643)
              ·
                refine ⟨20375180141057669403645965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13583453427371779602430643 20375180141057669403645965)
                ·
                  refine ⟨7640692552896626026367237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20375180141057669403645965 7640692552896626026367237)
                  ·
                    refine ⟨1432629853668117379943857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7640692552896626026367237 1432629853668117379943857)
                    ·
                      rfl

theorem cell23_8370110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_8370110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370110 prefixEnd_8370110 := by exact prefixLift 8370110
  have htrace : WordTrace (prefixWord ++ tailWord_8370110) baseStart_8370110 baseEnd_8370110 := by
    simpa [prefixWord, tailWord_8370110, baseEnd_8370110] using wordTrace_append hprefix tailTrace_8370110
  have hstable : (prefixWord ++ tailWord_8370110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370110).length < 2 ^ (prefixWord ++ tailWord_8370110).sum := by decide
  have hdescent : baseEnd_8370110 < baseStart_8370110 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8370119 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 2, 9]
def baseStart_8370119 : Nat := 118140960795 + 8370119 * 2 ^ 59
def prefixEnd_8370119 : Nat := 4983230072969 + 3 ^ 40 * 8370119 * 2
def baseEnd_8370119 : Nat := 1432631394110080868206343

theorem tailTrace_8370119 : CollatzResearch.WordTrace tailWord_8370119 prefixEnd_8370119 1432631394110080868206343 := by
  unfold tailWord_8370119
  simp only [CollatzResearch.WordTrace]
  refine ⟨305283319963495840361801411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203522213308997226907867607 305283319963495840361801411)
  ·
    refine ⟨457924979945243760542702117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305283319963495840361801411 457924979945243760542702117)
    ·
      refine ⟨85860933739733205101756647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 457924979945243760542702117 85860933739733205101756647)
      ·
        refine ⟨128791400609599807652634971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85860933739733205101756647 128791400609599807652634971)
        ·
          refine ⟨193187100914399711478952457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128791400609599807652634971 193187100914399711478952457)
          ·
            refine ⟨144890325685799783609214343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193187100914399711478952457 144890325685799783609214343)
            ·
              refine ⟨217335488528699675413821515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144890325685799783609214343 217335488528699675413821515)
              ·
                refine ⟨326003232793049513120732273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217335488528699675413821515 326003232793049513120732273)
                ·
                  refine ⟨244502424594787134840549205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 326003232793049513120732273 244502424594787134840549205)
                  ·
                    refine ⟨1432631394110080868206343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 244502424594787134840549205 1432631394110080868206343)
                    ·
                      rfl

theorem cell23_8370119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_8370119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370119 prefixEnd_8370119 := by exact prefixLift 8370119
  have htrace : WordTrace (prefixWord ++ tailWord_8370119) baseStart_8370119 baseEnd_8370119 := by
    simpa [prefixWord, tailWord_8370119, baseEnd_8370119] using wordTrace_append hprefix tailTrace_8370119
  have hstable : (prefixWord ++ tailWord_8370119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370119).length < 2 ^ (prefixWord ++ tailWord_8370119).sum := by decide
  have hdescent : baseEnd_8370119 < baseStart_8370119 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8370129 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 1, 3, 7]
def baseStart_8370129 : Nat := 118140960795 + 8370129 * 2 ^ 59
def prefixEnd_8370129 : Nat := 4983230072969 + 3 ^ 40 * 8370129 * 2
def baseEnd_8370129 : Nat := 4297899317136787565493983

theorem tailTrace_8370129 : CollatzResearch.WordTrace tailWord_8370129 prefixEnd_8370129 4297899317136787565493983 := by
  unfold tailWord_8370129
  simp only [CollatzResearch.WordTrace]
  refine ⟨305283684693459612069665441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203522456462306408046443627 305283684693459612069665441)
  ·
    refine ⟨228962763520094709052249081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305283684693459612069665441 228962763520094709052249081)
    ·
      refine ⟨171722072640071031789186811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228962763520094709052249081 171722072640071031789186811)
      ·
        refine ⟨257583108960106547683780217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171722072640071031789186811 257583108960106547683780217)
        ·
          refine ⟨193187331720079910762835163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257583108960106547683780217 193187331720079910762835163)
          ·
            refine ⟨289780997580119866144252745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193187331720079910762835163 289780997580119866144252745)
            ·
              refine ⟨217335748185089899608189559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289780997580119866144252745 217335748185089899608189559)
              ·
                refine ⟨326003622277634849412284339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217335748185089899608189559 326003622277634849412284339)
                ·
                  refine ⟨489005433416452274118426509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 326003622277634849412284339 489005433416452274118426509)
                  ·
                    refine ⟨183377037531169602794409941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 489005433416452274118426509 183377037531169602794409941)
                    ·
                      refine ⟨4297899317136787565493983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 183377037531169602794409941 4297899317136787565493983)
                      ·
                        rfl

theorem cell23_8370129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_8370129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370129 prefixEnd_8370129 := by exact prefixLift 8370129
  have htrace : WordTrace (prefixWord ++ tailWord_8370129) baseStart_8370129 baseEnd_8370129 := by
    simpa [prefixWord, tailWord_8370129, baseEnd_8370129] using wordTrace_append hprefix tailTrace_8370129
  have hstable : (prefixWord ++ tailWord_8370129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370129).length < 2 ^ (prefixWord ++ tailWord_8370129).sum := by decide
  have hdescent : baseEnd_8370129 < baseStart_8370129 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8370136 : List Nat := [2, 1, 2, 2, 2, 2, 3, 1, 3, 5]
def baseStart_8370136 : Nat := 118140960795 + 8370136 * 2 ^ 59
def prefixEnd_8370136 : Nat := 4983230072969 + 3 ^ 40 * 8370136 * 2
def baseEnd_8370136 : Nat := 1432634303833789679368817

theorem tailTrace_8370136 : CollatzResearch.WordTrace tailWord_8370136 prefixEnd_8370136 1432634303833789679368817 := by
  unfold tailWord_8370136
  simp only [CollatzResearch.WordTrace]
  refine ⟨152641970002217126132585131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203522626669622834843446841 152641970002217126132585131)
  ·
    refine ⟨228962955003325689198877697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152641970002217126132585131 228962955003325689198877697)
    ·
      refine ⟨171722216252494266899158273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228962955003325689198877697 171722216252494266899158273)
      ·
        refine ⟨128791662189370700174368705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171722216252494266899158273 128791662189370700174368705)
        ·
          refine ⟨96593746642028025130776529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128791662189370700174368705 96593746642028025130776529)
          ·
            refine ⟨72445309981521018848082397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96593746642028025130776529 72445309981521018848082397)
            ·
              refine ⟨27166991243070382068030899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72445309981521018848082397 27166991243070382068030899)
              ·
                refine ⟨40750486864605573102046349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27166991243070382068030899 40750486864605573102046349)
                ·
                  refine ⟨15281432574227089913267381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40750486864605573102046349 15281432574227089913267381)
                  ·
                    refine ⟨1432634303833789679368817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15281432574227089913267381 1432634303833789679368817)
                    ·
                      rfl

theorem cell23_8370136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 3, 5].length) (baseStart_8370136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370136 prefixEnd_8370136 := by exact prefixLift 8370136
  have htrace : WordTrace (prefixWord ++ tailWord_8370136) baseStart_8370136 baseEnd_8370136 := by
    simpa [prefixWord, tailWord_8370136, baseEnd_8370136] using wordTrace_append hprefix tailTrace_8370136
  have hstable : (prefixWord ++ tailWord_8370136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370136).length < 2 ^ (prefixWord ++ tailWord_8370136).sum := by decide
  have hdescent : baseEnd_8370136 < baseStart_8370136 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8370183 : List Nat := [1, 1, 4, 3, 1, 3, 2, 1, 1, 6]
def baseStart_8370183 : Nat := 118140960795 + 8370183 * 2 ^ 59
def prefixEnd_8370183 : Nat := 4983230072969 + 3 ^ 40 * 8370183 * 2
def baseEnd_8370183 : Nat := 1432642348364043451406245

theorem tailTrace_8370183 : CollatzResearch.WordTrace tailWord_8370183 prefixEnd_8370183 1432642348364043451406245 := by
  unfold tailWord_8370183
  simp only [CollatzResearch.WordTrace]
  refine ⟨305285654235263979292131203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203523769490175986194754135 305285654235263979292131203)
  ·
    refine ⟨457928481352895968938196805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305285654235263979292131203 457928481352895968938196805)
    ·
      refine ⟨85861590253667994175911901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 457928481352895968938196805 85861590253667994175911901)
      ·
        refine ⟨32198096345125497815966963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85861590253667994175911901 32198096345125497815966963)
        ·
          refine ⟨48297144517688246723950445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32198096345125497815966963 48297144517688246723950445)
          ·
            refine ⟨18111429194133092521481417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48297144517688246723950445 18111429194133092521481417)
            ·
              refine ⟨13583571895599819391111063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18111429194133092521481417 13583571895599819391111063)
              ·
                refine ⟨20375357843399729086666595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13583571895599819391111063 20375357843399729086666595)
                ·
                  refine ⟨30563036765099593629999893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20375357843399729086666595 30563036765099593629999893)
                  ·
                    refine ⟨1432642348364043451406245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30563036765099593629999893 1432642348364043451406245)
                    ·
                      rfl

theorem cell23_8370183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 6].length) (baseStart_8370183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370183 prefixEnd_8370183 := by exact prefixLift 8370183
  have htrace : WordTrace (prefixWord ++ tailWord_8370183) baseStart_8370183 baseEnd_8370183 := by
    simpa [prefixWord, tailWord_8370183, baseEnd_8370183] using wordTrace_append hprefix tailTrace_8370183
  have hstable : (prefixWord ++ tailWord_8370183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370183).length < 2 ^ (prefixWord ++ tailWord_8370183).sum := by decide
  have hdescent : baseEnd_8370183 < baseStart_8370183 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8370210 : List Nat := [3, 3, 1, 1, 1, 2, 3, 3, 1, 2, 3]
def baseStart_8370210 : Nat := 118140960795 + 8370210 * 2 ^ 59
def prefixEnd_8370210 : Nat := 4983230072969 + 3 ^ 40 * 8370210 * 2
def baseEnd_8370210 : Nat := 4297940909069801748581111

theorem tailTrace_8370210 : CollatzResearch.WordTrace tailWord_8370210 prefixEnd_8370210 4297940909069801748581111 := by
  unfold tailWord_8370210
  simp only [CollatzResearch.WordTrace]
  refine ⟨76321659751541540725841021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203524426004110775268909389 76321659751541540725841021)
  ·
    refine ⟨28620622406828077772190383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76321659751541540725841021 28620622406828077772190383)
    ·
      refine ⟨42930933610242116658285575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28620622406828077772190383 42930933610242116658285575)
      ·
        refine ⟨64396400415363174987428363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42930933610242116658285575 64396400415363174987428363)
        ·
          refine ⟨96594600623044762481142545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64396400415363174987428363 96594600623044762481142545)
          ·
            refine ⟨72445950467283571860856909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96594600623044762481142545 72445950467283571860856909)
            ·
              refine ⟨27167231425231339447821341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72445950467283571860856909 27167231425231339447821341)
              ·
                refine ⟨10187711784461752292933003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27167231425231339447821341 10187711784461752292933003)
                ·
                  refine ⟨15281567676692628439399505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10187711784461752292933003 15281567676692628439399505)
                  ·
                    refine ⟨11461175757519471329549629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15281567676692628439399505 11461175757519471329549629)
                    ·
                      refine ⟨4297940909069801748581111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11461175757519471329549629 4297940909069801748581111)
                      ·
                        rfl

theorem cell23_8370210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_8370210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370210 prefixEnd_8370210 := by exact prefixLift 8370210
  have htrace : WordTrace (prefixWord ++ tailWord_8370210) baseStart_8370210 baseEnd_8370210 := by
    simpa [prefixWord, tailWord_8370210, baseEnd_8370210] using wordTrace_append hprefix tailTrace_8370210
  have hstable : (prefixWord ++ tailWord_8370210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370210).length < 2 ^ (prefixWord ++ tailWord_8370210).sum := by decide
  have hdescent : baseEnd_8370210 < baseStart_8370210 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8370240 : List Nat := [2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 3]
def baseStart_8370240 : Nat := 118140960795 + 8370240 * 2 ^ 59
def prefixEnd_8370240 : Nat := 4983230072969 + 3 ^ 40 * 8370240 * 2
def baseEnd_8370240 : Nat := 4297956313489436631205973

theorem tailTrace_8370240 : CollatzResearch.WordTrace tailWord_8370240 prefixEnd_8370240 4297956313489436631205973 := by
  unfold tailWord_8370240
  simp only [CollatzResearch.WordTrace]
  refine ⟨152643866598028739013478087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203525155464038318684637449 152643866598028739013478087)
  ·
    refine ⟨228965799897043108520217131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152643866598028739013478087 228965799897043108520217131)
    ·
      refine ⟨343448699845564662780325697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228965799897043108520217131 343448699845564662780325697)
      ·
        refine ⟨257586524884173497085244273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343448699845564662780325697 257586524884173497085244273)
        ·
          refine ⟨193189893663130122813933205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257586524884173497085244273 193189893663130122813933205)
          ·
            refine ⟨9055776265459224506903119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 193189893663130122813933205 9055776265459224506903119)
            ·
              refine ⟨13583664398188836760354679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9055776265459224506903119 13583664398188836760354679)
              ·
                refine ⟨20375496597283255140532019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13583664398188836760354679 20375496597283255140532019)
                ·
                  refine ⟨30563244895924882710798029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20375496597283255140532019 30563244895924882710798029)
                  ·
                    refine ⟨11461216835971831016549261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30563244895924882710798029 11461216835971831016549261)
                    ·
                      refine ⟨4297956313489436631205973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11461216835971831016549261 4297956313489436631205973)
                      ·
                        rfl

theorem cell23_8370240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 3].length) (baseStart_8370240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370240 prefixEnd_8370240 := by exact prefixLift 8370240
  have htrace : WordTrace (prefixWord ++ tailWord_8370240) baseStart_8370240 baseEnd_8370240 := by
    simpa [prefixWord, tailWord_8370240, baseEnd_8370240] using wordTrace_append hprefix tailTrace_8370240
  have hstable : (prefixWord ++ tailWord_8370240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370240).length < 2 ^ (prefixWord ++ tailWord_8370240).sum := by decide
  have hdescent : baseEnd_8370240 < baseStart_8370240 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8370253 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 1, 4, 5]
def baseStart_8370253 : Nat := 118140960795 + 8370253 * 2 ^ 59
def prefixEnd_8370253 : Nat := 4983230072969 + 3 ^ 40 * 8370253 * 2
def baseEnd_8370253 : Nat := 4297962988737945080343413

theorem tailTrace_8370253 : CollatzResearch.WordTrace tailWord_8370253 prefixEnd_8370253 4297962988737945080343413 := by
  unfold tailWord_8370253
  simp only [CollatzResearch.WordTrace]
  refine ⟨305288207345010381247179413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203525471563340254164786275 305288207345010381247179413)
  ·
    refine ⟨14310384719297361620961535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 305288207345010381247179413 14310384719297361620961535)
    ·
      refine ⟨21465577078946042431442303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14310384719297361620961535 21465577078946042431442303)
      ·
        refine ⟨32198365618419063647163455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21465577078946042431442303 32198365618419063647163455)
        ·
          refine ⟨48297548427628595470745183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32198365618419063647163455 48297548427628595470745183)
          ·
            refine ⟨72446322641442893206117775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48297548427628595470745183 72446322641442893206117775)
            ·
              refine ⟨108669483962164339809176663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72446322641442893206117775 108669483962164339809176663)
              ·
                refine ⟨163004225943246509713764995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108669483962164339809176663 163004225943246509713764995)
                ·
                  refine ⟨244506338914869764570647493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163004225943246509713764995 244506338914869764570647493)
                  ·
                    refine ⟨45844938546538080856996405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 244506338914869764570647493 45844938546538080856996405)
                    ·
                      refine ⟨4297962988737945080343413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45844938546538080856996405 4297962988737945080343413)
                      ·
                        rfl

theorem cell23_8370253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_8370253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370253 prefixEnd_8370253 := by exact prefixLift 8370253
  have htrace : WordTrace (prefixWord ++ tailWord_8370253) baseStart_8370253 baseEnd_8370253 := by
    simpa [prefixWord, tailWord_8370253, baseEnd_8370253] using wordTrace_append hprefix tailTrace_8370253
  have hstable : (prefixWord ++ tailWord_8370253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370253).length < 2 ^ (prefixWord ++ tailWord_8370253).sum := by decide
  have hdescent : baseEnd_8370253 < baseStart_8370253 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8370258 : List Nat := [3, 2, 2, 1, 5, 1, 1, 3, 1, 2, 2]
def baseStart_8370258 : Nat := 118140960795 + 8370258 * 2 ^ 59
def prefixEnd_8370258 : Nat := 4983230072969 + 3 ^ 40 * 8370258 * 2
def baseEnd_8370258 : Nat := 4297965556141217560780891

theorem tailTrace_8370258 : CollatzResearch.WordTrace tailWord_8370258 prefixEnd_8370258 4297965556141217560780891 := by
  unfold tailWord_8370258
  simp only [CollatzResearch.WordTrace]
  refine ⟨76322097427498066775277857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203525593139994844734074285 76322097427498066775277857)
  ·
    refine ⟨57241573070623550081458393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76322097427498066775277857 57241573070623550081458393)
    ·
      refine ⟨42931179802967662561093795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57241573070623550081458393 42931179802967662561093795)
      ·
        refine ⟨64396769704451493841640693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42931179802967662561093795 64396769704451493841640693)
        ·
          refine ⟨6037197159792327547653815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64396769704451493841640693 6037197159792327547653815)
          ·
            refine ⟨9055795739688491321480723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6037197159792327547653815 9055795739688491321480723)
            ·
              refine ⟨13583693609532736982221085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9055795739688491321480723 13583693609532736982221085)
              ·
                refine ⟨5093885103574776368332907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13583693609532736982221085 5093885103574776368332907)
                ·
                  refine ⟨7640827655362164552499361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5093885103574776368332907 7640827655362164552499361)
                  ·
                    refine ⟨5730620741521623414374521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7640827655362164552499361 5730620741521623414374521)
                    ·
                      refine ⟨4297965556141217560780891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5730620741521623414374521 4297965556141217560780891)
                      ·
                        rfl

theorem cell23_8370258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 3, 1, 2, 2].length) (baseStart_8370258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370258 prefixEnd_8370258 := by exact prefixLift 8370258
  have htrace : WordTrace (prefixWord ++ tailWord_8370258) baseStart_8370258 baseEnd_8370258 := by
    simpa [prefixWord, tailWord_8370258, baseEnd_8370258] using wordTrace_append hprefix tailTrace_8370258
  have hstable : (prefixWord ++ tailWord_8370258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370258).length < 2 ^ (prefixWord ++ tailWord_8370258).sum := by decide
  have hdescent : baseEnd_8370258 < baseStart_8370258 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8370326 : List Nat := [5, 3, 2, 1, 2, 1, 2, 2, 1, 2, 2]
def baseStart_8370326 : Nat := 118140960795 + 8370326 * 2 ^ 59
def prefixEnd_8370326 : Nat := 4983230072969 + 3 ^ 40 * 8370326 * 2
def baseEnd_8370326 : Nat := 4298000472825723294730579

theorem tailTrace_8370326 : CollatzResearch.WordTrace tailWord_8370326 prefixEnd_8370326 4298000472825723294730579 := by
  unfold tailWord_8370326
  simp only [CollatzResearch.WordTrace]
  refine ⟨19080679367109119669661677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203527246582497276476391221 19080679367109119669661677)
  ·
    refine ⟨7155254762665919876123129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19080679367109119669661677 7155254762665919876123129)
    ·
      refine ⟨5366441071999439907092347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7155254762665919876123129 5366441071999439907092347)
      ·
        refine ⟨8049661607999159860638521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5366441071999439907092347 8049661607999159860638521)
        ·
          refine ⟨6037246205999369895478891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8049661607999159860638521 6037246205999369895478891)
          ·
            refine ⟨9055869308999054843218337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6037246205999369895478891 9055869308999054843218337)
            ·
              refine ⟨6791901981749291132413753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9055869308999054843218337 6791901981749291132413753)
              ·
                refine ⟨5093926486311968349310315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6791901981749291132413753 5093926486311968349310315)
                ·
                  refine ⟨7640889729467952523965473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5093926486311968349310315 7640889729467952523965473)
                  ·
                    refine ⟨5730667297100964392974105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7640889729467952523965473 5730667297100964392974105)
                    ·
                      refine ⟨4298000472825723294730579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5730667297100964392974105 4298000472825723294730579)
                      ·
                        rfl

theorem cell23_8370326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_8370326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370326 prefixEnd_8370326 := by exact prefixLift 8370326
  have htrace : WordTrace (prefixWord ++ tailWord_8370326) baseStart_8370326 baseEnd_8370326 := by
    simpa [prefixWord, tailWord_8370326, baseEnd_8370326] using wordTrace_append hprefix tailTrace_8370326
  have hstable : (prefixWord ++ tailWord_8370326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370326).length < 2 ^ (prefixWord ++ tailWord_8370326).sum := by decide
  have hdescent : baseEnd_8370326 < baseStart_8370326 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8370337 : List Nat := [1, 2, 3, 3, 1, 2, 4, 2, 5]
def baseStart_8370337 : Nat := 118140960795 + 8370337 * 2 ^ 59
def prefixEnd_8370337 : Nat := 4983230072969 + 3 ^ 40 * 8370337 * 2
def baseEnd_8370337 : Nat := 477556235679213639077003

theorem tailTrace_8370337 : CollatzResearch.WordTrace tailWord_8370337 prefixEnd_8370337 477556235679213639077003 := by
  unfold tailWord_8370337
  simp only [CollatzResearch.WordTrace]
  refine ⟨305291271076706063593237265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203527514051137375728824843 305291271076706063593237265)
  ·
    refine ⟨228968453307529547694927949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305291271076706063593237265 228968453307529547694927949)
    ·
      refine ⟨85863169990323580385597981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228968453307529547694927949 85863169990323580385597981)
      ·
        refine ⟨32198688746371342644599243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85863169990323580385597981 32198688746371342644599243)
        ·
          refine ⟨48298033119557013966898865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32198688746371342644599243 48298033119557013966898865)
          ·
            refine ⟨36223524839667760475174149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48298033119557013966898865 36223524839667760475174149)
            ·
              refine ⟨6791910907437705089095153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36223524839667760475174149 6791910907437705089095153)
              ·
                refine ⟨5093933180578278816821365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6791910907437705089095153 5093933180578278816821365)
                ·
                  refine ⟨477556235679213639077003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5093933180578278816821365 477556235679213639077003)
                  ·
                    rfl

theorem cell23_8370337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 2, 5].length) (baseStart_8370337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370337 prefixEnd_8370337 := by exact prefixLift 8370337
  have htrace : WordTrace (prefixWord ++ tailWord_8370337) baseStart_8370337 baseEnd_8370337 := by
    simpa [prefixWord, tailWord_8370337, baseEnd_8370337] using wordTrace_append hprefix tailTrace_8370337
  have hstable : (prefixWord ++ tailWord_8370337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370337).length < 2 ^ (prefixWord ++ tailWord_8370337).sum := by decide
  have hdescent : baseEnd_8370337 < baseStart_8370337 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8370397 : List Nat := [1, 4, 3, 2, 1, 1, 1, 3, 3, 4]
def baseStart_8370397 : Nat := 118140960795 + 8370397 * 2 ^ 59
def prefixEnd_8370397 : Nat := 4983230072969 + 3 ^ 40 * 8370397 * 2
def baseEnd_8370397 : Nat := 1432678976650730838980917

theorem tailTrace_8370397 : CollatzResearch.WordTrace tailWord_8370397 prefixEnd_8370397 1432678976650730838980917 := by
  unfold tailWord_8370397
  simp only [CollatzResearch.WordTrace]
  refine ⟨305293459456488693840421445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203528972970992462560280963 305293459456488693840421445)
  ·
    refine ⟨57242523648091630095079021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305293459456488693840421445 57242523648091630095079021)
    ·
      refine ⟨21465946368034361285654633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57242523648091630095079021 21465946368034361285654633)
      ·
        refine ⟨16099459776025770964240975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21465946368034361285654633 16099459776025770964240975)
        ·
          refine ⟨24149189664038656446361463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16099459776025770964240975 24149189664038656446361463)
          ·
            refine ⟨36223784496057984669542195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24149189664038656446361463 36223784496057984669542195)
            ·
              refine ⟨54335676744086977004313293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36223784496057984669542195 54335676744086977004313293)
              ·
                refine ⟨20375878779032616376617485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54335676744086977004313293 20375878779032616376617485)
                ·
                  refine ⟨7640954542137231141231557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20375878779032616376617485 7640954542137231141231557)
                  ·
                    refine ⟨1432678976650730838980917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7640954542137231141231557 1432678976650730838980917)
                    ·
                      rfl

theorem cell23_8370397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_8370397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370397 prefixEnd_8370397 := by exact prefixLift 8370397
  have htrace : WordTrace (prefixWord ++ tailWord_8370397) baseStart_8370397 baseEnd_8370397 := by
    simpa [prefixWord, tailWord_8370397, baseEnd_8370397] using wordTrace_append hprefix tailTrace_8370397
  have hstable : (prefixWord ++ tailWord_8370397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370397).length < 2 ^ (prefixWord ++ tailWord_8370397).sum := by decide
  have hdescent : baseEnd_8370397 < baseStart_8370397 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8370460 : List Nat := [2, 2, 3, 1, 1, 1, 1, 4, 3, 1, 4]
def baseStart_8370460 : Nat := 118140960795 + 8370460 * 2 ^ 59
def prefixEnd_8370460 : Nat := 4983230072969 + 3 ^ 40 * 8370460 * 2
def baseEnd_8370460 : Nat := 4298069279233425770454961

theorem tailTrace_8370460 : CollatzResearch.WordTrace tailWord_8370460 prefixEnd_8370460 4298069279233425770454961 := by
  unfold tailWord_8370460
  simp only [CollatzResearch.WordTrace]
  refine ⟨152647878627630227799982417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203530504836840303733309889 152647878627630227799982417)
  ·
    refine ⟨114485908970722670849986813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152647878627630227799982417 114485908970722670849986813)
    ·
      refine ⟨42932215864021001568745055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114485908970722670849986813 42932215864021001568745055)
      ·
        refine ⟨64398323796031502353117583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42932215864021001568745055 64398323796031502353117583)
        ·
          refine ⟨96597485694047253529676375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64398323796031502353117583 96597485694047253529676375)
          ·
            refine ⟨144896228541070880294514563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96597485694047253529676375 144896228541070880294514563)
            ·
              refine ⟨217344342811606320441771845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144896228541070880294514563 217344342811606320441771845)
              ·
                refine ⟨40752064277176185082832221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 217344342811606320441771845 40752064277176185082832221)
                ·
                  refine ⟨15282024103941069406062083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40752064277176185082832221 15282024103941069406062083)
                  ·
                    refine ⟨22923036155911604109093125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15282024103941069406062083 22923036155911604109093125)
                    ·
                      refine ⟨4298069279233425770454961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22923036155911604109093125 4298069279233425770454961)
                      ·
                        rfl

theorem cell23_8370460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_8370460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370460 prefixEnd_8370460 := by exact prefixLift 8370460
  have htrace : WordTrace (prefixWord ++ tailWord_8370460) baseStart_8370460 baseEnd_8370460 := by
    simpa [prefixWord, tailWord_8370460, baseEnd_8370460] using wordTrace_append hprefix tailTrace_8370460
  have hstable : (prefixWord ++ tailWord_8370460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370460).length < 2 ^ (prefixWord ++ tailWord_8370460).sum := by decide
  have hdescent : baseEnd_8370460 < baseStart_8370460 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8370461 : List Nat := [1, 4, 2, 3, 3, 1, 2, 1, 6]
def baseStart_8370461 : Nat := 118140960795 + 8370461 * 2 ^ 59
def prefixEnd_8370461 : Nat := 4983230072969 + 3 ^ 40 * 8370461 * 2
def baseEnd_8370461 : Nat := 477563310301564474060273

theorem tailTrace_8370461 : CollatzResearch.WordTrace tailWord_8370461 prefixEnd_8370461 477563310301564474060273 := by
  unfold tailWord_8370461
  simp only [CollatzResearch.WordTrace]
  refine ⟨305295793728256832770751237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203530529152171221847167491 305295793728256832770751237)
  ·
    refine ⟨57242961324048156144515857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305295793728256832770751237 57242961324048156144515857)
    ·
      refine ⟨42932220993036117108386893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57242961324048156144515857 42932220993036117108386893)
      ·
        refine ⟨16099582872388543915645085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42932220993036117108386893 16099582872388543915645085)
        ·
          refine ⟨6037343577145703968366907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16099582872388543915645085 6037343577145703968366907)
          ·
            refine ⟨9056015365718555952550361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6037343577145703968366907 9056015365718555952550361)
            ·
              refine ⟨6792011524288916964412771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9056015365718555952550361 6792011524288916964412771)
              ·
                refine ⟨10188017286433375446619157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6792011524288916964412771 10188017286433375446619157)
                ·
                  refine ⟨477563310301564474060273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10188017286433375446619157 477563310301564474060273)
                  ·
                    rfl

theorem cell23_8370461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 6].length) (baseStart_8370461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370461 prefixEnd_8370461 := by exact prefixLift 8370461
  have htrace : WordTrace (prefixWord ++ tailWord_8370461) baseStart_8370461 baseEnd_8370461 := by
    simpa [prefixWord, tailWord_8370461, baseEnd_8370461] using wordTrace_append hprefix tailTrace_8370461
  have hstable : (prefixWord ++ tailWord_8370461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370461).length < 2 ^ (prefixWord ++ tailWord_8370461).sum := by decide
  have hdescent : baseEnd_8370461 < baseStart_8370461 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8370473 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 1, 8, 4]
def baseStart_8370473 : Nat := 118140960795 + 8370473 * 2 ^ 59
def prefixEnd_8370473 : Nat := 4983230072969 + 3 ^ 40 * 8370473 * 2
def baseEnd_8370473 : Nat := 4298075954481934219592401

theorem tailTrace_8370473 : CollatzResearch.WordTrace tailWord_8370473 prefixEnd_8370473 4298075954481934219592401 := by
  unfold tailWord_8370473
  simp only [CollatzResearch.WordTrace]
  refine ⟨305296231404213358820188073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203530820936142239213458715 305296231404213358820188073)
  ·
    refine ⟨228972173553160019115141055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305296231404213358820188073 228972173553160019115141055)
    ·
      refine ⟨343458260329740028672711583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228972173553160019115141055 343458260329740028672711583)
      ·
        refine ⟨515187390494610043009067375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343458260329740028672711583 515187390494610043009067375)
        ·
          refine ⟨772781085741915064513601063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515187390494610043009067375 772781085741915064513601063)
          ·
            refine ⟨1159171628612872596770401595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 772781085741915064513601063 1159171628612872596770401595)
            ·
              refine ⟨1738757442919308895155602393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1159171628612872596770401595 1738757442919308895155602393)
              ·
                refine ⟨1304068082189481671366701795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1738757442919308895155602393 1304068082189481671366701795)
                ·
                  refine ⟨1956102123284222507050052693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1304068082189481671366701795 1956102123284222507050052693)
                  ·
                    refine ⟨22923071757236982504492805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1956102123284222507050052693 22923071757236982504492805)
                    ·
                      refine ⟨4298075954481934219592401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22923071757236982504492805 4298075954481934219592401)
                      ·
                        rfl

theorem cell23_8370473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 8, 4].length) (baseStart_8370473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370473 prefixEnd_8370473 := by exact prefixLift 8370473
  have htrace : WordTrace (prefixWord ++ tailWord_8370473) baseStart_8370473 baseEnd_8370473 := by
    simpa [prefixWord, tailWord_8370473, baseEnd_8370473] using wordTrace_append hprefix tailTrace_8370473
  have hstable : (prefixWord ++ tailWord_8370473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370473).length < 2 ^ (prefixWord ++ tailWord_8370473).sum := by decide
  have hdescent : baseEnd_8370473 < baseStart_8370473 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8370483 : List Nat := [1, 1, 1, 2, 5, 1, 1, 11]
def baseStart_8370483 : Nat := 118140960795 + 8370483 * 2 ^ 59
def prefixEnd_8370483 : Nat := 4983230072969 + 3 ^ 40 * 8370483 * 2
def baseEnd_8370483 : Nat := 159188188492165895572865

theorem tailTrace_8370483 : CollatzResearch.WordTrace tailWord_8370483 prefixEnd_8370483 159188188492165895572865 := by
  unfold tailWord_8370483
  simp only [CollatzResearch.WordTrace]
  refine ⟨305296596134177130528052103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203531064089451420352034735 305296596134177130528052103)
  ·
    refine ⟨457944894201265695792078155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305296596134177130528052103 457944894201265695792078155)
    ·
      refine ⟨686917341301898543688117233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457944894201265695792078155 686917341301898543688117233)
      ·
        refine ⟨515188005976423907766087925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 686917341301898543688117233 515188005976423907766087925)
        ·
          refine ⟨48298875560289741353070743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 515188005976423907766087925 48298875560289741353070743)
          ·
            refine ⟨72448313340434612029606115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48298875560289741353070743 72448313340434612029606115)
            ·
              refine ⟨108672470010651918044409173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72448313340434612029606115 108672470010651918044409173)
              ·
                refine ⟨159188188492165895572865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 108672470010651918044409173 159188188492165895572865)
                ·
                  rfl

theorem cell23_8370483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 11].length) (baseStart_8370483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370483 prefixEnd_8370483 := by exact prefixLift 8370483
  have htrace : WordTrace (prefixWord ++ tailWord_8370483) baseStart_8370483 baseEnd_8370483 := by
    simpa [prefixWord, tailWord_8370483, baseEnd_8370483] using wordTrace_append hprefix tailTrace_8370483
  have hstable : (prefixWord ++ tailWord_8370483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370483).length < 2 ^ (prefixWord ++ tailWord_8370483).sum := by decide
  have hdescent : baseEnd_8370483 < baseStart_8370483 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8370490 : List Nat := [3, 1, 1, 1, 4, 2, 1, 1, 3, 2, 4]
def baseStart_8370490 : Nat := 118140960795 + 8370490 * 2 ^ 59
def prefixEnd_8370490 : Nat := 4983230072969 + 3 ^ 40 * 8370490 * 2
def baseEnd_8370490 : Nat := 4298084683653060653079823

theorem tailTrace_8370490 : CollatzResearch.WordTrace tailWord_8370490 prefixEnd_8370490 4298084683653060653079823 := by
  unfold tailWord_8370490
  simp only [CollatzResearch.WordTrace]
  refine ⟨76324212861287942680889231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203531234296767847149037949 76324212861287942680889231)
  ·
    refine ⟨114486319291931914021333847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76324212861287942680889231 114486319291931914021333847)
    ·
      refine ⟨171729478937897871032000771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114486319291931914021333847 171729478937897871032000771)
      ·
        refine ⟨257594218406846806548001157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171729478937897871032000771 257594218406846806548001157)
        ·
          refine ⟨48298915951283776227750217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 257594218406846806548001157 48298915951283776227750217)
          ·
            refine ⟨36224186963462832170812663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48298915951283776227750217 36224186963462832170812663)
            ·
              refine ⟨54336280445194248256218995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36224186963462832170812663 54336280445194248256218995)
              ·
                refine ⟨81504420667791372384328493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54336280445194248256218995 81504420667791372384328493)
                ·
                  refine ⟨30564157750421764644123185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81504420667791372384328493 30564157750421764644123185)
                  ·
                    refine ⟨22923118312816323483092389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30564157750421764644123185 22923118312816323483092389)
                    ·
                      refine ⟨4298084683653060653079823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22923118312816323483092389 4298084683653060653079823)
                      ·
                        rfl

theorem cell23_8370490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 3, 2, 4].length) (baseStart_8370490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370490 prefixEnd_8370490 := by exact prefixLift 8370490
  have htrace : WordTrace (prefixWord ++ tailWord_8370490) baseStart_8370490 baseEnd_8370490 := by
    simpa [prefixWord, tailWord_8370490, baseEnd_8370490] using wordTrace_append hprefix tailTrace_8370490
  have hstable : (prefixWord ++ tailWord_8370490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370490).length < 2 ^ (prefixWord ++ tailWord_8370490).sum := by decide
  have hdescent : baseEnd_8370490 < baseStart_8370490 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8370500 : List Nat := [2, 3, 4, 1, 13]
def baseStart_8370500 : Nat := 118140960795 + 8370500 * 2 ^ 59
def prefixEnd_8370500 : Nat := 4983230072969 + 3 ^ 40 * 8370500 * 2
def baseEnd_8370500 : Nat := 5895870807214822515713

theorem tailTrace_8370500 : CollatzResearch.WordTrace tailWord_8370500 prefixEnd_8370500 5895870807214822515713 := by
  unfold tailWord_8370500
  simp only [CollatzResearch.WordTrace]
  refine ⟨152648608087557771215710477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203531477450077028287613969 152648608087557771215710477)
  ·
    refine ⟨57243228032834164205891429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152648608087557771215710477 57243228032834164205891429)
    ·
      refine ⟨10733105256156405788604643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57243228032834164205891429 10733105256156405788604643)
      ·
        refine ⟨16099657884234608682906965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10733105256156405788604643 16099657884234608682906965)
        ·
          refine ⟨5895870807214822515713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 16099657884234608682906965 5895870807214822515713)
          ·
            rfl

theorem cell23_8370500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 13].length) (baseStart_8370500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370500 prefixEnd_8370500 := by exact prefixLift 8370500
  have htrace : WordTrace (prefixWord ++ tailWord_8370500) baseStart_8370500 baseEnd_8370500 := by
    simpa [prefixWord, tailWord_8370500, baseEnd_8370500] using wordTrace_append hprefix tailTrace_8370500
  have hstable : (prefixWord ++ tailWord_8370500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370500).length < 2 ^ (prefixWord ++ tailWord_8370500).sum := by decide
  have hdescent : baseEnd_8370500 < baseStart_8370500 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8370517 : List Nat := [1, 3, 2, 2, 4, 2, 1, 8]
def baseStart_8370517 : Nat := 118140960795 + 8370517 * 2 ^ 59
def prefixEnd_8370517 : Nat := 4983230072969 + 3 ^ 40 * 8370517 * 2
def baseEnd_8370517 : Nat := 159188835097434520275637

theorem tailTrace_8370517 : CollatzResearch.WordTrace tailWord_8370517 prefixEnd_8370517 159188835097434520275637 := by
  unfold tailWord_8370517
  simp only [CollatzResearch.WordTrace]
  refine ⟨305297836216053954334789805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203531890810702636223193203 305297836216053954334789805)
  ·
    refine ⟨114486688581020232875546177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305297836216053954334789805 114486688581020232875546177)
    ·
      refine ⟨85865016435765174656659633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114486688581020232875546177 85865016435765174656659633)
      ·
        refine ⟨64398762326823880992494725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85865016435765174656659633 64398762326823880992494725)
        ·
          refine ⟨12074767936279477686092761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64398762326823880992494725 12074767936279477686092761)
          ·
            refine ⟨9056075952209608264569571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12074767936279477686092761 9056075952209608264569571)
            ·
              refine ⟨13584113928314412396854357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9056075952209608264569571 13584113928314412396854357)
              ·
                refine ⟨159188835097434520275637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13584113928314412396854357 159188835097434520275637)
                ·
                  rfl

theorem cell23_8370517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 8].length) (baseStart_8370517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370517 prefixEnd_8370517 := by exact prefixLift 8370517
  have htrace : WordTrace (prefixWord ++ tailWord_8370517) baseStart_8370517 baseEnd_8370517 := by
    simpa [prefixWord, tailWord_8370517, baseEnd_8370517] using wordTrace_append hprefix tailTrace_8370517
  have hstable : (prefixWord ++ tailWord_8370517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370517).length < 2 ^ (prefixWord ++ tailWord_8370517).sum := by decide
  have hdescent : baseEnd_8370517 < baseStart_8370517 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8370537 : List Nat := [1, 2, 1, 1, 1, 3, 3, 3, 3, 3, 2]
def baseStart_8370537 : Nat := 118140960795 + 8370537 * 2 ^ 59
def prefixEnd_8370537 : Nat := 4983230072969 + 3 ^ 40 * 8370537 * 2
def baseEnd_8370537 : Nat := 4298108817243821969192107

theorem tailTrace_8370537 : CollatzResearch.WordTrace tailWord_8370537 prefixEnd_8370537 4298108817243821969192107 := by
  unfold tailWord_8370537
  simp only [CollatzResearch.WordTrace]
  refine ⟨305298565675981497750517865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203532377117320998500345243 305298565675981497750517865)
  ·
    refine ⟨228973924256986123312888399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305298565675981497750517865 228973924256986123312888399)
    ·
      refine ⟨343460886385479184969332599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228973924256986123312888399 343460886385479184969332599)
      ·
        refine ⟨515191329578218777453998899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343460886385479184969332599 515191329578218777453998899)
        ·
          refine ⟨772786994367328166180998349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515191329578218777453998899 772786994367328166180998349)
          ·
            refine ⟨289795122887748062317874381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 772786994367328166180998349 289795122887748062317874381)
            ·
              refine ⟨108673171082905523369202893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 289795122887748062317874381 108673171082905523369202893)
              ·
                refine ⟨40752439156089571263451085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108673171082905523369202893 40752439156089571263451085)
                ·
                  refine ⟨15282164683533589223794157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40752439156089571263451085 15282164683533589223794157)
                  ·
                    refine ⟨5730811756325095958922809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15282164683533589223794157 5730811756325095958922809)
                    ·
                      refine ⟨4298108817243821969192107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5730811756325095958922809 4298108817243821969192107)
                      ·
                        rfl

theorem cell23_8370537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 3, 2].length) (baseStart_8370537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370537 prefixEnd_8370537 := by exact prefixLift 8370537
  have htrace : WordTrace (prefixWord ++ tailWord_8370537) baseStart_8370537 baseEnd_8370537 := by
    simpa [prefixWord, tailWord_8370537, baseEnd_8370537] using wordTrace_append hprefix tailTrace_8370537
  have hstable : (prefixWord ++ tailWord_8370537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370537).length < 2 ^ (prefixWord ++ tailWord_8370537).sum := by decide
  have hdescent : baseEnd_8370537 < baseStart_8370537 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8370561 : List Nat := [1, 2, 4, 3, 1, 1, 3, 2, 2, 1, 3]
def baseStart_8370561 : Nat := 118140960795 + 8370561 * 2 ^ 59
def prefixEnd_8370561 : Nat := 4983230072969 + 3 ^ 40 * 8370561 * 2
def baseEnd_8370561 : Nat := 4298121140779529875291997

theorem tailTrace_8370561 : CollatzResearch.WordTrace tailWord_8370561 prefixEnd_8370561 4298121140779529875291997 := by
  unfold tailWord_8370561
  simp only [CollatzResearch.WordTrace]
  refine ⟨305299441027894549849391537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203532960685263033232927691 305299441027894549849391537)
  ·
    refine ⟨228974580770920912387043653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305299441027894549849391537 228974580770920912387043653)
    ·
      refine ⟨42932733894547671072570685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228974580770920912387043653 42932733894547671072570685)
      ·
        refine ⟨16099775210455376652214007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42932733894547671072570685 16099775210455376652214007)
        ·
          refine ⟨24149662815683064978321011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16099775210455376652214007 24149662815683064978321011)
          ·
            refine ⟨36224494223524597467481517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24149662815683064978321011 36224494223524597467481517)
            ·
              refine ⟨13584185333821724050305569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36224494223524597467481517 13584185333821724050305569)
              ·
                refine ⟨10188139000366293037729177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13584185333821724050305569 10188139000366293037729177)
                ·
                  refine ⟨7641104250274719778296883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10188139000366293037729177 7641104250274719778296883)
                  ·
                    refine ⟨11461656375412079667445325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7641104250274719778296883 11461656375412079667445325)
                    ·
                      refine ⟨4298121140779529875291997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11461656375412079667445325 4298121140779529875291997)
                      ·
                        rfl

theorem cell23_8370561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_8370561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370561 prefixEnd_8370561 := by exact prefixLift 8370561
  have htrace : WordTrace (prefixWord ++ tailWord_8370561) baseStart_8370561 baseEnd_8370561 := by
    simpa [prefixWord, tailWord_8370561, baseEnd_8370561] using wordTrace_append hprefix tailTrace_8370561
  have hstable : (prefixWord ++ tailWord_8370561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370561).length < 2 ^ (prefixWord ++ tailWord_8370561).sum := by decide
  have hdescent : baseEnd_8370561 < baseStart_8370561 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8370627 : List Nat := [1, 1, 1, 3, 1, 1, 3, 3, 2, 5, 2]
def baseStart_8370627 : Nat := 118140960795 + 8370627 * 2 ^ 59
def prefixEnd_8370627 : Nat := 4983230072969 + 3 ^ 40 * 8370627 * 2
def baseEnd_8370627 : Nat := 4298155030502726617066693

theorem tailTrace_8370627 : CollatzResearch.WordTrace tailWord_8370627 prefixEnd_8370627 4298155030502726617066693 := by
  unfold tailWord_8370627
  simp only [CollatzResearch.WordTrace]
  refine ⟨305301848245655443121294135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203534565497103628747529423 305301848245655443121294135)
  ·
    refine ⟨457952772368483164681941203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305301848245655443121294135 457952772368483164681941203)
    ·
      refine ⟨686929158552724747022911805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457952772368483164681941203 686929158552724747022911805)
      ·
        refine ⟨257598434457271780133591927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 686929158552724747022911805 257598434457271780133591927)
        ·
          refine ⟨386397651685907670200387891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257598434457271780133591927 386397651685907670200387891)
          ·
            refine ⟨579596477528861505300581837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386397651685907670200387891 579596477528861505300581837)
            ·
              refine ⟨217348679073323064487718189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 579596477528861505300581837 217348679073323064487718189)
              ·
                refine ⟨81505754652496149182894321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217348679073323064487718189 81505754652496149182894321)
                ·
                  refine ⟨61129315989372111887170741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81505754652496149182894321 61129315989372111887170741)
                  ·
                    refine ⟨5730873374003635489422257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61129315989372111887170741 5730873374003635489422257)
                    ·
                      refine ⟨4298155030502726617066693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5730873374003635489422257 4298155030502726617066693)
                      ·
                        rfl

theorem cell23_8370627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 5, 2].length) (baseStart_8370627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370627 prefixEnd_8370627 := by exact prefixLift 8370627
  have htrace : WordTrace (prefixWord ++ tailWord_8370627) baseStart_8370627 baseEnd_8370627 := by
    simpa [prefixWord, tailWord_8370627, baseEnd_8370627] using wordTrace_append hprefix tailTrace_8370627
  have hstable : (prefixWord ++ tailWord_8370627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370627).length < 2 ^ (prefixWord ++ tailWord_8370627).sum := by decide
  have hdescent : baseEnd_8370627 < baseStart_8370627 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8370660 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 1, 2, 9]
def baseStart_8370660 : Nat := 118140960795 + 8370660 * 2 ^ 59
def prefixEnd_8370660 : Nat := 4983230072969 + 3 ^ 40 * 8370660 * 2
def baseEnd_8370660 : Nat := 4298171975364324987954041

theorem tailTrace_8370660 : CollatzResearch.WordTrace tailWord_8370660 prefixEnd_8370660 4298171975364324987954041 := by
  unfold tailWord_8370660
  simp only [CollatzResearch.WordTrace]
  refine ⟨152651525927267944878622717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203535367903023926504830289 152651525927267944878622717)
  ·
    refine ⟨57244322222725479329483519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152651525927267944878622717 57244322222725479329483519)
    ·
      refine ⟨85866483334088218994225279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57244322222725479329483519 85866483334088218994225279)
      ·
        refine ⟨128799725001132328491337919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85866483334088218994225279 128799725001132328491337919)
        ·
          refine ⟨193199587501698492737006879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128799725001132328491337919 193199587501698492737006879)
          ·
            refine ⟨289799381252547739105510319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193199587501698492737006879 289799381252547739105510319)
            ·
              refine ⟨434699071878821608658265479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289799381252547739105510319 434699071878821608658265479)
              ·
                refine ⟨652048607818232412987398219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434699071878821608658265479 652048607818232412987398219)
                ·
                  refine ⟨978072911727348619481097329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 652048607818232412987398219 978072911727348619481097329)
                  ·
                    refine ⟨733554683795511464610822997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 978072911727348619481097329 733554683795511464610822997)
                    ·
                      refine ⟨4298171975364324987954041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 733554683795511464610822997 4298171975364324987954041)
                      ·
                        rfl

theorem cell23_8370660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_8370660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370660 prefixEnd_8370660 := by exact prefixLift 8370660
  have htrace : WordTrace (prefixWord ++ tailWord_8370660) baseStart_8370660 baseEnd_8370660 := by
    simpa [prefixWord, tailWord_8370660, baseEnd_8370660] using wordTrace_append hprefix tailTrace_8370660
  have hstable : (prefixWord ++ tailWord_8370660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370660).length < 2 ^ (prefixWord ++ tailWord_8370660).sum := by decide
  have hdescent : baseEnd_8370660 < baseStart_8370660 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8370708 : List Nat := [2, 4, 3, 1, 1, 3, 1, 1, 2, 1, 4]
def baseStart_8370708 : Nat := 118140960795 + 8370708 * 2 ^ 59
def prefixEnd_8370708 : Nat := 4983230072969 + 3 ^ 40 * 8370708 * 2
def baseEnd_8370708 : Nat := 4298196622435740800153821

theorem tailTrace_8370708 : CollatzResearch.WordTrace tailWord_8370708 prefixEnd_8370708 4298196622435740800153821 := by
  unfold tailWord_8370708
  simp only [CollatzResearch.WordTrace]
  refine ⟨152652401279180996977496389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203536535038907995969995185 152652401279180996977496389)
  ·
    refine ⟨28622325239846436933280573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152652401279180996977496389 28622325239846436933280573)
    ·
      refine ⟨10733371964942413849980215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28622325239846436933280573 10733371964942413849980215)
      ·
        refine ⟨16100057947413620774970323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10733371964942413849980215 16100057947413620774970323)
        ·
          refine ⟨24150086921120431162455485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16100057947413620774970323 24150086921120431162455485)
          ·
            refine ⟨9056282595420161685920807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24150086921120431162455485 9056282595420161685920807)
            ·
              refine ⟨13584423893130242528881211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9056282595420161685920807 13584423893130242528881211)
              ·
                refine ⟨20376635839695363793321817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13584423893130242528881211 20376635839695363793321817)
                ·
                  refine ⟨15282476879771522844991363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20376635839695363793321817 15282476879771522844991363)
                  ·
                    refine ⟨22923715319657284267487045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15282476879771522844991363 22923715319657284267487045)
                    ·
                      refine ⟨4298196622435740800153821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22923715319657284267487045 4298196622435740800153821)
                      ·
                        rfl

theorem cell23_8370708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_8370708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370708 prefixEnd_8370708 := by exact prefixLift 8370708
  have htrace : WordTrace (prefixWord ++ tailWord_8370708) baseStart_8370708 baseEnd_8370708 := by
    simpa [prefixWord, tailWord_8370708, baseEnd_8370708] using wordTrace_append hprefix tailTrace_8370708
  have hstable : (prefixWord ++ tailWord_8370708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370708).length < 2 ^ (prefixWord ++ tailWord_8370708).sum := by decide
  have hdescent : baseEnd_8370708 < baseStart_8370708 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8370711 : List Nat := [1, 1, 3, 6, 1, 1, 1, 1, 1, 4, 3]
def baseStart_8370711 : Nat := 118140960795 + 8370711 * 2 ^ 59
def prefixEnd_8370711 : Nat := 4983230072969 + 3 ^ 40 * 8370711 * 2
def baseEnd_8370711 : Nat := 4298198162877704288416307

theorem tailTrace_8370711 : CollatzResearch.WordTrace tailWord_8370711 prefixEnd_8370711 4298198162877704288416307 := by
  unfold tailWord_8370711
  simp only [CollatzResearch.WordTrace]
  refine ⟨305304911977351125467351987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203536607984900750311567991 305304911977351125467351987)
  ·
    refine ⟨457957367966026688201027981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305304911977351125467351987 457957367966026688201027981)
    ·
      refine ⟨171734012987260008075385493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 457957367966026688201027981 171734012987260008075385493)
      ·
        refine ⟨8050031858777812878533695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 171734012987260008075385493 8050031858777812878533695)
        ·
          refine ⟨12075047788166719317800543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8050031858777812878533695 12075047788166719317800543)
          ·
            refine ⟨18112571682250078976700815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12075047788166719317800543 18112571682250078976700815)
            ·
              refine ⟨27168857523375118465051223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18112571682250078976700815 27168857523375118465051223)
              ·
                refine ⟨40753286285062677697576835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27168857523375118465051223 40753286285062677697576835)
                ·
                  refine ⟨61129929427594016546365253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40753286285062677697576835 61129929427594016546365253)
                  ·
                    refine ⟨11461861767673878102443485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61129929427594016546365253 11461861767673878102443485)
                    ·
                      refine ⟨4298198162877704288416307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11461861767673878102443485 4298198162877704288416307)
                      ·
                        rfl

theorem cell23_8370711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_8370711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370711 prefixEnd_8370711 := by exact prefixLift 8370711
  have htrace : WordTrace (prefixWord ++ tailWord_8370711) baseStart_8370711 baseEnd_8370711 := by
    simpa [prefixWord, tailWord_8370711, baseEnd_8370711] using wordTrace_append hprefix tailTrace_8370711
  have hstable : (prefixWord ++ tailWord_8370711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370711).length < 2 ^ (prefixWord ++ tailWord_8370711).sum := by decide
  have hdescent : baseEnd_8370711 < baseStart_8370711 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8370741 : List Nat := [1, 3, 3, 1, 1, 2, 4, 1, 3, 1, 3]
def baseStart_8370741 : Nat := 118140960795 + 8370741 * 2 ^ 59
def prefixEnd_8370741 : Nat := 4983230072969 + 3 ^ 40 * 8370741 * 2
def baseEnd_8370741 : Nat := 4298213567297339171041169

theorem tailTrace_8370741 : CollatzResearch.WordTrace tailWord_8370741 prefixEnd_8370741 4298213567297339171041169 := by
  unfold tailWord_8370741
  simp only [CollatzResearch.WordTrace]
  refine ⟨305306006167242440590944077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203537337444828293727296051 305306006167242440590944077)
  ·
    refine ⟨114489752312715915221604029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305306006167242440590944077 114489752312715915221604029)
    ·
      refine ⟨42933657117268468208101511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114489752312715915221604029 42933657117268468208101511)
      ·
        refine ⟨64400485675902702312152267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42933657117268468208101511 64400485675902702312152267)
        ·
          refine ⟨96600728513854053468228401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64400485675902702312152267 96600728513854053468228401)
          ·
            refine ⟨72450546385390540101171301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96600728513854053468228401 72450546385390540101171301)
            ·
              refine ⟨13584477447260726268969619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72450546385390540101171301 13584477447260726268969619)
              ·
                refine ⟨20376716170891089403454429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13584477447260726268969619 20376716170891089403454429)
                ·
                  refine ⟨7641268564084158526295411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20376716170891089403454429 7641268564084158526295411)
                  ·
                    refine ⟨11461902846126237789443117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7641268564084158526295411 11461902846126237789443117)
                    ·
                      refine ⟨4298213567297339171041169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11461902846126237789443117 4298213567297339171041169)
                      ·
                        rfl

theorem cell23_8370741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_8370741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370741 prefixEnd_8370741 := by exact prefixLift 8370741
  have htrace : WordTrace (prefixWord ++ tailWord_8370741) baseStart_8370741 baseEnd_8370741 := by
    simpa [prefixWord, tailWord_8370741, baseEnd_8370741] using wordTrace_append hprefix tailTrace_8370741
  have hstable : (prefixWord ++ tailWord_8370741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370741).length < 2 ^ (prefixWord ++ tailWord_8370741).sum := by decide
  have hdescent : baseEnd_8370741 < baseStart_8370741 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
