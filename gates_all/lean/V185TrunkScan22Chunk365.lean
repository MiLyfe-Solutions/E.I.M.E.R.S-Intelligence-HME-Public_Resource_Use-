import V185TrunkScan22Chunk364

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3255507 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 6, 4]
def baseStart_3255507 : Nat := 118140960795 + 3255507 * 2 ^ 59
def prefixEnd_3255507 : Nat := 4983230072969 + 3 ^ 40 * 3255507 * 2
def baseEnd_3255507 : Nat := 1114426576717799698393801

theorem tailTrace_3255507 : CollatzResearch.WordTrace tailWord_3255507 prefixEnd_3255507 1114426576717799698393801 := by
  unfold tailWord_3255507
  simp only [CollatzResearch.WordTrace]
  refine ⟨118738095016861610175580775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79158730011241073450387183 118738095016861610175580775)
  ·
    refine ⟨178107142525292415263371163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118738095016861610175580775 178107142525292415263371163)
    ·
      refine ⟨267160713787938622895056745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178107142525292415263371163 267160713787938622895056745)
      ·
        refine ⟨200370535340953967171292559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267160713787938622895056745 200370535340953967171292559)
        ·
          refine ⟨300555803011430950756938839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200370535340953967171292559 300555803011430950756938839)
          ·
            refine ⟨450833704517146426135408259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300555803011430950756938839 450833704517146426135408259)
            ·
              refine ⟨676250556775719639203112389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450833704517146426135408259 676250556775719639203112389)
              ·
                refine ⟨126796979395447432350583573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 676250556775719639203112389 126796979395447432350583573)
                ·
                  refine ⟨5943608409161598391433605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 126796979395447432350583573 5943608409161598391433605)
                  ·
                    refine ⟨1114426576717799698393801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5943608409161598391433605 1114426576717799698393801)
                    ·
                      rfl

theorem cell22_3255507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 4].length) (baseStart_3255507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3255507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3255507 prefixEnd_3255507 := by exact prefixLift 3255507
  have htrace : WordTrace (prefixWord ++ tailWord_3255507) baseStart_3255507 baseEnd_3255507 := by
    simpa [prefixWord, tailWord_3255507, baseEnd_3255507] using wordTrace_append hprefix tailTrace_3255507
  have hstable : (prefixWord ++ tailWord_3255507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255507).length < 2 ^ (prefixWord ++ tailWord_3255507).sum := by decide
  have hdescent : baseEnd_3255507 < baseStart_3255507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255509 : List Nat := [1, 3, 2, 4, 1, 1, 1, 1, 3, 5]
def baseStart_3255509 : Nat := 118140960795 + 3255509 * 2 ^ 59
def prefixEnd_3255509 : Nat := 4983230072969 + 3 ^ 40 * 3255509 * 2
def baseEnd_3255509 : Nat := 1114427261358672359843795

theorem tailTrace_3255509 : CollatzResearch.WordTrace tailWord_3255509 prefixEnd_3255509 1114427261358672359843795 := by
  unfold tailWord_3255509
  simp only [CollatzResearch.WordTrace]
  refine ⟨118738167962854364517153581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79158778641902909678102387 118738167962854364517153581)
  ·
    refine ⟨44526812986070386693932593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118738167962854364517153581 44526812986070386693932593)
    ·
      refine ⟨33395109739552790020449445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44526812986070386693932593 33395109739552790020449445)
      ·
        refine ⟨6261583076166148128834271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33395109739552790020449445 6261583076166148128834271)
        ·
          refine ⟨9392374614249222193251407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6261583076166148128834271 9392374614249222193251407)
          ·
            refine ⟨14088561921373833289877111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9392374614249222193251407 14088561921373833289877111)
            ·
              refine ⟨21132842882060749934815667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14088561921373833289877111 21132842882060749934815667)
              ·
                refine ⟨31699264323091124902223501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21132842882060749934815667 31699264323091124902223501)
                ·
                  refine ⟨11887224121159171838333813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31699264323091124902223501 11887224121159171838333813)
                  ·
                    refine ⟨1114427261358672359843795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11887224121159171838333813 1114427261358672359843795)
                    ·
                      rfl

theorem cell22_3255509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_3255509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3255509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3255509 prefixEnd_3255509 := by exact prefixLift 3255509
  have htrace : WordTrace (prefixWord ++ tailWord_3255509) baseStart_3255509 baseEnd_3255509 := by
    simpa [prefixWord, tailWord_3255509, baseEnd_3255509] using wordTrace_append hprefix tailTrace_3255509
  have hstable : (prefixWord ++ tailWord_3255509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255509).length < 2 ^ (prefixWord ++ tailWord_3255509).sum := by decide
  have hdescent : baseEnd_3255509 < baseStart_3255509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255524 : List Nat := [2, 3, 1, 1, 1, 2, 4, 2, 2, 4]
def baseStart_3255524 : Nat := 118140960795 + 3255524 * 2 ^ 59
def prefixEnd_3255524 : Nat := 4983230072969 + 3 ^ 40 * 3255524 * 2
def baseEnd_3255524 : Nat := 1114432396165217320718749

theorem tailTrace_3255524 : CollatzResearch.WordTrace tailWord_3255524 prefixEnd_3255524 1114432396165217320718749 := by
  unfold tailWord_3255524
  simp only [CollatzResearch.WordTrace]
  refine ⟨59369357528900011039474813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79159143371866681385966417 59369357528900011039474813)
  ·
    refine ⟨22263509073337504139803055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59369357528900011039474813 22263509073337504139803055)
    ·
      refine ⟨33395263610006256209704583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22263509073337504139803055 33395263610006256209704583)
      ·
        refine ⟨50092895415009384314556875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33395263610006256209704583 50092895415009384314556875)
        ·
          refine ⟨75139343122514076471835313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50092895415009384314556875 75139343122514076471835313)
          ·
            refine ⟨56354507341885557353876485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75139343122514076471835313 56354507341885557353876485)
            ·
              refine ⟨10566470126603542003851841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56354507341885557353876485 10566470126603542003851841)
              ·
                refine ⟨7924852594952656502888881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10566470126603542003851841 7924852594952656502888881)
                ·
                  refine ⟨5943639446214492377166661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7924852594952656502888881 5943639446214492377166661)
                  ·
                    refine ⟨1114432396165217320718749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5943639446214492377166661 1114432396165217320718749)
                    ·
                      rfl

theorem cell22_3255524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_3255524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3255524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3255524 prefixEnd_3255524 := by exact prefixLift 3255524
  have htrace : WordTrace (prefixWord ++ tailWord_3255524) baseStart_3255524 baseEnd_3255524 := by
    simpa [prefixWord, tailWord_3255524, baseEnd_3255524] using wordTrace_append hprefix tailTrace_3255524
  have hstable : (prefixWord ++ tailWord_3255524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255524).length < 2 ^ (prefixWord ++ tailWord_3255524).sum := by decide
  have hdescent : baseEnd_3255524 < baseStart_3255524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255537 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 2, 7]
def baseStart_3255537 : Nat := 118140960795 + 3255537 * 2 ^ 59
def prefixEnd_3255537 : Nat := 4983230072969 + 3 ^ 40 * 3255537 * 2
def baseEnd_3255537 : Nat := 1114436846330889620143709

theorem tailTrace_3255537 : CollatzResearch.WordTrace tailWord_3255537 prefixEnd_3255537 1114436846330889620143709 := by
  unfold tailWord_3255537
  simp only [CollatzResearch.WordTrace]
  refine ⟨118739189206752925299172865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79159459471168616866115243 118739189206752925299172865)
  ·
    refine ⟨89054391905064693974379649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118739189206752925299172865 89054391905064693974379649)
    ·
      refine ⟨66790793928798520480784737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89054391905064693974379649 66790793928798520480784737)
      ·
        refine ⟨50093095446598890360588553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66790793928798520480784737 50093095446598890360588553)
        ·
          refine ⟨37569821584949167770441415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50093095446598890360588553 37569821584949167770441415)
          ·
            refine ⟨56354732377423751655662123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37569821584949167770441415 56354732377423751655662123)
            ·
              refine ⟨84532098566135627483493185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56354732377423751655662123 84532098566135627483493185)
              ·
                refine ⟨63399073924601720612619889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84532098566135627483493185 63399073924601720612619889)
                ·
                  refine ⟨47549305443451290459464917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63399073924601720612619889 47549305443451290459464917)
                  ·
                    refine ⟨1114436846330889620143709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47549305443451290459464917 1114436846330889620143709)
                    ·
                      rfl

theorem cell22_3255537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_3255537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3255537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3255537 prefixEnd_3255537 := by exact prefixLift 3255537
  have htrace : WordTrace (prefixWord ++ tailWord_3255537) baseStart_3255537 baseEnd_3255537 := by
    simpa [prefixWord, tailWord_3255537, baseEnd_3255537] using wordTrace_append hprefix tailTrace_3255537
  have hstable : (prefixWord ++ tailWord_3255537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255537).length < 2 ^ (prefixWord ++ tailWord_3255537).sum := by decide
  have hdescent : baseEnd_3255537 < baseStart_3255537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255539 : List Nat := [1, 1, 1, 2, 2, 7, 1, 7]
def baseStart_3255539 : Nat := 118140960795 + 3255539 * 2 ^ 59
def prefixEnd_3255539 : Nat := 4983230072969 + 3 ^ 40 * 3255539 * 2
def baseEnd_3255539 : Nat := 123826392330195809065967

theorem tailTrace_3255539 : CollatzResearch.WordTrace tailWord_3255539 prefixEnd_3255539 123826392330195809065967 := by
  unfold tailWord_3255539
  simp only [CollatzResearch.WordTrace]
  refine ⟨118739262152745679640745671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79159508101830453093830447 118739262152745679640745671)
  ·
    refine ⟨178108893229118519461118507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118739262152745679640745671 178108893229118519461118507)
    ·
      refine ⟨267163339843677779191677761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178108893229118519461118507 267163339843677779191677761)
      ·
        refine ⟨200372504882758334393758321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267163339843677779191677761 200372504882758334393758321)
        ·
          refine ⟨150279378662068750795318741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200372504882758334393758321 150279378662068750795318741)
          ·
            refine ⟨3522172937392236346765283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 150279378662068750795318741 3522172937392236346765283)
            ·
              refine ⟨5283259406088354520147925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3522172937392236346765283 5283259406088354520147925)
              ·
                refine ⟨123826392330195809065967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5283259406088354520147925 123826392330195809065967)
                ·
                  rfl

theorem cell22_3255539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 7].length) (baseStart_3255539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3255539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3255539 prefixEnd_3255539 := by exact prefixLift 3255539
  have htrace : WordTrace (prefixWord ++ tailWord_3255539) baseStart_3255539 baseEnd_3255539 := by
    simpa [prefixWord, tailWord_3255539, baseEnd_3255539] using wordTrace_append hprefix tailTrace_3255539
  have hstable : (prefixWord ++ tailWord_3255539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255539).length < 2 ^ (prefixWord ++ tailWord_3255539).sum := by decide
  have hdescent : baseEnd_3255539 < baseStart_3255539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255552 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 4, 6]
def baseStart_3255552 : Nat := 118140960795 + 3255552 * 2 ^ 59
def prefixEnd_3255552 : Nat := 4983230072969 + 3 ^ 40 * 3255552 * 2
def baseEnd_3255552 : Nat := 1114441981137434581018663

theorem tailTrace_3255552 : CollatzResearch.WordTrace tailWord_3255552 prefixEnd_3255552 1114441981137434581018663 := by
  unfold tailWord_3255552
  simp only [CollatzResearch.WordTrace]
  refine ⟨59369868150849291430484455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79159824201132388573979273 59369868150849291430484455)
  ·
    refine ⟨89054802226273937145726683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59369868150849291430484455 89054802226273937145726683)
    ·
      refine ⟨133582203339410905718590025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89054802226273937145726683 133582203339410905718590025)
      ·
        refine ⟨100186652504558179288942519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133582203339410905718590025 100186652504558179288942519)
        ·
          refine ⟨150279978756837268933413779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100186652504558179288942519 150279978756837268933413779)
          ·
            refine ⟨225419968135255903400120669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150279978756837268933413779 225419968135255903400120669)
            ·
              refine ⟨84532488050720963775045251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 225419968135255903400120669 84532488050720963775045251)
              ·
                refine ⟨126798732076081445662567877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84532488050720963775045251 126798732076081445662567877)
                ·
                  refine ⟨23774762264265271061731477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126798732076081445662567877 23774762264265271061731477)
                  ·
                    refine ⟨1114441981137434581018663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23774762264265271061731477 1114441981137434581018663)
                    ·
                      rfl

theorem cell22_3255552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 4, 6].length) (baseStart_3255552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3255552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3255552 prefixEnd_3255552 := by exact prefixLift 3255552
  have htrace : WordTrace (prefixWord ++ tailWord_3255552) baseStart_3255552 baseEnd_3255552 := by
    simpa [prefixWord, tailWord_3255552, baseEnd_3255552] using wordTrace_append hprefix tailTrace_3255552
  have hstable : (prefixWord ++ tailWord_3255552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255552).length < 2 ^ (prefixWord ++ tailWord_3255552).sum := by decide
  have hdescent : baseEnd_3255552 < baseStart_3255552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255556 : List Nat := [2, 3, 2, 2, 2, 2, 3, 6]
def baseStart_3255556 : Nat := 118140960795 + 3255556 * 2 ^ 59
def prefixEnd_3255556 : Nat := 4983230072969 + 3 ^ 40 * 3255556 * 2
def baseEnd_3255556 : Nat := 123827038935464433768739

theorem tailTrace_3255556 : CollatzResearch.WordTrace tailWord_3255556 prefixEnd_3255556 123827038935464433768739 := by
  unfold tailWord_3255556
  simp only [CollatzResearch.WordTrace]
  refine ⟨59369941096842045772057261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79159921462456061029409681 59369941096842045772057261)
  ·
    refine ⟨22263727911315767164521473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59369941096842045772057261 22263727911315767164521473)
    ·
      refine ⟨16697795933486825373391105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22263727911315767164521473 16697795933486825373391105)
      ·
        refine ⟨12523346950115119030043329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16697795933486825373391105 12523346950115119030043329)
        ·
          refine ⟨9392510212586339272532497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12523346950115119030043329 9392510212586339272532497)
          ·
            refine ⟨7044382659439754454399373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9392510212586339272532497 7044382659439754454399373)
            ·
              refine ⟨2641643497289907920399765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7044382659439754454399373 2641643497289907920399765)
              ·
                refine ⟨123827038935464433768739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2641643497289907920399765 123827038935464433768739)
                ·
                  rfl

theorem cell22_3255556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 6].length) (baseStart_3255556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3255556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3255556 prefixEnd_3255556 := by exact prefixLift 3255556
  have htrace : WordTrace (prefixWord ++ tailWord_3255556) baseStart_3255556 baseEnd_3255556 := by
    simpa [prefixWord, tailWord_3255556, baseEnd_3255556] using wordTrace_append hprefix tailTrace_3255556
  have hstable : (prefixWord ++ tailWord_3255556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255556).length < 2 ^ (prefixWord ++ tailWord_3255556).sum := by decide
  have hdescent : baseEnd_3255556 < baseStart_3255556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255588 : List Nat := [2, 3, 1, 3, 1, 1, 1, 6, 1, 3]
def baseStart_3255588 : Nat := 118140960795 + 3255588 * 2 ^ 59
def prefixEnd_3255588 : Nat := 4983230072969 + 3 ^ 40 * 3255588 * 2
def baseEnd_3255588 : Nat := 1114454304673142487118553

theorem tailTrace_3255588 : CollatzResearch.WordTrace tailWord_3255588 prefixEnd_3255588 1114454304673142487118553 := by
  unfold tailWord_3255588
  simp only [CollatzResearch.WordTrace]
  refine ⟨59370524664784080504639709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79160699553045440672852945 59370524664784080504639709)
  ·
    refine ⟨22263946749294030189239891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59370524664784080504639709 22263946749294030189239891)
    ·
      refine ⟨33395920123941045283859837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22263946749294030189239891 33395920123941045283859837)
      ·
        refine ⟨12523470046477891981447439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33395920123941045283859837 12523470046477891981447439)
        ·
          refine ⟨18785205069716837972171159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12523470046477891981447439 18785205069716837972171159)
          ·
            refine ⟨28177807604575256958256739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18785205069716837972171159 28177807604575256958256739)
            ·
              refine ⟨42266711406862885437385109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28177807604575256958256739 42266711406862885437385109)
              ·
                refine ⟨1981252097196697754877427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42266711406862885437385109 1981252097196697754877427)
                ·
                  refine ⟨2971878145795046632316141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1981252097196697754877427 2971878145795046632316141)
                  ·
                    refine ⟨1114454304673142487118553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2971878145795046632316141 1114454304673142487118553)
                    ·
                      rfl

theorem cell22_3255588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 6, 1, 3].length) (baseStart_3255588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3255588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3255588 prefixEnd_3255588 := by exact prefixLift 3255588
  have htrace : WordTrace (prefixWord ++ tailWord_3255588) baseStart_3255588 baseEnd_3255588 := by
    simpa [prefixWord, tailWord_3255588, baseEnd_3255588] using wordTrace_append hprefix tailTrace_3255588
  have hstable : (prefixWord ++ tailWord_3255588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255588).length < 2 ^ (prefixWord ++ tailWord_3255588).sum := by decide
  have hdescent : baseEnd_3255588 < baseStart_3255588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255676 : List Nat := [2, 2, 2, 1, 1, 1, 6, 1, 2, 4]
def baseStart_3255676 : Nat := 118140960795 + 3255676 * 2 ^ 59
def prefixEnd_3255676 : Nat := 4983230072969 + 3 ^ 40 * 3255676 * 2
def baseEnd_3255676 : Nat := 1114484428871539590918283

theorem tailTrace_3255676 : CollatzResearch.WordTrace tailWord_3255676 prefixEnd_3255676 1114484428871539590918283 := by
  unfold tailWord_3255676
  simp only [CollatzResearch.WordTrace]
  refine ⟨59372129476624676019241441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79162839302166234692321921 59372129476624676019241441)
  ·
    refine ⟨44529097107468507014431081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59372129476624676019241441 44529097107468507014431081)
    ·
      refine ⟨33396822830601380260823311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44529097107468507014431081 33396822830601380260823311)
      ·
        refine ⟨50095234245902070391234967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33396822830601380260823311 50095234245902070391234967)
        ·
          refine ⟨75142851368853105586852451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50095234245902070391234967 75142851368853105586852451)
          ·
            refine ⟨112714277053279658380278677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75142851368853105586852451 112714277053279658380278677)
            ·
              refine ⟨5283481736872483986575563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 112714277053279658380278677 5283481736872483986575563)
              ·
                refine ⟨7925222605308725979863345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5283481736872483986575563 7925222605308725979863345)
                ·
                  refine ⟨5943916953981544484897509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7925222605308725979863345 5943916953981544484897509)
                  ·
                    refine ⟨1114484428871539590918283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5943916953981544484897509 1114484428871539590918283)
                    ·
                      rfl

theorem cell22_3255676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_3255676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3255676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3255676 prefixEnd_3255676 := by exact prefixLift 3255676
  have htrace : WordTrace (prefixWord ++ tailWord_3255676) baseStart_3255676 baseEnd_3255676 := by
    simpa [prefixWord, tailWord_3255676, baseEnd_3255676] using wordTrace_append hprefix tailTrace_3255676
  have hstable : (prefixWord ++ tailWord_3255676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255676).length < 2 ^ (prefixWord ++ tailWord_3255676).sum := by decide
  have hdescent : baseEnd_3255676 < baseStart_3255676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255682 : List Nat := [3, 4, 2, 1, 1, 2, 3, 1, 1, 4]
def baseStart_3255682 : Nat := 118140960795 + 3255682 * 2 ^ 59
def prefixEnd_3255682 : Nat := 4983230072969 + 3 ^ 40 * 3255682 * 2
def baseEnd_3255682 : Nat := 1114486482794157575268265

theorem tailTrace_3255682 : CollatzResearch.WordTrace tailWord_3255682 prefixEnd_3255682 1114486482794157575268265 := by
  unfold tailWord_3255682
  simp only [CollatzResearch.WordTrace]
  refine ⟨29686119447806903765800325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79162985194151743375467533 29686119447806903765800325)
  ·
    refine ⟨5566147396463794456087561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29686119447806903765800325 5566147396463794456087561)
    ·
      refine ⟨4174610547347845842065671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5566147396463794456087561 4174610547347845842065671)
      ·
        refine ⟨6261915821021768763098507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4174610547347845842065671 6261915821021768763098507)
        ·
          refine ⟨9392873731532653144647761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6261915821021768763098507 9392873731532653144647761)
          ·
            refine ⟨7044655298649489858485821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9392873731532653144647761 7044655298649489858485821)
            ·
              refine ⟨2641745736993558696932183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7044655298649489858485821 2641745736993558696932183)
              ·
                refine ⟨3962618605490338045398275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2641745736993558696932183 3962618605490338045398275)
                ·
                  refine ⟨5943927908235507068097413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3962618605490338045398275 5943927908235507068097413)
                  ·
                    refine ⟨1114486482794157575268265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5943927908235507068097413 1114486482794157575268265)
                    ·
                      rfl

theorem cell22_3255682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_3255682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3255682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3255682 prefixEnd_3255682 := by exact prefixLift 3255682
  have htrace : WordTrace (prefixWord ++ tailWord_3255682) baseStart_3255682 baseEnd_3255682 := by
    simpa [prefixWord, tailWord_3255682, baseEnd_3255682] using wordTrace_append hprefix tailTrace_3255682
  have hstable : (prefixWord ++ tailWord_3255682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255682).length < 2 ^ (prefixWord ++ tailWord_3255682).sum := by decide
  have hdescent : baseEnd_3255682 < baseStart_3255682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255783 : List Nat := [1, 1, 5, 2, 1, 2, 1, 4, 1, 4]
def baseStart_3255783 : Nat := 118140960795 + 3255783 * 2 ^ 59
def prefixEnd_3255783 : Nat := 4983230072969 + 3 ^ 40 * 3255783 * 2
def baseEnd_3255783 : Nat := 1114521057158226978492955

theorem tailTrace_3255783 : CollatzResearch.WordTrace tailWord_3255783 prefixEnd_3255783 1114521057158226978492955 := by
  unfold tailWord_3255783
  simp only [CollatzResearch.WordTrace]
  refine ⟨118748161563861709312628003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79165441042574472875085335 118748161563861709312628003)
  ·
    refine ⟨178122242345792563968942005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118748161563861709312628003 178122242345792563968942005)
    ·
      refine ⟨16698960219918052872088313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 178122242345792563968942005 16698960219918052872088313)
      ·
        refine ⟨12524220164938539654066235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16698960219918052872088313 12524220164938539654066235)
        ·
          refine ⟨18786330247407809481099353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12524220164938539654066235 18786330247407809481099353)
          ·
            refine ⟨14089747685555857110824515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18786330247407809481099353 14089747685555857110824515)
            ·
              refine ⟨21134621528333785666236773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14089747685555857110824515 21134621528333785666236773)
              ·
                refine ⟨3962741536562584812419395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21134621528333785666236773 3962741536562584812419395)
                ·
                  refine ⟨5944112304843877218629093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3962741536562584812419395 5944112304843877218629093)
                  ·
                    refine ⟨1114521057158226978492955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5944112304843877218629093 1114521057158226978492955)
                    ·
                      rfl

theorem cell22_3255783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_3255783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3255783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3255783 prefixEnd_3255783 := by exact prefixLift 3255783
  have htrace : WordTrace (prefixWord ++ tailWord_3255783) baseStart_3255783 baseEnd_3255783 := by
    simpa [prefixWord, tailWord_3255783, baseEnd_3255783] using wordTrace_append hprefix tailTrace_3255783
  have hstable : (prefixWord ++ tailWord_3255783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255783).length < 2 ^ (prefixWord ++ tailWord_3255783).sum := by decide
  have hdescent : baseEnd_3255783 < baseStart_3255783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255813 : List Nat := [1, 3, 1, 1, 2, 2, 1, 6, 2, 3]
def baseStart_3255813 : Nat := 118140960795 + 3255813 * 2 ^ 59
def prefixEnd_3255813 : Nat := 4983230072969 + 3 ^ 40 * 3255813 * 2
def baseEnd_3255813 : Nat := 1114531326771316900242863

theorem tailTrace_3255813 : CollatzResearch.WordTrace tailWord_3255813 prefixEnd_3255813 1114531326771316900242863 := by
  unfold tailWord_3255813
  simp only [CollatzResearch.WordTrace]
  refine ⟨118749255753753024436220093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79166170502502016290813395 118749255753753024436220093)
  ·
    refine ⟨44530970907657384163582535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118749255753753024436220093 44530970907657384163582535)
    ·
      refine ⟨66796456361486076245373803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44530970907657384163582535 66796456361486076245373803)
      ·
        refine ⟨100194684542229114368060705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66796456361486076245373803 100194684542229114368060705)
        ·
          refine ⟨75146013406671835776045529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100194684542229114368060705 75146013406671835776045529)
          ·
            refine ⟨56359510055003876832034147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75146013406671835776045529 56359510055003876832034147)
            ·
              refine ⟨84539265082505815248051221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56359510055003876832034147 84539265082505815248051221)
              ·
                refine ⟨3962778050742460089752401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 84539265082505815248051221 3962778050742460089752401)
                ·
                  refine ⟨2972083538056845067314301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3962778050742460089752401 2972083538056845067314301)
                  ·
                    refine ⟨1114531326771316900242863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2972083538056845067314301 1114531326771316900242863)
                    ·
                      rfl

theorem cell22_3255813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 2, 3].length) (baseStart_3255813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3255813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3255813 prefixEnd_3255813 := by exact prefixLift 3255813
  have htrace : WordTrace (prefixWord ++ tailWord_3255813) baseStart_3255813 baseEnd_3255813 := by
    simpa [prefixWord, tailWord_3255813, baseEnd_3255813] using wordTrace_append hprefix tailTrace_3255813
  have hstable : (prefixWord ++ tailWord_3255813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255813).length < 2 ^ (prefixWord ++ tailWord_3255813).sum := by decide
  have hdescent : baseEnd_3255813 < baseStart_3255813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255821 : List Nat := [1, 7, 1, 1, 3, 1, 2, 1, 5]
def baseStart_3255821 : Nat := 118140960795 + 3255821 * 2 ^ 59
def prefixEnd_3255821 : Nat := 4983230072969 + 3 ^ 40 * 3255821 * 2
def baseEnd_3255821 : Nat := 371511355111602515347613

theorem tailTrace_3255821 : CollatzResearch.WordTrace tailWord_3255821 prefixEnd_3255821 371511355111602515347613 := by
  unfold tailWord_3255821
  simp only [CollatzResearch.WordTrace]
  refine ⟨118749547537724041802511317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79166365025149361201674211 118749547537724041802511317)
  ·
    refine ⟨2783192520415407229746359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 118749547537724041802511317 2783192520415407229746359)
    ·
      refine ⟨4174788780623110844619539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2783192520415407229746359 4174788780623110844619539)
      ·
        refine ⟨6262183170934666266929309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4174788780623110844619539 6262183170934666266929309)
        ·
          refine ⟨2348318689100499850098491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6262183170934666266929309 2348318689100499850098491)
          ·
            refine ⟨3522478033650749775147737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2348318689100499850098491 3522478033650749775147737)
            ·
              refine ⟨2641858525238062331360803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3522478033650749775147737 2641858525238062331360803)
              ·
                refine ⟨3962787787857093497041205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2641858525238062331360803 3962787787857093497041205)
                ·
                  refine ⟨371511355111602515347613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3962787787857093497041205 371511355111602515347613)
                  ·
                    rfl

theorem cell22_3255821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_3255821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3255821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3255821 prefixEnd_3255821 := by exact prefixLift 3255821
  have htrace : WordTrace (prefixWord ++ tailWord_3255821) baseStart_3255821 baseEnd_3255821 := by
    simpa [prefixWord, tailWord_3255821, baseEnd_3255821] using wordTrace_append hprefix tailTrace_3255821
  have hstable : (prefixWord ++ tailWord_3255821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255821).length < 2 ^ (prefixWord ++ tailWord_3255821).sum := by decide
  have hdescent : baseEnd_3255821 < baseStart_3255821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255894 : List Nat := [5, 2, 2, 2, 1, 1, 3, 6]
def baseStart_3255894 : Nat := 118140960795 + 3255894 * 2 ^ 59
def prefixEnd_3255894 : Nat := 4983230072969 + 3 ^ 40 * 3255894 * 2
def baseEnd_3255894 : Nat := 123839894969628854329735

theorem tailTrace_3255894 : CollatzResearch.WordTrace tailWord_3255894 prefixEnd_3255894 123839894969628854329735 := by
  unfold tailWord_3255894
  simp only [CollatzResearch.WordTrace]
  refine ⟨7422013129153723454369921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79168140044306383513279157 7422013129153723454369921)
  ·
    refine ⟨5566509846865292590777441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7422013129153723454369921 5566509846865292590777441)
    ·
      refine ⟨4174882385148969443083081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5566509846865292590777441 4174882385148969443083081)
      ·
        refine ⟨3131161788861727082312311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4174882385148969443083081 3131161788861727082312311)
        ·
          refine ⟨4696742683292590623468467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3131161788861727082312311 4696742683292590623468467)
          ·
            refine ⟨7045114024938885935202701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4696742683292590623468467 7045114024938885935202701)
            ·
              refine ⟨2641917759352082225701013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7045114024938885935202701 2641917759352082225701013)
              ·
                refine ⟨123839894969628854329735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2641917759352082225701013 123839894969628854329735)
                ·
                  rfl

theorem cell22_3255894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_3255894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3255894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3255894 prefixEnd_3255894 := by exact prefixLift 3255894
  have htrace : WordTrace (prefixWord ++ tailWord_3255894) baseStart_3255894 baseEnd_3255894 := by
    simpa [prefixWord, tailWord_3255894, baseEnd_3255894] using wordTrace_append hprefix tailTrace_3255894
  have hstable : (prefixWord ++ tailWord_3255894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255894).length < 2 ^ (prefixWord ++ tailWord_3255894).sum := by decide
  have hdescent : baseEnd_3255894 < baseStart_3255894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255916 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 10]
def baseStart_3255916 : Nat := 118140960795 + 3255916 * 2 ^ 59
def prefixEnd_3255916 : Nat := 4983230072969 + 3 ^ 40 * 3255916 * 2
def baseEnd_3255916 : Nat := 371522195258752988305849

theorem tailTrace_3255916 : CollatzResearch.WordTrace tailWord_3255916 prefixEnd_3255916 371522195258752988305849 := by
  unfold tailWord_3255916
  simp only [CollatzResearch.WordTrace]
  refine ⟨59376506236189936513609801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79168674981586582018146401 59376506236189936513609801)
  ·
    refine ⟨44532379677142452385207351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59376506236189936513609801 44532379677142452385207351)
    ·
      refine ⟨66798569515713678577811027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44532379677142452385207351 66798569515713678577811027)
      ·
        refine ⟨100197854273570517866716541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66798569515713678577811027 100197854273570517866716541)
        ·
          refine ⟨37574195352588944200018703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100197854273570517866716541 37574195352588944200018703)
          ·
            refine ⟨56361293028883416300028055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37574195352588944200018703 56361293028883416300028055)
            ·
              refine ⟨84541939543325124450042083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56361293028883416300028055 84541939543325124450042083)
              ·
                refine ⟨126812909314987686675063125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84541939543325124450042083 126812909314987686675063125)
                ·
                  refine ⟨371522195258752988305849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 126812909314987686675063125 371522195258752988305849)
                  ·
                    rfl

theorem cell22_3255916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 10].length) (baseStart_3255916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3255916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3255916 prefixEnd_3255916 := by exact prefixLift 3255916
  have htrace : WordTrace (prefixWord ++ tailWord_3255916) baseStart_3255916 baseEnd_3255916 := by
    simpa [prefixWord, tailWord_3255916, baseEnd_3255916] using wordTrace_append hprefix tailTrace_3255916
  have hstable : (prefixWord ++ tailWord_3255916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255916).length < 2 ^ (prefixWord ++ tailWord_3255916).sum := by decide
  have hdescent : baseEnd_3255916 < baseStart_3255916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255933 : List Nat := [1, 4, 1, 1, 4, 1, 1, 3, 6]
def baseStart_3255933 : Nat := 118140960795 + 3255933 * 2 ^ 59
def prefixEnd_3255933 : Nat := 4983230072969 + 3 ^ 40 * 3255933 * 2
def baseEnd_3255933 : Nat := 371524135074558862414165

theorem tailTrace_3255933 : CollatzResearch.WordTrace tailWord_3255933 prefixEnd_3255933 371524135074558862414165 := by
  unfold tailWord_3255933
  simp only [CollatzResearch.WordTrace]
  refine ⟨118753632513318284930588453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79169088342212189953725635 118753632513318284930588453)
  ·
    refine ⟨22266306096247178424485335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118753632513318284930588453 22266306096247178424485335)
    ·
      refine ⟨33399459144370767636728003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22266306096247178424485335 33399459144370767636728003)
      ·
        refine ⟨50099188716556151455092005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33399459144370767636728003 50099188716556151455092005)
        ·
          refine ⟨9393597884354278397829751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50099188716556151455092005 9393597884354278397829751)
          ·
            refine ⟨14090396826531417596744627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9393597884354278397829751 14090396826531417596744627)
            ·
              refine ⟨21135595239797126395116941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14090396826531417596744627 21135595239797126395116941)
              ·
                refine ⟨7925848214923922398168853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21135595239797126395116941 7925848214923922398168853)
                ·
                  refine ⟨371524135074558862414165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7925848214923922398168853 371524135074558862414165)
                  ·
                    rfl

theorem cell22_3255933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_3255933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3255933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3255933 prefixEnd_3255933 := by exact prefixLift 3255933
  have htrace : WordTrace (prefixWord ++ tailWord_3255933) baseStart_3255933 baseEnd_3255933 := by
    simpa [prefixWord, tailWord_3255933, baseEnd_3255933] using wordTrace_append hprefix tailTrace_3255933
  have hstable : (prefixWord ++ tailWord_3255933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255933).length < 2 ^ (prefixWord ++ tailWord_3255933).sum := by decide
  have hdescent : baseEnd_3255933 < baseStart_3255933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256040 : List Nat := [2, 1, 4, 1, 3, 1, 1, 4, 5]
def baseStart_3256040 : Nat := 118140960795 + 3256040 * 2 ^ 59
def prefixEnd_3256040 : Nat := 4983230072969 + 3 ^ 40 * 3256040 * 2
def baseEnd_3256040 : Nat := 371536344503454658272389

theorem tailTrace_3256040 : CollatzResearch.WordTrace tailWord_3256040 prefixEnd_3256040 371536344503454658272389 := by
  unfold tailWord_3256040
  simp only [CollatzResearch.WordTrace]
  refine ⟨59378767561965321102366787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79171690082620428136489049 59378767561965321102366787)
  ·
    refine ⟨89068151342947981653550181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59378767561965321102366787 89068151342947981653550181)
    ·
      refine ⟨16700278376802746560040659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89068151342947981653550181 16700278376802746560040659)
      ·
        refine ⟨25050417565204119840060989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16700278376802746560040659 25050417565204119840060989)
        ·
          refine ⟨9393906586951544940022871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25050417565204119840060989 9393906586951544940022871)
          ·
            refine ⟨14090859880427317410034307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9393906586951544940022871 14090859880427317410034307)
            ·
              refine ⟨21136289820640976115051461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14090859880427317410034307 21136289820640976115051461)
              ·
                refine ⟨3963054341370183021572149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21136289820640976115051461 3963054341370183021572149)
                ·
                  refine ⟨371536344503454658272389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3963054341370183021572149 371536344503454658272389)
                  ·
                    rfl

theorem cell22_3256040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 5].length) (baseStart_3256040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3256040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3256040 prefixEnd_3256040 := by exact prefixLift 3256040
  have htrace : WordTrace (prefixWord ++ tailWord_3256040) baseStart_3256040 baseEnd_3256040 := by
    simpa [prefixWord, tailWord_3256040, baseEnd_3256040] using wordTrace_append hprefix tailTrace_3256040
  have hstable : (prefixWord ++ tailWord_3256040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256040).length < 2 ^ (prefixWord ++ tailWord_3256040).sum := by decide
  have hdescent : baseEnd_3256040 < baseStart_3256040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256044 : List Nat := [2, 2, 1, 1, 2, 2, 6, 2, 1, 3]
def baseStart_3256044 : Nat := 118140960795 + 3256044 * 2 ^ 59
def prefixEnd_3256044 : Nat := 4983230072969 + 3 ^ 40 * 3256044 * 2
def baseEnd_3256044 : Nat := 1114610402792109297717155

theorem tailTrace_3256044 : CollatzResearch.WordTrace tailWord_3256044 prefixEnd_3256044 1114610402792109297717155 := by
  unfold tailWord_3256044
  simp only [CollatzResearch.WordTrace]
  refine ⟨59378840507958075443939593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79171787343944100591919457 59378840507958075443939593)
  ·
    refine ⟨44534130380968556582954695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59378840507958075443939593 44534130380968556582954695)
    ·
      refine ⟨66801195571452834874432043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44534130380968556582954695 66801195571452834874432043)
      ·
        refine ⟨100201793357179252311648065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66801195571452834874432043 100201793357179252311648065)
        ·
          refine ⟨75151345017884439233736049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100201793357179252311648065 75151345017884439233736049)
          ·
            refine ⟨56363508763413329425302037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75151345017884439233736049 56363508763413329425302037)
            ·
              refine ⟨2642039473284999816811033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56363508763413329425302037 2642039473284999816811033)
              ·
                refine ⟨1981529604963749862608275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2642039473284999816811033 1981529604963749862608275)
                ·
                  refine ⟨2972294407445624793912413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1981529604963749862608275 2972294407445624793912413)
                  ·
                    refine ⟨1114610402792109297717155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2972294407445624793912413 1114610402792109297717155)
                    ·
                      rfl

theorem cell22_3256044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 2, 1, 3].length) (baseStart_3256044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3256044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3256044 prefixEnd_3256044 := by exact prefixLift 3256044
  have htrace : WordTrace (prefixWord ++ tailWord_3256044) baseStart_3256044 baseEnd_3256044 := by
    simpa [prefixWord, tailWord_3256044, baseEnd_3256044] using wordTrace_append hprefix tailTrace_3256044
  have hstable : (prefixWord ++ tailWord_3256044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256044).length < 2 ^ (prefixWord ++ tailWord_3256044).sum := by decide
  have hdescent : baseEnd_3256044 < baseStart_3256044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256083 : List Nat := [1, 1, 1, 2, 1, 3, 2, 3, 3, 5]
def baseStart_3256083 : Nat := 118140960795 + 3256083 * 2 ^ 59
def prefixEnd_3256083 : Nat := 4983230072969 + 3 ^ 40 * 3256083 * 2
def baseEnd_3256083 : Nat := 1114623753289126195992035

theorem tailTrace_3256083 : CollatzResearch.WordTrace tailWord_3256083 prefixEnd_3256083 1114623753289126195992035 := by
  unfold tailWord_3256083
  simp only [CollatzResearch.WordTrace]
  refine ⟨118759103462774860548548903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79172735641849907032365935 118759103462774860548548903)
  ·
    refine ⟨178138655194162290822823355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118759103462774860548548903 178138655194162290822823355)
    ·
      refine ⟨267207982791243436234235033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178138655194162290822823355 267207982791243436234235033)
      ·
        refine ⟨200405987093432577175676275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267207982791243436234235033 200405987093432577175676275)
        ·
          refine ⟨300608980640148865763514413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200405987093432577175676275 300608980640148865763514413)
          ·
            refine ⟨112728367740055824661317905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 300608980640148865763514413 112728367740055824661317905)
            ·
              refine ⟨84546275805041868495988429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112728367740055824661317905 84546275805041868495988429)
              ·
                refine ⟨31704853426890700685995661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84546275805041868495988429 31704853426890700685995661)
                ·
                  refine ⟨11889320035084012757248373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31704853426890700685995661 11889320035084012757248373)
                  ·
                    refine ⟨1114623753289126195992035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11889320035084012757248373 1114623753289126195992035)
                    ·
                      rfl

theorem cell22_3256083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 5].length) (baseStart_3256083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3256083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3256083 prefixEnd_3256083 := by exact prefixLift 3256083
  have htrace : WordTrace (prefixWord ++ tailWord_3256083) baseStart_3256083 baseEnd_3256083 := by
    simpa [prefixWord, tailWord_3256083, baseEnd_3256083] using wordTrace_append hprefix tailTrace_3256083
  have hstable : (prefixWord ++ tailWord_3256083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256083).length < 2 ^ (prefixWord ++ tailWord_3256083).sum := by decide
  have hdescent : baseEnd_3256083 < baseStart_3256083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256087 : List Nat := [1, 1, 3, 4, 2, 2, 1, 3, 1, 4]
def baseStart_3256087 : Nat := 118140960795 + 3256087 * 2 ^ 59
def prefixEnd_3256087 : Nat := 4983230072969 + 3 ^ 40 * 3256087 * 2
def baseEnd_3256087 : Nat := 1114625122570871518892023

theorem tailTrace_3256087 : CollatzResearch.WordTrace tailWord_3256087 prefixEnd_3256087 1114625122570871518892023 := by
  unfold tailWord_3256087
  simp only [CollatzResearch.WordTrace]
  refine ⟨118759249354760369231694515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79172832903173579487796343 118759249354760369231694515)
  ·
    refine ⟨178138874032140553847541773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118759249354760369231694515 178138874032140553847541773)
    ·
      refine ⟨66802077762052707692828165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178138874032140553847541773 66802077762052707692828165)
      ·
        refine ⟨12525389580384882692405281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66802077762052707692828165 12525389580384882692405281)
        ·
          refine ⟨9394042185288662019303961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12525389580384882692405281 9394042185288662019303961)
          ·
            refine ⟨7045531638966496514477971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9394042185288662019303961 7045531638966496514477971)
            ·
              refine ⟨10568297458449744771716957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7045531638966496514477971 10568297458449744771716957)
              ·
                refine ⟨3963111546918654289393859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10568297458449744771716957 3963111546918654289393859)
                ·
                  refine ⟨5944667320377981434090789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3963111546918654289393859 5944667320377981434090789)
                  ·
                    refine ⟨1114625122570871518892023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5944667320377981434090789 1114625122570871518892023)
                    ·
                      rfl

theorem cell22_3256087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 4].length) (baseStart_3256087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3256087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3256087 prefixEnd_3256087 := by exact prefixLift 3256087
  have htrace : WordTrace (prefixWord ++ tailWord_3256087) baseStart_3256087 baseEnd_3256087 := by
    simpa [prefixWord, tailWord_3256087, baseEnd_3256087] using wordTrace_append hprefix tailTrace_3256087
  have hstable : (prefixWord ++ tailWord_3256087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256087).length < 2 ^ (prefixWord ++ tailWord_3256087).sum := by decide
  have hdescent : baseEnd_3256087 < baseStart_3256087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256254 : List Nat := [4, 2, 1, 1, 1, 3, 1, 5, 4]
def baseStart_3256254 : Nat := 118140960795 + 3256254 * 2 ^ 59
def prefixEnd_3256254 : Nat := 4983230072969 + 3 ^ 40 * 3256254 * 2
def baseEnd_3256254 : Nat := 371560763361246249988837

theorem tailTrace_3256254 : CollatzResearch.WordTrace tailWord_3256254 prefixEnd_3256254 371560763361246249988837 := by
  unfold tailWord_3256254
  simp only [CollatzResearch.WordTrace]
  refine ⟨14845667543144419594127977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79176893563436904502015877 14845667543144419594127977)
  ·
    refine ⟨11134250657358314695595983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14845667543144419594127977 11134250657358314695595983)
    ·
      refine ⟨16701375986037472043393975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11134250657358314695595983 16701375986037472043393975)
      ·
        refine ⟨25052063979056208065090963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16701375986037472043393975 25052063979056208065090963)
        ·
          refine ⟨37578095968584312097636445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25052063979056208065090963 37578095968584312097636445)
          ·
            refine ⟨14091785988219117036613667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37578095968584312097636445 14091785988219117036613667)
            ·
              refine ⟨21137678982328675554920501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14091785988219117036613667 21137678982328675554920501)
              ·
                refine ⟨1981657404593313333273797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21137678982328675554920501 1981657404593313333273797)
                ·
                  refine ⟨371560763361246249988837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1981657404593313333273797 371560763361246249988837)
                  ·
                    rfl

theorem cell22_3256254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_3256254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3256254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3256254 prefixEnd_3256254 := by exact prefixLift 3256254
  have htrace : WordTrace (prefixWord ++ tailWord_3256254) baseStart_3256254 baseEnd_3256254 := by
    simpa [prefixWord, tailWord_3256254, baseEnd_3256254] using wordTrace_append hprefix tailTrace_3256254
  have hstable : (prefixWord ++ tailWord_3256254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256254).length < 2 ^ (prefixWord ++ tailWord_3256254).sum := by decide
  have hdescent : baseEnd_3256254 < baseStart_3256254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256327 : List Nat := [1, 1, 4, 3, 1, 2, 2, 1, 7]
def baseStart_3256327 : Nat := 118140960795 + 3256327 * 2 ^ 59
def prefixEnd_3256327 : Nat := 4983230072969 + 3 ^ 40 * 3256327 * 2
def baseEnd_3256327 : Nat := 371569093158530297630429

theorem tailTrace_3256327 : CollatzResearch.WordTrace tailWord_3256327 prefixEnd_3256327 371569093158530297630429 := by
  unfold tailWord_3256327
  simp only [CollatzResearch.WordTrace]
  refine ⟨118768002873890890220431235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79178668582593926813620823 118768002873890890220431235)
  ·
    refine ⟨178152004310836335330646853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118768002873890890220431235 178152004310836335330646853)
    ·
      refine ⟨33403500808281812874496285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178152004310836335330646853 33403500808281812874496285)
      ·
        refine ⟨12526312803105679827936107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33403500808281812874496285 12526312803105679827936107)
        ·
          refine ⟨18789469204658519741904161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12526312803105679827936107 18789469204658519741904161)
          ·
            refine ⟨14092101903493889806428121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18789469204658519741904161 14092101903493889806428121)
            ·
              refine ⟨10569076427620417354821091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14092101903493889806428121 10569076427620417354821091)
              ·
                refine ⟨15853614641430626032231637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10569076427620417354821091 15853614641430626032231637)
                ·
                  refine ⟨371569093158530297630429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15853614641430626032231637 371569093158530297630429)
                  ·
                    rfl

theorem cell22_3256327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 7].length) (baseStart_3256327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3256327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3256327 prefixEnd_3256327 := by exact prefixLift 3256327
  have htrace : WordTrace (prefixWord ++ tailWord_3256327) baseStart_3256327 baseEnd_3256327 := by
    simpa [prefixWord, tailWord_3256327, baseEnd_3256327] using wordTrace_append hprefix tailTrace_3256327
  have hstable : (prefixWord ++ tailWord_3256327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256327).length < 2 ^ (prefixWord ++ tailWord_3256327).sum := by decide
  have hdescent : baseEnd_3256327 < baseStart_3256327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256333 : List Nat := [1, 7, 1, 2, 1, 1, 2, 7]
def baseStart_3256333 : Nat := 118140960795 + 3256333 * 2 ^ 59
def prefixEnd_3256333 : Nat := 4983230072969 + 3 ^ 40 * 3256333 * 2
def baseEnd_3256333 : Nat := 123856592599800986360141

theorem tailTrace_3256333 : CollatzResearch.WordTrace tailWord_3256333 prefixEnd_3256333 123856592599800986360141 := by
  unfold tailWord_3256333
  simp only [CollatzResearch.WordTrace]
  refine ⟨118768221711869153245149653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79178814474579435496766435 118768221711869153245149653)
  ·
    refine ⟨2783630196371933279183195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 118768221711869153245149653 2783630196371933279183195)
    ·
      refine ⟨4175445294557899918774793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2783630196371933279183195 4175445294557899918774793)
      ·
        refine ⟨3131583970918424939081095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4175445294557899918774793 3131583970918424939081095)
        ·
          refine ⟨4697375956377637408621643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3131583970918424939081095 4697375956377637408621643)
          ·
            refine ⟨7046063934566456112932465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4697375956377637408621643 7046063934566456112932465)
            ·
              refine ⟨5284547950924842084699349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7046063934566456112932465 5284547950924842084699349)
              ·
                refine ⟨123856592599800986360141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5284547950924842084699349 123856592599800986360141)
                ·
                  rfl

theorem cell22_3256333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 7].length) (baseStart_3256333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3256333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3256333 prefixEnd_3256333 := by exact prefixLift 3256333
  have htrace : WordTrace (prefixWord ++ tailWord_3256333) baseStart_3256333 baseEnd_3256333 := by
    simpa [prefixWord, tailWord_3256333, baseEnd_3256333] using wordTrace_append hprefix tailTrace_3256333
  have hstable : (prefixWord ++ tailWord_3256333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256333).length < 2 ^ (prefixWord ++ tailWord_3256333).sum := by decide
  have hdescent : baseEnd_3256333 < baseStart_3256333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256382 : List Nat := [4, 2, 1, 3, 2, 2, 2, 2, 1, 3]
def baseStart_3256382 : Nat := 118140960795 + 3256382 * 2 ^ 59
def prefixEnd_3256382 : Nat := 4983230072969 + 3 ^ 40 * 3256382 * 2
def baseEnd_3256382 : Nat := 1114726107099589082766119

theorem tailTrace_3256382 : CollatzResearch.WordTrace tailWord_3256382 prefixEnd_3256382 1114726107099589082766119 := by
  unfold tailWord_3256382
  simp only [CollatzResearch.WordTrace]
  refine ⟨14846251111086454326710425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79180005925794423075788933 14846251111086454326710425)
  ·
    refine ⟨11134688333314840745032819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14846251111086454326710425 11134688333314840745032819)
    ·
      refine ⟨16702032499972261117549229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11134688333314840745032819 16702032499972261117549229)
      ·
        refine ⟨6263262187489597919080961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16702032499972261117549229 6263262187489597919080961)
        ·
          refine ⟨4697446640617198439310721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6263262187489597919080961 4697446640617198439310721)
          ·
            refine ⟨3523084980462898829483041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4697446640617198439310721 3523084980462898829483041)
            ·
              refine ⟨2642313735347174122112281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3523084980462898829483041 2642313735347174122112281)
              ·
                refine ⟨1981735301510380591584211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2642313735347174122112281 1981735301510380591584211)
                ·
                  refine ⟨2972602952265570887376317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1981735301510380591584211 2972602952265570887376317)
                  ·
                    refine ⟨1114726107099589082766119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2972602952265570887376317 1114726107099589082766119)
                    ·
                      rfl

theorem cell22_3256382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_3256382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3256382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3256382 prefixEnd_3256382 := by exact prefixLift 3256382
  have htrace : WordTrace (prefixWord ++ tailWord_3256382) baseStart_3256382 baseEnd_3256382 := by
    simpa [prefixWord, tailWord_3256382, baseEnd_3256382] using wordTrace_append hprefix tailTrace_3256382
  have hstable : (prefixWord ++ tailWord_3256382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256382).length < 2 ^ (prefixWord ++ tailWord_3256382).sum := by decide
  have hdescent : baseEnd_3256382 < baseStart_3256382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256404 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 6, 3]
def baseStart_3256404 : Nat := 118140960795 + 3256404 * 2 ^ 59
def prefixEnd_3256404 : Nat := 4983230072969 + 3 ^ 40 * 3256404 * 2
def baseEnd_3256404 : Nat := 1114733638149188358716051

theorem tailTrace_3256404 : CollatzResearch.WordTrace tailWord_3256404 prefixEnd_3256404 1114733638149188358716051 := by
  unfold tailWord_3256404
  simp only [CollatzResearch.WordTrace]
  refine ⟨59385405647305966185492133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79180540863074621580656177 59385405647305966185492133)
  ·
    refine ⟨11134763558869868659779775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59385405647305966185492133 11134763558869868659779775)
    ·
      refine ⟨16702145338304802989669663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11134763558869868659779775 16702145338304802989669663)
      ·
        refine ⟨25053218007457204484504495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16702145338304802989669663 25053218007457204484504495)
        ·
          refine ⟨37579827011185806726756743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25053218007457204484504495 37579827011185806726756743)
          ·
            refine ⟨56369740516778710090135115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37579827011185806726756743 56369740516778710090135115)
            ·
              refine ⟨84554610775168065135202673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56369740516778710090135115 84554610775168065135202673)
              ·
                refine ⟨63415958081376048851402005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84554610775168065135202673 63415958081376048851402005)
                ·
                  refine ⟨2972623035064502289909469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 63415958081376048851402005 2972623035064502289909469)
                  ·
                    refine ⟨1114733638149188358716051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2972623035064502289909469 1114733638149188358716051)
                    ·
                      rfl

theorem cell22_3256404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_3256404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3256404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3256404 prefixEnd_3256404 := by exact prefixLift 3256404
  have htrace : WordTrace (prefixWord ++ tailWord_3256404) baseStart_3256404 baseEnd_3256404 := by
    simpa [prefixWord, tailWord_3256404, baseEnd_3256404] using wordTrace_append hprefix tailTrace_3256404
  have hstable : (prefixWord ++ tailWord_3256404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256404).length < 2 ^ (prefixWord ++ tailWord_3256404).sum := by decide
  have hdescent : baseEnd_3256404 < baseStart_3256404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256406 : List Nat := [5, 2, 2, 1, 1, 1, 1, 1, 8]
def baseStart_3256406 : Nat := 118140960795 + 3256406 * 2 ^ 59
def prefixEnd_3256406 : Nat := 4983230072969 + 3 ^ 40 * 3256406 * 2
def baseEnd_3256406 : Nat := 371578107596687006722015

theorem tailTrace_3256406 : CollatzResearch.WordTrace tailWord_3256406 prefixEnd_3256406 371578107596687006722015 := by
  unfold tailWord_3256406
  simp only [CollatzResearch.WordTrace]
  refine ⟨7423180265037792919534817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79180589493736457808371381 7423180265037792919534817)
  ·
    refine ⟨5567385198778344689651113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7423180265037792919534817 5567385198778344689651113)
    ·
      refine ⟨4175538899083758517238335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5567385198778344689651113 4175538899083758517238335)
      ·
        refine ⟨6263308348625637775857503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4175538899083758517238335 6263308348625637775857503)
        ·
          refine ⟨9394962522938456663786255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6263308348625637775857503 9394962522938456663786255)
          ·
            refine ⟨14092443784407684995679383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9394962522938456663786255 14092443784407684995679383)
            ·
              refine ⟨21138665676611527493519075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14092443784407684995679383 21138665676611527493519075)
              ·
                refine ⟨31707998514917291240278613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21138665676611527493519075 31707998514917291240278613)
                ·
                  refine ⟨371578107596687006722015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31707998514917291240278613 371578107596687006722015)
                  ·
                    rfl

theorem cell22_3256406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_3256406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3256406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3256406 prefixEnd_3256406 := by exact prefixLift 3256406
  have htrace : WordTrace (prefixWord ++ tailWord_3256406) baseStart_3256406 baseEnd_3256406 := by
    simpa [prefixWord, tailWord_3256406, baseEnd_3256406] using wordTrace_append hprefix tailTrace_3256406
  have hstable : (prefixWord ++ tailWord_3256406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256406).length < 2 ^ (prefixWord ++ tailWord_3256406).sum := by decide
  have hdescent : baseEnd_3256406 < baseStart_3256406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256419 : List Nat := [1, 1, 1, 5, 1, 1, 5, 1, 2, 4]
def baseStart_3256419 : Nat := 118140960795 + 3256419 * 2 ^ 59
def prefixEnd_3256419 : Nat := 4983230072969 + 3 ^ 40 * 3256419 * 2
def baseEnd_3256419 : Nat := 1114738772955733319591005

theorem tailTrace_3256419 : CollatzResearch.WordTrace tailWord_3256419 prefixEnd_3256419 1114738772955733319591005 := by
  unfold tailWord_3256419
  simp only [CollatzResearch.WordTrace]
  refine ⟨118771358389557589932780311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79180905593038393288520207 118771358389557589932780311)
  ·
    refine ⟨178157037584336384899170467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118771358389557589932780311 178157037584336384899170467)
    ·
      refine ⟨267235556376504577348755701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178157037584336384899170467 267235556376504577348755701)
      ·
        refine ⟨25053333410297304126445847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 267235556376504577348755701 25053333410297304126445847)
        ·
          refine ⟨37580000115445956189668771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25053333410297304126445847 37580000115445956189668771)
          ·
            refine ⟨56370000173168934284503157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37580000115445956189668771 56370000173168934284503157)
            ·
              refine ⟨5284687516234587589172171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56370000173168934284503157 5284687516234587589172171)
              ·
                refine ⟨7927031274351881383758257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5284687516234587589172171 7927031274351881383758257)
                ·
                  refine ⟨5945273455763911037818693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7927031274351881383758257 5945273455763911037818693)
                  ·
                    refine ⟨1114738772955733319591005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5945273455763911037818693 1114738772955733319591005)
                    ·
                      rfl

theorem cell22_3256419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 4].length) (baseStart_3256419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3256419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3256419 prefixEnd_3256419 := by exact prefixLift 3256419
  have htrace : WordTrace (prefixWord ++ tailWord_3256419) baseStart_3256419 baseEnd_3256419 := by
    simpa [prefixWord, tailWord_3256419, baseEnd_3256419] using wordTrace_append hprefix tailTrace_3256419
  have hstable : (prefixWord ++ tailWord_3256419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256419).length < 2 ^ (prefixWord ++ tailWord_3256419).sum := by decide
  have hdescent : baseEnd_3256419 < baseStart_3256419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256438 : List Nat := [5, 1, 1, 2, 1, 2, 3, 2, 2, 3]
def baseStart_3256438 : Nat := 118140960795 + 3256438 * 2 ^ 59
def prefixEnd_3256438 : Nat := 4983230072969 + 3 ^ 40 * 3256438 * 2
def baseEnd_3256438 : Nat := 1114745277044023603365947

theorem tailTrace_3256438 : CollatzResearch.WordTrace tailWord_3256438 prefixEnd_3256438 1114745277044023603365947 := by
  unfold tailWord_3256438
  simp only [CollatzResearch.WordTrace]
  refine ⟨7423253211030547261107623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79181367584325837451814645 7423253211030547261107623)
  ·
    refine ⟨11134879816545820891661435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7423253211030547261107623 11134879816545820891661435)
    ·
      refine ⟨16702319724818731337492153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11134879816545820891661435 16702319724818731337492153)
      ·
        refine ⟨12526739793614048503119115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16702319724818731337492153 12526739793614048503119115)
        ·
          refine ⟨18790109690421072754678673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12526739793614048503119115 18790109690421072754678673)
          ·
            refine ⟨14092582267815804566009005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18790109690421072754678673 14092582267815804566009005)
            ·
              refine ⟨5284718350430926712253377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14092582267815804566009005 5284718350430926712253377)
              ·
                refine ⟨3963538762823195034190033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5284718350430926712253377 3963538762823195034190033)
                ·
                  refine ⟨2972654072117396275642525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3963538762823195034190033 2972654072117396275642525)
                  ·
                    refine ⟨1114745277044023603365947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2972654072117396275642525 1114745277044023603365947)
                    ·
                      rfl

theorem cell22_3256438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_3256438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3256438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3256438 prefixEnd_3256438 := by exact prefixLift 3256438
  have htrace : WordTrace (prefixWord ++ tailWord_3256438) baseStart_3256438 baseEnd_3256438 := by
    simpa [prefixWord, tailWord_3256438, baseEnd_3256438] using wordTrace_append hprefix tailTrace_3256438
  have hstable : (prefixWord ++ tailWord_3256438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256438).length < 2 ^ (prefixWord ++ tailWord_3256438).sum := by decide
  have hdescent : baseEnd_3256438 < baseStart_3256438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256466 : List Nat := [3, 2, 3, 1, 1, 1, 1, 4, 3, 3]
def baseStart_3256466 : Nat := 118140960795 + 3256466 * 2 ^ 59
def prefixEnd_3256466 : Nat := 4983230072969 + 3 ^ 40 * 3256466 * 2
def baseEnd_3256466 : Nat := 1114754862016240863665861

theorem tailTrace_3256466 : CollatzResearch.WordTrace tailWord_3256466 prefixEnd_3256466 1114754862016240863665861 := by
  unfold tailWord_3256466
  simp only [CollatzResearch.WordTrace]
  refine ⟨29693268155096829239935313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79182048413591544639827501 29693268155096829239935313)
  ·
    refine ⟨22269951116322621929951485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29693268155096829239935313 22269951116322621929951485)
    ·
      refine ⟨8351231668620983223731807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22269951116322621929951485 8351231668620983223731807)
      ·
        refine ⟨12526847502931474835597711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8351231668620983223731807 12526847502931474835597711)
        ·
          refine ⟨18790271254397212253396567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12526847502931474835597711 18790271254397212253396567)
          ·
            refine ⟨28185406881595818380094851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18790271254397212253396567 28185406881595818380094851)
            ·
              refine ⟨42278110322393727570142277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28185406881595818380094851 42278110322393727570142277)
              ·
                refine ⟨7927145685448823919401677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42278110322393727570142277 7927145685448823919401677)
                ·
                  refine ⟨2972679632043308969775629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7927145685448823919401677 2972679632043308969775629)
                  ·
                    refine ⟨1114754862016240863665861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2972679632043308969775629 1114754862016240863665861)
                    ·
                      rfl

theorem cell22_3256466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_3256466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3256466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3256466 prefixEnd_3256466 := by exact prefixLift 3256466
  have htrace : WordTrace (prefixWord ++ tailWord_3256466) baseStart_3256466 baseEnd_3256466 := by
    simpa [prefixWord, tailWord_3256466, baseEnd_3256466] using wordTrace_append hprefix tailTrace_3256466
  have hstable : (prefixWord ++ tailWord_3256466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256466).length < 2 ^ (prefixWord ++ tailWord_3256466).sum := by decide
  have hdescent : baseEnd_3256466 < baseStart_3256466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256479 : List Nat := [1, 1, 2, 6, 1, 1, 1, 2, 7]
def baseStart_3256479 : Nat := 118140960795 + 3256479 * 2 ^ 59
def prefixEnd_3256479 : Nat := 4983230072969 + 3 ^ 40 * 3256479 * 2
def baseEnd_3256479 : Nat := 371586437393971054363607

theorem tailTrace_3256479 : CollatzResearch.WordTrace tailWord_3256479 prefixEnd_3256479 371586437393971054363607 := by
  unfold tailWord_3256479
  simp only [CollatzResearch.WordTrace]
  refine ⟨118773546769340220179964491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79182364512893480119976327 118773546769340220179964491)
  ·
    refine ⟨178160320154010330269946737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118773546769340220179964491 178160320154010330269946737)
    ·
      refine ⟨133620240115507747702460053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178160320154010330269946737 133620240115507747702460053)
      ·
        refine ⟨6263448755414425673552815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 133620240115507747702460053 6263448755414425673552815)
        ·
          refine ⟨9395173133121638510329223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6263448755414425673552815 9395173133121638510329223)
          ·
            refine ⟨14092759699682457765493835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9395173133121638510329223 14092759699682457765493835)
            ·
              refine ⟨21139139549523686648240753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14092759699682457765493835 21139139549523686648240753)
              ·
                refine ⟨15854354662142764986180565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21139139549523686648240753 15854354662142764986180565)
                ·
                  refine ⟨371586437393971054363607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15854354662142764986180565 371586437393971054363607)
                  ·
                    rfl

theorem cell22_3256479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 7].length) (baseStart_3256479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3256479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3256479 prefixEnd_3256479 := by exact prefixLift 3256479
  have htrace : WordTrace (prefixWord ++ tailWord_3256479) baseStart_3256479 baseEnd_3256479 := by
    simpa [prefixWord, tailWord_3256479, baseEnd_3256479] using wordTrace_append hprefix tailTrace_3256479
  have hstable : (prefixWord ++ tailWord_3256479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256479).length < 2 ^ (prefixWord ++ tailWord_3256479).sum := by decide
  have hdescent : baseEnd_3256479 < baseStart_3256479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256492 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 1, 10]
def baseStart_3256492 : Nat := 118140960795 + 3256492 * 2 ^ 59
def prefixEnd_3256492 : Nat := 4983230072969 + 3 ^ 40 * 3256492 * 2
def baseEnd_3256492 : Nat := 1114763762347585462515781

theorem tailTrace_3256492 : CollatzResearch.WordTrace tailWord_3256492 prefixEnd_3256492 1114763762347585462515781 := by
  unfold tailWord_3256492
  simp only [CollatzResearch.WordTrace]
  refine ⟨59387010459146561700093865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79182680612195415600125153 59387010459146561700093865)
  ·
    refine ⟨44540257844359921275070399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59387010459146561700093865 44540257844359921275070399)
    ·
      refine ⟨66810386766539881912605599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44540257844359921275070399 66810386766539881912605599)
      ·
        refine ⟨100215580149809822868908399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66810386766539881912605599 100215580149809822868908399)
        ·
          refine ⟨150323370224714734303362599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100215580149809822868908399 150323370224714734303362599)
          ·
            refine ⟨225485055337072101455043899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150323370224714734303362599 225485055337072101455043899)
            ·
              refine ⟨338227583005608152182565849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225485055337072101455043899 338227583005608152182565849)
              ·
                refine ⟨253670687254206114136924387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 338227583005608152182565849 253670687254206114136924387)
                ·
                  refine ⟨380506030881309171205386581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 253670687254206114136924387 380506030881309171205386581)
                  ·
                    refine ⟨1114763762347585462515781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 380506030881309171205386581 1114763762347585462515781)
                    ·
                      rfl

theorem cell22_3256492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_3256492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3256492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3256492 prefixEnd_3256492 := by exact prefixLift 3256492
  have htrace : WordTrace (prefixWord ++ tailWord_3256492) baseStart_3256492 baseEnd_3256492 := by
    simpa [prefixWord, tailWord_3256492, baseEnd_3256492] using wordTrace_append hprefix tailTrace_3256492
  have hstable : (prefixWord ++ tailWord_3256492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256492).length < 2 ^ (prefixWord ++ tailWord_3256492).sum := by decide
  have hdescent : baseEnd_3256492 < baseStart_3256492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256509 : List Nat := [1, 4, 1, 2, 1, 1, 1, 4, 3, 4]
def baseStart_3256509 : Nat := 118140960795 + 3256509 * 2 ^ 59
def prefixEnd_3256509 : Nat := 4983230072969 + 3 ^ 40 * 3256509 * 2
def baseEnd_3256509 : Nat := 1114769581795003084840729

theorem tailTrace_3256509 : CollatzResearch.WordTrace tailWord_3256509 prefixEnd_3256509 1114769581795003084840729 := by
  unfold tailWord_3256509
  simp only [CollatzResearch.WordTrace]
  refine ⟨118774640959231535303556581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79183093972821023535704387 118774640959231535303556581)
  ·
    refine ⟨22270245179855912869416859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118774640959231535303556581 22270245179855912869416859)
    ·
      refine ⟨33405367769783869304125289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22270245179855912869416859 33405367769783869304125289)
      ·
        refine ⟨25054025827337901978093967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33405367769783869304125289 25054025827337901978093967)
        ·
          refine ⟨37581038741006852967140951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25054025827337901978093967 37581038741006852967140951)
          ·
            refine ⟨56371558111510279450711427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37581038741006852967140951 56371558111510279450711427)
            ·
              refine ⟨84557337167265419176067141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56371558111510279450711427 84557337167265419176067141)
              ·
                refine ⟨15854500718862266095512589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84557337167265419176067141 15854500718862266095512589)
                ·
                  refine ⟨5945437769573349785817221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15854500718862266095512589 5945437769573349785817221)
                  ·
                    refine ⟨1114769581795003084840729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5945437769573349785817221 1114769581795003084840729)
                    ·
                      rfl

theorem cell22_3256509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_3256509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3256509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3256509 prefixEnd_3256509 := by exact prefixLift 3256509
  have htrace : WordTrace (prefixWord ++ tailWord_3256509) baseStart_3256509 baseEnd_3256509 := by
    simpa [prefixWord, tailWord_3256509, baseEnd_3256509] using wordTrace_append hprefix tailTrace_3256509
  have hstable : (prefixWord ++ tailWord_3256509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256509).length < 2 ^ (prefixWord ++ tailWord_3256509).sum := by decide
  have hdescent : baseEnd_3256509 < baseStart_3256509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256513 : List Nat := [1, 2, 6, 1, 2, 1, 1, 3, 5]
def baseStart_3256513 : Nat := 118140960795 + 3256513 * 2 ^ 59
def prefixEnd_3256513 : Nat := 4983230072969 + 3 ^ 40 * 3256513 * 2
def baseEnd_3256513 : Nat := 371590317025582802580239

theorem tailTrace_3256513 : CollatzResearch.WordTrace tailWord_3256513 prefixEnd_3256513 371590317025582802580239 := by
  unfold tailWord_3256513
  simp only [CollatzResearch.WordTrace]
  refine ⟨118774786851217043986702193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79183191234144695991134795 118774786851217043986702193)
  ·
    refine ⟨89081090138412782990026645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118774786851217043986702193 89081090138412782990026645)
    ·
      refine ⟨4175676100238099202657499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 89081090138412782990026645 4175676100238099202657499)
      ·
        refine ⟨6263514150357148803986249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4175676100238099202657499 6263514150357148803986249)
        ·
          refine ⟨4697635612767861602989687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6263514150357148803986249 4697635612767861602989687)
          ·
            refine ⟨7046453419151792404484531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4697635612767861602989687 7046453419151792404484531)
            ·
              refine ⟨10569680128727688606726797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7046453419151792404484531 10569680128727688606726797)
              ·
                refine ⟨3963630048272883227522549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10569680128727688606726797 3963630048272883227522549)
                ·
                  refine ⟨371590317025582802580239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3963630048272883227522549 371590317025582802580239)
                  ·
                    rfl

theorem cell22_3256513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 5].length) (baseStart_3256513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3256513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3256513 prefixEnd_3256513 := by exact prefixLift 3256513
  have htrace : WordTrace (prefixWord ++ tailWord_3256513) baseStart_3256513 baseEnd_3256513 := by
    simpa [prefixWord, tailWord_3256513, baseEnd_3256513] using wordTrace_append hprefix tailTrace_3256513
  have hstable : (prefixWord ++ tailWord_3256513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256513).length < 2 ^ (prefixWord ++ tailWord_3256513).sum := by decide
  have hdescent : baseEnd_3256513 < baseStart_3256513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256526 : List Nat := [4, 1, 1, 1, 4, 2, 1, 1, 3, 4]
def baseStart_3256526 : Nat := 118140960795 + 3256526 * 2 ^ 59
def prefixEnd_3256526 : Nat := 4983230072969 + 3 ^ 40 * 3256526 * 2
def baseEnd_3256526 : Nat := 1114775401242420707165677

theorem tailTrace_3256526 : CollatzResearch.WordTrace tailWord_3256526 prefixEnd_3256526 1114775401242420707165677 := by
  unfold tailWord_3256526
  simp only [CollatzResearch.WordTrace]
  refine ⟨14846907625021243400865679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79183507333446631471283621 14846907625021243400865679)
  ·
    refine ⟨22270361437531865101298519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14846907625021243400865679 22270361437531865101298519)
    ·
      refine ⟨33405542156297797651947779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22270361437531865101298519 33405542156297797651947779)
      ·
        refine ⟨50108313234446696477921669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33405542156297797651947779 50108313234446696477921669)
        ·
          refine ⟨9395308731458755589610313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50108313234446696477921669 9395308731458755589610313)
          ·
            refine ⟨7046481548594066692207735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9395308731458755589610313 7046481548594066692207735)
            ·
              refine ⟨10569722322891100038311603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7046481548594066692207735 10569722322891100038311603)
              ·
                refine ⟨15854583484336650057467405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10569722322891100038311603 15854583484336650057467405)
                ·
                  refine ⟨5945468806626243771550277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15854583484336650057467405 5945468806626243771550277)
                  ·
                    refine ⟨1114775401242420707165677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5945468806626243771550277 1114775401242420707165677)
                    ·
                      rfl

theorem cell22_3256526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_3256526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3256526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3256526 prefixEnd_3256526 := by exact prefixLift 3256526
  have htrace : WordTrace (prefixWord ++ tailWord_3256526) baseStart_3256526 baseEnd_3256526 := by
    simpa [prefixWord, tailWord_3256526, baseEnd_3256526] using wordTrace_append hprefix tailTrace_3256526
  have hstable : (prefixWord ++ tailWord_3256526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256526).length < 2 ^ (prefixWord ++ tailWord_3256526).sum := by decide
  have hdescent : baseEnd_3256526 < baseStart_3256526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256753 : List Nat := [1, 2, 2, 4, 1, 2, 1, 1, 5, 3]
def baseStart_3256753 : Nat := 118140960795 + 3256753 * 2 ^ 59
def prefixEnd_3256753 : Nat := 4983230072969 + 3 ^ 40 * 3256753 * 2
def baseEnd_3256753 : Nat := 1114853107981467781739981

theorem tailTrace_3256753 : CollatzResearch.WordTrace tailWord_3256753 prefixEnd_3256753 1114853107981467781739981 := by
  unfold tailWord_3256753
  simp only [CollatzResearch.WordTrace]
  refine ⟨118783540370347564975438913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79189026913565043316959275 118783540370347564975438913)
  ·
    refine ⟨89087655277760673731579185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118783540370347564975438913 89087655277760673731579185)
    ·
      refine ⟨66815741458320505298684389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89087655277760673731579185 66815741458320505298684389)
      ·
        refine ⟨12527951523435094743503323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66815741458320505298684389 12527951523435094743503323)
        ·
          refine ⟨18791927285152642115254985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12527951523435094743503323 18791927285152642115254985)
          ·
            refine ⟨14093945463864481586441239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18791927285152642115254985 14093945463864481586441239)
            ·
              refine ⟨21140918195796722379661859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14093945463864481586441239 21140918195796722379661859)
              ·
                refine ⟨31711377293695083569492789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21140918195796722379661859 31711377293695083569492789)
                ·
                  refine ⟨2972941621283914084639949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31711377293695083569492789 2972941621283914084639949)
                  ·
                    refine ⟨1114853107981467781739981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2972941621283914084639949 1114853107981467781739981)
                    ·
                      rfl

theorem cell22_3256753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 5, 3].length) (baseStart_3256753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3256753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3256753 prefixEnd_3256753 := by exact prefixLift 3256753
  have htrace : WordTrace (prefixWord ++ tailWord_3256753) baseStart_3256753 baseEnd_3256753 := by
    simpa [prefixWord, tailWord_3256753, baseEnd_3256753] using wordTrace_append hprefix tailTrace_3256753
  have hstable : (prefixWord ++ tailWord_3256753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256753).length < 2 ^ (prefixWord ++ tailWord_3256753).sum := by decide
  have hdescent : baseEnd_3256753 < baseStart_3256753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256757 : List Nat := [1, 3, 3, 2, 4, 1, 1, 1, 2, 4]
def baseStart_3256757 : Nat := 118140960795 + 3256757 * 2 ^ 59
def prefixEnd_3256757 : Nat := 4983230072969 + 3 ^ 40 * 3256757 * 2
def baseEnd_3256757 : Nat := 1114854477263213104639969

theorem tailTrace_3256757 : CollatzResearch.WordTrace tailWord_3256757 prefixEnd_3256757 1114854477263213104639969 := by
  unfold tailWord_3256757
  simp only [CollatzResearch.WordTrace]
  refine ⟨118783686262333073658584525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79189124174888715772389683 118783686262333073658584525)
  ·
    refine ⟨44543882348374902621969197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118783686262333073658584525 44543882348374902621969197)
    ·
      refine ⟨16703955880640588483238449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44543882348374902621969197 16703955880640588483238449)
      ·
        refine ⟨12527966910480441362428837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16703955880640588483238449 12527966910480441362428837)
        ·
          refine ⟨2348993795715082755455407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12527966910480441362428837 2348993795715082755455407)
          ·
            refine ⟨3523490693572624133183111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2348993795715082755455407 3523490693572624133183111)
            ·
              refine ⟨5285236040358936199774667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3523490693572624133183111 5285236040358936199774667)
              ·
                refine ⟨7927854060538404299662001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5285236040358936199774667 7927854060538404299662001)
                ·
                  refine ⟨5945890545403803224746501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7927854060538404299662001 5945890545403803224746501)
                  ·
                    refine ⟨1114854477263213104639969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5945890545403803224746501 1114854477263213104639969)
                    ·
                      rfl

theorem cell22_3256757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_3256757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3256757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3256757 prefixEnd_3256757 := by exact prefixLift 3256757
  have htrace : WordTrace (prefixWord ++ tailWord_3256757) baseStart_3256757 baseEnd_3256757 := by
    simpa [prefixWord, tailWord_3256757, baseEnd_3256757] using wordTrace_append hprefix tailTrace_3256757
  have hstable : (prefixWord ++ tailWord_3256757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256757).length < 2 ^ (prefixWord ++ tailWord_3256757).sum := by decide
  have hdescent : baseEnd_3256757 < baseStart_3256757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256811 : List Nat := [1, 1, 1, 1, 2, 3, 3, 4, 6]
def baseStart_3256811 : Nat := 118140960795 + 3256811 * 2 ^ 59
def prefixEnd_3256811 : Nat := 4983230072969 + 3 ^ 40 * 3256811 * 2
def baseEnd_3256811 : Nat := 371624320855591654596601

theorem tailTrace_3256811 : CollatzResearch.WordTrace tailWord_3256811 prefixEnd_3256811 371624320855591654596601 := by
  unfold tailWord_3256811
  simp only [CollatzResearch.WordTrace]
  refine ⟨118785655804137440881050287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79190437202758293920700191 118785655804137440881050287)
  ·
    refine ⟨178178483706206161321575431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118785655804137440881050287 178178483706206161321575431)
    ·
      refine ⟨267267725559309241982363147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178178483706206161321575431 267267725559309241982363147)
      ·
        refine ⟨400901588338963862973544721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267267725559309241982363147 400901588338963862973544721)
        ·
          refine ⟨300676191254222897230158541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400901588338963862973544721 300676191254222897230158541)
          ·
            refine ⟨112753571720333586461309453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 300676191254222897230158541 112753571720333586461309453)
            ·
              refine ⟨42282589395125094922991045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112753571720333586461309453 42282589395125094922991045)
              ·
                refine ⟨7927985511585955298060821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42282589395125094922991045 7927985511585955298060821)
                ·
                  refine ⟨371624320855591654596601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7927985511585955298060821 371624320855591654596601)
                  ·
                    rfl

theorem cell22_3256811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 6].length) (baseStart_3256811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3256811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3256811 prefixEnd_3256811 := by exact prefixLift 3256811
  have htrace : WordTrace (prefixWord ++ tailWord_3256811) baseStart_3256811 baseEnd_3256811 := by
    simpa [prefixWord, tailWord_3256811, baseEnd_3256811] using wordTrace_append hprefix tailTrace_3256811
  have hstable : (prefixWord ++ tailWord_3256811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256811).length < 2 ^ (prefixWord ++ tailWord_3256811).sum := by decide
  have hdescent : baseEnd_3256811 < baseStart_3256811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256821 : List Nat := [1, 3, 5, 1, 2, 2, 1, 3, 1, 3]
def baseStart_3256821 : Nat := 118140960795 + 3256821 * 2 ^ 59
def prefixEnd_3256821 : Nat := 4983230072969 + 3 ^ 40 * 3256821 * 2
def baseEnd_3256821 : Nat := 1114876385771138271039773

theorem tailTrace_3256821 : CollatzResearch.WordTrace tailWord_3256821 prefixEnd_3256821 1114876385771138271039773 := by
  unfold tailWord_3256821
  simp only [CollatzResearch.WordTrace]
  refine ⟨118786020534101212588914317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79190680356067475059276211 118786020534101212588914317)
  ·
    refine ⟨44544757700287954720842869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118786020534101212588914317 44544757700287954720842869)
    ·
      refine ⟨4176071034401995755079019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44544757700287954720842869 4176071034401995755079019)
      ·
        refine ⟨6264106551602993632618529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4176071034401995755079019 6264106551602993632618529)
        ·
          refine ⟨4698079913702245224463897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6264106551602993632618529 4698079913702245224463897)
          ·
            refine ⟨3523559935276683918347923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4698079913702245224463897 3523559935276683918347923)
            ·
              refine ⟨5285339902915025877521885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3523559935276683918347923 5285339902915025877521885)
              ·
                refine ⟨1982002463593134704070707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5285339902915025877521885 1982002463593134704070707)
                ·
                  refine ⟨2973003695389702056106061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1982002463593134704070707 2973003695389702056106061)
                  ·
                    refine ⟨1114876385771138271039773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2973003695389702056106061 1114876385771138271039773)
                    ·
                      rfl

theorem cell22_3256821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_3256821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3256821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3256821 prefixEnd_3256821 := by exact prefixLift 3256821
  have htrace : WordTrace (prefixWord ++ tailWord_3256821) baseStart_3256821 baseEnd_3256821 := by
    simpa [prefixWord, tailWord_3256821, baseEnd_3256821] using wordTrace_append hprefix tailTrace_3256821
  have hstable : (prefixWord ++ tailWord_3256821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256821).length < 2 ^ (prefixWord ++ tailWord_3256821).sum := by decide
  have hdescent : baseEnd_3256821 < baseStart_3256821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256841 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 3, 6]
def baseStart_3256841 : Nat := 118140960795 + 3256841 * 2 ^ 59
def prefixEnd_3256841 : Nat := 4983230072969 + 3 ^ 40 * 3256841 * 2
def baseEnd_3256841 : Nat := 1114883232179864885539711

theorem tailTrace_3256841 : CollatzResearch.WordTrace tailWord_3256841 prefixEnd_3256841 1114883232179864885539711 := by
  unfold tailWord_3256841
  simp only [CollatzResearch.WordTrace]
  refine ⟨118786749994028756004642377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79191166662685837336428251 118786749994028756004642377)
  ·
    refine ⟨89090062495521567003481783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118786749994028756004642377 89090062495521567003481783)
    ·
      refine ⟨133635093743282350505222675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89090062495521567003481783 133635093743282350505222675)
      ·
        refine ⟨200452640614923525757834013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133635093743282350505222675 200452640614923525757834013)
        ·
          refine ⟨75169740230596322159187755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200452640614923525757834013 75169740230596322159187755)
          ·
            refine ⟨112754610345894483238781633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75169740230596322159187755 112754610345894483238781633)
            ·
              refine ⟨84565957759420862429086225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112754610345894483238781633 84565957759420862429086225)
              ·
                refine ⟨63424468319565646821814669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84565957759420862429086225 63424468319565646821814669)
                ·
                  refine ⟨23784175619837117558180501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63424468319565646821814669 23784175619837117558180501)
                  ·
                    refine ⟨1114883232179864885539711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23784175619837117558180501 1114883232179864885539711)
                    ·
                      rfl

theorem cell22_3256841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 6].length) (baseStart_3256841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3256841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3256841 prefixEnd_3256841 := by exact prefixLift 3256841
  have htrace : WordTrace (prefixWord ++ tailWord_3256841) baseStart_3256841 baseEnd_3256841 := by
    simpa [prefixWord, tailWord_3256841, baseEnd_3256841] using wordTrace_append hprefix tailTrace_3256841
  have hstable : (prefixWord ++ tailWord_3256841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256841).length < 2 ^ (prefixWord ++ tailWord_3256841).sum := by decide
  have hdescent : baseEnd_3256841 < baseStart_3256841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256864 : List Nat := [2, 1, 1, 6, 3, 1, 1, 2, 1, 4]
def baseStart_3256864 : Nat := 118140960795 + 3256864 * 2 ^ 59
def prefixEnd_3256864 : Nat := 4983230072969 + 3 ^ 40 * 3256864 * 2
def baseEnd_3256864 : Nat := 1114891105549900492214641

theorem tailTrace_3256864 : CollatzResearch.WordTrace tailWord_3256864 prefixEnd_3256864 1114891105549900492214641 := by
  unfold tailWord_3256864
  simp only [CollatzResearch.WordTrace]
  refine ⟨59393794436472715466364823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79191725915296953955153097 59393794436472715466364823)
  ·
    refine ⟨89090691654709073199547235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59393794436472715466364823 89090691654709073199547235)
    ·
      refine ⟨133636037482063609799320853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89090691654709073199547235 133636037482063609799320853)
      ·
        refine ⟨6264189256971731709343165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 133636037482063609799320853 6264189256971731709343165)
        ·
          refine ⟨2349070971364399391003687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6264189256971731709343165 2349070971364399391003687)
          ·
            refine ⟨3523606457046599086505531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2349070971364399391003687 3523606457046599086505531)
            ·
              refine ⟨5285409685569898629758297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3523606457046599086505531 5285409685569898629758297)
              ·
                refine ⟨3964057264177423972318723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5285409685569898629758297 3964057264177423972318723)
                ·
                  refine ⟨5946085896266135958478085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3964057264177423972318723 5946085896266135958478085)
                  ·
                    refine ⟨1114891105549900492214641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5946085896266135958478085 1114891105549900492214641)
                    ·
                      rfl

theorem cell22_3256864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 1, 4].length) (baseStart_3256864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3256864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3256864 prefixEnd_3256864 := by exact prefixLift 3256864
  have htrace : WordTrace (prefixWord ++ tailWord_3256864) baseStart_3256864 baseEnd_3256864 := by
    simpa [prefixWord, tailWord_3256864, baseEnd_3256864] using wordTrace_append hprefix tailTrace_3256864
  have hstable : (prefixWord ++ tailWord_3256864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256864).length < 2 ^ (prefixWord ++ tailWord_3256864).sum := by decide
  have hdescent : baseEnd_3256864 < baseStart_3256864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256903 : List Nat := [1, 1, 4, 1, 4, 1, 1, 1, 2, 6]
def baseStart_3256903 : Nat := 118140960795 + 3256903 * 2 ^ 59
def prefixEnd_3256903 : Nat := 4983230072969 + 3 ^ 40 * 3256903 * 2
def baseEnd_3256903 : Nat := 1114904456046917390489521

theorem tailTrace_3256903 : CollatzResearch.WordTrace tailWord_3256903 prefixEnd_3256903 1114904456046917390489521 := by
  unfold tailWord_3256903
  simp only [CollatzResearch.WordTrace]
  refine ⟨118789011319804140593399363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79192674213202760395599575 118789011319804140593399363)
  ·
    refine ⟨178183516979706210890099045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118789011319804140593399363 178183516979706210890099045)
    ·
      refine ⟨33409409433694914541893571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178183516979706210890099045 33409409433694914541893571)
      ·
        refine ⟨50114114150542371812840357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33409409433694914541893571 50114114150542371812840357)
        ·
          refine ⟨9396396403226694714907567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50114114150542371812840357 9396396403226694714907567)
          ·
            refine ⟨14094594604840042072361351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9396396403226694714907567 14094594604840042072361351)
            ·
              refine ⟨21141891907260063108542027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14094594604840042072361351 21141891907260063108542027)
              ·
                refine ⟨31712837860890094662813041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21141891907260063108542027 31712837860890094662813041)
                ·
                  refine ⟨23784628395667570997109781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31712837860890094662813041 23784628395667570997109781)
                  ·
                    refine ⟨1114904456046917390489521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23784628395667570997109781 1114904456046917390489521)
                    ·
                      rfl

theorem cell22_3256903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_3256903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3256903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3256903 prefixEnd_3256903 := by exact prefixLift 3256903
  have htrace : WordTrace (prefixWord ++ tailWord_3256903) baseStart_3256903 baseEnd_3256903 := by
    simpa [prefixWord, tailWord_3256903, baseEnd_3256903] using wordTrace_append hprefix tailTrace_3256903
  have hstable : (prefixWord ++ tailWord_3256903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256903).length < 2 ^ (prefixWord ++ tailWord_3256903).sum := by decide
  have hdescent : baseEnd_3256903 < baseStart_3256903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256963 : List Nat := [1, 1, 1, 3, 3, 1, 3, 3, 6]
def baseStart_3256963 : Nat := 118140960795 + 3256963 * 2 ^ 59
def prefixEnd_3256963 : Nat := 4983230072969 + 3 ^ 40 * 3256963 * 2
def baseEnd_3256963 : Nat := 371641665091032411329779

theorem tailTrace_3256963 : CollatzResearch.WordTrace tailWord_3256963 prefixEnd_3256963 371641665091032411329779 := by
  unfold tailWord_3256963
  simp only [CollatzResearch.WordTrace]
  refine ⟨118791199699586770840583543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79194133133057847227055695 118791199699586770840583543)
  ·
    refine ⟨178186799549380156260875315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118791199699586770840583543 178186799549380156260875315)
    ·
      refine ⟨267280199324070234391312973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178186799549380156260875315 267280199324070234391312973)
      ·
        refine ⟨100230074746526337896742365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267280199324070234391312973 100230074746526337896742365)
        ·
          refine ⟨37586278029947376711278387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100230074746526337896742365 37586278029947376711278387)
          ·
            refine ⟨56379417044921065066917581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37586278029947376711278387 56379417044921065066917581)
            ·
              refine ⟨21142281391845399400094093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56379417044921065066917581 21142281391845399400094093)
              ·
                refine ⟨7928355521942024775035285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21142281391845399400094093 7928355521942024775035285)
                ·
                  refine ⟨371641665091032411329779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7928355521942024775035285 371641665091032411329779)
                  ·
                    rfl

theorem cell22_3256963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 6].length) (baseStart_3256963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3256963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3256963 prefixEnd_3256963 := by exact prefixLift 3256963
  have htrace : WordTrace (prefixWord ++ tailWord_3256963) baseStart_3256963 baseEnd_3256963 := by
    simpa [prefixWord, tailWord_3256963, baseEnd_3256963] using wordTrace_append hprefix tailTrace_3256963
  have hstable : (prefixWord ++ tailWord_3256963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256963).length < 2 ^ (prefixWord ++ tailWord_3256963).sum := by decide
  have hdescent : baseEnd_3256963 < baseStart_3256963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257044 : List Nat := [2, 4, 1, 3, 2, 1, 2, 1, 2, 4]
def baseStart_3257044 : Nat := 118140960795 + 3257044 * 2 ^ 59
def prefixEnd_3257044 : Nat := 4983230072969 + 3 ^ 40 * 3257044 * 2
def baseEnd_3257044 : Nat := 1114952723228440022714089

theorem tailTrace_3257044 : CollatzResearch.WordTrace tailWord_3257044 prefixEnd_3257044 1114952723228440022714089 := by
  unfold tailWord_3257044
  simp only [CollatzResearch.WordTrace]
  refine ⟨59397077006146660837141093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79196102674862214449521457 59397077006146660837141093)
  ·
    refine ⟨11136951938652498906963955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59397077006146660837141093 11136951938652498906963955)
    ·
      refine ⟨16705427907978748360445933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11136951938652498906963955 16705427907978748360445933)
      ·
        refine ⟨6264535465492030635167225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16705427907978748360445933 6264535465492030635167225)
        ·
          refine ⟨4698401599119022976375419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6264535465492030635167225 4698401599119022976375419)
          ·
            refine ⟨7047602398678534464563129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4698401599119022976375419 7047602398678534464563129)
            ·
              refine ⟨5285701799008900848422347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7047602398678534464563129 5285701799008900848422347)
              ·
                refine ⟨7928552698513351272633521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5285701799008900848422347 7928552698513351272633521)
                ·
                  refine ⟨5946414523885013454475141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7928552698513351272633521 5946414523885013454475141)
                  ·
                    refine ⟨1114952723228440022714089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5946414523885013454475141 1114952723228440022714089)
                    ·
                      rfl

theorem cell22_3257044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_3257044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3257044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3257044 prefixEnd_3257044 := by exact prefixLift 3257044
  have htrace : WordTrace (prefixWord ++ tailWord_3257044) baseStart_3257044 baseEnd_3257044 := by
    simpa [prefixWord, tailWord_3257044, baseEnd_3257044] using wordTrace_append hprefix tailTrace_3257044
  have hstable : (prefixWord ++ tailWord_3257044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257044).length < 2 ^ (prefixWord ++ tailWord_3257044).sum := by decide
  have hdescent : baseEnd_3257044 < baseStart_3257044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257076 : List Nat := [2, 6, 1, 1, 2, 2, 1, 7]
def baseStart_3257076 : Nat := 118140960795 + 3257076 * 2 ^ 59
def prefixEnd_3257076 : Nat := 4983230072969 + 3 ^ 40 * 3257076 * 2
def baseEnd_3257076 : Nat := 123884853053600289545999

theorem tailTrace_3257076 : CollatzResearch.WordTrace tailWord_3257076 prefixEnd_3257076 123884853053600289545999 := by
  unfold tailWord_3257076
  simp only [CollatzResearch.WordTrace]
  refine ⟨59397660574088695569723541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79196880765451594092964721 59397660574088695569723541)
  ·
    refine ⟨2784265339410407604830791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 59397660574088695569723541 2784265339410407604830791)
    ·
      refine ⟨4176398009115611407246187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2784265339410407604830791 4176398009115611407246187)
      ·
        refine ⟨6264597013673417110869281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4176398009115611407246187 6264597013673417110869281)
        ·
          refine ⟨4698447760255062833151961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6264597013673417110869281 4698447760255062833151961)
          ·
            refine ⟨3523835820191297124863971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4698447760255062833151961 3523835820191297124863971)
            ·
              refine ⟨5285753730286945687295957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3523835820191297124863971 5285753730286945687295957)
              ·
                refine ⟨123884853053600289545999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5285753730286945687295957 123884853053600289545999)
                ·
                  rfl

theorem cell22_3257076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 7].length) (baseStart_3257076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3257076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3257076 prefixEnd_3257076 := by exact prefixLift 3257076
  have htrace : WordTrace (prefixWord ++ tailWord_3257076) baseStart_3257076 baseEnd_3257076 := by
    simpa [prefixWord, tailWord_3257076, baseEnd_3257076] using wordTrace_append hprefix tailTrace_3257076
  have hstable : (prefixWord ++ tailWord_3257076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257076).length < 2 ^ (prefixWord ++ tailWord_3257076).sum := by decide
  have hdescent : baseEnd_3257076 < baseStart_3257076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257085 : List Nat := [1, 4, 1, 1, 1, 1, 5, 1, 2, 5]
def baseStart_3257085 : Nat := 118140960795 + 3257085 * 2 ^ 59
def prefixEnd_3257085 : Nat := 4983230072969 + 3 ^ 40 * 3257085 * 2
def baseEnd_3257085 : Nat := 1114966758366329582438963

theorem tailTrace_3257085 : CollatzResearch.WordTrace tailWord_3257085 prefixEnd_3257085 1114966758366329582438963 := by
  unfold tailWord_3257085
  simp only [CollatzResearch.WordTrace]
  refine ⟨118795649405144785676524709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79197099603429857117683139 118795649405144785676524709)
  ·
    refine ⟨22274184263464647314348383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118795649405144785676524709 22274184263464647314348383)
    ·
      refine ⟨33411276395196970971522575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22274184263464647314348383 33411276395196970971522575)
      ·
        refine ⟨50116914592795456457283863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33411276395196970971522575 50116914592795456457283863)
        ·
          refine ⟨75175371889193184685925795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50116914592795456457283863 75175371889193184685925795)
          ·
            refine ⟨112763057833789777028888693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75175371889193184685925795 112763057833789777028888693)
            ·
              refine ⟨10571536671917791596458315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 112763057833789777028888693 10571536671917791596458315)
              ·
                refine ⟨15857305007876687394687473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10571536671917791596458315 15857305007876687394687473)
                ·
                  refine ⟨11892978755907515546015605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15857305007876687394687473 11892978755907515546015605)
                  ·
                    refine ⟨1114966758366329582438963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11892978755907515546015605 1114966758366329582438963)
                    ·
                      rfl

theorem cell22_3257085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_3257085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3257085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3257085 prefixEnd_3257085 := by exact prefixLift 3257085
  have htrace : WordTrace (prefixWord ++ tailWord_3257085) baseStart_3257085 baseEnd_3257085 := by
    simpa [prefixWord, tailWord_3257085, baseEnd_3257085] using wordTrace_append hprefix tailTrace_3257085
  have hstable : (prefixWord ++ tailWord_3257085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257085).length < 2 ^ (prefixWord ++ tailWord_3257085).sum := by decide
  have hdescent : baseEnd_3257085 < baseStart_3257085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257132 : List Nat := [2, 2, 1, 1, 1, 4, 1, 6, 4]
def baseStart_3257132 : Nat := 118140960795 + 3257132 * 2 ^ 59
def prefixEnd_3257132 : Nat := 4983230072969 + 3 ^ 40 * 3257132 * 2
def baseEnd_3257132 : Nat := 371660949142279042171273

theorem tailTrace_3257132 : CollatzResearch.WordTrace tailWord_3257132 prefixEnd_3257132 371660949142279042171273 := by
  unfold tailWord_3257132
  simp only [CollatzResearch.WordTrace]
  refine ⟨59398681817987256351742825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79198242423983008468990433 59398681817987256351742825)
  ·
    refine ⟨44549011363490442263807119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59398681817987256351742825 44549011363490442263807119)
    ·
      refine ⟨66823517045235663395710679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44549011363490442263807119 66823517045235663395710679)
      ·
        refine ⟨100235275567853495093566019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66823517045235663395710679 100235275567853495093566019)
        ·
          refine ⟨150352913351780242640349029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100235275567853495093566019 150352913351780242640349029)
          ·
            refine ⟨28191171253458795495065443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150352913351780242640349029 28191171253458795495065443)
            ·
              refine ⟨42286756880188193242598165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28191171253458795495065443 42286756880188193242598165)
              ·
                refine ⟨1982191728758821558246789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42286756880188193242598165 1982191728758821558246789)
                ·
                  refine ⟨371660949142279042171273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1982191728758821558246789 371660949142279042171273)
                  ·
                    rfl

theorem cell22_3257132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 6, 4].length) (baseStart_3257132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3257132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3257132 prefixEnd_3257132 := by exact prefixLift 3257132
  have htrace : WordTrace (prefixWord ++ tailWord_3257132) baseStart_3257132 baseEnd_3257132 := by
    simpa [prefixWord, tailWord_3257132, baseEnd_3257132] using wordTrace_append hprefix tailTrace_3257132
  have hstable : (prefixWord ++ tailWord_3257132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257132).length < 2 ^ (prefixWord ++ tailWord_3257132).sum := by decide
  have hdescent : baseEnd_3257132 < baseStart_3257132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257160 : List Nat := [2, 1, 3, 1, 1, 3, 3, 8]
def baseStart_3257160 : Nat := 118140960795 + 3257160 * 2 ^ 59
def prefixEnd_3257160 : Nat := 4983230072969 + 3 ^ 40 * 3257160 * 2
def baseEnd_3257160 : Nat := 123888048044339376312637

theorem tailTrace_3257160 : CollatzResearch.WordTrace tailWord_3257160 prefixEnd_3257160 123888048044339376312637 := by
  unfold tailWord_3257160
  simp only [CollatzResearch.WordTrace]
  refine ⟨59399192439936536742752467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79198923253248715657003289 59399192439936536742752467)
  ·
    refine ⟨89098788659904805114128701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59399192439936536742752467 89098788659904805114128701)
    ·
      refine ⟨33412045747464301917798263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89098788659904805114128701 33412045747464301917798263)
      ·
        refine ⟨50118068621196452876697395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33412045747464301917798263 50118068621196452876697395)
        ·
          refine ⟨75177102931794679315046093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50118068621196452876697395 75177102931794679315046093)
          ·
            refine ⟨28191413599423004743142285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75177102931794679315046093 28191413599423004743142285)
            ·
              refine ⟨10571780099783626778678357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28191413599423004743142285 10571780099783626778678357)
              ·
                refine ⟨123888048044339376312637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10571780099783626778678357 123888048044339376312637)
                ·
                  rfl

theorem cell22_3257160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 8].length) (baseStart_3257160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3257160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3257160 prefixEnd_3257160 := by exact prefixLift 3257160
  have htrace : WordTrace (prefixWord ++ tailWord_3257160) baseStart_3257160 baseEnd_3257160 := by
    simpa [prefixWord, tailWord_3257160, baseEnd_3257160] using wordTrace_append hprefix tailTrace_3257160
  have hstable : (prefixWord ++ tailWord_3257160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257160).length < 2 ^ (prefixWord ++ tailWord_3257160).sum := by decide
  have hdescent : baseEnd_3257160 < baseStart_3257160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257252 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 5, 4]
def baseStart_3257252 : Nat := 118140960795 + 3257252 * 2 ^ 59
def prefixEnd_3257252 : Nat := 4983230072969 + 3 ^ 40 * 3257252 * 2
def baseEnd_3257252 : Nat := 1115023925879196813513451

theorem tailTrace_3257252 : CollatzResearch.WordTrace tailWord_3257252 prefixEnd_3257252 1115023925879196813513451 := by
  unfold tailWord_3257252
  simp only [CollatzResearch.WordTrace]
  refine ⟨59400870197769886598927005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79201160263693182131902673 59400870197769886598927005)
  ·
    refine ⟨22275326324163707474597627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59400870197769886598927005 22275326324163707474597627)
    ·
      refine ⟨33412989486245561211896441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22275326324163707474597627 33412989486245561211896441)
      ·
        refine ⟨25059742114684170908922331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33412989486245561211896441 25059742114684170908922331)
        ·
          refine ⟨37589613172026256363383497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25059742114684170908922331 37589613172026256363383497)
          ·
            refine ⟨28192209879019692272537623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37589613172026256363383497 28192209879019692272537623)
            ·
              refine ⟨42288314818529538408806435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28192209879019692272537623 42288314818529538408806435)
              ·
                refine ⟨63432472227794307613209653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42288314818529538408806435 63432472227794307613209653)
                ·
                  refine ⟨5946794271355716338738405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63432472227794307613209653 5946794271355716338738405)
                  ·
                    refine ⟨1115023925879196813513451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5946794271355716338738405 1115023925879196813513451)
                    ·
                      rfl

theorem cell22_3257252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_3257252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3257252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3257252 prefixEnd_3257252 := by exact prefixLift 3257252
  have htrace : WordTrace (prefixWord ++ tailWord_3257252) baseStart_3257252 baseEnd_3257252 := by
    simpa [prefixWord, tailWord_3257252, baseEnd_3257252] using wordTrace_append hprefix tailTrace_3257252
  have hstable : (prefixWord ++ tailWord_3257252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257252).length < 2 ^ (prefixWord ++ tailWord_3257252).sum := by decide
  have hdescent : baseEnd_3257252 < baseStart_3257252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257269 : List Nat := [1, 3, 3, 2, 1, 1, 2, 4, 1, 4]
def baseStart_3257269 : Nat := 118140960795 + 3257269 * 2 ^ 59
def prefixEnd_3257269 : Nat := 4983230072969 + 3 ^ 40 * 3257269 * 2
def baseEnd_3257269 : Nat := 1115029745326614435838399

theorem tailTrace_3257269 : CollatzResearch.WordTrace tailWord_3257269 prefixEnd_3257269 1115029745326614435838399 := by
  unfold tailWord_3257269
  simp only [CollatzResearch.WordTrace]
  refine ⟨118802360436478185101222861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79201573624318790067481907 118802360436478185101222861)
  ·
    refine ⟨44550885163679319412958573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118802360436478185101222861 44550885163679319412958573)
    ·
      refine ⟨16706581936379744779859465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44550885163679319412958573 16706581936379744779859465)
      ·
        refine ⟨12529936452284808584894599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16706581936379744779859465 12529936452284808584894599)
        ·
          refine ⟨18794904678427212877341899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12529936452284808584894599 18794904678427212877341899)
          ·
            refine ⟨28192357017640819316012849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18794904678427212877341899 28192357017640819316012849)
            ·
              refine ⟨21144267763230614487009637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28192357017640819316012849 21144267763230614487009637)
              ·
                refine ⟨3964550205605740216314307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21144267763230614487009637 3964550205605740216314307)
                ·
                  refine ⟨5946825308408610324471461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3964550205605740216314307 5946825308408610324471461)
                  ·
                    refine ⟨1115029745326614435838399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5946825308408610324471461 1115029745326614435838399)
                    ·
                      rfl

theorem cell22_3257269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_3257269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3257269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3257269 prefixEnd_3257269 := by exact prefixLift 3257269
  have htrace : WordTrace (prefixWord ++ tailWord_3257269) baseStart_3257269 baseEnd_3257269 := by
    simpa [prefixWord, tailWord_3257269, baseEnd_3257269] using wordTrace_append hprefix tailTrace_3257269
  have hstable : (prefixWord ++ tailWord_3257269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257269).length < 2 ^ (prefixWord ++ tailWord_3257269).sum := by decide
  have hdescent : baseEnd_3257269 < baseStart_3257269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257297 : List Nat := [1, 2, 2, 1, 2, 1, 4, 1, 4, 4]
def baseStart_3257297 : Nat := 118140960795 + 3257297 * 2 ^ 59
def prefixEnd_3257297 : Nat := 4983230072969 + 3 ^ 40 * 3257297 * 2
def baseEnd_3257297 : Nat := 1115039330298831696138313

theorem tailTrace_3257297 : CollatzResearch.WordTrace tailWord_3257297 prefixEnd_3257297 1115039330298831696138313 := by
  unfold tailWord_3257297
  simp only [CollatzResearch.WordTrace]
  refine ⟨118803381680376745883242145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79202254453584497255494763 118803381680376745883242145)
  ·
    refine ⟨89102536260282559412431609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118803381680376745883242145 89102536260282559412431609)
    ·
      refine ⟨66826902195211919559323707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89102536260282559412431609 66826902195211919559323707)
      ·
        refine ⟨100240353292817879338985561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66826902195211919559323707 100240353292817879338985561)
        ·
          refine ⟨75180264969613409504239171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100240353292817879338985561 75180264969613409504239171)
          ·
            refine ⟨112770397454420114256358757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75180264969613409504239171 112770397454420114256358757)
            ·
              refine ⟨21144449522703771423067267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112770397454420114256358757 21144449522703771423067267)
              ·
                refine ⟨31716674284055657134600901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21144449522703771423067267 31716674284055657134600901)
                ·
                  refine ⟨5946876428260435712737669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31716674284055657134600901 5946876428260435712737669)
                  ·
                    refine ⟨1115039330298831696138313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5946876428260435712737669 1115039330298831696138313)
                    ·
                      rfl

theorem cell22_3257297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 4].length) (baseStart_3257297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3257297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3257297 prefixEnd_3257297 := by exact prefixLift 3257297
  have htrace : WordTrace (prefixWord ++ tailWord_3257297) baseStart_3257297 baseEnd_3257297 := by
    simpa [prefixWord, tailWord_3257297, baseEnd_3257297] using wordTrace_append hprefix tailTrace_3257297
  have hstable : (prefixWord ++ tailWord_3257297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257297).length < 2 ^ (prefixWord ++ tailWord_3257297).sum := by decide
  have hdescent : baseEnd_3257297 < baseStart_3257297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257329 : List Nat := [1, 2, 2, 2, 4, 1, 4, 6]
def baseStart_3257329 : Nat := 118140960795 + 3257329 * 2 ^ 59
def prefixEnd_3257329 : Nat := 4983230072969 + 3 ^ 40 * 3257329 * 2
def baseEnd_3257329 : Nat := 123894476061421586593135

theorem tailTrace_3257329 : CollatzResearch.WordTrace tailWord_3257329 prefixEnd_3257329 123894476061421586593135 := by
  unfold tailWord_3257329
  simp only [CollatzResearch.WordTrace]
  refine ⟨118804548816260815348407041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79203032544173876898938027 118804548816260815348407041)
  ·
    refine ⟨89103411612195611511305281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118804548816260815348407041 89103411612195611511305281)
    ·
      refine ⟨66827558709146708633478961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89103411612195611511305281 66827558709146708633478961)
      ·
        refine ⟨50120669031860031475109221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66827558709146708633478961 50120669031860031475109221)
        ·
          refine ⟨9397625443473755901582979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50120669031860031475109221 9397625443473755901582979)
          ·
            refine ⟨14096438165210633852374469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9397625443473755901582979 14096438165210633852374469)
            ·
              refine ⟨2643082155976993847320213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14096438165210633852374469 2643082155976993847320213)
              ·
                refine ⟨123894476061421586593135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2643082155976993847320213 123894476061421586593135)
                ·
                  rfl

theorem cell22_3257329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 6].length) (baseStart_3257329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3257329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3257329 prefixEnd_3257329 := by exact prefixLift 3257329
  have htrace : WordTrace (prefixWord ++ tailWord_3257329) baseStart_3257329 baseEnd_3257329 := by
    simpa [prefixWord, tailWord_3257329, baseEnd_3257329] using wordTrace_append hprefix tailTrace_3257329
  have hstable : (prefixWord ++ tailWord_3257329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257329).length < 2 ^ (prefixWord ++ tailWord_3257329).sum := by decide
  have hdescent : baseEnd_3257329 < baseStart_3257329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257361 : List Nat := [1, 2, 2, 1, 1, 2, 1, 8, 1, 3]
def baseStart_3257361 : Nat := 118140960795 + 3257361 * 2 ^ 59
def prefixEnd_3257361 : Nat := 4983230072969 + 3 ^ 40 * 3257361 * 2
def baseEnd_3257361 : Nat := 1115061238806756862538117

theorem tailTrace_3257361 : CollatzResearch.WordTrace tailWord_3257361 prefixEnd_3257361 1115061238806756862538117 := by
  unfold tailWord_3257361
  simp only [CollatzResearch.WordTrace]
  refine ⟨118805715952144884813571937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79203810634763256542381291 118805715952144884813571937)
  ·
    refine ⟨89104286964108663610178953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118805715952144884813571937 89104286964108663610178953)
    ·
      refine ⟨66828215223081497707634215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89104286964108663610178953 66828215223081497707634215)
      ·
        refine ⟨100242322834622246561451323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66828215223081497707634215 100242322834622246561451323)
        ·
          refine ⟨150363484251933369842176985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100242322834622246561451323 150363484251933369842176985)
          ·
            refine ⟨112772613188950027381632739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150363484251933369842176985 112772613188950027381632739)
            ·
              refine ⟨169158919783425041072449109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112772613188950027381632739 169158919783425041072449109)
              ·
                refine ⟨1982331091212012200067763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 169158919783425041072449109 1982331091212012200067763)
                ·
                  refine ⟨2973496636818018300101645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1982331091212012200067763 2973496636818018300101645)
                  ·
                    refine ⟨1115061238806756862538117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2973496636818018300101645 1115061238806756862538117)
                    ·
                      rfl

theorem cell22_3257361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 8, 1, 3].length) (baseStart_3257361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3257361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3257361 prefixEnd_3257361 := by exact prefixLift 3257361
  have htrace : WordTrace (prefixWord ++ tailWord_3257361) baseStart_3257361 baseEnd_3257361 := by
    simpa [prefixWord, tailWord_3257361, baseEnd_3257361] using wordTrace_append hprefix tailTrace_3257361
  have hstable : (prefixWord ++ tailWord_3257361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257361).length < 2 ^ (prefixWord ++ tailWord_3257361).sum := by decide
  have hdescent : baseEnd_3257361 < baseStart_3257361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257421 : List Nat := [1, 6, 1, 1, 1, 2, 1, 2, 3, 4]
def baseStart_3257421 : Nat := 118140960795 + 3257421 * 2 ^ 59
def prefixEnd_3257421 : Nat := 4983230072969 + 3 ^ 40 * 3257421 * 2
def baseEnd_3257421 : Nat := 1115081778032936706037933

theorem tailTrace_3257421 : CollatzResearch.WordTrace tailWord_3257421 prefixEnd_3257421 1115081778032936706037933 := by
  unfold tailWord_3257421
  simp only [CollatzResearch.WordTrace]
  refine ⟨118807904331927515060756117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79205269554618343373837411 118807904331927515060756117)
  ·
    refine ⟨5569120515559102268472943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 118807904331927515060756117 5569120515559102268472943)
    ·
      refine ⟨8353680773338653402709415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5569120515559102268472943 8353680773338653402709415)
      ·
        refine ⟨12530521160007980104064123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8353680773338653402709415 12530521160007980104064123)
        ·
          refine ⟨18795781740011970156096185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12530521160007980104064123 18795781740011970156096185)
          ·
            refine ⟨14096836305008977617072139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18795781740011970156096185 14096836305008977617072139)
            ·
              refine ⟨21145254457513466425608209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14096836305008977617072139 21145254457513466425608209)
              ·
                refine ⟨15858940843135099819206157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21145254457513466425608209 15858940843135099819206157)
                ·
                  refine ⟨5947102816175662432202309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15858940843135099819206157 5947102816175662432202309)
                  ·
                    refine ⟨1115081778032936706037933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5947102816175662432202309 1115081778032936706037933)
                    ·
                      rfl

theorem cell22_3257421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_3257421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3257421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3257421 prefixEnd_3257421 := by exact prefixLift 3257421
  have htrace : WordTrace (prefixWord ++ tailWord_3257421) baseStart_3257421 baseEnd_3257421 := by
    simpa [prefixWord, tailWord_3257421, baseEnd_3257421] using wordTrace_append hprefix tailTrace_3257421
  have hstable : (prefixWord ++ tailWord_3257421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257421).length < 2 ^ (prefixWord ++ tailWord_3257421).sum := by decide
  have hdescent : baseEnd_3257421 < baseStart_3257421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257449 : List Nat := [1, 2, 1, 1, 1, 7, 1, 1, 1, 6]
def baseStart_3257449 : Nat := 118140960795 + 3257449 * 2 ^ 59
def prefixEnd_3257449 : Nat := 4983230072969 + 3 ^ 40 * 3257449 * 2
def baseEnd_3257449 : Nat := 1115091363005153966337847

theorem tailTrace_3257449 : CollatzResearch.WordTrace tailWord_3257449 prefixEnd_3257449 1115091363005153966337847 := by
  unfold tailWord_3257449
  simp only [CollatzResearch.WordTrace]
  refine ⟨118808925575826075842775401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79205950383884050561850267 118808925575826075842775401)
  ·
    refine ⟨89106694181869556882081551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118808925575826075842775401 89106694181869556882081551)
    ·
      refine ⟨133660041272804335323122327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89106694181869556882081551 133660041272804335323122327)
      ·
        refine ⟨200490061909206502984683491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133660041272804335323122327 200490061909206502984683491)
        ·
          refine ⟨300735092863809754477025237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200490061909206502984683491 300735092863809754477025237)
          ·
            refine ⟨7048478738995541120555279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 300735092863809754477025237 7048478738995541120555279)
            ·
              refine ⟨10572718108493311680832919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7048478738995541120555279 10572718108493311680832919)
              ·
                refine ⟨15859077162739967521249379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10572718108493311680832919 15859077162739967521249379)
                ·
                  refine ⟨23788615744109951281874069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15859077162739967521249379 23788615744109951281874069)
                  ·
                    refine ⟨1115091363005153966337847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23788615744109951281874069 1115091363005153966337847)
                    ·
                      rfl

theorem cell22_3257449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 6].length) (baseStart_3257449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3257449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3257449 prefixEnd_3257449 := by exact prefixLift 3257449
  have htrace : WordTrace (prefixWord ++ tailWord_3257449) baseStart_3257449 baseEnd_3257449 := by
    simpa [prefixWord, tailWord_3257449, baseEnd_3257449] using wordTrace_append hprefix tailTrace_3257449
  have hstable : (prefixWord ++ tailWord_3257449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257449).length < 2 ^ (prefixWord ++ tailWord_3257449).sum := by decide
  have hdescent : baseEnd_3257449 < baseStart_3257449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257453 : List Nat := [1, 5, 1, 1, 2, 3, 2, 3, 4]
def baseStart_3257453 : Nat := 118140960795 + 3257453 * 2 ^ 59
def prefixEnd_3257453 : Nat := 4983230072969 + 3 ^ 40 * 3257453 * 2
def baseEnd_3257453 : Nat := 371697577428966429745945

theorem tailTrace_3257453 : CollatzResearch.WordTrace tailWord_3257453 prefixEnd_3257453 371697577428966429745945 := by
  unfold tailWord_3257453
  simp only [CollatzResearch.WordTrace]
  refine ⟨118809071467811584525921013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79206047645207723017280675 118809071467811584525921013)
  ·
    refine ⟨11138350450107336049305095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118809071467811584525921013 11138350450107336049305095)
    ·
      refine ⟨16707525675161004073957643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11138350450107336049305095 16707525675161004073957643)
      ·
        refine ⟨25061288512741506110936465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16707525675161004073957643 25061288512741506110936465)
        ·
          refine ⟨18795966384556129583202349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25061288512741506110936465 18795966384556129583202349)
          ·
            refine ⟨7048487394208548593700881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18795966384556129583202349 7048487394208548593700881)
            ·
              refine ⟨5286365545656411445275661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7048487394208548593700881 5286365545656411445275661)
              ·
                refine ⟨1982387079621154291978373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5286365545656411445275661 1982387079621154291978373)
                ·
                  refine ⟨371697577428966429745945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1982387079621154291978373 371697577428966429745945)
                  ·
                    rfl

theorem cell22_3257453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_3257453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3257453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3257453 prefixEnd_3257453 := by exact prefixLift 3257453
  have htrace : WordTrace (prefixWord ++ tailWord_3257453) baseStart_3257453 baseEnd_3257453 := by
    simpa [prefixWord, tailWord_3257453, baseEnd_3257453] using wordTrace_append hprefix tailTrace_3257453
  have hstable : (prefixWord ++ tailWord_3257453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257453).length < 2 ^ (prefixWord ++ tailWord_3257453).sum := by decide
  have hdescent : baseEnd_3257453 < baseStart_3257453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257498 : List Nat := [3, 1, 1, 5, 1, 3, 2, 6]
def baseStart_3257498 : Nat := 118140960795 + 3257498 * 2 ^ 59
def prefixEnd_3257498 : Nat := 4983230072969 + 3 ^ 40 * 3257498 * 2
def baseEnd_3257498 : Nat := 123900904078503796873633

theorem tailTrace_3257498 : CollatzResearch.WordTrace tailWord_3257498 prefixEnd_3257498 123900904078503796873633 := by
  unfold tailWord_3257498
  simp only [CollatzResearch.WordTrace]
  refine ⟨29702678188162139302827287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79207141835099038140872765 29702678188162139302827287)
  ·
    refine ⟨44554017282243208954240931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29702678188162139302827287 44554017282243208954240931)
    ·
      refine ⟨66831025923364813431361397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44554017282243208954240931 66831025923364813431361397)
      ·
        refine ⟨6265408680315451259190131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66831025923364813431361397 6265408680315451259190131)
        ·
          refine ⟨9398113020473176888785197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6265408680315451259190131 9398113020473176888785197)
          ·
            refine ⟨3524292382677441333294449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9398113020473176888785197 3524292382677441333294449)
            ·
              refine ⟨2643219287008080999970837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3524292382677441333294449 2643219287008080999970837)
              ·
                refine ⟨123900904078503796873633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2643219287008080999970837 123900904078503796873633)
                ·
                  rfl

theorem cell22_3257498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 6].length) (baseStart_3257498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3257498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3257498 prefixEnd_3257498 := by exact prefixLift 3257498
  have htrace : WordTrace (prefixWord ++ tailWord_3257498) baseStart_3257498 baseEnd_3257498 := by
    simpa [prefixWord, tailWord_3257498, baseEnd_3257498] using wordTrace_append hprefix tailTrace_3257498
  have hstable : (prefixWord ++ tailWord_3257498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257498).length < 2 ^ (prefixWord ++ tailWord_3257498).sum := by decide
  have hdescent : baseEnd_3257498 < baseStart_3257498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257509 : List Nat := [1, 3, 1, 2, 1, 4, 1, 2, 7]
def baseStart_3257509 : Nat := 118140960795 + 3257509 * 2 ^ 59
def prefixEnd_3257509 : Nat := 4983230072969 + 3 ^ 40 * 3257509 * 2
def baseEnd_3257509 : Nat := 371703967410444603279221

theorem tailTrace_3257509 : CollatzResearch.WordTrace tailWord_3257509 prefixEnd_3257509 371703967410444603279221 := by
  unfold tailWord_3257509
  simp only [CollatzResearch.WordTrace]
  refine ⟨118811113955608706089959581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79207409303739137393306387 118811113955608706089959581)
  ·
    refine ⟨44554167733353264783734843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118811113955608706089959581 44554167733353264783734843)
    ·
      refine ⟨66831251600029897175602265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44554167733353264783734843 66831251600029897175602265)
      ·
        refine ⟨50123438700022422881701699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66831251600029897175602265 50123438700022422881701699)
        ·
          refine ⟨75185158050033634322552549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50123438700022422881701699 75185158050033634322552549)
          ·
            refine ⟨14097217134381306435478603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75185158050033634322552549 14097217134381306435478603)
            ·
              refine ⟨21145825701571959653217905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14097217134381306435478603 21145825701571959653217905)
              ·
                refine ⟨15859369276178969739913429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21145825701571959653217905 15859369276178969739913429)
                ·
                  refine ⟨371703967410444603279221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15859369276178969739913429 371703967410444603279221)
                  ·
                    rfl

theorem cell22_3257509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 7].length) (baseStart_3257509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3257509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3257509 prefixEnd_3257509 := by exact prefixLift 3257509
  have htrace : WordTrace (prefixWord ++ tailWord_3257509) baseStart_3257509 baseEnd_3257509 := by
    simpa [prefixWord, tailWord_3257509, baseEnd_3257509] using wordTrace_append hprefix tailTrace_3257509
  have hstable : (prefixWord ++ tailWord_3257509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257509).length < 2 ^ (prefixWord ++ tailWord_3257509).sum := by decide
  have hdescent : baseEnd_3257509 < baseStart_3257509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257584 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 5, 6]
def baseStart_3257584 : Nat := 118140960795 + 3257584 * 2 ^ 59
def prefixEnd_3257584 : Nat := 4983230072969 + 3 ^ 40 * 3257584 * 2
def baseEnd_3257584 : Nat := 1115137576264058614212433

theorem tailTrace_3257584 : CollatzResearch.WordTrace tailWord_3257584 prefixEnd_3257584 1115137576264058614212433 := by
  unfold tailWord_3257584
  simp only [CollatzResearch.WordTrace]
  refine ⟨59406924715168496949469903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79209232953557995932626537 59406924715168496949469903)
  ·
    refine ⟨89110387072752745424204855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59406924715168496949469903 89110387072752745424204855)
    ·
      refine ⟨133665580609129118136307283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89110387072752745424204855 133665580609129118136307283)
      ·
        refine ⟨200498370913693677204460925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133665580609129118136307283 200498370913693677204460925)
        ·
          refine ⟨75186889092635128951672847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200498370913693677204460925 75186889092635128951672847)
          ·
            refine ⟨112780333638952693427509271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75186889092635128951672847 112780333638952693427509271)
            ·
              refine ⟨169170500458429040141263907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112780333638952693427509271 169170500458429040141263907)
              ·
                refine ⟨253755750687643560211895861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169170500458429040141263907 253755750687643560211895861)
                ·
                  refine ⟨23789601626966583769865237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 253755750687643560211895861 23789601626966583769865237)
                  ·
                    refine ⟨1115137576264058614212433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23789601626966583769865237 1115137576264058614212433)
                    ·
                      rfl

theorem cell22_3257584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 5, 6].length) (baseStart_3257584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3257584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3257584 prefixEnd_3257584 := by exact prefixLift 3257584
  have htrace : WordTrace (prefixWord ++ tailWord_3257584) baseStart_3257584 baseEnd_3257584 := by
    simpa [prefixWord, tailWord_3257584, baseEnd_3257584] using wordTrace_append hprefix tailTrace_3257584
  have hstable : (prefixWord ++ tailWord_3257584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257584).length < 2 ^ (prefixWord ++ tailWord_3257584).sum := by decide
  have hdescent : baseEnd_3257584 < baseStart_3257584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257603 : List Nat := [1, 1, 1, 3, 2, 4, 2, 3, 2, 3]
def baseStart_3257603 : Nat := 118140960795 + 3257603 * 2 ^ 59
def prefixEnd_3257603 : Nat := 4983230072969 + 3 ^ 40 * 3257603 * 2
def baseEnd_3257603 : Nat := 1115144080352348897987375

theorem tailTrace_3257603 : CollatzResearch.WordTrace tailWord_3257603 prefixEnd_3257603 1115144080352348897987375 := by
  unfold tailWord_3257603
  simp only [CollatzResearch.WordTrace]
  refine ⟨118814542417268160143881463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79209694944845440095920975 118814542417268160143881463)
  ·
    refine ⟨178221813625902240215822195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118814542417268160143881463 178221813625902240215822195)
    ·
      refine ⟨267332720438853360323733293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178221813625902240215822195 267332720438853360323733293)
      ·
        refine ⟨100249770164570010121399985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267332720438853360323733293 100249770164570010121399985)
        ·
          refine ⟨75187327623427507591049989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100249770164570010121399985 75187327623427507591049989)
          ·
            refine ⟨14097623929392657673321873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75187327623427507591049989 14097623929392657673321873)
            ·
              refine ⟨10573217947044493254991405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14097623929392657673321873 10573217947044493254991405)
              ·
                refine ⟨3964956730141684970621777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10573217947044493254991405 3964956730141684970621777)
                ·
                  refine ⟨2973717547606263727966333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3964956730141684970621777 2973717547606263727966333)
                  ·
                    refine ⟨1115144080352348897987375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2973717547606263727966333 1115144080352348897987375)
                    ·
                      rfl

theorem cell22_3257603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 2, 3].length) (baseStart_3257603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3257603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3257603 prefixEnd_3257603 := by exact prefixLift 3257603
  have htrace : WordTrace (prefixWord ++ tailWord_3257603) baseStart_3257603 baseEnd_3257603 := by
    simpa [prefixWord, tailWord_3257603, baseEnd_3257603] using wordTrace_append hprefix tailTrace_3257603
  have hstable : (prefixWord ++ tailWord_3257603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257603).length < 2 ^ (prefixWord ++ tailWord_3257603).sum := by decide
  have hdescent : baseEnd_3257603 < baseStart_3257603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257648 : List Nat := [2, 1, 1, 1, 2, 2, 6, 1, 3, 3]
def baseStart_3257648 : Nat := 118140960795 + 3257648 * 2 ^ 59
def prefixEnd_3257648 : Nat := 4983230072969 + 3 ^ 40 * 3257648 * 2
def baseEnd_3257648 : Nat := 1115159484771983780612237

theorem tailTrace_3257648 : CollatzResearch.WordTrace tailWord_3257648 prefixEnd_3257648 1115159484771983780612237 := by
  unfold tailWord_3257648
  simp only [CollatzResearch.WordTrace]
  refine ⟨59408091851052566414634799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79210789134736755219513065 59408091851052566414634799)
  ·
    refine ⟨89112137776578849621952199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59408091851052566414634799 89112137776578849621952199)
    ·
      refine ⟨133668206664868274432928299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89112137776578849621952199 133668206664868274432928299)
      ·
        refine ⟨200502309997302411649392449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133668206664868274432928299 200502309997302411649392449)
        ·
          refine ⟨150376732497976808737044337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200502309997302411649392449 150376732497976808737044337)
          ·
            refine ⟨112782549373482606552783253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150376732497976808737044337 112782549373482606552783253)
            ·
              refine ⟨5286682001881997182161715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 112782549373482606552783253 5286682001881997182161715)
              ·
                refine ⟨7930023002822995773242573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5286682001881997182161715 7930023002822995773242573)
                ·
                  refine ⟨2973758626058623414965965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7930023002822995773242573 2973758626058623414965965)
                  ·
                    refine ⟨1115159484771983780612237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2973758626058623414965965 1115159484771983780612237)
                    ·
                      rfl

theorem cell22_3257648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 3, 3].length) (baseStart_3257648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3257648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3257648 prefixEnd_3257648 := by exact prefixLift 3257648
  have htrace : WordTrace (prefixWord ++ tailWord_3257648) baseStart_3257648 baseEnd_3257648 := by
    simpa [prefixWord, tailWord_3257648, baseEnd_3257648] using wordTrace_append hprefix tailTrace_3257648
  have hstable : (prefixWord ++ tailWord_3257648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257648).length < 2 ^ (prefixWord ++ tailWord_3257648).sum := by decide
  have hdescent : baseEnd_3257648 < baseStart_3257648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257654 : List Nat := [5, 1, 2, 3, 2, 1, 1, 1, 1, 5]
def baseStart_3257654 : Nat := 118140960795 + 3257654 * 2 ^ 59
def prefixEnd_3257654 : Nat := 4983230072969 + 3 ^ 40 * 3257654 * 2
def baseEnd_3257654 : Nat := 1115161538694601764962219

theorem tailTrace_3257654 : CollatzResearch.WordTrace tailWord_3257654 prefixEnd_3257654 1115161538694601764962219 := by
  unfold tailWord_3257654
  simp only [CollatzResearch.WordTrace]
  refine ⟨7426025158755212240874251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79210935026722263902658677 7426025158755212240874251)
  ·
    refine ⟨11139037738132818361311377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7426025158755212240874251 11139037738132818361311377)
    ·
      refine ⟨8354278303599613770983533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11139037738132818361311377 8354278303599613770983533)
      ·
        refine ⟨3132854363849855164118825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8354278303599613770983533 3132854363849855164118825)
        ·
          refine ⟨2349640772887391373089119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3132854363849855164118825 2349640772887391373089119)
          ·
            refine ⟨3524461159331087059633679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2349640772887391373089119 3524461159331087059633679)
            ·
              refine ⟨5286691738996630589450519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3524461159331087059633679 5286691738996630589450519)
              ·
                refine ⟨7930037608494945884175779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5286691738996630589450519 7930037608494945884175779)
                ·
                  refine ⟨11895056412742418826263669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7930037608494945884175779 11895056412742418826263669)
                  ·
                    refine ⟨1115161538694601764962219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11895056412742418826263669 1115161538694601764962219)
                    ·
                      rfl

theorem cell22_3257654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_3257654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3257654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3257654 prefixEnd_3257654 := by exact prefixLift 3257654
  have htrace : WordTrace (prefixWord ++ tailWord_3257654) baseStart_3257654 baseEnd_3257654 := by
    simpa [prefixWord, tailWord_3257654, baseEnd_3257654] using wordTrace_append hprefix tailTrace_3257654
  have hstable : (prefixWord ++ tailWord_3257654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257654).length < 2 ^ (prefixWord ++ tailWord_3257654).sum := by decide
  have hdescent : baseEnd_3257654 < baseStart_3257654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257665 : List Nat := [1, 2, 5, 2, 1, 1, 2, 2, 3, 3]
def baseStart_3257665 : Nat := 118140960795 + 3257665 * 2 ^ 59
def prefixEnd_3257665 : Nat := 4983230072969 + 3 ^ 40 * 3257665 * 2
def baseEnd_3257665 : Nat := 1115165304219401402937185

theorem tailTrace_3257665 : CollatzResearch.WordTrace tailWord_3257665 prefixEnd_3257665 1115165304219401402937185 := by
  unfold tailWord_3257665
  simp only [CollatzResearch.WordTrace]
  refine ⟨118816803743043544732638449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79211202495362363155092299 118816803743043544732638449)
  ·
    refine ⟨89112602807282658549478837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118816803743043544732638449 89112602807282658549478837)
    ·
      refine ⟨8354306513182749239013641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89112602807282658549478837 8354306513182749239013641)
      ·
        refine ⟨6265729884887061929260231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8354306513182749239013641 6265729884887061929260231)
        ·
          refine ⟨9398594827330592893890347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6265729884887061929260231 9398594827330592893890347)
          ·
            refine ⟨14097892240995889340835521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9398594827330592893890347 14097892240995889340835521)
            ·
              refine ⟨10573419180746917005626641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14097892240995889340835521 10573419180746917005626641)
              ·
                refine ⟨7930064385560187754219981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10573419180746917005626641 7930064385560187754219981)
                ·
                  refine ⟨2973774144585070407832493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7930064385560187754219981 2973774144585070407832493)
                  ·
                    refine ⟨1115165304219401402937185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2973774144585070407832493 1115165304219401402937185)
                    ·
                      rfl

theorem cell22_3257665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_3257665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3257665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3257665 prefixEnd_3257665 := by exact prefixLift 3257665
  have htrace : WordTrace (prefixWord ++ tailWord_3257665) baseStart_3257665 baseEnd_3257665 := by
    simpa [prefixWord, tailWord_3257665, baseEnd_3257665] using wordTrace_append hprefix tailTrace_3257665
  have hstable : (prefixWord ++ tailWord_3257665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257665).length < 2 ^ (prefixWord ++ tailWord_3257665).sum := by decide
  have hdescent : baseEnd_3257665 < baseStart_3257665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257753 : List Nat := [1, 2, 1, 2, 1, 5, 2, 2, 2, 4]
def baseStart_3257753 : Nat := 118140960795 + 3257753 * 2 ^ 59
def prefixEnd_3257753 : Nat := 4983230072969 + 3 ^ 40 * 3257753 * 2
def baseEnd_3257753 : Nat := 1115195428417798506736915

theorem tailTrace_3257753 : CollatzResearch.WordTrace tailWord_3257753 prefixEnd_3257753 1115195428417798506736915 := by
  unfold tailWord_3257753
  simp only [CollatzResearch.WordTrace]
  refine ⟨118820013366724735761841913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79213342244483157174561275 118820013366724735761841913)
  ·
    refine ⟨89115010025043551821381435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118820013366724735761841913 89115010025043551821381435)
    ·
      refine ⟨133672515037565327732072153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89115010025043551821381435 133672515037565327732072153)
      ·
        refine ⟨100254386278173995799054115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133672515037565327732072153 100254386278173995799054115)
        ·
          refine ⟨150381579417260993698581173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100254386278173995799054115 150381579417260993698581173)
          ·
            refine ⟨14098273070368218159241985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150381579417260993698581173 14098273070368218159241985)
            ·
              refine ⟨10573704802776163619431489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14098273070368218159241985 10573704802776163619431489)
              ·
                refine ⟨7930278602082122714573617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10573704802776163619431489 7930278602082122714573617)
                ·
                  refine ⟨5947708951561592035930213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7930278602082122714573617 5947708951561592035930213)
                  ·
                    refine ⟨1115195428417798506736915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5947708951561592035930213 1115195428417798506736915)
                    ·
                      rfl

theorem cell22_3257753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 4].length) (baseStart_3257753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3257753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3257753 prefixEnd_3257753 := by exact prefixLift 3257753
  have htrace : WordTrace (prefixWord ++ tailWord_3257753) baseStart_3257753 baseEnd_3257753 := by
    simpa [prefixWord, tailWord_3257753, baseEnd_3257753] using wordTrace_append hprefix tailTrace_3257753
  have hstable : (prefixWord ++ tailWord_3257753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257753).length < 2 ^ (prefixWord ++ tailWord_3257753).sum := by decide
  have hdescent : baseEnd_3257753 < baseStart_3257753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257757 : List Nat := [1, 4, 2, 1, 3, 1, 4, 2, 4]
def baseStart_3257757 : Nat := 118140960795 + 3257757 * 2 ^ 59
def prefixEnd_3257757 : Nat := 4983230072969 + 3 ^ 40 * 3257757 * 2
def baseEnd_3257757 : Nat := 371732265899847943212301

theorem tailTrace_3257757 : CollatzResearch.WordTrace tailWord_3257757 prefixEnd_3257757 371732265899847943212301 := by
  unfold tailWord_3257757
  simp only [CollatzResearch.WordTrace]
  refine ⟨118820159258710244444987525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79213439505806829629991683 118820159258710244444987525)
  ·
    refine ⟨22278779861008170833435161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118820159258710244444987525 22278779861008170833435161)
    ·
      refine ⟨16709084895756128125076371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22278779861008170833435161 16709084895756128125076371)
      ·
        refine ⟨25063627343634192187614557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16709084895756128125076371 25063627343634192187614557)
        ·
          refine ⟨9398860253862822070355459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25063627343634192187614557 9398860253862822070355459)
          ·
            refine ⟨14098290380794233105533189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9398860253862822070355459 14098290380794233105533189)
            ·
              refine ⟨2643429446398918707287473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14098290380794233105533189 2643429446398918707287473)
              ·
                refine ⟨1982572084799189030465605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2643429446398918707287473 1982572084799189030465605)
                ·
                  refine ⟨371732265899847943212301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1982572084799189030465605 371732265899847943212301)
                  ·
                    rfl

theorem cell22_3257757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 2, 4].length) (baseStart_3257757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3257757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3257757 prefixEnd_3257757 := by exact prefixLift 3257757
  have htrace : WordTrace (prefixWord ++ tailWord_3257757) baseStart_3257757 baseEnd_3257757 := by
    simpa [prefixWord, tailWord_3257757, baseEnd_3257757] using wordTrace_append hprefix tailTrace_3257757
  have hstable : (prefixWord ++ tailWord_3257757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257757).length < 2 ^ (prefixWord ++ tailWord_3257757).sum := by decide
  have hdescent : baseEnd_3257757 < baseStart_3257757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257785 : List Nat := [1, 2, 1, 4, 4, 1, 3, 6]
def baseStart_3257785 : Nat := 118140960795 + 3257785 * 2 ^ 59
def prefixEnd_3257785 : Nat := 4983230072969 + 3 ^ 40 * 3257785 * 2
def baseEnd_3257785 : Nat := 123911820296862343326313

theorem tailTrace_3257785 : CollatzResearch.WordTrace tailWord_3257785 prefixEnd_3257785 123911820296862343326313 := by
  unfold tailWord_3257785
  simp only [CollatzResearch.WordTrace]
  refine ⟨118821180502608805227006809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79214120335072536818004539 118821180502608805227006809)
  ·
    refine ⟨89115885376956603920255107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118821180502608805227006809 89115885376956603920255107)
    ·
      refine ⟨133673828065434905880382661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89115885376956603920255107 133673828065434905880382661)
      ·
        refine ⟨25063842762269044852571749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133673828065434905880382661 25063842762269044852571749)
        ·
          refine ⟨4699470517925445909857203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25063842762269044852571749 4699470517925445909857203)
          ·
            refine ⟨7049205776888168864785805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4699470517925445909857203 7049205776888168864785805)
            ·
              refine ⟨2643452166333063324294677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7049205776888168864785805 2643452166333063324294677)
              ·
                refine ⟨123911820296862343326313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2643452166333063324294677 123911820296862343326313)
                ·
                  rfl

theorem cell22_3257785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 6].length) (baseStart_3257785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3257785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3257785 prefixEnd_3257785 := by exact prefixLift 3257785
  have htrace : WordTrace (prefixWord ++ tailWord_3257785) baseStart_3257785 baseEnd_3257785 := by
    simpa [prefixWord, tailWord_3257785, baseEnd_3257785] using wordTrace_append hprefix tailTrace_3257785
  have hstable : (prefixWord ++ tailWord_3257785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257785).length < 2 ^ (prefixWord ++ tailWord_3257785).sum := by decide
  have hdescent : baseEnd_3257785 < baseStart_3257785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257811 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 2, 11]
def baseStart_3257811 : Nat := 118140960795 + 3257811 * 2 ^ 59
def prefixEnd_3257811 : Nat := 4983230072969 + 3 ^ 40 * 3257811 * 2
def baseEnd_3257811 : Nat := 1115215283003105688786737

theorem tailTrace_3257811 : CollatzResearch.WordTrace tailWord_3257811 prefixEnd_3257811 1115215283003105688786737 := by
  unfold tailWord_3257811
  simp only [CollatzResearch.WordTrace]
  refine ⟨118822128800514611667453287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79214752533676407778302191 118822128800514611667453287)
  ·
    refine ⟨178233193200771917501179931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118822128800514611667453287 178233193200771917501179931)
    ·
      refine ⟨267349789801157876251769897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178233193200771917501179931 267349789801157876251769897)
      ·
        refine ⟨200512342350868407188827423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267349789801157876251769897 200512342350868407188827423)
        ·
          refine ⟨300768513526302610783241135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200512342350868407188827423 300768513526302610783241135)
          ·
            refine ⟨451152770289453916174861703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300768513526302610783241135 451152770289453916174861703)
            ·
              refine ⟨676729155434180874262292555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 451152770289453916174861703 676729155434180874262292555)
              ·
                refine ⟨1015093733151271311393438833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 676729155434180874262292555 1015093733151271311393438833)
                ·
                  refine ⟨761320299863453483545079125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1015093733151271311393438833 761320299863453483545079125)
                  ·
                    refine ⟨1115215283003105688786737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 761320299863453483545079125 1115215283003105688786737)
                    ·
                      rfl

theorem cell22_3257811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 11].length) (baseStart_3257811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3257811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3257811 prefixEnd_3257811 := by exact prefixLift 3257811
  have htrace : WordTrace (prefixWord ++ tailWord_3257811) baseStart_3257811 baseEnd_3257811 := by
    simpa [prefixWord, tailWord_3257811, baseEnd_3257811] using wordTrace_append hprefix tailTrace_3257811
  have hstable : (prefixWord ++ tailWord_3257811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257811).length < 2 ^ (prefixWord ++ tailWord_3257811).sum := by decide
  have hdescent : baseEnd_3257811 < baseStart_3257811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257813 : List Nat := [1, 3, 2, 3, 1, 1, 3, 1, 7]
def baseStart_3257813 : Nat := 118140960795 + 3257813 * 2 ^ 59
def prefixEnd_3257813 : Nat := 4983230072969 + 3 ^ 40 * 3257813 * 2
def baseEnd_3257813 : Nat := 371738655881326116745577

theorem tailTrace_3257813 : CollatzResearch.WordTrace tailWord_3257813 prefixEnd_3257813 371738655881326116745577 := by
  unfold tailWord_3257813
  simp only [CollatzResearch.WordTrace]
  refine ⟨118822201746507366009026093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79214801164338244006017395 118822201746507366009026093)
  ·
    refine ⟨44558325654940262253384785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118822201746507366009026093 44558325654940262253384785)
    ·
      refine ⟨33418744241205196690038589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44558325654940262253384785 33418744241205196690038589)
      ·
        refine ⟨12532029090451948758764471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33418744241205196690038589 12532029090451948758764471)
        ·
          refine ⟨18798043635677923138146707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12532029090451948758764471 18798043635677923138146707)
          ·
            refine ⟨28197065453516884707220061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18798043635677923138146707 28197065453516884707220061)
            ·
              refine ⟨10573899545068831765207523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28197065453516884707220061 10573899545068831765207523)
              ·
                refine ⟨15860849317603247647811285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10573899545068831765207523 15860849317603247647811285)
                ·
                  refine ⟨371738655881326116745577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15860849317603247647811285 371738655881326116745577)
                  ·
                    rfl

theorem cell22_3257813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 7].length) (baseStart_3257813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3257813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3257813 prefixEnd_3257813 := by exact prefixLift 3257813
  have htrace : WordTrace (prefixWord ++ tailWord_3257813) baseStart_3257813 baseEnd_3257813 := by
    simpa [prefixWord, tailWord_3257813, baseEnd_3257813] using wordTrace_append hprefix tailTrace_3257813
  have hstable : (prefixWord ++ tailWord_3257813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257813).length < 2 ^ (prefixWord ++ tailWord_3257813).sum := by decide
  have hdescent : baseEnd_3257813 < baseStart_3257813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257817 : List Nat := [1, 2, 1, 2, 4, 2, 2, 4, 1, 3]
def baseStart_3257817 : Nat := 118140960795 + 3257817 * 2 ^ 59
def prefixEnd_3257817 : Nat := 4983230072969 + 3 ^ 40 * 3257817 * 2
def baseEnd_3257817 : Nat := 1115217336925723673136719

theorem tailTrace_3257817 : CollatzResearch.WordTrace tailWord_3257817 prefixEnd_3257817 1115217336925723673136719 := by
  unfold tailWord_3257817
  simp only [CollatzResearch.WordTrace]
  refine ⟨118822347638492874692171705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79214898425661916461447803 118822347638492874692171705)
  ·
    refine ⟨89116760728869656019128779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118822347638492874692171705 89116760728869656019128779)
    ·
      refine ⟨133675141093304484028693169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89116760728869656019128779 133675141093304484028693169)
      ·
        refine ⟨100256355819978363021519877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133675141093304484028693169 100256355819978363021519877)
        ·
          refine ⟨18798066716245943066534977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100256355819978363021519877 18798066716245943066534977)
          ·
            refine ⟨14098550037184457299901233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18798066716245943066534977 14098550037184457299901233)
            ·
              refine ⟨10573912527888342974925925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14098550037184457299901233 10573912527888342974925925)
              ·
                refine ⟨1982608598979064307798611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10573912527888342974925925 1982608598979064307798611)
                ·
                  refine ⟨2973912898468596461697917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1982608598979064307798611 2973912898468596461697917)
                  ·
                    refine ⟨1115217336925723673136719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2973912898468596461697917 1115217336925723673136719)
                    ·
                      rfl

theorem cell22_3257817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 4, 1, 3].length) (baseStart_3257817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3257817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3257817 prefixEnd_3257817 := by exact prefixLift 3257817
  have htrace : WordTrace (prefixWord ++ tailWord_3257817) baseStart_3257817 baseEnd_3257817 := by
    simpa [prefixWord, tailWord_3257817, baseEnd_3257817] using wordTrace_append hprefix tailTrace_3257817
  have hstable : (prefixWord ++ tailWord_3257817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257817).length < 2 ^ (prefixWord ++ tailWord_3257817).sum := by decide
  have hdescent : baseEnd_3257817 < baseStart_3257817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257875 : List Nat := [1, 1, 1, 2, 1, 8, 1, 1, 6]
def baseStart_3257875 : Nat := 118140960795 + 3257875 * 2 ^ 59
def prefixEnd_3257875 : Nat := 4983230072969 + 3 ^ 40 * 3257875 * 2
def baseEnd_3257875 : Nat := 371745730503676951728847

theorem tailTrace_3257875 : CollatzResearch.WordTrace tailWord_3257875 prefixEnd_3257875 371745730503676951728847 := by
  unfold tailWord_3257875
  simp only [CollatzResearch.WordTrace]
  refine ⟨118824463072282750597783079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79216308714855167065188719 118824463072282750597783079)
  ·
    refine ⟨178236694608424125896674619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118824463072282750597783079 178236694608424125896674619)
    ·
      refine ⟨267355041912636188845011929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178236694608424125896674619 267355041912636188845011929)
      ·
        refine ⟨200516281434477141633758947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267355041912636188845011929 200516281434477141633758947)
        ·
          refine ⟨300774422151715712450638421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200516281434477141633758947 300774422151715712450638421)
          ·
            refine ⟨3524700259590418505280919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 300774422151715712450638421 3524700259590418505280919)
            ·
              refine ⟨5287050389385627757921379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3524700259590418505280919 5287050389385627757921379)
              ·
                refine ⟨7930575584078441636882069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5287050389385627757921379 7930575584078441636882069)
                ·
                  refine ⟨371745730503676951728847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7930575584078441636882069 371745730503676951728847)
                  ·
                    rfl

theorem cell22_3257875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 6].length) (baseStart_3257875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3257875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3257875 prefixEnd_3257875 := by exact prefixLift 3257875
  have htrace : WordTrace (prefixWord ++ tailWord_3257875) baseStart_3257875 baseEnd_3257875 := by
    simpa [prefixWord, tailWord_3257875, baseEnd_3257875] using wordTrace_append hprefix tailTrace_3257875
  have hstable : (prefixWord ++ tailWord_3257875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257875).length < 2 ^ (prefixWord ++ tailWord_3257875).sum := by decide
  have hdescent : baseEnd_3257875 < baseStart_3257875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257926 : List Nat := [6, 1, 1, 1, 3, 1, 1, 4, 4]
def baseStart_3257926 : Nat := 118140960795 + 3257926 * 2 ^ 59
def prefixEnd_3257926 : Nat := 4983230072969 + 3 ^ 40 * 3257926 * 2
def baseEnd_3257926 : Nat := 371751549951094574053795

theorem tailTrace_3257926 : CollatzResearch.WordTrace tailWord_3257926 prefixEnd_3257926 371751549951094574053795 := by
  unfold tailWord_3257926
  simp only [CollatzResearch.WordTrace]
  refine ⟨3713322599846812072121551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 79217548796731990871926421 3713322599846812072121551)
  ·
    refine ⟨5569983899770218108182327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3713322599846812072121551 5569983899770218108182327)
    ·
      refine ⟨8354975849655327162273491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5569983899770218108182327 8354975849655327162273491)
      ·
        refine ⟨12532463774482990743410237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8354975849655327162273491 12532463774482990743410237)
        ·
          refine ⟨4699673915431121528778839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12532463774482990743410237 4699673915431121528778839)
          ·
            refine ⟨7049510873146682293168259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4699673915431121528778839 7049510873146682293168259)
            ·
              refine ⟨10574266309720023439752389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7049510873146682293168259 10574266309720023439752389)
              ·
                refine ⟨1982674933072504394953573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10574266309720023439752389 1982674933072504394953573)
                ·
                  refine ⟨371751549951094574053795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1982674933072504394953573 371751549951094574053795)
                  ·
                    rfl

theorem cell22_3257926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_3257926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3257926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3257926 prefixEnd_3257926 := by exact prefixLift 3257926
  have htrace : WordTrace (prefixWord ++ tailWord_3257926) baseStart_3257926 baseEnd_3257926 := by
    simpa [prefixWord, tailWord_3257926, baseEnd_3257926] using wordTrace_append hprefix tailTrace_3257926
  have hstable : (prefixWord ++ tailWord_3257926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257926).length < 2 ^ (prefixWord ++ tailWord_3257926).sum := by decide
  have hdescent : baseEnd_3257926 < baseStart_3257926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257935 : List Nat := [1, 1, 2, 1, 1, 2, 3, 5, 3, 3]
def baseStart_3257935 : Nat := 118140960795 + 3257935 * 2 ^ 59
def prefixEnd_3257935 : Nat := 4983230072969 + 3 ^ 40 * 3257935 * 2
def baseEnd_3257935 : Nat := 1115257730737210698686357

theorem tailTrace_3257935 : CollatzResearch.WordTrace tailWord_3257935 prefixEnd_3257935 1115257730737210698686357 := by
  unfold tailWord_3257935
  simp only [CollatzResearch.WordTrace]
  refine ⟨118826651452065380844967259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79217767634710253896644839 118826651452065380844967259)
  ·
    refine ⟨178239977178098071267450889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118826651452065380844967259 178239977178098071267450889)
    ·
      refine ⟨133679982883573553450588167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178239977178098071267450889 133679982883573553450588167)
      ·
        refine ⟨200519974325360330175882251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133679982883573553450588167 200519974325360330175882251)
        ·
          refine ⟨300779961488040495263823377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200519974325360330175882251 300779961488040495263823377)
          ·
            refine ⟨225584971116030371447867533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300779961488040495263823377 225584971116030371447867533)
            ·
              refine ⟨84594364168511389292950325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 225584971116030371447867533 84594364168511389292950325)
              ·
                refine ⟨7930721640797942746214093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84594364168511389292950325 7930721640797942746214093)
                ·
                  refine ⟨2974020615299228529830285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7930721640797942746214093 2974020615299228529830285)
                  ·
                    refine ⟨1115257730737210698686357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2974020615299228529830285 1115257730737210698686357)
                    ·
                      rfl

theorem cell22_3257935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 3, 3].length) (baseStart_3257935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3257935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3257935 prefixEnd_3257935 := by exact prefixLift 3257935
  have htrace : WordTrace (prefixWord ++ tailWord_3257935) baseStart_3257935 baseEnd_3257935 := by
    simpa [prefixWord, tailWord_3257935, baseEnd_3257935] using wordTrace_append hprefix tailTrace_3257935
  have hstable : (prefixWord ++ tailWord_3257935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257935).length < 2 ^ (prefixWord ++ tailWord_3257935).sum := by decide
  have hdescent : baseEnd_3257935 < baseStart_3257935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258042 : List Nat := [3, 1, 1, 1, 2, 4, 2, 1, 4, 3]
def baseStart_3258042 : Nat := 118140960795 + 3258042 * 2 ^ 59
def prefixEnd_3258042 : Nat := 4983230072969 + 3 ^ 40 * 3258042 * 2
def baseEnd_3258042 : Nat := 1115294359023898086261029

theorem tailTrace_3258042 : CollatzResearch.WordTrace tailWord_3258042 prefixEnd_3258042 1115294359023898086261029 := by
  unfold tailWord_3258042
  simp only [CollatzResearch.WordTrace]
  refine ⟨29707638515669434529778095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79220369375118492079408253 29707638515669434529778095)
  ·
    refine ⟨44561457773504151794667143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29707638515669434529778095 44561457773504151794667143)
    ·
      refine ⟨66842186660256227692000715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44561457773504151794667143 66842186660256227692000715)
      ·
        refine ⟨100263279990384341538001073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66842186660256227692000715 100263279990384341538001073)
        ·
          refine ⟨75197459992788256153500805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100263279990384341538001073 75197459992788256153500805)
          ·
            refine ⟨14099523748647798028781401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75197459992788256153500805 14099523748647798028781401)
            ·
              refine ⟨10574642811485848521586051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14099523748647798028781401 10574642811485848521586051)
              ·
                refine ⟨15861964217228772782379077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10574642811485848521586051 15861964217228772782379077)
                ·
                  refine ⟨2974118290730394896696077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15861964217228772782379077 2974118290730394896696077)
                  ·
                    refine ⟨1115294359023898086261029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2974118290730394896696077 1115294359023898086261029)
                    ·
                      rfl

theorem cell22_3258042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 4, 3].length) (baseStart_3258042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3258042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3258042 prefixEnd_3258042 := by exact prefixLift 3258042
  have htrace : WordTrace (prefixWord ++ tailWord_3258042) baseStart_3258042 baseEnd_3258042 := by
    simpa [prefixWord, tailWord_3258042, baseEnd_3258042] using wordTrace_append hprefix tailTrace_3258042
  have hstable : (prefixWord ++ tailWord_3258042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258042).length < 2 ^ (prefixWord ++ tailWord_3258042).sum := by decide
  have hdescent : baseEnd_3258042 < baseStart_3258042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258050 : List Nat := [3, 5, 1, 2, 1, 2, 2, 1, 5]
def baseStart_3258050 : Nat := 118140960795 + 3258050 * 2 ^ 59
def prefixEnd_3258050 : Nat := 4983230072969 + 3 ^ 40 * 3258050 * 2
def baseEnd_3258050 : Nat := 371765699195796244020335

theorem tailTrace_3258050 : CollatzResearch.WordTrace tailWord_3258050 prefixEnd_3258050 371765699195796244020335 := by
  unfold tailWord_3258050
  simp only [CollatzResearch.WordTrace]
  refine ⟨29707711461662188871350901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79220563897765836990269069 29707711461662188871350901)
  ·
    refine ⟨2785097949530830206689147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29707711461662188871350901 2785097949530830206689147)
    ·
      refine ⟨4177646924296245310033721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2785097949530830206689147 4177646924296245310033721)
      ·
        refine ⟨3133235193222183982525291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4177646924296245310033721 3133235193222183982525291)
        ·
          refine ⟨4699852789833275973787937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3133235193222183982525291 4699852789833275973787937)
          ·
            refine ⟨3524889592374956980340953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4699852789833275973787937 3524889592374956980340953)
            ·
              refine ⟨2643667194281217735255715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3524889592374956980340953 2643667194281217735255715)
              ·
                refine ⟨3965500791421826602883573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2643667194281217735255715 3965500791421826602883573)
                ·
                  refine ⟨371765699195796244020335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3965500791421826602883573 371765699195796244020335)
                  ·
                    rfl

theorem cell22_3258050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_3258050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3258050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3258050 prefixEnd_3258050 := by exact prefixLift 3258050
  have htrace : WordTrace (prefixWord ++ tailWord_3258050) baseStart_3258050 baseEnd_3258050 := by
    simpa [prefixWord, tailWord_3258050, baseEnd_3258050] using wordTrace_append hprefix tailTrace_3258050
  have hstable : (prefixWord ++ tailWord_3258050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258050).length < 2 ^ (prefixWord ++ tailWord_3258050).sum := by decide
  have hdescent : baseEnd_3258050 < baseStart_3258050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258055 : List Nat := [1, 1, 4, 1, 1, 1, 6, 7]
def baseStart_3258055 : Nat := 118140960795 + 3258055 * 2 ^ 59
def prefixEnd_3258055 : Nat := 4983230072969 + 3 ^ 40 * 3258055 * 2
def baseEnd_3258055 : Nat := 123922089909952265076221

theorem tailTrace_3258055 : CollatzResearch.WordTrace tailWord_3258055 prefixEnd_3258055 123922089909952265076221 := by
  unfold tailWord_3258055
  simp only [CollatzResearch.WordTrace]
  refine ⟨118831028211630641339335619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79220685474420427559557079 118831028211630641339335619)
  ·
    refine ⟨178246542317445962009003429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118831028211630641339335619 178246542317445962009003429)
    ·
      refine ⟨33421226684521117876688143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178246542317445962009003429 33421226684521117876688143)
      ·
        refine ⟨50131840026781676815032215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33421226684521117876688143 50131840026781676815032215)
        ·
          refine ⟨75197760040172515222548323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50131840026781676815032215 75197760040172515222548323)
          ·
            refine ⟨112796640060258772833822485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75197760040172515222548323 112796640060258772833822485)
            ·
              refine ⟨5287342502824629976585429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 112796640060258772833822485 5287342502824629976585429)
              ·
                refine ⟨123922089909952265076221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5287342502824629976585429 123922089909952265076221)
                ·
                  rfl

theorem cell22_3258055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 7].length) (baseStart_3258055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3258055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3258055 prefixEnd_3258055 := by exact prefixLift 3258055
  have htrace : WordTrace (prefixWord ++ tailWord_3258055) baseStart_3258055 baseEnd_3258055 := by
    simpa [prefixWord, tailWord_3258055, baseEnd_3258055] using wordTrace_append hprefix tailTrace_3258055
  have hstable : (prefixWord ++ tailWord_3258055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258055).length < 2 ^ (prefixWord ++ tailWord_3258055).sum := by decide
  have hdescent : baseEnd_3258055 < baseStart_3258055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258102 : List Nat := [5, 1, 1, 1, 1, 3, 1, 1, 2, 6]
def baseStart_3258102 : Nat := 118140960795 + 3258102 * 2 ^ 59
def prefixEnd_3258102 : Nat := 4983230072969 + 3 ^ 40 * 3258102 * 2
def baseEnd_3258102 : Nat := 1115314898250077929760845

theorem tailTrace_3258102 : CollatzResearch.WordTrace tailWord_3258102 prefixEnd_3258102 1115314898250077929760845 := by
  unfold tailWord_3258102
  simp only [CollatzResearch.WordTrace]
  refine ⟨7427046402653773022893535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79221828294973578910864373 7427046402653773022893535)
  ·
    refine ⟨11140569603980659534340303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7427046402653773022893535 11140569603980659534340303)
    ·
      refine ⟨16710854405970989301510455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11140569603980659534340303 16710854405970989301510455)
      ·
        refine ⟨25066281608956483952265683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16710854405970989301510455 25066281608956483952265683)
        ·
          refine ⟨37599422413434725928398525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25066281608956483952265683 37599422413434725928398525)
          ·
            refine ⟨14099783405038022223149447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37599422413434725928398525 14099783405038022223149447)
            ·
              refine ⟨21149675107557033334724171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14099783405038022223149447 21149675107557033334724171)
              ·
                refine ⟨31724512661335550002086257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21149675107557033334724171 31724512661335550002086257)
                ·
                  refine ⟨23793384496001662501564693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31724512661335550002086257 23793384496001662501564693)
                  ·
                    refine ⟨1115314898250077929760845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23793384496001662501564693 1115314898250077929760845)
                    ·
                      rfl

theorem cell22_3258102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_3258102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3258102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3258102 prefixEnd_3258102 := by exact prefixLift 3258102
  have htrace : WordTrace (prefixWord ++ tailWord_3258102) baseStart_3258102 baseEnd_3258102 := by
    simpa [prefixWord, tailWord_3258102, baseEnd_3258102] using wordTrace_append hprefix tailTrace_3258102
  have hstable : (prefixWord ++ tailWord_3258102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258102).length < 2 ^ (prefixWord ++ tailWord_3258102).sum := by decide
  have hdescent : baseEnd_3258102 < baseStart_3258102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258115 : List Nat := [1, 1, 1, 3, 2, 2, 3, 1, 1, 7]
def baseStart_3258115 : Nat := 118140960795 + 3258115 * 2 ^ 59
def prefixEnd_3258115 : Nat := 4983230072969 + 3 ^ 40 * 3258115 * 2
def baseEnd_3258115 : Nat := 1115319348415750229185805

theorem tailTrace_3258115 : CollatzResearch.WordTrace tailWord_3258115 prefixEnd_3258115 1115319348415750229185805 := by
  unfold tailWord_3258115
  simp only [CollatzResearch.WordTrace]
  refine ⟨118833216591413271586519799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79222144394275514391013199 118833216591413271586519799)
  ·
    refine ⟨178249824887119907379779699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118833216591413271586519799 178249824887119907379779699)
    ·
      refine ⟨267374737330679861069669549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178249824887119907379779699 267374737330679861069669549)
      ·
        refine ⟨100265526499004947901126081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267374737330679861069669549 100265526499004947901126081)
        ·
          refine ⟨75199144874253710925844561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100265526499004947901126081 75199144874253710925844561)
          ·
            refine ⟨56399358655690283194383421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75199144874253710925844561 56399358655690283194383421)
            ·
              refine ⟨21149759495883856197893783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56399358655690283194383421 21149759495883856197893783)
              ·
                refine ⟨31724639243825784296840675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21149759495883856197893783 31724639243825784296840675)
                ·
                  refine ⟨47586958865738676445261013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31724639243825784296840675 47586958865738676445261013)
                  ·
                    refine ⟨1115319348415750229185805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47586958865738676445261013 1115319348415750229185805)
                    ·
                      rfl

theorem cell22_3258115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 7].length) (baseStart_3258115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3258115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3258115 prefixEnd_3258115 := by exact prefixLift 3258115
  have htrace : WordTrace (prefixWord ++ tailWord_3258115) baseStart_3258115 baseEnd_3258115 := by
    simpa [prefixWord, tailWord_3258115, baseEnd_3258115] using wordTrace_append hprefix tailTrace_3258115
  have hstable : (prefixWord ++ tailWord_3258115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258115).length < 2 ^ (prefixWord ++ tailWord_3258115).sum := by decide
  have hdescent : baseEnd_3258115 < baseStart_3258115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258160 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 2, 9]
def baseStart_3258160 : Nat := 118140960795 + 3258160 * 2 ^ 59
def prefixEnd_3258160 : Nat := 4983230072969 + 3 ^ 40 * 3258160 * 2
def baseEnd_3258160 : Nat := 1115334752835385111810667

theorem tailTrace_3258160 : CollatzResearch.WordTrace tailWord_3258160 prefixEnd_3258160 1115334752835385111810667 := by
  unfold tailWord_3258160
  simp only [CollatzResearch.WordTrace]
  refine ⟨59417428938125122135953967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79223238584166829514605289 59417428938125122135953967)
  ·
    refine ⟨89126143407187683203930951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59417428938125122135953967 89126143407187683203930951)
    ·
      refine ⟨133689215110781524805896427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89126143407187683203930951 133689215110781524805896427)
      ·
        refine ⟨200533822666172287208844641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133689215110781524805896427 200533822666172287208844641)
        ·
          refine ⟨150400366999629215406633481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200533822666172287208844641 150400366999629215406633481)
          ·
            refine ⟨112800275249721911554975111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150400366999629215406633481 112800275249721911554975111)
            ·
              refine ⟨169200412874582867332462667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112800275249721911554975111 169200412874582867332462667)
              ·
                refine ⟨253800619311874300998694001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169200412874582867332462667 253800619311874300998694001)
                ·
                  refine ⟨190350464483905725749020501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 253800619311874300998694001 190350464483905725749020501)
                  ·
                    refine ⟨1115334752835385111810667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 190350464483905725749020501 1115334752835385111810667)
                    ·
                      rfl

theorem cell22_3258160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 9].length) (baseStart_3258160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3258160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3258160 prefixEnd_3258160 := by exact prefixLift 3258160
  have htrace : WordTrace (prefixWord ++ tailWord_3258160) baseStart_3258160 baseEnd_3258160 := by
    simpa [prefixWord, tailWord_3258160, baseEnd_3258160] using wordTrace_append hprefix tailTrace_3258160
  have hstable : (prefixWord ++ tailWord_3258160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258160).length < 2 ^ (prefixWord ++ tailWord_3258160).sum := by decide
  have hdescent : baseEnd_3258160 < baseStart_3258160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258162 : List Nat := [3, 2, 1, 1, 3, 2, 1, 3, 6]
def baseStart_3258162 : Nat := 118140960795 + 3258162 * 2 ^ 59
def prefixEnd_3258162 : Nat := 4983230072969 + 3 ^ 40 * 3258162 * 2
def baseEnd_3258162 : Nat := 371778479158752591086887

theorem tailTrace_3258162 : CollatzResearch.WordTrace tailWord_3258162 prefixEnd_3258162 371778479158752591086887 := by
  unfold tailWord_3258162
  simp only [CollatzResearch.WordTrace]
  refine ⟨29708732705560749653370185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79223287214828665742320493 29708732705560749653370185)
  ·
    refine ⟨22281549529170562240027639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29708732705560749653370185 22281549529170562240027639)
    ·
      refine ⟨33422324293755843360041459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22281549529170562240027639 33422324293755843360041459)
      ·
        refine ⟨50133486440633765040062189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33422324293755843360041459 50133486440633765040062189)
        ·
          refine ⟨18800057415237661890023321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50133486440633765040062189 18800057415237661890023321)
          ·
            refine ⟨14100043061428246417517491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18800057415237661890023321 14100043061428246417517491)
            ·
              refine ⟨21150064592142369626276237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14100043061428246417517491 21150064592142369626276237)
              ·
                refine ⟨7931274222053388609853589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21150064592142369626276237 7931274222053388609853589)
                ·
                  refine ⟨371778479158752591086887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7931274222053388609853589 371778479158752591086887)
                  ·
                    rfl

theorem cell22_3258162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_3258162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3258162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3258162 prefixEnd_3258162 := by exact prefixLift 3258162
  have htrace : WordTrace (prefixWord ++ tailWord_3258162) baseStart_3258162 baseEnd_3258162 := by
    simpa [prefixWord, tailWord_3258162, baseEnd_3258162] using wordTrace_append hprefix tailTrace_3258162
  have hstable : (prefixWord ++ tailWord_3258162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258162).length < 2 ^ (prefixWord ++ tailWord_3258162).sum := by decide
  have hdescent : baseEnd_3258162 < baseStart_3258162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258192 : List Nat := [2, 1, 1, 1, 1, 4, 1, 5, 2, 4]
def baseStart_3258192 : Nat := 118140960795 + 3258192 * 2 ^ 59
def prefixEnd_3258192 : Nat := 4983230072969 + 3 ^ 40 * 3258192 * 2
def baseEnd_3258192 : Nat := 1115345707089347695010569

theorem tailTrace_3258192 : CollatzResearch.WordTrace tailWord_3258192 prefixEnd_3258192 1115345707089347695010569 := by
  unfold tailWord_3258192
  simp only [CollatzResearch.WordTrace]
  refine ⟨59418012506067156868536415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79224016674756209158048553 59418012506067156868536415)
  ·
    refine ⟨89127018759100735302804623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59418012506067156868536415 89127018759100735302804623)
    ·
      refine ⟨133690528138651102954206935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89127018759100735302804623 133690528138651102954206935)
      ·
        refine ⟨200535792207976654431310403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133690528138651102954206935 200535792207976654431310403)
        ·
          refine ⟨300803688311964981646965605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200535792207976654431310403 300803688311964981646965605)
          ·
            refine ⟨56400691558493434058806051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 300803688311964981646965605 56400691558493434058806051)
            ·
              refine ⟨84601037337740151088209077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56400691558493434058806051 84601037337740151088209077)
              ·
                refine ⟨7931347250413139164519601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84601037337740151088209077 7931347250413139164519601)
                ·
                  refine ⟨5948510437809854373389701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7931347250413139164519601 5948510437809854373389701)
                  ·
                    refine ⟨1115345707089347695010569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5948510437809854373389701 1115345707089347695010569)
                    ·
                      rfl

theorem cell22_3258192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 2, 4].length) (baseStart_3258192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3258192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3258192 prefixEnd_3258192 := by exact prefixLift 3258192
  have htrace : WordTrace (prefixWord ++ tailWord_3258192) baseStart_3258192 baseEnd_3258192 := by
    simpa [prefixWord, tailWord_3258192, baseEnd_3258192] using wordTrace_append hprefix tailTrace_3258192
  have hstable : (prefixWord ++ tailWord_3258192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258192).length < 2 ^ (prefixWord ++ tailWord_3258192).sum := by decide
  have hdescent : baseEnd_3258192 < baseStart_3258192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258194 : List Nat := [3, 2, 2, 1, 1, 3, 1, 2, 4, 3]
def baseStart_3258194 : Nat := 118140960795 + 3258194 * 2 ^ 59
def prefixEnd_3258194 : Nat := 4983230072969 + 3 ^ 40 * 3258194 * 2
def baseEnd_3258194 : Nat := 1115346391730220356460563

theorem tailTrace_3258194 : CollatzResearch.WordTrace tailWord_3258194 prefixEnd_3258194 1115346391730220356460563 := by
  unfold tailWord_3258194
  simp only [CollatzResearch.WordTrace]
  refine ⟨29709024489531767019661409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79224065305418045385763757 29709024489531767019661409)
  ·
    refine ⟨22281768367148825264746057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29709024489531767019661409 22281768367148825264746057)
    ·
      refine ⟨16711326275361618948559543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22281768367148825264746057 16711326275361618948559543)
      ·
        refine ⟨25066989413042428422839315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16711326275361618948559543 25066989413042428422839315)
        ·
          refine ⟨37600484119563642634258973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25066989413042428422839315 37600484119563642634258973)
          ·
            refine ⟨14100181544836365987847115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37600484119563642634258973 14100181544836365987847115)
            ·
              refine ⟨21150272317254548981770673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14100181544836365987847115 21150272317254548981770673)
              ·
                refine ⟨15862704237940911736328005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21150272317254548981770673 15862704237940911736328005)
                ·
                  refine ⟨2974257044613920950561501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15862704237940911736328005 2974257044613920950561501)
                  ·
                    refine ⟨1115346391730220356460563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2974257044613920950561501 1115346391730220356460563)
                    ·
                      rfl

theorem cell22_3258194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_3258194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3258194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3258194 prefixEnd_3258194 := by exact prefixLift 3258194
  have htrace : WordTrace (prefixWord ++ tailWord_3258194) baseStart_3258194 baseEnd_3258194 := by
    simpa [prefixWord, tailWord_3258194, baseEnd_3258194] using wordTrace_append hprefix tailTrace_3258194
  have hstable : (prefixWord ++ tailWord_3258194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258194).length < 2 ^ (prefixWord ++ tailWord_3258194).sum := by decide
  have hdescent : baseEnd_3258194 < baseStart_3258194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258196 : List Nat := [2, 4, 1, 1, 3, 1, 3, 3, 4]
def baseStart_3258196 : Nat := 118140960795 + 3258196 * 2 ^ 59
def prefixEnd_3258196 : Nat := 4983230072969 + 3 ^ 40 * 3258196 * 2
def baseEnd_3258196 : Nat := 371782358790364339303519

theorem tailTrace_3258196 : CollatzResearch.WordTrace tailWord_3258196 prefixEnd_3258196 371782358790364339303519 := by
  unfold tailWord_3258196
  simp only [CollatzResearch.WordTrace]
  refine ⟨59418085452059911210109221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79224113936079881613478961 59418085452059911210109221)
  ·
    refine ⟨11140891022261233351895479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59418085452059911210109221 11140891022261233351895479)
    ·
      refine ⟨16711336533391850027843219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11140891022261233351895479 16711336533391850027843219)
      ·
        refine ⟨25067004800087775041764829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16711336533391850027843219 25067004800087775041764829)
        ·
          refine ⟨9400126800032915640661811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25067004800087775041764829 9400126800032915640661811)
          ·
            refine ⟨14100190200049373460992717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9400126800032915640661811 14100190200049373460992717)
            ·
              refine ⟨5287571325018515047872269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14100190200049373460992717 5287571325018515047872269)
              ·
                refine ⟨1982839246881943142952101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5287571325018515047872269 1982839246881943142952101)
                ·
                  refine ⟨371782358790364339303519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1982839246881943142952101 371782358790364339303519)
                  ·
                    rfl

theorem cell22_3258196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_3258196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3258196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3258196 prefixEnd_3258196 := by exact prefixLift 3258196
  have htrace : WordTrace (prefixWord ++ tailWord_3258196) baseStart_3258196 baseEnd_3258196 := by
    simpa [prefixWord, tailWord_3258196, baseEnd_3258196] using wordTrace_append hprefix tailTrace_3258196
  have hstable : (prefixWord ++ tailWord_3258196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258196).length < 2 ^ (prefixWord ++ tailWord_3258196).sum := by decide
  have hdescent : baseEnd_3258196 < baseStart_3258196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258207 : List Nat := [1, 1, 2, 3, 1, 6, 8]
def baseStart_3258207 : Nat := 118140960795 + 3258207 * 2 ^ 59
def prefixEnd_3258207 : Nat := 4983230072969 + 3 ^ 40 * 3258207 * 2
def baseEnd_3258207 : Nat := 41309290440588616884649

theorem tailTrace_3258207 : CollatzResearch.WordTrace tailWord_3258207 prefixEnd_3258207 41309290440588616884649 := by
  unfold tailWord_3258207
  simp only [CollatzResearch.WordTrace]
  refine ⟨118836572107079971298868875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79224381404719980865912583 118836572107079971298868875)
  ·
    refine ⟨178254858160619956948303313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118836572107079971298868875 178254858160619956948303313)
    ·
      refine ⟨133691143620464967711227485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178254858160619956948303313 133691143620464967711227485)
      ·
        refine ⟨50134178857674362891710307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133691143620464967711227485 50134178857674362891710307)
        ·
          refine ⟨75201268286511544337565461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50134178857674362891710307 75201268286511544337565461)
          ·
            refine ⟨3525059450930228640823381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 75201268286511544337565461 3525059450930228640823381)
            ·
              refine ⟨41309290440588616884649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3525059450930228640823381 41309290440588616884649)
              ·
                rfl

theorem cell22_3258207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 8].length) (baseStart_3258207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3258207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3258207 prefixEnd_3258207 := by exact prefixLift 3258207
  have htrace : WordTrace (prefixWord ++ tailWord_3258207) baseStart_3258207 baseEnd_3258207 := by
    simpa [prefixWord, tailWord_3258207, baseEnd_3258207] using wordTrace_append hprefix tailTrace_3258207
  have hstable : (prefixWord ++ tailWord_3258207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258207).length < 2 ^ (prefixWord ++ tailWord_3258207).sum := by decide
  have hdescent : baseEnd_3258207 < baseStart_3258207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258262 : List Nat := [5, 3, 1, 1, 2, 1, 2, 2, 2, 3]
def baseStart_3258262 : Nat := 118140960795 + 3258262 * 2 ^ 59
def prefixEnd_3258262 : Nat := 4983230072969 + 3 ^ 40 * 3258262 * 2
def baseEnd_3258262 : Nat := 1115369669519890845760355

theorem tailTrace_3258262 : CollatzResearch.WordTrace tailWord_3258262 prefixEnd_3258262 1115369669519890845760355 := by
  unfold tailWord_3258262
  simp only [CollatzResearch.WordTrace]
  refine ⟨7427411132617544730757565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79225718747920477128080693 7427411132617544730757565)
  ·
    refine ⟨2785279174731579274034087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7427411132617544730757565 2785279174731579274034087)
    ·
      refine ⟨4177918762097368911051131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2785279174731579274034087 4177918762097368911051131)
      ·
        refine ⟨6266878143146053366576697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4177918762097368911051131 6266878143146053366576697)
        ·
          refine ⟨4700158607359540024932523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6266878143146053366576697 4700158607359540024932523)
          ·
            refine ⟨7050237911039310037398785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4700158607359540024932523 7050237911039310037398785)
            ·
              refine ⟨5287678433279482528049089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7050237911039310037398785 5287678433279482528049089)
              ·
                refine ⟨3965758824959611896036817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5287678433279482528049089 3965758824959611896036817)
                ·
                  refine ⟨2974319118719708922027613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3965758824959611896036817 2974319118719708922027613)
                  ·
                    refine ⟨1115369669519890845760355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2974319118719708922027613 1115369669519890845760355)
                    ·
                      rfl

theorem cell22_3258262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_3258262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3258262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3258262 prefixEnd_3258262 := by exact prefixLift 3258262
  have htrace : WordTrace (prefixWord ++ tailWord_3258262) baseStart_3258262 baseEnd_3258262 := by
    simpa [prefixWord, tailWord_3258262, baseEnd_3258262] using wordTrace_append hprefix tailTrace_3258262
  have hstable : (prefixWord ++ tailWord_3258262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258262).length < 2 ^ (prefixWord ++ tailWord_3258262).sum := by decide
  have hdescent : baseEnd_3258262 < baseStart_3258262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258269 : List Nat := [1, 4, 2, 1, 2, 2, 1, 4, 5]
def baseStart_3258269 : Nat := 118140960795 + 3258269 * 2 ^ 59
def prefixEnd_3258269 : Nat := 4983230072969 + 3 ^ 40 * 3258269 * 2
def baseEnd_3258269 : Nat := 371790688587648386945111

theorem tailTrace_3258269 : CollatzResearch.WordTrace tailWord_3258269 prefixEnd_3258269 371790688587648386945111 := by
  unfold tailWord_3258269
  simp only [CollatzResearch.WordTrace]
  refine ⟨118838833432855355887625861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79225888955236903925083907 118838833432855355887625861)
  ·
    refine ⟨22282281268660379228929849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118838833432855355887625861 22282281268660379228929849)
    ·
      refine ⟨16711710951495284421697387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22282281268660379228929849 16711710951495284421697387)
      ·
        refine ⟨25067566427242926632546081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16711710951495284421697387 25067566427242926632546081)
        ·
          refine ⟨18800674820432194974409561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25067566427242926632546081 18800674820432194974409561)
          ·
            refine ⟨14100506115324146230807171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18800674820432194974409561 14100506115324146230807171)
            ·
              refine ⟨21150759172986219346210757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14100506115324146230807171 21150759172986219346210757)
              ·
                refine ⟨3965767344934916127414517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21150759172986219346210757 3965767344934916127414517)
                ·
                  refine ⟨371790688587648386945111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3965767344934916127414517 371790688587648386945111)
                  ·
                    rfl

theorem cell22_3258269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_3258269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3258269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3258269 prefixEnd_3258269 := by exact prefixLift 3258269
  have htrace : WordTrace (prefixWord ++ tailWord_3258269) baseStart_3258269 baseEnd_3258269 := by
    simpa [prefixWord, tailWord_3258269, baseEnd_3258269] using wordTrace_append hprefix tailTrace_3258269
  have hstable : (prefixWord ++ tailWord_3258269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258269).length < 2 ^ (prefixWord ++ tailWord_3258269).sum := by decide
  have hdescent : baseEnd_3258269 < baseStart_3258269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258316 : List Nat := [2, 2, 1, 4, 1, 3, 1, 3, 1, 4]
def baseStart_3258316 : Nat := 118140960795 + 3258316 * 2 ^ 59
def prefixEnd_3258316 : Nat := 4983230072969 + 3 ^ 40 * 3258316 * 2
def baseEnd_3258316 : Nat := 1115388154823452704910189

theorem tailTrace_3258316 : CollatzResearch.WordTrace tailWord_3258316 prefixEnd_3258316 1115388154823452704910189 := by
  unfold tailWord_3258316
  simp only [CollatzResearch.WordTrace]
  refine ⟨59420273831842541457293401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79227031775790055276391201 59420273831842541457293401)
  ·
    refine ⟨44565205373881906092970051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59420273831842541457293401 44565205373881906092970051)
    ·
      refine ⟨66847808060822859139455077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44565205373881906092970051 66847808060822859139455077)
      ·
        refine ⟨12533964011404286088647827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66847808060822859139455077 12533964011404286088647827)
        ·
          refine ⟨18800946017106429132971741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12533964011404286088647827 18800946017106429132971741)
          ·
            refine ⟨7050354756414910924864403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18800946017106429132971741 7050354756414910924864403)
            ·
              refine ⟨10575532134622366387296605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7050354756414910924864403 10575532134622366387296605)
              ·
                refine ⟨3965824550483387395236227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10575532134622366387296605 3965824550483387395236227)
                ·
                  refine ⟨5948736825725081092854341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3965824550483387395236227 5948736825725081092854341)
                  ·
                    refine ⟨1115388154823452704910189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5948736825725081092854341 1115388154823452704910189)
                    ·
                      rfl

theorem cell22_3258316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 1, 4].length) (baseStart_3258316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3258316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3258316 prefixEnd_3258316 := by exact prefixLift 3258316
  have htrace : WordTrace (prefixWord ++ tailWord_3258316) baseStart_3258316 baseEnd_3258316 := by
    simpa [prefixWord, tailWord_3258316, baseEnd_3258316] using wordTrace_append hprefix tailTrace_3258316
  have hstable : (prefixWord ++ tailWord_3258316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258316).length < 2 ^ (prefixWord ++ tailWord_3258316).sum := by decide
  have hdescent : baseEnd_3258316 < baseStart_3258316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258449 : List Nat := [1, 2, 2, 1, 3, 1, 1, 5, 6]
def baseStart_3258449 : Nat := 118140960795 + 3258449 * 2 ^ 59
def prefixEnd_3258449 : Nat := 4983230072969 + 3 ^ 40 * 3258449 * 2
def baseEnd_3258449 : Nat := 371811227813828230444927

theorem tailTrace_3258449 : CollatzResearch.WordTrace tailWord_3258449 prefixEnd_3258449 371811227813828230444927 := by
  unfold tailWord_3258449
  simp only [CollatzResearch.WordTrace]
  refine ⟨118845398572203246629178401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79230265714802164419452267 118845398572203246629178401)
  ·
    refine ⟨89134048929152434971883801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118845398572203246629178401 89134048929152434971883801)
    ·
      refine ⟨66850536696864326228912851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89134048929152434971883801 66850536696864326228912851)
      ·
        refine ⟨100275805045296489343369277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66850536696864326228912851 100275805045296489343369277)
        ·
          refine ⟨37603426891986183503763479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100275805045296489343369277 37603426891986183503763479)
          ·
            refine ⟨56405140337979275255645219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37603426891986183503763479 56405140337979275255645219)
            ·
              refine ⟨84607710506968912883467829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56405140337979275255645219 84607710506968912883467829)
              ·
                refine ⟨7931972860028335582825109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84607710506968912883467829 7931972860028335582825109)
                ·
                  refine ⟨371811227813828230444927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7931972860028335582825109 371811227813828230444927)
                  ·
                    rfl

theorem cell22_3258449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 6].length) (baseStart_3258449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3258449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3258449 prefixEnd_3258449 := by exact prefixLift 3258449
  have htrace : WordTrace (prefixWord ++ tailWord_3258449) baseStart_3258449 baseEnd_3258449 := by
    simpa [prefixWord, tailWord_3258449, baseEnd_3258449] using wordTrace_append hprefix tailTrace_3258449
  have hstable : (prefixWord ++ tailWord_3258449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258449).length < 2 ^ (prefixWord ++ tailWord_3258449).sum := by decide
  have hdescent : baseEnd_3258449 < baseStart_3258449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258481 : List Nat := [1, 2, 2, 2, 1, 1, 4, 2, 4, 3]
def baseStart_3258481 : Nat := 118140960795 + 3258481 * 2 ^ 59
def prefixEnd_3258481 : Nat := 4983230072969 + 3 ^ 40 * 3258481 * 2
def baseEnd_3258481 : Nat := 1115444637695447274534683

theorem tailTrace_3258481 : CollatzResearch.WordTrace tailWord_3258481 prefixEnd_3258481 1115444637695447274534683 := by
  unfold tailWord_3258481
  simp only [CollatzResearch.WordTrace]
  refine ⟨118846565708087316094343297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79231043805391544062895531 118846565708087316094343297)
  ·
    refine ⟨89134924281065487070757473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118846565708087316094343297 89134924281065487070757473)
    ·
      refine ⟨66851193210799115303068105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89134924281065487070757473 66851193210799115303068105)
      ·
        refine ⟨50138394908099336477301079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66851193210799115303068105 50138394908099336477301079)
        ·
          refine ⟨75207592362149004715951619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50138394908099336477301079 75207592362149004715951619)
          ·
            refine ⟨112811388543223507073927429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75207592362149004715951619 112811388543223507073927429)
            ·
              refine ⟨21152135351854407576361393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112811388543223507073927429 21152135351854407576361393)
              ·
                refine ⟨15864101513890805682271045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21152135351854407576361393 15864101513890805682271045)
                ·
                  refine ⟨2974519033854526065425821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15864101513890805682271045 2974519033854526065425821)
                  ·
                    refine ⟨1115444637695447274534683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2974519033854526065425821 1115444637695447274534683)
                    ·
                      rfl

theorem cell22_3258481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 4, 3].length) (baseStart_3258481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3258481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3258481 prefixEnd_3258481 := by exact prefixLift 3258481
  have htrace : WordTrace (prefixWord ++ tailWord_3258481) baseStart_3258481 baseEnd_3258481 := by
    simpa [prefixWord, tailWord_3258481, baseEnd_3258481] using wordTrace_append hprefix tailTrace_3258481
  have hstable : (prefixWord ++ tailWord_3258481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258481).length < 2 ^ (prefixWord ++ tailWord_3258481).sum := by decide
  have hdescent : baseEnd_3258481 < baseStart_3258481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258528 : List Nat := [2, 1, 1, 4, 2, 4, 2, 6]
def baseStart_3258528 : Nat := 118140960795 + 3258528 * 2 ^ 59
def prefixEnd_3258528 : Nat := 4983230072969 + 3 ^ 40 * 3258528 * 2
def baseEnd_3258528 : Nat := 123940080750661646512171

theorem tailTrace_3258528 : CollatzResearch.WordTrace tailWord_3258528 prefixEnd_3258528 123940080750661646512171 := by
  unfold tailWord_3258528
  simp only [CollatzResearch.WordTrace]
  refine ⟨59424139969458521560652119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79232186625944695414202825 59424139969458521560652119)
  ·
    refine ⟨89136209954187782340978179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59424139969458521560652119 89136209954187782340978179)
    ·
      refine ⟨133704314931281673511467269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89136209954187782340978179 133704314931281673511467269)
      ·
        refine ⟨25069559049615313783400113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133704314931281673511467269 25069559049615313783400113)
        ·
          refine ⟨18802169287211485337550085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25069559049615313783400113 18802169287211485337550085)
          ·
            refine ⟨3525406741352153500790641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18802169287211485337550085 3525406741352153500790641)
            ·
              refine ⟨2644055056014115125592981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3525406741352153500790641 2644055056014115125592981)
              ·
                refine ⟨123940080750661646512171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2644055056014115125592981 123940080750661646512171)
                ·
                  rfl

theorem cell22_3258528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 6].length) (baseStart_3258528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3258528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3258528 prefixEnd_3258528 := by exact prefixLift 3258528
  have htrace : WordTrace (prefixWord ++ tailWord_3258528) baseStart_3258528 baseEnd_3258528 := by
    simpa [prefixWord, tailWord_3258528, baseEnd_3258528] using wordTrace_append hprefix tailTrace_3258528
  have hstable : (prefixWord ++ tailWord_3258528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258528).length < 2 ^ (prefixWord ++ tailWord_3258528).sum := by decide
  have hdescent : baseEnd_3258528 < baseStart_3258528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258560 : List Nat := [2, 1, 1, 2, 5, 3, 1, 1, 3, 3]
def baseStart_3258560 : Nat := 118140960795 + 3258560 * 2 ^ 59
def prefixEnd_3258560 : Nat := 4983230072969 + 3 ^ 40 * 3258560 * 2
def baseEnd_3258560 : Nat := 1115471681009917401809441

theorem tailTrace_3258560 : CollatzResearch.WordTrace tailWord_3258560 prefixEnd_3258560 1115471681009917401809441 := by
  unfold tailWord_3258560
  simp only [CollatzResearch.WordTrace]
  refine ⟨59424723537400556293234567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79232964716534075057646089 59424723537400556293234567)
  ·
    refine ⟨89137085306100834439851851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59424723537400556293234567 89137085306100834439851851)
    ·
      refine ⟨133705627959151251659777777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89137085306100834439851851 133705627959151251659777777)
      ·
        refine ⟨100279220969363438744833333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133705627959151251659777777 100279220969363438744833333)
        ·
          refine ⟨9401176965877822382328125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 100279220969363438744833333 9401176965877822382328125)
          ·
            refine ⟨3525441362204183393373047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9401176965877822382328125 3525441362204183393373047)
            ·
              refine ⟨5288162043306275090059571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3525441362204183393373047 5288162043306275090059571)
              ·
                refine ⟨7932243064959412635089357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5288162043306275090059571 7932243064959412635089357)
                ·
                  refine ⟨2974591149359779738158509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7932243064959412635089357 2974591149359779738158509)
                  ·
                    refine ⟨1115471681009917401809441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2974591149359779738158509 1115471681009917401809441)
                    ·
                      rfl

theorem cell22_3258560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 3, 3].length) (baseStart_3258560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3258560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3258560 prefixEnd_3258560 := by exact prefixLift 3258560
  have htrace : WordTrace (prefixWord ++ tailWord_3258560) baseStart_3258560 baseEnd_3258560 := by
    simpa [prefixWord, tailWord_3258560, baseEnd_3258560] using wordTrace_append hprefix tailTrace_3258560
  have hstable : (prefixWord ++ tailWord_3258560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258560).length < 2 ^ (prefixWord ++ tailWord_3258560).sum := by decide
  have hdescent : baseEnd_3258560 < baseStart_3258560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258633 : List Nat := [1, 2, 1, 1, 3, 5, 2, 1, 1, 5]
def baseStart_3258633 : Nat := 118140960795 + 3258633 * 2 ^ 59
def prefixEnd_3258633 : Nat := 4983230072969 + 3 ^ 40 * 3258633 * 2
def baseEnd_3258633 : Nat := 1115496670401769544734217

theorem tailTrace_3258633 : CollatzResearch.WordTrace tailWord_3258633 prefixEnd_3258633 1115496670401769544734217 := by
  unfold tailWord_3258633
  simp only [CollatzResearch.WordTrace]
  refine ⟨118852109603536646053876553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79234739735691097369251035 118852109603536646053876553)
  ·
    refine ⟨89139082202652484540407415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118852109603536646053876553 89139082202652484540407415)
    ·
      refine ⟨133708623303978726810611123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89139082202652484540407415 133708623303978726810611123)
      ·
        refine ⟨200562934955968090215916685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133708623303978726810611123 200562934955968090215916685)
        ·
          refine ⟨75211100608488033830968757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200562934955968090215916685 75211100608488033830968757)
          ·
            refine ⟨7051040682045753171653321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75211100608488033830968757 7051040682045753171653321)
            ·
              refine ⟨5288280511534314878739991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7051040682045753171653321 5288280511534314878739991)
              ·
                refine ⟨7932420767301472318109987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5288280511534314878739991 7932420767301472318109987)
                ·
                  refine ⟨11898631150952208477164981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7932420767301472318109987 11898631150952208477164981)
                  ·
                    refine ⟨1115496670401769544734217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11898631150952208477164981 1115496670401769544734217)
                    ·
                      rfl

theorem cell22_3258633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 5].length) (baseStart_3258633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3258633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3258633 prefixEnd_3258633 := by exact prefixLift 3258633
  have htrace : WordTrace (prefixWord ++ tailWord_3258633) baseStart_3258633 baseEnd_3258633 := by
    simpa [prefixWord, tailWord_3258633, baseEnd_3258633] using wordTrace_append hprefix tailTrace_3258633
  have hstable : (prefixWord ++ tailWord_3258633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258633).length < 2 ^ (prefixWord ++ tailWord_3258633).sum := by decide
  have hdescent : baseEnd_3258633 < baseStart_3258633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258654 : List Nat := [4, 3, 2, 1, 1, 1, 4, 1, 1, 4]
def baseStart_3258654 : Nat := 118140960795 + 3258654 * 2 ^ 59
def prefixEnd_3258654 : Nat := 4983230072969 + 3 ^ 40 * 3258654 * 2
def baseEnd_3258654 : Nat := 1115503859130932489959153

theorem tailTrace_3258654 : CollatzResearch.WordTrace tailWord_3258654 prefixEnd_3258654 1115503859130932489959153 := by
  unfold tailWord_3258654
  simp only [CollatzResearch.WordTrace]
  refine ⟨14856609442057570830048877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79235250357640377760260677 14856609442057570830048877)
  ·
    refine ⟨5571228540771589061268329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14856609442057570830048877 5571228540771589061268329)
    ·
      refine ⟨4178421405578691795951247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5571228540771589061268329 4178421405578691795951247)
      ·
        refine ⟨6267632108368037693926871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4178421405578691795951247 6267632108368037693926871)
        ·
          refine ⟨9401448162552056540890307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6267632108368037693926871 9401448162552056540890307)
          ·
            refine ⟨14102172243828084811335461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9401448162552056540890307 14102172243828084811335461)
            ·
              refine ⟨2644157295717765902125399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14102172243828084811335461 2644157295717765902125399)
              ·
                refine ⟨3966235943576648853188099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2644157295717765902125399 3966235943576648853188099)
                ·
                  refine ⟨5949353915364973279782149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3966235943576648853188099 5949353915364973279782149)
                  ·
                    refine ⟨1115503859130932489959153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5949353915364973279782149 1115503859130932489959153)
                    ·
                      rfl

theorem cell22_3258654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_3258654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3258654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3258654 prefixEnd_3258654 := by exact prefixLift 3258654
  have htrace : WordTrace (prefixWord ++ tailWord_3258654) baseStart_3258654 baseEnd_3258654 := by
    simpa [prefixWord, tailWord_3258654, baseEnd_3258654] using wordTrace_append hprefix tailTrace_3258654
  have hstable : (prefixWord ++ tailWord_3258654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258654).length < 2 ^ (prefixWord ++ tailWord_3258654).sum := by decide
  have hdescent : baseEnd_3258654 < baseStart_3258654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258708 : List Nat := [2, 4, 1, 1, 2, 2, 1, 2, 7]
def baseStart_3258708 : Nat := 118140960795 + 3258708 * 2 ^ 59
def prefixEnd_3258708 : Nat := 4983230072969 + 3 ^ 40 * 3258708 * 2
def baseEnd_3258708 : Nat := 371840781478164783036329

theorem tailTrace_3258708 : CollatzResearch.WordTrace tailWord_3258708 prefixEnd_3258708 371840781478164783036329 := by
  unfold tailWord_3258708
  simp only [CollatzResearch.WordTrace]
  refine ⟨59427422539132466931428389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79236563385509955908571185 59427422539132466931428389)
  ·
    refine ⟨11142641726087337549642823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59427422539132466931428389 11142641726087337549642823)
    ·
      refine ⟨16713962589131006324464235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11142641726087337549642823 16713962589131006324464235)
      ·
        refine ⟨25070943883696509486696353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16713962589131006324464235 25070943883696509486696353)
        ·
          refine ⟨18803207912772382115022265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25070943883696509486696353 18803207912772382115022265)
          ·
            refine ⟨14102405934579286586266699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18803207912772382115022265 14102405934579286586266699)
            ·
              refine ⟨21153608901868929879400049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14102405934579286586266699 21153608901868929879400049)
              ·
                refine ⟨15865206676401697409550037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21153608901868929879400049 15865206676401697409550037)
                ·
                  refine ⟨371840781478164783036329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15865206676401697409550037 371840781478164783036329)
                  ·
                    rfl

theorem cell22_3258708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_3258708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3258708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3258708 prefixEnd_3258708 := by exact prefixLift 3258708
  have htrace : WordTrace (prefixWord ++ tailWord_3258708) baseStart_3258708 baseEnd_3258708 := by
    simpa [prefixWord, tailWord_3258708, baseEnd_3258708] using wordTrace_append hprefix tailTrace_3258708
  have hstable : (prefixWord ++ tailWord_3258708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258708).length < 2 ^ (prefixWord ++ tailWord_3258708).sum := by decide
  have hdescent : baseEnd_3258708 < baseStart_3258708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258755 : List Nat := [1, 1, 1, 3, 6, 1, 1, 1, 3, 4]
def baseStart_3258755 : Nat := 118140960795 + 3258755 * 2 ^ 59
def prefixEnd_3258755 : Nat := 4983230072969 + 3 ^ 40 * 3258755 * 2
def baseEnd_3258755 : Nat := 1115538433495001893183843

theorem tailTrace_3258755 : CollatzResearch.WordTrace tailWord_3258755 prefixEnd_3258755 1115538433495001893183843 := by
  unfold tailWord_3258755
  simp only [CollatzResearch.WordTrace]
  refine ⟨118856559309094660889817719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79237706206063107259878479 118856559309094660889817719)
  ·
    refine ⟨178284838963641991334726579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118856559309094660889817719 178284838963641991334726579)
    ·
      refine ⟨267427258445462987002089869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178284838963641991334726579 267427258445462987002089869)
      ·
        refine ⟨100285221917048620125783701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267427258445462987002089869 100285221917048620125783701)
        ·
          refine ⟨4700869777361654068396111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 100285221917048620125783701 4700869777361654068396111)
          ·
            refine ⟨7051304666042481102594167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4700869777361654068396111 7051304666042481102594167)
            ·
              refine ⟨10576956999063721653891251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7051304666042481102594167 10576956999063721653891251)
              ·
                refine ⟨15865435498595582480836877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10576956999063721653891251 15865435498595582480836877)
                ·
                  refine ⟨5949538311973343430313829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15865435498595582480836877 5949538311973343430313829)
                  ·
                    refine ⟨1115538433495001893183843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5949538311973343430313829 1115538433495001893183843)
                    ·
                      rfl

theorem cell22_3258755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 4].length) (baseStart_3258755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3258755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3258755 prefixEnd_3258755 := by exact prefixLift 3258755
  have htrace : WordTrace (prefixWord ++ tailWord_3258755) baseStart_3258755 baseEnd_3258755 := by
    simpa [prefixWord, tailWord_3258755, baseEnd_3258755] using wordTrace_append hprefix tailTrace_3258755
  have hstable : (prefixWord ++ tailWord_3258755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258755).length < 2 ^ (prefixWord ++ tailWord_3258755).sum := by decide
  have hdescent : baseEnd_3258755 < baseStart_3258755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258787 : List Nat := [1, 1, 1, 4, 1, 4, 4, 2, 4]
def baseStart_3258787 : Nat := 118140960795 + 3258787 * 2 ^ 59
def prefixEnd_3258787 : Nat := 4983230072969 + 3 ^ 40 * 3258787 * 2
def baseEnd_3258787 : Nat := 371849795916321492127915

theorem tailTrace_3258787 : CollatzResearch.WordTrace tailWord_3258787 prefixEnd_3258787 371849795916321492127915 := by
  unfold tailWord_3258787
  simp only [CollatzResearch.WordTrace]
  refine ⟨118857726444978730354982615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79238484296652486903321743 118857726444978730354982615)
  ·
    refine ⟨178286589667468095532473923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118857726444978730354982615 178286589667468095532473923)
    ·
      refine ⟨267429884501202143298710885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178286589667468095532473923 267429884501202143298710885)
      ·
        refine ⟨50143103343975401868508291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 267429884501202143298710885 50143103343975401868508291)
        ·
          refine ⟨75214655015963102802762437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50143103343975401868508291 75214655015963102802762437)
          ·
            refine ⟨14102747815493081775517957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75214655015963102802762437 14102747815493081775517957)
            ·
              refine ⟨2644265215404952832909617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14102747815493081775517957 2644265215404952832909617)
              ·
                refine ⟨1983198911553714624682213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2644265215404952832909617 1983198911553714624682213)
                ·
                  refine ⟨371849795916321492127915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1983198911553714624682213 371849795916321492127915)
                  ·
                    rfl

theorem cell22_3258787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 2, 4].length) (baseStart_3258787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3258787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3258787 prefixEnd_3258787 := by exact prefixLift 3258787
  have htrace : WordTrace (prefixWord ++ tailWord_3258787) baseStart_3258787 baseEnd_3258787 := by
    simpa [prefixWord, tailWord_3258787, baseEnd_3258787] using wordTrace_append hprefix tailTrace_3258787
  have hstable : (prefixWord ++ tailWord_3258787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258787).length < 2 ^ (prefixWord ++ tailWord_3258787).sum := by decide
  have hdescent : baseEnd_3258787 < baseStart_3258787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258804 : List Nat := [2, 5, 2, 2, 1, 1, 1, 2, 6]
def baseStart_3258804 : Nat := 118140960795 + 3258804 * 2 ^ 59
def prefixEnd_3258804 : Nat := 4983230072969 + 3 ^ 40 * 3258804 * 2
def baseEnd_3258804 : Nat := 371851735732127366236231

theorem tailTrace_3258804 : CollatzResearch.WordTrace tailWord_3258804 prefixEnd_3258804 371851735732127366236231 := by
  unfold tailWord_3258804
  simp only [CollatzResearch.WordTrace]
  refine ⟨59429173242958571129175733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79238897657278094838900977 59429173242958571129175733)
  ·
    refine ⟨5571484991527366043360225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59429173242958571129175733 5571484991527366043360225)
    ·
      refine ⟨4178613743645524532520169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5571484991527366043360225 4178613743645524532520169)
      ·
        refine ⟨3133960307734143399390127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4178613743645524532520169 3133960307734143399390127)
        ·
          refine ⟨4700940461601215099085191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3133960307734143399390127 4700940461601215099085191)
          ·
            refine ⟨7051410692401822648627787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4700940461601215099085191 7051410692401822648627787)
            ·
              refine ⟨10577116038602733972941681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7051410692401822648627787 10577116038602733972941681)
              ·
                refine ⟨7932837028952050479706261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10577116038602733972941681 7932837028952050479706261)
                ·
                  refine ⟨371851735732127366236231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7932837028952050479706261 371851735732127366236231)
                  ·
                    rfl

theorem cell22_3258804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_3258804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3258804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3258804 prefixEnd_3258804 := by exact prefixLift 3258804
  have htrace : WordTrace (prefixWord ++ tailWord_3258804) baseStart_3258804 baseEnd_3258804 := by
    simpa [prefixWord, tailWord_3258804, baseEnd_3258804] using wordTrace_append hprefix tailTrace_3258804
  have hstable : (prefixWord ++ tailWord_3258804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258804).length < 2 ^ (prefixWord ++ tailWord_3258804).sum := by decide
  have hdescent : baseEnd_3258804 < baseStart_3258804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258830 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 7, 3]
def baseStart_3258830 : Nat := 118140960795 + 3258830 * 2 ^ 59
def prefixEnd_3258830 : Nat := 4983230072969 + 3 ^ 40 * 3258830 * 2
def baseEnd_3258830 : Nat := 1115564107527726697558613

theorem tailTrace_3258830 : CollatzResearch.WordTrace tailWord_3258830 prefixEnd_3258830 1115564107527726697558613 := by
  unfold tailWord_3258830
  simp only [CollatzResearch.WordTrace]
  refine ⟨14857411847977868587349743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79239529855881965799198629 14857411847977868587349743)
  ·
    refine ⟨22286117771966802881024615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14857411847977868587349743 22286117771966802881024615)
    ·
      refine ⟨33429176657950204321536923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22286117771966802881024615 33429176657950204321536923)
      ·
        refine ⟨50143764986925306482305385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33429176657950204321536923 50143764986925306482305385)
        ·
          refine ⟨37607823740193979861729039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50143764986925306482305385 37607823740193979861729039)
          ·
            refine ⟨56411735610290969792593559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37607823740193979861729039 56411735610290969792593559)
            ·
              refine ⟨84617603415436454688890339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56411735610290969792593559 84617603415436454688890339)
              ·
                refine ⟨126926405123154682033335509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84617603415436454688890339 126926405123154682033335509)
                ·
                  refine ⟨2974837620073937860156301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 126926405123154682033335509 2974837620073937860156301)
                  ·
                    refine ⟨1115564107527726697558613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2974837620073937860156301 1115564107527726697558613)
                    ·
                      rfl

theorem cell22_3258830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 7, 3].length) (baseStart_3258830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3258830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3258830 prefixEnd_3258830 := by exact prefixLift 3258830
  have htrace : WordTrace (prefixWord ++ tailWord_3258830) baseStart_3258830 baseEnd_3258830 := by
    simpa [prefixWord, tailWord_3258830, baseEnd_3258830] using wordTrace_append hprefix tailTrace_3258830
  have hstable : (prefixWord ++ tailWord_3258830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258830).length < 2 ^ (prefixWord ++ tailWord_3258830).sum := by decide
  have hdescent : baseEnd_3258830 < baseStart_3258830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258847 : List Nat := [1, 1, 2, 3, 3, 3, 2, 1, 3, 3]
def baseStart_3258847 : Nat := 118140960795 + 3258847 * 2 ^ 59
def prefixEnd_3258847 : Nat := 4983230072969 + 3 ^ 40 * 3258847 * 2
def baseEnd_3258847 : Nat := 1115569926975144319883561

theorem tailTrace_3258847 : CollatzResearch.WordTrace tailWord_3258847 prefixEnd_3258847 1115569926975144319883561 := by
  unfold tailWord_3258847
  simp only [CollatzResearch.WordTrace]
  refine ⟨118859914824761360602166795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79239943216507573734777863 118859914824761360602166795)
  ·
    refine ⟨178289872237142040903250193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118859914824761360602166795 178289872237142040903250193)
    ·
      refine ⟨133717404177856530677437645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178289872237142040903250193 133717404177856530677437645)
      ·
        refine ⟨50144026566696199004039117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133717404177856530677437645 50144026566696199004039117)
        ·
          refine ⟨18804009962511074626514669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50144026566696199004039117 18804009962511074626514669)
          ·
            refine ⟨7051503735941652984943001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18804009962511074626514669 7051503735941652984943001)
            ·
              refine ⟨5288627801956239738707251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7051503735941652984943001 5288627801956239738707251)
              ·
                refine ⟨7932941702934359608060877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5288627801956239738707251 7932941702934359608060877)
                ·
                  refine ⟨2974853138600384853022829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7932941702934359608060877 2974853138600384853022829)
                  ·
                    refine ⟨1115569926975144319883561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2974853138600384853022829 1115569926975144319883561)
                    ·
                      rfl

theorem cell22_3258847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 3, 3].length) (baseStart_3258847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3258847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3258847 prefixEnd_3258847 := by exact prefixLift 3258847
  have htrace : WordTrace (prefixWord ++ tailWord_3258847) baseStart_3258847 baseEnd_3258847 := by
    simpa [prefixWord, tailWord_3258847, baseEnd_3258847] using wordTrace_append hprefix tailTrace_3258847
  have hstable : (prefixWord ++ tailWord_3258847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258847).length < 2 ^ (prefixWord ++ tailWord_3258847).sum := by decide
  have hdescent : baseEnd_3258847 < baseStart_3258847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258881 : List Nat := [1, 2, 4, 1, 3, 3, 1, 3, 1, 3]
def baseStart_3258881 : Nat := 118140960795 + 3258881 * 2 ^ 59
def prefixEnd_3258881 : Nat := 4983230072969 + 3 ^ 40 * 3258881 * 2
def baseEnd_3258881 : Nat := 1115581565869979564533457

theorem tailTrace_3258881 : CollatzResearch.WordTrace tailWord_3258881 prefixEnd_3258881 1115581565869979564533457 := by
  unfold tailWord_3258881
  simp only [CollatzResearch.WordTrace]
  refine ⟨118861154906638184408904497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79240769937758789605936331 118861154906638184408904497)
  ·
    refine ⟨89145866179978638306678373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118861154906638184408904497 89145866179978638306678373)
    ·
      refine ⟨16714849908745994682502195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89145866179978638306678373 16714849908745994682502195)
      ·
        refine ⟨25072274863118992023753293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16714849908745994682502195 25072274863118992023753293)
        ·
          refine ⟨9402103073669622008907485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25072274863118992023753293 9402103073669622008907485)
          ·
            refine ⟨3525788652626108253340307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9402103073669622008907485 3525788652626108253340307)
            ·
              refine ⟨5288682978939162380010461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3525788652626108253340307 5288682978939162380010461)
              ·
                refine ⟨1983256117102185892503923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5288682978939162380010461 1983256117102185892503923)
                ·
                  refine ⟨2974884175653278838755885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1983256117102185892503923 2974884175653278838755885)
                  ·
                    refine ⟨1115581565869979564533457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2974884175653278838755885 1115581565869979564533457)
                    ·
                      rfl

theorem cell22_3258881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_3258881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3258881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3258881 prefixEnd_3258881 := by exact prefixLift 3258881
  have htrace : WordTrace (prefixWord ++ tailWord_3258881) baseStart_3258881 baseEnd_3258881 := by
    simpa [prefixWord, tailWord_3258881, baseEnd_3258881] using wordTrace_append hprefix tailTrace_3258881
  have hstable : (prefixWord ++ tailWord_3258881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258881).length < 2 ^ (prefixWord ++ tailWord_3258881).sum := by decide
  have hdescent : baseEnd_3258881 < baseStart_3258881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258954 : List Nat := [3, 1, 2, 1, 1, 5, 2, 2, 2, 3]
def baseStart_3258954 : Nat := 118140960795 + 3258954 * 2 ^ 59
def prefixEnd_3258954 : Nat := 4983230072969 + 3 ^ 40 * 3258954 * 2
def baseEnd_3258954 : Nat := 1115606555261831707458233

theorem tailTrace_3258954 : CollatzResearch.WordTrace tailWord_3258954 prefixEnd_3258954 1115606555261831707458233 := by
  unfold tailWord_3258954
  simp only [CollatzResearch.WordTrace]
  refine ⟨29715954358843429469077979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79242544956915811917541277 29715954358843429469077979)
  ·
    refine ⟨44573931538265144203616969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29715954358843429469077979 44573931538265144203616969)
    ·
      refine ⟨33430448653698858152712727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44573931538265144203616969 33430448653698858152712727)
      ·
        refine ⟨50145672980548287229069091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33430448653698858152712727 50145672980548287229069091)
        ·
          refine ⟨75218509470822430843603637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50145672980548287229069091 75218509470822430843603637)
          ·
            refine ⟨7051735262889602891587841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75218509470822430843603637 7051735262889602891587841)
            ·
              refine ⟨5288801447167202168690881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7051735262889602891587841 5288801447167202168690881)
              ·
                refine ⟨3966601085375401626518161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5288801447167202168690881 3966601085375401626518161)
                ·
                  refine ⟨2974950814031551219888621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3966601085375401626518161 2974950814031551219888621)
                  ·
                    refine ⟨1115606555261831707458233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2974950814031551219888621 1115606555261831707458233)
                    ·
                      rfl

theorem cell22_3258954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 2, 3].length) (baseStart_3258954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3258954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3258954 prefixEnd_3258954 := by exact prefixLift 3258954
  have htrace : WordTrace (prefixWord ++ tailWord_3258954) baseStart_3258954 baseEnd_3258954 := by
    simpa [prefixWord, tailWord_3258954, baseEnd_3258954] using wordTrace_append hprefix tailTrace_3258954
  have hstable : (prefixWord ++ tailWord_3258954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258954).length < 2 ^ (prefixWord ++ tailWord_3258954).sum := by decide
  have hdescent : baseEnd_3258954 < baseStart_3258954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258980 : List Nat := [2, 3, 1, 1, 2, 2, 1, 2, 2, 6]
def baseStart_3258980 : Nat := 118140960795 + 3258980 * 2 ^ 59
def prefixEnd_3258980 : Nat := 4983230072969 + 3 ^ 40 * 3258980 * 2
def baseEnd_3258980 : Nat := 1115615455593176306308153

theorem tailTrace_3258980 : CollatzResearch.WordTrace tailWord_3258980 prefixEnd_3258980 1115615455593176306308153 := by
  unfold tailWord_3258980
  simp only [CollatzResearch.WordTrace]
  refine ⟨59432382866639762158379197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79243177155519682877838929 59432382866639762158379197)
  ·
    refine ⟨22287143574989910809392199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59432382866639762158379197 22287143574989910809392199)
    ·
      refine ⟨33430715362484866214088299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22287143574989910809392199 33430715362484866214088299)
      ·
        refine ⟨50146073043727299321132449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33430715362484866214088299 50146073043727299321132449)
        ·
          refine ⟨37609554782795474490849337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50146073043727299321132449 37609554782795474490849337)
          ·
            refine ⟨28207166087096605868137003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37609554782795474490849337 28207166087096605868137003)
            ·
              refine ⟨42310749130644908802205505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28207166087096605868137003 42310749130644908802205505)
              ·
                refine ⟨31733061847983681601654129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42310749130644908802205505 31733061847983681601654129)
                ·
                  refine ⟨23799796385987761201240597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31733061847983681601654129 23799796385987761201240597)
                  ·
                    refine ⟨1115615455593176306308153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23799796385987761201240597 1115615455593176306308153)
                    ·
                      rfl

theorem cell22_3258980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_3258980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3258980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3258980 prefixEnd_3258980 := by exact prefixLift 3258980
  have htrace : WordTrace (prefixWord ++ tailWord_3258980) baseStart_3258980 baseEnd_3258980 := by
    simpa [prefixWord, tailWord_3258980, baseEnd_3258980] using wordTrace_append hprefix tailTrace_3258980
  have hstable : (prefixWord ++ tailWord_3258980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258980).length < 2 ^ (prefixWord ++ tailWord_3258980).sum := by decide
  have hdescent : baseEnd_3258980 < baseStart_3258980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258984 : List Nat := [2, 1, 4, 3, 2, 1, 3, 6]
def baseStart_3258984 : Nat := 118140960795 + 3258984 * 2 ^ 59
def prefixEnd_3258984 : Nat := 4983230072969 + 3 ^ 40 * 3258984 * 2
def baseEnd_3258984 : Nat := 123957424986102403245349

theorem tailTrace_3258984 : CollatzResearch.WordTrace tailWord_3258984 prefixEnd_3258984 123957424986102403245349 := by
  unfold tailWord_3258984
  simp only [CollatzResearch.WordTrace]
  refine ⟨59432455812632516499952003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79243274416843355333269337 59432455812632516499952003)
  ·
    refine ⟨89148683718948774749928005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59432455812632516499952003 89148683718948774749928005)
    ·
      refine ⟨16715378197302895265611501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89148683718948774749928005 16715378197302895265611501)
      ·
        refine ⟨6268266823988585724604313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16715378197302895265611501 6268266823988585724604313)
        ·
          refine ⟨4701200117991439293453235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6268266823988585724604313 4701200117991439293453235)
          ·
            refine ⟨7051800176987158940179853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4701200117991439293453235 7051800176987158940179853)
            ·
              refine ⟨2644425066370184602567445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7051800176987158940179853 2644425066370184602567445)
              ·
                refine ⟨123957424986102403245349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2644425066370184602567445 123957424986102403245349)
                ·
                  rfl

theorem cell22_3258984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 6].length) (baseStart_3258984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3258984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3258984 prefixEnd_3258984 := by exact prefixLift 3258984
  have htrace : WordTrace (prefixWord ++ tailWord_3258984) baseStart_3258984 baseEnd_3258984 := by
    simpa [prefixWord, tailWord_3258984, baseEnd_3258984] using wordTrace_append hprefix tailTrace_3258984
  have hstable : (prefixWord ++ tailWord_3258984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258984).length < 2 ^ (prefixWord ++ tailWord_3258984).sum := by decide
  have hdescent : baseEnd_3258984 < baseStart_3258984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258999 : List Nat := [1, 1, 3, 1, 1, 3, 3, 5, 1, 3]
def baseStart_3258999 : Nat := 118140960795 + 3258999 * 2 ^ 59
def prefixEnd_3258999 : Nat := 4983230072969 + 3 ^ 40 * 3258999 * 2
def baseEnd_3258999 : Nat := 1115621959681466590083095

theorem tailTrace_3258999 : CollatzResearch.WordTrace tailWord_3258999 prefixEnd_3258999 1115621959681466590083095 := by
  unfold tailWord_3258999
  simp only [CollatzResearch.WordTrace]
  refine ⟨118865458720210690561700051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79243639146807127041133367 118865458720210690561700051)
  ·
    refine ⟨178298188080316035842550077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118865458720210690561700051 178298188080316035842550077)
    ·
      refine ⟨66861820530118513440956279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178298188080316035842550077 66861820530118513440956279)
      ·
        refine ⟨100292730795177770161434419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66861820530118513440956279 100292730795177770161434419)
        ·
          refine ⟨150439096192766655242151629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100292730795177770161434419 150439096192766655242151629)
          ·
            refine ⟨56414661072287495715806861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150439096192766655242151629 56414661072287495715806861)
            ·
              refine ⟨21155497902107810893427573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56414661072287495715806861 21155497902107810893427573)
              ·
                refine ⟨1983327928322607271258835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21155497902107810893427573 1983327928322607271258835)
                ·
                  refine ⟨2974991892483910906888253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1983327928322607271258835 2974991892483910906888253)
                  ·
                    refine ⟨1115621959681466590083095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2974991892483910906888253 1115621959681466590083095)
                    ·
                      rfl

theorem cell22_3258999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 5, 1, 3].length) (baseStart_3258999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3258999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3258999 prefixEnd_3258999 := by exact prefixLift 3258999
  have htrace : WordTrace (prefixWord ++ tailWord_3258999) baseStart_3258999 baseEnd_3258999 := by
    simpa [prefixWord, tailWord_3258999, baseEnd_3258999] using wordTrace_append hprefix tailTrace_3258999
  have hstable : (prefixWord ++ tailWord_3258999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258999).length < 2 ^ (prefixWord ++ tailWord_3258999).sum := by decide
  have hdescent : baseEnd_3258999 < baseStart_3258999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259012 : List Nat := [2, 3, 2, 1, 3, 2, 1, 1, 7]
def baseStart_3259012 : Nat := 118140960795 + 3259012 * 2 ^ 59
def prefixEnd_3259012 : Nat := 4983230072969 + 3 ^ 40 * 3259012 * 2
def baseEnd_3259012 : Nat := 371875469949046296502685

theorem tailTrace_3259012 : CollatzResearch.WordTrace tailWord_3259012 prefixEnd_3259012 371875469949046296502685 := by
  unfold tailWord_3259012
  simp only [CollatzResearch.WordTrace]
  refine ⟨59432966434581796890961645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79243955246109062521282193 59432966434581796890961645)
  ·
    refine ⟨22287362412968173834110617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59432966434581796890961645 22287362412968173834110617)
    ·
      refine ⟨16715521809726130375582963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22287362412968173834110617 16715521809726130375582963)
      ·
        refine ⟨25073282714589195563374445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16715521809726130375582963 25073282714589195563374445)
        ·
          refine ⟨9402481017970948336265417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25073282714589195563374445 9402481017970948336265417)
          ·
            refine ⟨7051860763478211252199063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9402481017970948336265417 7051860763478211252199063)
            ·
              refine ⟨10577791145217316878298595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7051860763478211252199063 10577791145217316878298595)
              ·
                refine ⟨15866686717825975317447893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10577791145217316878298595 15866686717825975317447893)
                ·
                  refine ⟨371875469949046296502685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15866686717825975317447893 371875469949046296502685)
                  ·
                    rfl

theorem cell22_3259012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_3259012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3259012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3259012 prefixEnd_3259012 := by exact prefixLift 3259012
  have htrace : WordTrace (prefixWord ++ tailWord_3259012) baseStart_3259012 baseEnd_3259012 := by
    simpa [prefixWord, tailWord_3259012, baseEnd_3259012] using wordTrace_append hprefix tailTrace_3259012
  have hstable : (prefixWord ++ tailWord_3259012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259012).length < 2 ^ (prefixWord ++ tailWord_3259012).sum := by decide
  have hdescent : baseEnd_3259012 < baseStart_3259012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259089 : List Nat := [1, 2, 2, 1, 2, 3, 3, 3, 2, 3]
def baseStart_3259089 : Nat := 118140960795 + 3259089 * 2 ^ 59
def prefixEnd_3259089 : Nat := 4983230072969 + 3 ^ 40 * 3259089 * 2
def baseEnd_3259089 : Nat := 1115652768520736355332819

theorem tailTrace_3259089 : CollatzResearch.WordTrace tailWord_3259089 prefixEnd_3259089 1115652768520736355332819 := by
  unfold tailWord_3259089
  simp only [CollatzResearch.WordTrace]
  refine ⟨118868741289884635932476321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79245827526589757288317547 118868741289884635932476321)
  ·
    refine ⟨89151555967413476949357241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118868741289884635932476321 89151555967413476949357241)
    ·
      refine ⟨66863666975560107712017931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89151555967413476949357241 66863666975560107712017931)
      ·
        refine ⟨100295500463340161568026897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66863666975560107712017931 100295500463340161568026897)
        ·
          refine ⟨75221625347505121176020173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100295500463340161568026897 75221625347505121176020173)
          ·
            refine ⟨28208109505314420441007565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75221625347505121176020173 28208109505314420441007565)
            ·
              refine ⟨10578041064492907665377837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28208109505314420441007565 10578041064492907665377837)
              ·
                refine ⟨3966765399184840374516689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10578041064492907665377837 3966765399184840374516689)
                ·
                  refine ⟨2975074049388630280887517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3966765399184840374516689 2975074049388630280887517)
                  ·
                    refine ⟨1115652768520736355332819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2975074049388630280887517 1115652768520736355332819)
                    ·
                      rfl

theorem cell22_3259089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 2, 3].length) (baseStart_3259089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3259089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3259089 prefixEnd_3259089 := by exact prefixLift 3259089
  have htrace : WordTrace (prefixWord ++ tailWord_3259089) baseStart_3259089 baseEnd_3259089 := by
    simpa [prefixWord, tailWord_3259089, baseEnd_3259089] using wordTrace_append hprefix tailTrace_3259089
  have hstable : (prefixWord ++ tailWord_3259089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259089).length < 2 ^ (prefixWord ++ tailWord_3259089).sum := by decide
  have hdescent : baseEnd_3259089 < baseStart_3259089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259093 : List Nat := [1, 3, 2, 5, 1, 2, 1, 2, 1, 4]
def baseStart_3259093 : Nat := 118140960795 + 3259093 * 2 ^ 59
def prefixEnd_3259093 : Nat := 4983230072969 + 3 ^ 40 * 3259093 * 2
def baseEnd_3259093 : Nat := 1115654137802481678232807

theorem tailTrace_3259093 : CollatzResearch.WordTrace tailWord_3259093 prefixEnd_3259093 1115654137802481678232807 := by
  unfold tailWord_3259093
  simp only [CollatzResearch.WordTrace]
  refine ⟨118868887181870144615621933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79245924787913429743747955 118868887181870144615621933)
  ·
    refine ⟨44575832693201304230858225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118868887181870144615621933 44575832693201304230858225)
    ·
      refine ⟨33431874519900978173143669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44575832693201304230858225 33431874519900978173143669)
      ·
        refine ⟨3134238236240716703732219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33431874519900978173143669 3134238236240716703732219)
        ·
          refine ⟨4701357354361075055598329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3134238236240716703732219 4701357354361075055598329)
          ·
            refine ⟨3526018015770806291698747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4701357354361075055598329 3526018015770806291698747)
            ·
              refine ⟨5289027023656209437548121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3526018015770806291698747 5289027023656209437548121)
              ·
                refine ⟨3966770267742157078161091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5289027023656209437548121 3966770267742157078161091)
                ·
                  refine ⟨5950155401613235617241637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3966770267742157078161091 5950155401613235617241637)
                  ·
                    refine ⟨1115654137802481678232807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5950155401613235617241637 1115654137802481678232807)
                    ·
                      rfl

theorem cell22_3259093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 4].length) (baseStart_3259093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3259093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3259093 prefixEnd_3259093 := by exact prefixLift 3259093
  have htrace : WordTrace (prefixWord ++ tailWord_3259093) baseStart_3259093 baseEnd_3259093 := by
    simpa [prefixWord, tailWord_3259093, baseEnd_3259093] using wordTrace_append hprefix tailTrace_3259093
  have hstable : (prefixWord ++ tailWord_3259093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259093).length < 2 ^ (prefixWord ++ tailWord_3259093).sum := by decide
  have hdescent : baseEnd_3259093 < baseStart_3259093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259125 : List Nat := [1, 3, 6, 1, 1, 1, 1, 4, 4]
def baseStart_3259125 : Nat := 118140960795 + 3259125 * 2 ^ 59
def prefixEnd_3259125 : Nat := 4983230072969 + 3 ^ 40 * 3259125 * 2
def baseEnd_3259125 : Nat := 371888364018814753810903

theorem tailTrace_3259125 : CollatzResearch.WordTrace tailWord_3259125 prefixEnd_3259125 371888364018814753810903 := by
  unfold tailWord_3259125
  simp only [CollatzResearch.WordTrace]
  refine ⟨118870054317754214080786829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79246702878502809387191219 118870054317754214080786829)
  ·
    refine ⟨44576270369157830280295061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118870054317754214080786829 44576270369157830280295061)
    ·
      refine ⟨2089512673554273294388831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44576270369157830280295061 2089512673554273294388831)
      ·
        refine ⟨3134269010331409941583247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2089512673554273294388831 3134269010331409941583247)
        ·
          refine ⟨4701403515497114912374871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3134269010331409941583247 4701403515497114912374871)
          ·
            refine ⟨7052105273245672368562307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4701403515497114912374871 7052105273245672368562307)
            ·
              refine ⟨10578157909868508552843461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7052105273245672368562307 10578157909868508552843461)
              ·
                refine ⟨1983404608100345353658149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10578157909868508552843461 1983404608100345353658149)
                ·
                  refine ⟨371888364018814753810903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1983404608100345353658149 371888364018814753810903)
                  ·
                    rfl

theorem cell22_3259125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 4, 4].length) (baseStart_3259125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3259125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3259125 prefixEnd_3259125 := by exact prefixLift 3259125
  have htrace : WordTrace (prefixWord ++ tailWord_3259125) baseStart_3259125 baseEnd_3259125 := by
    simpa [prefixWord, tailWord_3259125, baseEnd_3259125] using wordTrace_append hprefix tailTrace_3259125
  have hstable : (prefixWord ++ tailWord_3259125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259125).length < 2 ^ (prefixWord ++ tailWord_3259125).sum := by decide
  have hdescent : baseEnd_3259125 < baseStart_3259125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259132 : List Nat := [2, 2, 2, 1, 3, 2, 1, 1, 2, 6]
def baseStart_3259132 : Nat := 118140960795 + 3259132 * 2 ^ 59
def prefixEnd_3259132 : Nat := 4983230072969 + 3 ^ 40 * 3259132 * 2
def baseEnd_3259132 : Nat := 1115667488299498576507687

theorem tailTrace_3259132 : CollatzResearch.WordTrace tailWord_3259132 prefixEnd_3259132 1115667488299498576507687 := by
  unfold tailWord_3259132
  simp only [CollatzResearch.WordTrace]
  refine ⟨59435154814364427138145825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79246873085819236184194433 59435154814364427138145825)
  ·
    refine ⟨44576366110773320353609369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59435154814364427138145825 44576366110773320353609369)
    ·
      refine ⟨33432274583079990265207027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44576366110773320353609369 33432274583079990265207027)
      ·
        refine ⟨50148411874619985397810541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33432274583079990265207027 50148411874619985397810541)
        ·
          refine ⟨18805654452982494524178953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50148411874619985397810541 18805654452982494524178953)
          ·
            refine ⟨14104240839736870893134215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18805654452982494524178953 14104240839736870893134215)
            ·
              refine ⟨21156361259605306339701323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14104240839736870893134215 21156361259605306339701323)
              ·
                refine ⟨31734541889407959509551985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21156361259605306339701323 31734541889407959509551985)
                ·
                  refine ⟨23800906417055969632163989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31734541889407959509551985 23800906417055969632163989)
                  ·
                    refine ⟨1115667488299498576507687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23800906417055969632163989 1115667488299498576507687)
                    ·
                      rfl

theorem cell22_3259132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_3259132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3259132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3259132 prefixEnd_3259132 := by exact prefixLift 3259132
  have htrace : WordTrace (prefixWord ++ tailWord_3259132) baseStart_3259132 baseEnd_3259132 := by
    simpa [prefixWord, tailWord_3259132, baseEnd_3259132] using wordTrace_append hprefix tailTrace_3259132
  have hstable : (prefixWord ++ tailWord_3259132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259132).length < 2 ^ (prefixWord ++ tailWord_3259132).sum := by decide
  have hdescent : baseEnd_3259132 < baseStart_3259132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259162 : List Nat := [3, 1, 1, 3, 2, 1, 1, 2, 1, 7]
def baseStart_3259162 : Nat := 118140960795 + 3259162 * 2 ^ 59
def prefixEnd_3259162 : Nat := 4983230072969 + 3 ^ 40 * 3259162 * 2
def baseEnd_3259162 : Nat := 1115677757912588498257595

theorem tailTrace_3259162 : CollatzResearch.WordTrace tailWord_3259162 prefixEnd_3259162 1115677757912588498257595 := by
  unfold tailWord_3259162
  simp only [CollatzResearch.WordTrace]
  refine ⟨29717850954655042349970935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79247602545746779599922493 29717850954655042349970935)
  ·
    refine ⟨44576776431982563524956403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29717850954655042349970935 44576776431982563524956403)
    ·
      refine ⟨66865164647973845287434605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44576776431982563524956403 66865164647973845287434605)
      ·
        refine ⟨25074436742990191982787977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66865164647973845287434605 25074436742990191982787977)
        ·
          refine ⟨18805827557242643987090983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25074436742990191982787977 18805827557242643987090983)
          ·
            refine ⟨28208741335863965980636475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18805827557242643987090983 28208741335863965980636475)
            ·
              refine ⟨42313112003795948970954713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28208741335863965980636475 42313112003795948970954713)
              ·
                refine ⟨31734834002846961728216035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42313112003795948970954713 31734834002846961728216035)
                ·
                  refine ⟨47602251004270442592324053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31734834002846961728216035 47602251004270442592324053)
                  ·
                    refine ⟨1115677757912588498257595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47602251004270442592324053 1115677757912588498257595)
                    ·
                      rfl

theorem cell22_3259162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_3259162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3259162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3259162 prefixEnd_3259162 := by exact prefixLift 3259162
  have htrace : WordTrace (prefixWord ++ tailWord_3259162) baseStart_3259162 baseEnd_3259162 := by
    simpa [prefixWord, tailWord_3259162, baseEnd_3259162] using wordTrace_append hprefix tailTrace_3259162
  have hstable : (prefixWord ++ tailWord_3259162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259162).length < 2 ^ (prefixWord ++ tailWord_3259162).sum := by decide
  have hdescent : baseEnd_3259162 < baseStart_3259162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259168 : List Nat := [2, 1, 1, 5, 1, 3, 2, 3, 1, 3]
def baseStart_3259168 : Nat := 118140960795 + 3259168 * 2 ^ 59
def prefixEnd_3259168 : Nat := 4983230072969 + 3 ^ 40 * 3259168 * 2
def baseEnd_3259168 : Nat := 1115679811835206482607577

theorem tailTrace_3259168 : CollatzResearch.WordTrace tailWord_3259168 prefixEnd_3259168 1115679811835206482607577 := by
  unfold tailWord_3259168
  simp only [CollatzResearch.WordTrace]
  refine ⟨59435811328299216212301079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79247748437732288283068105 59435811328299216212301079)
  ·
    refine ⟨89153716992448824318451619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59435811328299216212301079 89153716992448824318451619)
    ·
      refine ⟨133730575488673236477677429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89153716992448824318451619 133730575488673236477677429)
      ·
        refine ⟨12537241452063115919782259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133730575488673236477677429 12537241452063115919782259)
        ·
          refine ⟨18805862178094673879673389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12537241452063115919782259 18805862178094673879673389)
          ·
            refine ⟨7052198316785502704877521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18805862178094673879673389 7052198316785502704877521)
            ·
              refine ⟨5289148737589127028658141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7052198316785502704877521 5289148737589127028658141)
              ·
                refine ⟨1983430776595922635746803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5289148737589127028658141 1983430776595922635746803)
                ·
                  refine ⟨2975146164893883953620205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1983430776595922635746803 2975146164893883953620205)
                  ·
                    refine ⟨1115679811835206482607577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2975146164893883953620205 1115679811835206482607577)
                    ·
                      rfl

theorem cell22_3259168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 3, 1, 3].length) (baseStart_3259168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3259168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3259168 prefixEnd_3259168 := by exact prefixLift 3259168
  have htrace : WordTrace (prefixWord ++ tailWord_3259168) baseStart_3259168 baseEnd_3259168 := by
    simpa [prefixWord, tailWord_3259168, baseEnd_3259168] using wordTrace_append hprefix tailTrace_3259168
  have hstable : (prefixWord ++ tailWord_3259168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259168).length < 2 ^ (prefixWord ++ tailWord_3259168).sum := by decide
  have hdescent : baseEnd_3259168 < baseStart_3259168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259198 : List Nat := [4, 2, 1, 2, 3, 1, 3, 1, 5]
def baseStart_3259198 : Nat := 118140960795 + 3259198 * 2 ^ 59
def prefixEnd_3259198 : Nat := 4983230072969 + 3 ^ 40 * 3259198 * 2
def baseEnd_3259198 : Nat := 371896693816098801452495

theorem tailTrace_3259198 : CollatzResearch.WordTrace tailWord_3259198 prefixEnd_3259198 371896693816098801452495 := by
  unfold tailWord_3259198
  simp only [CollatzResearch.WordTrace]
  refine ⟨14859089605811218443524281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79248477897659831698796165 14859089605811218443524281)
  ·
    refine ⟨11144317204358413832643211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14859089605811218443524281 11144317204358413832643211)
    ·
      refine ⟨16716475806537620748964817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11144317204358413832643211 16716475806537620748964817)
      ·
        refine ⟨12537356854903215561723613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16716475806537620748964817 12537356854903215561723613)
        ·
          refine ⟨4701508820588705835646355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12537356854903215561723613 4701508820588705835646355)
          ·
            refine ⟨7052263230883058753469533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4701508820588705835646355 7052263230883058753469533)
            ·
              refine ⟨2644598711581147032551075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7052263230883058753469533 2644598711581147032551075)
              ·
                refine ⟨3966898067371720548826613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2644598711581147032551075 3966898067371720548826613)
                ·
                  refine ⟨371896693816098801452495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3966898067371720548826613 371896693816098801452495)
                  ·
                    rfl

theorem cell22_3259198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_3259198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3259198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3259198 prefixEnd_3259198 := by exact prefixLift 3259198
  have htrace : WordTrace (prefixWord ++ tailWord_3259198) baseStart_3259198 baseEnd_3259198 := by
    simpa [prefixWord, tailWord_3259198, baseEnd_3259198] using wordTrace_append hprefix tailTrace_3259198
  have hstable : (prefixWord ++ tailWord_3259198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259198).length < 2 ^ (prefixWord ++ tailWord_3259198).sum := by decide
  have hdescent : baseEnd_3259198 < baseStart_3259198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259226 : List Nat := [3, 1, 1, 2, 1, 4, 3, 3, 4]
def baseStart_3259226 : Nat := 118140960795 + 3259226 * 2 ^ 59
def prefixEnd_3259226 : Nat := 4983230072969 + 3 ^ 40 * 3259226 * 2
def baseEnd_3259226 : Nat := 371899888806837888219133

theorem tailTrace_3259226 : CollatzResearch.WordTrace tailWord_3259226 prefixEnd_3259226 371899888806837888219133 := by
  unfold tailWord_3259226
  simp only [CollatzResearch.WordTrace]
  refine ⟨29718434522597077082553383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79249158726925538886809021 29718434522597077082553383)
  ·
    refine ⟨44577651783895615623830075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29718434522597077082553383 44577651783895615623830075)
    ·
      refine ⟨66866477675843423435745113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44577651783895615623830075 66866477675843423435745113)
      ·
        refine ⟨50149858256882567576808835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66866477675843423435745113 50149858256882567576808835)
        ·
          refine ⟨75224787385323851365213253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50149858256882567576808835 75224787385323851365213253)
          ·
            refine ⟨14104647634748222130977485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75224787385323851365213253 14104647634748222130977485)
            ·
              refine ⟨5289242863030583299116557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14104647634748222130977485 5289242863030583299116557)
              ·
                refine ⟨1983466073636468737168709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5289242863030583299116557 1983466073636468737168709)
                ·
                  refine ⟨371899888806837888219133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1983466073636468737168709 371899888806837888219133)
                  ·
                    rfl

theorem cell22_3259226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 3, 4].length) (baseStart_3259226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3259226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3259226 prefixEnd_3259226 := by exact prefixLift 3259226
  have htrace : WordTrace (prefixWord ++ tailWord_3259226) baseStart_3259226 baseEnd_3259226 := by
    simpa [prefixWord, tailWord_3259226, baseEnd_3259226] using wordTrace_append hprefix tailTrace_3259226
  have hstable : (prefixWord ++ tailWord_3259226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259226).length < 2 ^ (prefixWord ++ tailWord_3259226).sum := by decide
  have hdescent : baseEnd_3259226 < baseStart_3259226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259237 : List Nat := [1, 3, 1, 3, 1, 1, 12]
def baseStart_3259237 : Nat := 118140960795 + 3259237 * 2 ^ 59
def prefixEnd_3259237 : Nat := 4983230072969 + 3 ^ 40 * 3259237 * 2
def baseEnd_3259237 : Nat := 41322349331307900097495

theorem tailTrace_3259237 : CollatzResearch.WordTrace tailWord_3259237 prefixEnd_3259237 41322349331307900097495 := by
  unfold tailWord_3259237
  simp only [CollatzResearch.WordTrace]
  refine ⟨118874139293348457208863965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79249426195565638139242643 118874139293348457208863965)
  ·
    refine ⟨44577802235005671453323987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118874139293348457208863965 44577802235005671453323987)
    ·
      refine ⟨66866703352508507179985981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44577802235005671453323987 66866703352508507179985981)
      ·
        refine ⟨25075013757190690192494743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66866703352508507179985981 25075013757190690192494743)
        ·
          refine ⟨37612520635786035288742115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25075013757190690192494743 37612520635786035288742115)
          ·
            refine ⟨56418780953679052933113173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37612520635786035288742115 56418780953679052933113173)
            ·
              refine ⟨41322349331307900097495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 56418780953679052933113173 41322349331307900097495)
              ·
                rfl

theorem cell22_3259237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 12].length) (baseStart_3259237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3259237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3259237 prefixEnd_3259237 := by exact prefixLift 3259237
  have htrace : WordTrace (prefixWord ++ tailWord_3259237) baseStart_3259237 baseEnd_3259237 := by
    simpa [prefixWord, tailWord_3259237, baseEnd_3259237] using wordTrace_append hprefix tailTrace_3259237
  have hstable : (prefixWord ++ tailWord_3259237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259237).length < 2 ^ (prefixWord ++ tailWord_3259237).sum := by decide
  have hdescent : baseEnd_3259237 < baseStart_3259237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259239 : List Nat := [1, 1, 5, 1, 2, 2, 1, 1, 4, 4]
def baseStart_3259239 : Nat := 118140960795 + 3259239 * 2 ^ 59
def prefixEnd_3259239 : Nat := 4983230072969 + 3 ^ 40 * 3259239 * 2
def baseEnd_3259239 : Nat := 1115704116586185964082359

theorem tailTrace_3259239 : CollatzResearch.WordTrace tailWord_3259239 prefixEnd_3259239 1115704116586185964082359 := by
  unfold tailWord_3259239
  simp only [CollatzResearch.WordTrace]
  refine ⟨118874212239341211550436771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79249474826227474366957847 118874212239341211550436771)
  ·
    refine ⟨178311318359011817325655157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118874212239341211550436771 178311318359011817325655157)
    ·
      refine ⟨16716686096157357874280171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 178311318359011817325655157 16716686096157357874280171)
      ·
        refine ⟨25075029144236036811420257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16716686096157357874280171 25075029144236036811420257)
        ·
          refine ⟨18806271858177027608565193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25075029144236036811420257 18806271858177027608565193)
          ·
            refine ⟨14104703893632770706423895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18806271858177027608565193 14104703893632770706423895)
            ·
              refine ⟨21157055840449156059635843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14104703893632770706423895 21157055840449156059635843)
              ·
                refine ⟨31735583760673734089453765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21157055840449156059635843 31735583760673734089453765)
                ·
                  refine ⟨5950421955126325141772581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31735583760673734089453765 5950421955126325141772581)
                  ·
                    refine ⟨1115704116586185964082359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5950421955126325141772581 1115704116586185964082359)
                    ·
                      rfl

theorem cell22_3259239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_3259239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3259239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3259239 prefixEnd_3259239 := by exact prefixLift 3259239
  have htrace : WordTrace (prefixWord ++ tailWord_3259239) baseStart_3259239 baseEnd_3259239 := by
    simpa [prefixWord, tailWord_3259239, baseEnd_3259239] using wordTrace_append hprefix tailTrace_3259239
  have hstable : (prefixWord ++ tailWord_3259239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259239).length < 2 ^ (prefixWord ++ tailWord_3259239).sum := by decide
  have hdescent : baseEnd_3259239 < baseStart_3259239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259262 : List Nat := [4, 2, 3, 1, 3, 1, 1, 2, 1, 4]
def baseStart_3259262 : Nat := 118140960795 + 3259262 * 2 ^ 59
def prefixEnd_3259262 : Nat := 4983230072969 + 3 ^ 40 * 3259262 * 2
def baseEnd_3259262 : Nat := 1115711989956221570757289

theorem tailTrace_3259262 : CollatzResearch.WordTrace tailWord_3259262 prefixEnd_3259262 1115711989956221570757289 := by
  unfold tailWord_3259262
  simp only [CollatzResearch.WordTrace]
  refine ⟨14859381389782235809815505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79250034078838590985682693 14859381389782235809815505)
  ·
    refine ⟨11144536042336676857361629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14859381389782235809815505 11144536042336676857361629)
    ·
      refine ⟨4179201015876253821510611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11144536042336676857361629 4179201015876253821510611)
      ·
        refine ⟨6268801523814380732265917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4179201015876253821510611 6268801523814380732265917)
        ·
          refine ⟨2350800571430392774599719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6268801523814380732265917 2350800571430392774599719)
          ·
            refine ⟨3526200857145589161899579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2350800571430392774599719 3526200857145589161899579)
            ·
              refine ⟨5289301285718383742849369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3526200857145589161899579 5289301285718383742849369)
              ·
                refine ⟨3966975964288787807137027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5289301285718383742849369 3966975964288787807137027)
                ·
                  refine ⟨5950463946433181710705541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3966975964288787807137027 5950463946433181710705541)
                  ·
                    refine ⟨1115711989956221570757289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5950463946433181710705541 1115711989956221570757289)
                    ·
                      rfl

theorem cell22_3259262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_3259262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3259262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3259262 prefixEnd_3259262 := by exact prefixLift 3259262
  have htrace : WordTrace (prefixWord ++ tailWord_3259262) baseStart_3259262 baseEnd_3259262 := by
    simpa [prefixWord, tailWord_3259262, baseEnd_3259262] using wordTrace_append hprefix tailTrace_3259262
  have hstable : (prefixWord ++ tailWord_3259262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259262).length < 2 ^ (prefixWord ++ tailWord_3259262).sum := by decide
  have hdescent : baseEnd_3259262 < baseStart_3259262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259299 : List Nat := [1, 1, 1, 4, 1, 2, 3, 4, 5]
def baseStart_3259299 : Nat := 118140960795 + 3259299 * 2 ^ 59
def prefixEnd_3259299 : Nat := 4983230072969 + 3 ^ 40 * 3259299 * 2
def baseEnd_3259299 : Nat := 371908218604121935860725

theorem tailTrace_3259299 : CollatzResearch.WordTrace tailWord_3259299 prefixEnd_3259299 371908218604121935860725 := by
  unfold tailWord_3259299
  simp only [CollatzResearch.WordTrace]
  refine ⟨118876400619123841797620951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79250933746082561198413967 118876400619123841797620951)
  ·
    refine ⟨178314600928685762696431427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118876400619123841797620951 178314600928685762696431427)
    ·
      refine ⟨267471901393028644044647141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178314600928685762696431427 267471901393028644044647141)
      ·
        refine ⟨50150981511192870758371339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 267471901393028644044647141 50150981511192870758371339)
        ·
          refine ⟨75226472266789306137557009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50150981511192870758371339 75226472266789306137557009)
          ·
            refine ⟨56419854200091979603167757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75226472266789306137557009 56419854200091979603167757)
            ·
              refine ⟨21157445325034492351187909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56419854200091979603167757 21157445325034492351187909)
              ·
                refine ⟨3967020998443967315847733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21157445325034492351187909 3967020998443967315847733)
                ·
                  refine ⟨371908218604121935860725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3967020998443967315847733 371908218604121935860725)
                  ·
                    rfl

theorem cell22_3259299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 5].length) (baseStart_3259299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3259299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3259299 prefixEnd_3259299 := by exact prefixLift 3259299
  have htrace : WordTrace (prefixWord ++ tailWord_3259299) baseStart_3259299 baseEnd_3259299 := by
    simpa [prefixWord, tailWord_3259299, baseEnd_3259299] using wordTrace_append hprefix tailTrace_3259299
  have hstable : (prefixWord ++ tailWord_3259299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259299).length < 2 ^ (prefixWord ++ tailWord_3259299).sum := by decide
  have hdescent : baseEnd_3259299 < baseStart_3259299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259350 : List Nat := [5, 2, 1, 1, 2, 3, 1, 2, 5]
def baseStart_3259350 : Nat := 118140960795 + 3259350 * 2 ^ 59
def prefixEnd_3259350 : Nat := 4983230072969 + 3 ^ 40 * 3259350 * 2
def baseEnd_3259350 : Nat := 371914038051539558185673

theorem tailTrace_3259350 : CollatzResearch.WordTrace tailWord_3259350 prefixEnd_3259350 371914038051539558185673 := by
  unfold tailWord_3259350
  simp only [CollatzResearch.WordTrace]
  refine ⟨7429891296371192344232969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79252173827959385005151669 7429891296371192344232969)
  ·
    refine ⟨5572418472278394258174727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7429891296371192344232969 5572418472278394258174727)
    ·
      refine ⟨8358627708417591387262091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5572418472278394258174727 8358627708417591387262091)
      ·
        refine ⟨12537941562626387080893137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8358627708417591387262091 12537941562626387080893137)
        ·
          refine ⟨9403456171969790310669853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12537941562626387080893137 9403456171969790310669853)
          ·
            refine ⟨3526296064488671366501195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9403456171969790310669853 3526296064488671366501195)
            ·
              refine ⟨5289444096733007049751793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3526296064488671366501195 5289444096733007049751793)
              ·
                refine ⟨3967083072549755287313845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5289444096733007049751793 3967083072549755287313845)
                ·
                  refine ⟨371914038051539558185673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3967083072549755287313845 371914038051539558185673)
                  ·
                    rfl

theorem cell22_3259350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_3259350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3259350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3259350 prefixEnd_3259350 := by exact prefixLift 3259350
  have htrace : WordTrace (prefixWord ++ tailWord_3259350) baseStart_3259350 baseEnd_3259350 := by
    simpa [prefixWord, tailWord_3259350, baseEnd_3259350] using wordTrace_append hprefix tailTrace_3259350
  have hstable : (prefixWord ++ tailWord_3259350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259350).length < 2 ^ (prefixWord ++ tailWord_3259350).sum := by decide
  have hdescent : baseEnd_3259350 < baseStart_3259350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259406 : List Nat := [4, 1, 1, 2, 2, 4, 8]
def baseStart_3259406 : Nat := 118140960795 + 3259406 * 2 ^ 59
def prefixEnd_3259406 : Nat := 4983230072969 + 3 ^ 40 * 3259406 * 2
def baseEnd_3259406 : Nat := 41324492003668636857661

theorem tailTrace_3259406 : CollatzResearch.WordTrace tailWord_3259406 prefixEnd_3259406 41324492003668636857661 := by
  unfold tailWord_3259406
  simp only [CollatzResearch.WordTrace]
  refine ⟨14860037903717024883970759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79253535486490799381177381 14860037903717024883970759)
  ·
    refine ⟨22290056855575537325956139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14860037903717024883970759 22290056855575537325956139)
    ·
      refine ⟨33435085283363305988934209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22290056855575537325956139 33435085283363305988934209)
      ·
        refine ⟨25076313962522479491700657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33435085283363305988934209 25076313962522479491700657)
        ·
          refine ⟨18807235471891859618775493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25076313962522479491700657 18807235471891859618775493)
          ·
            refine ⟨3526356650979723678520405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18807235471891859618775493 3526356650979723678520405)
            ·
              refine ⟨41324492003668636857661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3526356650979723678520405 41324492003668636857661)
              ·
                rfl

theorem cell22_3259406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 8].length) (baseStart_3259406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3259406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3259406 prefixEnd_3259406 := by exact prefixLift 3259406
  have htrace : WordTrace (prefixWord ++ tailWord_3259406) baseStart_3259406 baseEnd_3259406 := by
    simpa [prefixWord, tailWord_3259406, baseEnd_3259406] using wordTrace_append hprefix tailTrace_3259406
  have hstable : (prefixWord ++ tailWord_3259406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259406).length < 2 ^ (prefixWord ++ tailWord_3259406).sum := by decide
  have hdescent : baseEnd_3259406 < baseStart_3259406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259438 : List Nat := [4, 1, 3, 1, 1, 1, 2, 1, 5, 3]
def baseStart_3259438 : Nat := 118140960795 + 3259438 * 2 ^ 59
def prefixEnd_3259438 : Nat := 4983230072969 + 3 ^ 40 * 3259438 * 2
def baseEnd_3259438 : Nat := 1115772238353015778356749

theorem tailTrace_3259438 : CollatzResearch.WordTrace tailWord_3259438 prefixEnd_3259438 1115772238353015778356749 := by
  unfold tailWord_3259438
  simp only [CollatzResearch.WordTrace]
  refine ⟨14860183795702533567116371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79254313577080179024620645 14860183795702533567116371)
  ·
    refine ⟨22290275693553800350674557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14860183795702533567116371 22290275693553800350674557)
    ·
      refine ⟨8358853385082675131502959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22290275693553800350674557 8358853385082675131502959)
      ·
        refine ⟨12538280077624012697254439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8358853385082675131502959 12538280077624012697254439)
        ·
          refine ⟨18807420116436019045881659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12538280077624012697254439 18807420116436019045881659)
          ·
            refine ⟨28211130174654028568822489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18807420116436019045881659 28211130174654028568822489)
            ·
              refine ⟨21158347630990521426616867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28211130174654028568822489 21158347630990521426616867)
              ·
                refine ⟨31737521446485782139925301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21158347630990521426616867 31737521446485782139925301)
                ·
                  refine ⟨2975392635608042075617997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31737521446485782139925301 2975392635608042075617997)
                  ·
                    refine ⟨1115772238353015778356749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2975392635608042075617997 1115772238353015778356749)
                    ·
                      rfl

theorem cell22_3259438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_3259438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3259438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3259438 prefixEnd_3259438 := by exact prefixLift 3259438
  have htrace : WordTrace (prefixWord ++ tailWord_3259438) baseStart_3259438 baseEnd_3259438 := by
    simpa [prefixWord, tailWord_3259438, baseEnd_3259438] using wordTrace_append hprefix tailTrace_3259438
  have hstable : (prefixWord ++ tailWord_3259438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259438).length < 2 ^ (prefixWord ++ tailWord_3259438).sum := by decide
  have hdescent : baseEnd_3259438 < baseStart_3259438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259498 : List Nat := [3, 1, 3, 2, 2, 1, 2, 1, 3, 4]
def baseStart_3259498 : Nat := 118140960795 + 3259498 * 2 ^ 59
def prefixEnd_3259498 : Nat := 4983230072969 + 3 ^ 40 * 3259498 * 2
def baseEnd_3259498 : Nat := 1115792777579195621856565

theorem tailTrace_3259498 : CollatzResearch.WordTrace tailWord_3259498 prefixEnd_3259498 1115792777579195621856565 := by
  unfold tailWord_3259498
  simp only [CollatzResearch.WordTrace]
  refine ⟨29720914686350724696028787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79255772496935265856076765 29720914686350724696028787)
  ·
    refine ⟨44581372029526087044043181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29720914686350724696028787 44581372029526087044043181)
    ·
      refine ⟨16718014511072282641516193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44581372029526087044043181 16718014511072282641516193)
      ·
        refine ⟨12538510883304211981137145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16718014511072282641516193 12538510883304211981137145)
        ·
          refine ⟨9403883162478158985852859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12538510883304211981137145 9403883162478158985852859)
          ·
            refine ⟨14105824743717238478779289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9403883162478158985852859 14105824743717238478779289)
            ·
              refine ⟨10579368557787928859084467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14105824743717238478779289 10579368557787928859084467)
              ·
                refine ⟨15869052836681893288626701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10579368557787928859084467 15869052836681893288626701)
                ·
                  refine ⟨5950894813755709983235013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15869052836681893288626701 5950894813755709983235013)
                  ·
                    refine ⟨1115792777579195621856565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5950894813755709983235013 1115792777579195621856565)
                    ·
                      rfl

theorem cell22_3259498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_3259498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3259498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3259498 prefixEnd_3259498 := by exact prefixLift 3259498
  have htrace : WordTrace (prefixWord ++ tailWord_3259498) baseStart_3259498 baseEnd_3259498 := by
    simpa [prefixWord, tailWord_3259498, baseEnd_3259498] using wordTrace_append hprefix tailTrace_3259498
  have hstable : (prefixWord ++ tailWord_3259498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259498).length < 2 ^ (prefixWord ++ tailWord_3259498).sum := by decide
  have hdescent : baseEnd_3259498 < baseStart_3259498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259511 : List Nat := [1, 1, 3, 1, 1, 4, 1, 4, 1, 5]
def baseStart_3259511 : Nat := 118140960795 + 3259511 * 2 ^ 59
def prefixEnd_3259511 : Nat := 4983230072969 + 3 ^ 40 * 3259511 * 2
def baseEnd_3259511 : Nat := 1115797227744867921281525

theorem tailTrace_3259511 : CollatzResearch.WordTrace tailWord_3259511 prefixEnd_3259511 1115797227744867921281525 := by
  unfold tailWord_3259511
  simp only [CollatzResearch.WordTrace]
  refine ⟨118884132894355802004338387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79256088596237201336225591 118884132894355802004338387)
  ·
    refine ⟨178326199341533703006507581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118884132894355802004338387 178326199341533703006507581)
    ·
      refine ⟨66872324753075138627440343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178326199341533703006507581 66872324753075138627440343)
      ·
        refine ⟨100308487129612707941160515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66872324753075138627440343 100308487129612707941160515)
        ·
          refine ⟨150462730694419061911740773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100308487129612707941160515 150462730694419061911740773)
          ·
            refine ⟨28211762005203574108451395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150462730694419061911740773 28211762005203574108451395)
            ·
              refine ⟨42317643007805361162677093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28211762005203574108451395 42317643007805361162677093)
              ·
                refine ⟨7934558063963505218001955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42317643007805361162677093 7934558063963505218001955)
                ·
                  refine ⟨11901837095945257827002933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7934558063963505218001955 11901837095945257827002933)
                  ·
                    refine ⟨1115797227744867921281525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11901837095945257827002933 1115797227744867921281525)
                    ·
                      rfl

theorem cell22_3259511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 5].length) (baseStart_3259511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3259511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3259511 prefixEnd_3259511 := by exact prefixLift 3259511
  have htrace : WordTrace (prefixWord ++ tailWord_3259511) baseStart_3259511 baseEnd_3259511 := by
    simpa [prefixWord, tailWord_3259511, baseEnd_3259511] using wordTrace_append hprefix tailTrace_3259511
  have hstable : (prefixWord ++ tailWord_3259511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259511).length < 2 ^ (prefixWord ++ tailWord_3259511).sum := by decide
  have hdescent : baseEnd_3259511 < baseStart_3259511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259601 : List Nat := [1, 2, 2, 1, 2, 2, 1, 3, 1, 7]
def baseStart_3259601 : Nat := 118140960795 + 3259601 * 2 ^ 59
def prefixEnd_3259601 : Nat := 4983230072969 + 3 ^ 40 * 3259601 * 2
def baseEnd_3259601 : Nat := 1115828036584137686531249

theorem tailTrace_3259601 : CollatzResearch.WordTrace tailWord_3259601 prefixEnd_3259601 1115828036584137686531249 := by
  unfold tailWord_3259601
  simp only [CollatzResearch.WordTrace]
  refine ⟨118887415464029747375114657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79258276976019831583409771 118887415464029747375114657)
  ·
    refine ⟨89165561598022310531335993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118887415464029747375114657 89165561598022310531335993)
    ·
      refine ⟨66874171198516732898501995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89165561598022310531335993 66874171198516732898501995)
      ·
        refine ⟨100311256797775099347752993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66874171198516732898501995 100311256797775099347752993)
        ·
          refine ⟨75233442598331324510814745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100311256797775099347752993 75233442598331324510814745)
          ·
            refine ⟨56425081948748493383111059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75233442598331324510814745 56425081948748493383111059)
            ·
              refine ⟨84637622923122740074666589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56425081948748493383111059 84637622923122740074666589)
              ·
                refine ⟨31739108596171027527999971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84637622923122740074666589 31739108596171027527999971)
                ·
                  refine ⟨47608662894256541291999957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31739108596171027527999971 47608662894256541291999957)
                  ·
                    refine ⟨1115828036584137686531249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47608662894256541291999957 1115828036584137686531249)
                    ·
                      rfl

theorem cell22_3259601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_3259601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3259601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3259601 prefixEnd_3259601 := by exact prefixLift 3259601
  have htrace : WordTrace (prefixWord ++ tailWord_3259601) baseStart_3259601 baseEnd_3259601 := by
    simpa [prefixWord, tailWord_3259601, baseEnd_3259601] using wordTrace_append hprefix tailTrace_3259601
  have hstable : (prefixWord ++ tailWord_3259601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259601).length < 2 ^ (prefixWord ++ tailWord_3259601).sum := by decide
  have hdescent : baseEnd_3259601 < baseStart_3259601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259663 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 8, 3]
def baseStart_3259663 : Nat := 118140960795 + 3259663 * 2 ^ 59
def prefixEnd_3259663 : Nat := 4983230072969 + 3 ^ 40 * 3259663 * 2
def baseEnd_3259663 : Nat := 1115849260451190191481059

theorem tailTrace_3259663 : CollatzResearch.WordTrace tailWord_3259663 prefixEnd_3259663 1115849260451190191481059 := by
  unfold tailWord_3259663
  simp only [CollatzResearch.WordTrace]
  refine ⟨118889676789805131963871643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79259784526536754642581095 118889676789805131963871643)
  ·
    refine ⟨178334515184707697945807465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118889676789805131963871643 178334515184707697945807465)
    ·
      refine ⟨133750886388530773459355599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178334515184707697945807465 133750886388530773459355599)
      ·
        refine ⟨200626329582796160189033399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133750886388530773459355599 200626329582796160189033399)
        ·
          refine ⟨300939494374194240283550099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200626329582796160189033399 300939494374194240283550099)
          ·
            refine ⟨451409241561291360425325149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300939494374194240283550099 451409241561291360425325149)
            ·
              refine ⟨169278465585484260159496931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 451409241561291360425325149 169278465585484260159496931)
              ·
                refine ⟨253917698378226390239245397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169278465585484260159496931 253917698378226390239245397)
                ·
                  refine ⟨2975598027869840510616157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 253917698378226390239245397 2975598027869840510616157)
                  ·
                    refine ⟨1115849260451190191481059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2975598027869840510616157 1115849260451190191481059)
                    ·
                      rfl

theorem cell22_3259663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 8, 3].length) (baseStart_3259663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3259663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3259663 prefixEnd_3259663 := by exact prefixLift 3259663
  have htrace : WordTrace (prefixWord ++ tailWord_3259663) baseStart_3259663 baseEnd_3259663 := by
    simpa [prefixWord, tailWord_3259663, baseEnd_3259663] using wordTrace_append hprefix tailTrace_3259663
  have hstable : (prefixWord ++ tailWord_3259663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259663).length < 2 ^ (prefixWord ++ tailWord_3259663).sum := by decide
  have hdescent : baseEnd_3259663 < baseStart_3259663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259697 : List Nat := [1, 2, 2, 3, 3, 1, 3, 2, 2, 3]
def baseStart_3259697 : Nat := 118140960795 + 3259697 * 2 ^ 59
def prefixEnd_3259697 : Nat := 4983230072969 + 3 ^ 40 * 3259697 * 2
def baseEnd_3259697 : Nat := 1115860899346025436130955

theorem tailTrace_3259697 : CollatzResearch.WordTrace tailWord_3259697 prefixEnd_3259697 1115860899346025436130955 := by
  unfold tailWord_3259697
  simp only [CollatzResearch.WordTrace]
  refine ⟨118890916871681955770609345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79260611247787970513739563 118890916871681955770609345)
  ·
    refine ⟨89168187653761466827957009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118890916871681955770609345 89168187653761466827957009)
    ·
      refine ⟨66876140740321100120967757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89168187653761466827957009 66876140740321100120967757)
      ·
        refine ⟨25078552777620412545362909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66876140740321100120967757 25078552777620412545362909)
        ·
          refine ⟨9404457291607654704511091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25078552777620412545362909 9404457291607654704511091)
          ·
            refine ⟨14106685937411482056766637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9404457291607654704511091 14106685937411482056766637)
            ·
              refine ⟨5290007226529305771287489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14106685937411482056766637 5290007226529305771287489)
              ·
                refine ⟨3967505419896979328465617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5290007226529305771287489 3967505419896979328465617)
                ·
                  refine ⟨2975629064922734496349213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3967505419896979328465617 2975629064922734496349213)
                  ·
                    refine ⟨1115860899346025436130955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2975629064922734496349213 1115860899346025436130955)
                    ·
                      rfl

theorem cell22_3259697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 2, 3].length) (baseStart_3259697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3259697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3259697 prefixEnd_3259697 := by exact prefixLift 3259697
  have htrace : WordTrace (prefixWord ++ tailWord_3259697) baseStart_3259697 baseEnd_3259697 := by
    simpa [prefixWord, tailWord_3259697, baseEnd_3259697] using wordTrace_append hprefix tailTrace_3259697
  have hstable : (prefixWord ++ tailWord_3259697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259697).length < 2 ^ (prefixWord ++ tailWord_3259697).sum := by decide
  have hdescent : baseEnd_3259697 < baseStart_3259697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259738 : List Nat := [3, 1, 1, 2, 1, 2, 3, 2, 7]
def baseStart_3259738 : Nat := 118140960795 + 3259738 * 2 ^ 59
def prefixEnd_3259738 : Nat := 4983230072969 + 3 ^ 40 * 3259738 * 2
def baseEnd_3259738 : Nat := 371958311494638331951943

theorem tailTrace_3259738 : CollatzResearch.WordTrace tailWord_3259738 prefixEnd_3259738 371958311494638331951943 := by
  unfold tailWord_3259738
  simp only [CollatzResearch.WordTrace]
  refine ⟨29723103066133354943212967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79261608176355613181901245 29723103066133354943212967)
  ·
    refine ⟨44584654599200032414819451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29723103066133354943212967 44584654599200032414819451)
    ·
      refine ⟨66876981898800048622229177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44584654599200032414819451 66876981898800048622229177)
      ·
        refine ⟨50157736424100036466671883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66876981898800048622229177 50157736424100036466671883)
        ·
          refine ⟨75236604636150054700007825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50157736424100036466671883 75236604636150054700007825)
          ·
            refine ⟨56427453477112541025005869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75236604636150054700007825 56427453477112541025005869)
            ·
              refine ⟨21160295053917202884377201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56427453477112541025005869 21160295053917202884377201)
              ·
                refine ⟨15870221290437902163282901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21160295053917202884377201 15870221290437902163282901)
                ·
                  refine ⟨371958311494638331951943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15870221290437902163282901 371958311494638331951943)
                  ·
                    rfl

theorem cell22_3259738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 7].length) (baseStart_3259738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3259738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3259738 prefixEnd_3259738 := by exact prefixLift 3259738
  have htrace : WordTrace (prefixWord ++ tailWord_3259738) baseStart_3259738 baseEnd_3259738 := by
    simpa [prefixWord, tailWord_3259738, baseEnd_3259738] using wordTrace_append hprefix tailTrace_3259738
  have hstable : (prefixWord ++ tailWord_3259738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259738).length < 2 ^ (prefixWord ++ tailWord_3259738).sum := by decide
  have hdescent : baseEnd_3259738 < baseStart_3259738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259753 : List Nat := [1, 2, 1, 1, 1, 3, 2, 4, 2, 5]
def baseStart_3259753 : Nat := 118140960795 + 3259753 * 2 ^ 59
def prefixEnd_3259753 : Nat := 4983230072969 + 3 ^ 40 * 3259753 * 2
def baseEnd_3259753 : Nat := 1115880069290459956730783

theorem tailTrace_3259753 : CollatzResearch.WordTrace tailWord_3259753 prefixEnd_3259753 1115880069290459956730783 := by
  unfold tailWord_3259753
  simp only [CollatzResearch.WordTrace]
  refine ⟨118892959359479077334647913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79261972906319384889765275 118892959359479077334647913)
  ·
    refine ⟨89169719519609308000985935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118892959359479077334647913 89169719519609308000985935)
    ·
      refine ⟨133754579279413962001478903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89169719519609308000985935 133754579279413962001478903)
      ·
        refine ⟨200631868919120943002218355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133754579279413962001478903 200631868919120943002218355)
        ·
          refine ⟨300947803378681414503327533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200631868919120943002218355 300947803378681414503327533)
          ·
            refine ⟨112855426267005530438747825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 300947803378681414503327533 112855426267005530438747825)
            ·
              refine ⟨84641569700254147829060869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112855426267005530438747825 84641569700254147829060869)
              ·
                refine ⟨15870294318797652717948913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84641569700254147829060869 15870294318797652717948913)
                ·
                  refine ⟨11902720739098239538461685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15870294318797652717948913 11902720739098239538461685)
                  ·
                    refine ⟨1115880069290459956730783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11902720739098239538461685 1115880069290459956730783)
                    ·
                      rfl

theorem cell22_3259753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 5].length) (baseStart_3259753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3259753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3259753 prefixEnd_3259753 := by exact prefixLift 3259753
  have htrace : WordTrace (prefixWord ++ tailWord_3259753) baseStart_3259753 baseEnd_3259753 := by
    simpa [prefixWord, tailWord_3259753, baseEnd_3259753] using wordTrace_append hprefix tailTrace_3259753
  have hstable : (prefixWord ++ tailWord_3259753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259753).length < 2 ^ (prefixWord ++ tailWord_3259753).sum := by decide
  have hdescent : baseEnd_3259753 < baseStart_3259753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259759 : List Nat := [1, 1, 2, 1, 3, 1, 7, 2, 1, 3]
def baseStart_3259759 : Nat := 118140960795 + 3259759 * 2 ^ 59
def prefixEnd_3259759 : Nat := 4983230072969 + 3 ^ 40 * 3259759 * 2
def baseEnd_3259759 : Nat := 1115882123213077941080765

theorem tailTrace_3259759 : CollatzResearch.WordTrace tailWord_3259759 prefixEnd_3259759 1115882123213077941080765 := by
  unfold tailWord_3259759
  simp only [CollatzResearch.WordTrace]
  refine ⟨118893178197457340359366331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79262118798304893572910887 118893178197457340359366331)
  ·
    refine ⟨178339767296186010539049497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118893178197457340359366331 178339767296186010539049497)
    ·
      refine ⟨133754825472139507904287123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178339767296186010539049497 133754825472139507904287123)
      ·
        refine ⟨200632238208209261856430685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133754825472139507904287123 200632238208209261856430685)
        ·
          refine ⟨75237089328078473196161507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200632238208209261856430685 75237089328078473196161507)
          ·
            refine ⟨112855633992117709794242261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75237089328078473196161507 112855633992117709794242261)
            ·
              refine ⟨2645053921690258823302553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 112855633992117709794242261 2645053921690258823302553)
              ·
                refine ⟨1983790441267694117476915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2645053921690258823302553 1983790441267694117476915)
                ·
                  refine ⟨2975685661901541176215373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1983790441267694117476915 2975685661901541176215373)
                  ·
                    refine ⟨1115882123213077941080765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2975685661901541176215373 1115882123213077941080765)
                    ·
                      rfl

theorem cell22_3259759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 2, 1, 3].length) (baseStart_3259759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3259759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3259759 prefixEnd_3259759 := by exact prefixLift 3259759
  have htrace : WordTrace (prefixWord ++ tailWord_3259759) baseStart_3259759 baseEnd_3259759 := by
    simpa [prefixWord, tailWord_3259759, baseEnd_3259759] using wordTrace_append hprefix tailTrace_3259759
  have hstable : (prefixWord ++ tailWord_3259759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259759).length < 2 ^ (prefixWord ++ tailWord_3259759).sum := by decide
  have hdescent : baseEnd_3259759 < baseStart_3259759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259815 : List Nat := [1, 1, 6, 1, 1, 1, 1, 2, 3, 5]
def baseStart_3259815 : Nat := 118140960795 + 3259815 * 2 ^ 59
def prefixEnd_3259815 : Nat := 4983230072969 + 3 ^ 40 * 3259815 * 2
def baseEnd_3259815 : Nat := 1115901293157512461680593

theorem tailTrace_3259815 : CollatzResearch.WordTrace tailWord_3259815 prefixEnd_3259815 1115901293157512461680593 := by
  unfold tailWord_3259815
  simp only [CollatzResearch.WordTrace]
  refine ⟨118895220685254461923404899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79263480456836307948936599 118895220685254461923404899)
  ·
    refine ⟨178342831027881692885107349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118895220685254461923404899 178342831027881692885107349)
    ·
      refine ⟨8359820204431954353989407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 178342831027881692885107349 8359820204431954353989407)
      ·
        refine ⟨12539730306647931530984111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8359820204431954353989407 12539730306647931530984111)
        ·
          refine ⟨18809595459971897296476167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12539730306647931530984111 18809595459971897296476167)
          ·
            refine ⟨28214393189957845944714251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18809595459971897296476167 28214393189957845944714251)
            ·
              refine ⟨42321589784936768917071377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28214393189957845944714251 42321589784936768917071377)
              ·
                refine ⟨31741192338702576687803533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42321589784936768917071377 31741192338702576687803533)
                ·
                  refine ⟨11902947127013466257926325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31741192338702576687803533 11902947127013466257926325)
                  ·
                    refine ⟨1115901293157512461680593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11902947127013466257926325 1115901293157512461680593)
                    ·
                      rfl

theorem cell22_3259815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_3259815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3259815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3259815 prefixEnd_3259815 := by exact prefixLift 3259815
  have htrace : WordTrace (prefixWord ++ tailWord_3259815) baseStart_3259815 baseEnd_3259815 := by
    simpa [prefixWord, tailWord_3259815, baseEnd_3259815] using wordTrace_append hprefix tailTrace_3259815
  have hstable : (prefixWord ++ tailWord_3259815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259815).length < 2 ^ (prefixWord ++ tailWord_3259815).sum := by decide
  have hdescent : baseEnd_3259815 < baseStart_3259815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259832 : List Nat := [2, 1, 2, 1, 2, 2, 4, 3, 2, 3]
def baseStart_3259832 : Nat := 118140960795 + 3259832 * 2 ^ 59
def prefixEnd_3259832 : Nat := 4983230072969 + 3 ^ 40 * 3259832 * 2
def baseEnd_3259832 : Nat := 1115907112604930084005541

theorem tailTrace_3259832 : CollatzResearch.WordTrace tailWord_3259832 prefixEnd_3259832 1115907112604930084005541 := by
  unfold tailWord_3259832
  simp only [CollatzResearch.WordTrace]
  refine ⟨59447920363096436913386875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79263893817461915884515833 59447920363096436913386875)
  ·
    refine ⟨89171880544644655370080313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59447920363096436913386875 89171880544644655370080313)
    ·
      refine ⟨66878910408483491527560235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89171880544644655370080313 66878910408483491527560235)
      ·
        refine ⟨100318365612725237291340353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66878910408483491527560235 100318365612725237291340353)
        ·
          refine ⟨75238774209543927968505265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100318365612725237291340353 75238774209543927968505265)
          ·
            refine ⟨56429080657157945976378949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75238774209543927968505265 56429080657157945976378949)
            ·
              refine ⟨10580452623217114870571053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56429080657157945976378949 10580452623217114870571053)
              ·
                refine ⟨3967669733706418076464145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10580452623217114870571053 3967669733706418076464145)
                ·
                  refine ⟨2975752300279813557348109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3967669733706418076464145 2975752300279813557348109)
                  ·
                    refine ⟨1115907112604930084005541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2975752300279813557348109 1115907112604930084005541)
                    ·
                      rfl

theorem cell22_3259832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 2, 3].length) (baseStart_3259832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3259832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3259832 prefixEnd_3259832 := by exact prefixLift 3259832
  have htrace : WordTrace (prefixWord ++ tailWord_3259832) baseStart_3259832 baseEnd_3259832 := by
    simpa [prefixWord, tailWord_3259832, baseEnd_3259832] using wordTrace_append hprefix tailTrace_3259832
  have hstable : (prefixWord ++ tailWord_3259832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259832).length < 2 ^ (prefixWord ++ tailWord_3259832).sum := by decide
  have hdescent : baseEnd_3259832 < baseStart_3259832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259862 : List Nat := [5, 2, 1, 1, 1, 3, 9]
def baseStart_3259862 : Nat := 118140960795 + 3259862 * 2 ^ 59
def prefixEnd_3259862 : Nat := 4983230072969 + 3 ^ 40 * 3259862 * 2
def baseEnd_3259862 : Nat := 41330273415482222435387

theorem tailTrace_3259862 : CollatzResearch.WordTrace tailWord_3259862 prefixEnd_3259862 41330273415482222435387 := by
  unfold tailWord_3259862
  simp only [CollatzResearch.WordTrace]
  refine ⟨7431058432255261809397865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79264623277389459300243893 7431058432255261809397865)
  ·
    refine ⟨5573293824191446357048399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7431058432255261809397865 5573293824191446357048399)
    ·
      refine ⟨8359940736287169535572599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5573293824191446357048399 8359940736287169535572599)
      ·
        refine ⟨12539911104430754303358899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8359940736287169535572599 12539911104430754303358899)
        ·
          refine ⟨18809866656646131455038349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12539911104430754303358899 18809866656646131455038349)
          ·
            refine ⟨7053699996242299295639381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18809866656646131455038349 7053699996242299295639381)
            ·
              refine ⟨41330273415482222435387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7053699996242299295639381 41330273415482222435387)
              ·
                rfl

theorem cell22_3259862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 9].length) (baseStart_3259862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3259862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3259862 prefixEnd_3259862 := by exact prefixLift 3259862
  have htrace : WordTrace (prefixWord ++ tailWord_3259862) baseStart_3259862 baseEnd_3259862 := by
    simpa [prefixWord, tailWord_3259862, baseEnd_3259862] using wordTrace_append hprefix tailTrace_3259862
  have hstable : (prefixWord ++ tailWord_3259862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259862).length < 2 ^ (prefixWord ++ tailWord_3259862).sum := by decide
  have hdescent : baseEnd_3259862 < baseStart_3259862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259894 : List Nat := [5, 1, 1, 1, 2, 2, 2, 2, 3, 3]
def baseStart_3259894 : Nat := 118140960795 + 3259894 * 2 ^ 59
def prefixEnd_3259894 : Nat := 4983230072969 + 3 ^ 40 * 3259894 * 2
def baseEnd_3259894 : Nat := 1115928336471982588955351

theorem tailTrace_3259894 : CollatzResearch.WordTrace tailWord_3259894 prefixEnd_3259894 1115928336471982588955351 := by
  unfold tailWord_3259894
  simp only [CollatzResearch.WordTrace]
  refine ⟨7431131378248016150970671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79265401367978838943687157 7431131378248016150970671)
  ·
    refine ⟨11146697067372024226456007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7431131378248016150970671 11146697067372024226456007)
    ·
      refine ⟨16720045601058036339684011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11146697067372024226456007 16720045601058036339684011)
      ·
        refine ⟨25080068401587054509526017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16720045601058036339684011 25080068401587054509526017)
        ·
          refine ⟨18810051301190290882144513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25080068401587054509526017 18810051301190290882144513)
          ·
            refine ⟨14107538475892718161608385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18810051301190290882144513 14107538475892718161608385)
            ·
              refine ⟨10580653856919538621206289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14107538475892718161608385 10580653856919538621206289)
              ·
                refine ⟨7935490392689653965904717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10580653856919538621206289 7935490392689653965904717)
                ·
                  refine ⟨2975808897258620237214269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7935490392689653965904717 2975808897258620237214269)
                  ·
                    refine ⟨1115928336471982588955351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2975808897258620237214269 1115928336471982588955351)
                    ·
                      rfl

theorem cell22_3259894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_3259894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3259894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3259894 prefixEnd_3259894 := by exact prefixLift 3259894
  have htrace : WordTrace (prefixWord ++ tailWord_3259894) baseStart_3259894 baseEnd_3259894 := by
    simpa [prefixWord, tailWord_3259894, baseEnd_3259894] using wordTrace_append hprefix tailTrace_3259894
  have hstable : (prefixWord ++ tailWord_3259894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259894).length < 2 ^ (prefixWord ++ tailWord_3259894).sum := by decide
  have hdescent : baseEnd_3259894 < baseStart_3259894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259911 : List Nat := [1, 1, 4, 3, 2, 1, 3, 3, 1, 3]
def baseStart_3259911 : Nat := 118140960795 + 3259911 * 2 ^ 59
def prefixEnd_3259911 : Nat := 4983230072969 + 3 ^ 40 * 3259911 * 2
def baseEnd_3259911 : Nat := 1115934155919400211280299

theorem tailTrace_3259911 : CollatzResearch.WordTrace tailWord_3259911 prefixEnd_3259911 1115934155919400211280299 := by
  unfold tailWord_3259911
  simp only [CollatzResearch.WordTrace]
  refine ⟨118898722092906670318899587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79265814728604446879266391 118898722092906670318899587)
  ·
    refine ⟨178348083139360005478349381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118898722092906670318899587 178348083139360005478349381)
    ·
      refine ⟨33440265588630001027190509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178348083139360005478349381 33440265588630001027190509)
      ·
        refine ⟨12540099595736250385196441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33440265588630001027190509 12540099595736250385196441)
        ·
          refine ⟨9405074696802187788897331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12540099595736250385196441 9405074696802187788897331)
          ·
            refine ⟨14107612045203281683345997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9405074696802187788897331 14107612045203281683345997)
            ·
              refine ⟨5290354516951230631254749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14107612045203281683345997 5290354516951230631254749)
              ·
                refine ⟨1983882943856711486720531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5290354516951230631254749 1983882943856711486720531)
                ·
                  refine ⟨2975824415785067230080797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1983882943856711486720531 2975824415785067230080797)
                  ·
                    refine ⟨1115934155919400211280299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2975824415785067230080797 1115934155919400211280299)
                    ·
                      rfl

theorem cell22_3259911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 3, 1, 3].length) (baseStart_3259911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3259911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3259911 prefixEnd_3259911 := by exact prefixLift 3259911
  have htrace : WordTrace (prefixWord ++ tailWord_3259911) baseStart_3259911 baseEnd_3259911 := by
    simpa [prefixWord, tailWord_3259911, baseEnd_3259911] using wordTrace_append hprefix tailTrace_3259911
  have hstable : (prefixWord ++ tailWord_3259911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259911).length < 2 ^ (prefixWord ++ tailWord_3259911).sum := by decide
  have hdescent : baseEnd_3259911 < baseStart_3259911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259928 : List Nat := [2, 1, 2, 3, 4, 1, 3, 2, 1, 3]
def baseStart_3259928 : Nat := 118140960795 + 3259928 * 2 ^ 59
def prefixEnd_3259928 : Nat := 4983230072969 + 3 ^ 40 * 3259928 * 2
def baseEnd_3259928 : Nat := 1115939975366817833605247

theorem tailTrace_3259928 : CollatzResearch.WordTrace tailWord_3259928 prefixEnd_3259928 1115939975366817833605247 := by
  unfold tailWord_3259928
  simp only [CollatzResearch.WordTrace]
  refine ⟨59449671066922541111134219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79266228089230054814845625 59449671066922541111134219)
  ·
    refine ⟨89174506600383811666701329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59449671066922541111134219 89174506600383811666701329)
    ·
      refine ⟨66880879950287858750025997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89174506600383811666701329 66880879950287858750025997)
      ·
        refine ⟨25080329981357947031259749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66880879950287858750025997 25080329981357947031259749)
        ·
          refine ⟨4702561871504615068361203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25080329981357947031259749 4702561871504615068361203)
          ·
            refine ⟨7053842807256922602541805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4702561871504615068361203 7053842807256922602541805)
            ·
              refine ⟨2645191052721345975953177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7053842807256922602541805 2645191052721345975953177)
              ·
                refine ⟨1983893289541009481964883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2645191052721345975953177 1983893289541009481964883)
                ·
                  refine ⟨2975839934311514222947325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1983893289541009481964883 2975839934311514222947325)
                  ·
                    refine ⟨1115939975366817833605247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2975839934311514222947325 1115939975366817833605247)
                    ·
                      rfl

theorem cell22_3259928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 2, 1, 3].length) (baseStart_3259928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3259928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3259928 prefixEnd_3259928 := by exact prefixLift 3259928
  have htrace : WordTrace (prefixWord ++ tailWord_3259928) baseStart_3259928 baseEnd_3259928 := by
    simpa [prefixWord, tailWord_3259928, baseEnd_3259928] using wordTrace_append hprefix tailTrace_3259928
  have hstable : (prefixWord ++ tailWord_3259928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259928).length < 2 ^ (prefixWord ++ tailWord_3259928).sum := by decide
  have hdescent : baseEnd_3259928 < baseStart_3259928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259934 : List Nat := [4, 3, 3, 1, 2, 1, 2, 1, 2, 3]
def baseStart_3259934 : Nat := 118140960795 + 3259934 * 2 ^ 59
def prefixEnd_3259934 : Nat := 4983230072969 + 3 ^ 40 * 3259934 * 2
def baseEnd_3259934 : Nat := 1115942029289435817955229

theorem tailTrace_3259934 : CollatzResearch.WordTrace tailWord_3259934 prefixEnd_3259934 1115942029289435817955229 := by
  unfold tailWord_3259934
  simp only [CollatzResearch.WordTrace]
  refine ⟨14862445121477918155873357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79266373981215563497991237 14862445121477918155873357)
  ·
    refine ⟨5573416920554219308452509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14862445121477918155873357 5573416920554219308452509)
    ·
      refine ⟨2090031345207832240669691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5573416920554219308452509 2090031345207832240669691)
      ·
        refine ⟨3135047017811748361004537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2090031345207832240669691 3135047017811748361004537)
        ·
          refine ⟨2351285263358811270753403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3135047017811748361004537 2351285263358811270753403)
          ·
            refine ⟨3526927895038216906130105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2351285263358811270753403 3526927895038216906130105)
            ·
              refine ⟨2645195921278662679597579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3526927895038216906130105 2645195921278662679597579)
              ·
                refine ⟨3967793881917994019396369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2645195921278662679597579 3967793881917994019396369)
                ·
                  refine ⟨2975845411438495514547277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3967793881917994019396369 2975845411438495514547277)
                  ·
                    refine ⟨1115942029289435817955229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2975845411438495514547277 1115942029289435817955229)
                    ·
                      rfl

theorem cell22_3259934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_3259934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3259934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3259934 prefixEnd_3259934 := by exact prefixLift 3259934
  have htrace : WordTrace (prefixWord ++ tailWord_3259934) baseStart_3259934 baseEnd_3259934 := by
    simpa [prefixWord, tailWord_3259934, baseEnd_3259934] using wordTrace_append hprefix tailTrace_3259934
  have hstable : (prefixWord ++ tailWord_3259934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259934).length < 2 ^ (prefixWord ++ tailWord_3259934).sum := by decide
  have hdescent : baseEnd_3259934 < baseStart_3259934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259967 : List Nat := [1, 1, 2, 2, 3, 4, 1, 2, 1, 5]
def baseStart_3259967 : Nat := 118140960795 + 3259967 * 2 ^ 59
def prefixEnd_3259967 : Nat := 4983230072969 + 3 ^ 40 * 3259967 * 2
def baseEnd_3259967 : Nat := 1115953325863834731880127

theorem tailTrace_3259967 : CollatzResearch.WordTrace tailWord_3259967 prefixEnd_3259967 1115953325863834731880127 := by
  unfold tailWord_3259967
  simp only [CollatzResearch.WordTrace]
  refine ⟨118900764580703791882938155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79267176387135861255292103 118900764580703791882938155)
  ·
    refine ⟨178351146871055687824407233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118900764580703791882938155 178351146871055687824407233)
    ·
      refine ⟨133763360153291765868305425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178351146871055687824407233 133763360153291765868305425)
      ·
        refine ⟨100322520114968824401229069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133763360153291765868305425 100322520114968824401229069)
        ·
          refine ⟨37620945043113309150460901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100322520114968824401229069 37620945043113309150460901)
          ·
            refine ⟨7053927195583745465711419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37620945043113309150460901 7053927195583745465711419)
            ·
              refine ⟨10580890793375618198567129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7053927195583745465711419 10580890793375618198567129)
              ·
                refine ⟨7935668095031713648925347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10580890793375618198567129 7935668095031713648925347)
                ·
                  refine ⟨11903502142547570473388021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7935668095031713648925347 11903502142547570473388021)
                  ·
                    refine ⟨1115953325863834731880127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11903502142547570473388021 1115953325863834731880127)
                    ·
                      rfl

theorem cell22_3259967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 5].length) (baseStart_3259967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3259967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3259967 prefixEnd_3259967 := by exact prefixLift 3259967
  have htrace : WordTrace (prefixWord ++ tailWord_3259967) baseStart_3259967 baseEnd_3259967 := by
    simpa [prefixWord, tailWord_3259967, baseEnd_3259967] using wordTrace_append hprefix tailTrace_3259967
  have hstable : (prefixWord ++ tailWord_3259967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259967).length < 2 ^ (prefixWord ++ tailWord_3259967).sum := by decide
  have hdescent : baseEnd_3259967 < baseStart_3259967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259969 : List Nat := [1, 2, 5, 1, 1, 1, 2, 5, 4]
def baseStart_3259969 : Nat := 118140960795 + 3259969 * 2 ^ 59
def prefixEnd_3259969 : Nat := 4983230072969 + 3 ^ 40 * 3259969 * 2
def baseEnd_3259969 : Nat := 371984670168235797776707

theorem tailTrace_3259969 : CollatzResearch.WordTrace tailWord_3259969 prefixEnd_3259969 371984670168235797776707 := by
  unfold tailWord_3259969
  simp only [CollatzResearch.WordTrace]
  refine ⟨118900837526696546224510961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79267225017797697483007307 118900837526696546224510961)
  ·
    refine ⟨89175628145022409668383221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118900837526696546224510961 89175628145022409668383221)
    ·
      refine ⟨8360215138595850906410927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89175628145022409668383221 8360215138595850906410927)
      ·
        refine ⟨12540322707893776359616391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8360215138595850906410927 12540322707893776359616391)
        ·
          refine ⟨18810484061840664539424587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12540322707893776359616391 18810484061840664539424587)
          ·
            refine ⟨28215726092760996809136881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18810484061840664539424587 28215726092760996809136881)
            ·
              refine ⟨21161794569570747606852661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28215726092760996809136881 21161794569570747606852661)
              ·
                refine ⟨1983918240897257588142437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21161794569570747606852661 1983918240897257588142437)
                ·
                  refine ⟨371984670168235797776707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1983918240897257588142437 371984670168235797776707)
                  ·
                    rfl

theorem cell22_3259969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 5, 4].length) (baseStart_3259969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3259969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3259969 prefixEnd_3259969 := by exact prefixLift 3259969
  have htrace : WordTrace (prefixWord ++ tailWord_3259969) baseStart_3259969 baseEnd_3259969 := by
    simpa [prefixWord, tailWord_3259969, baseEnd_3259969] using wordTrace_append hprefix tailTrace_3259969
  have hstable : (prefixWord ++ tailWord_3259969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259969).length < 2 ^ (prefixWord ++ tailWord_3259969).sum := by decide
  have hdescent : baseEnd_3259969 < baseStart_3259969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259980 : List Nat := [2, 2, 1, 3, 1, 13]
def baseStart_3259980 : Nat := 118140960795 + 3259980 * 2 ^ 59
def prefixEnd_3259980 : Nat := 4983230072969 + 3 ^ 40 * 3259980 * 2
def baseEnd_3259980 : Nat := 13777256494191444830927

theorem tailTrace_3259980 : CollatzResearch.WordTrace tailWord_3259980 prefixEnd_3259980 13777256494191444830927 := by
  unfold tailWord_3259980
  simp only [CollatzResearch.WordTrace]
  refine ⟨59450619364828347551580697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79267492486437796735440929 59450619364828347551580697)
  ·
    refine ⟨44587964523621260663685523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59450619364828347551580697 44587964523621260663685523)
    ·
      refine ⟨66881946785431890995528285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44587964523621260663685523 66881946785431890995528285)
      ·
        refine ⟨25080730044536959123323107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66881946785431890995528285 25080730044536959123323107)
        ·
          refine ⟨37621095066805438684984661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25080730044536959123323107 37621095066805438684984661)
          ·
            refine ⟨13777256494191444830927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 37621095066805438684984661 13777256494191444830927)
            ·
              rfl

theorem cell22_3259980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 13].length) (baseStart_3259980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3259980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3259980 prefixEnd_3259980 := by exact prefixLift 3259980
  have htrace : WordTrace (prefixWord ++ tailWord_3259980) baseStart_3259980 baseEnd_3259980 := by
    simpa [prefixWord, tailWord_3259980, baseEnd_3259980] using wordTrace_append hprefix tailTrace_3259980
  have hstable : (prefixWord ++ tailWord_3259980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259980).length < 2 ^ (prefixWord ++ tailWord_3259980).sum := by decide
  have hdescent : baseEnd_3259980 < baseStart_3259980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259984 : List Nat := [2, 1, 1, 1, 1, 3, 6, 2, 2, 3]
def baseStart_3259984 : Nat := 118140960795 + 3259984 * 2 ^ 59
def prefixEnd_3259984 : Nat := 4983230072969 + 3 ^ 40 * 3259984 * 2
def baseEnd_3259984 : Nat := 1115959145311252354205075

theorem tailTrace_3259984 : CollatzResearch.WordTrace tailWord_3259984 prefixEnd_3259984 1115959145311252354205075 := by
  unfold tailWord_3259984
  simp only [CollatzResearch.WordTrace]
  refine ⟨59450692310821101893153503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79267589747761469190871337 59450692310821101893153503)
  ·
    refine ⟨89176038466231652839730255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59450692310821101893153503 89176038466231652839730255)
    ·
      refine ⟨133764057699347479259595383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89176038466231652839730255 133764057699347479259595383)
      ·
        refine ⟨200646086549021218889393075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133764057699347479259595383 200646086549021218889393075)
        ·
          refine ⟨300969129823531828334089613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200646086549021218889393075 300969129823531828334089613)
          ·
            refine ⟨112863423683824435625283605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 300969129823531828334089613 112863423683824435625283605)
            ·
              refine ⟨5290472985179270419935169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 112863423683824435625283605 5290472985179270419935169)
              ·
                refine ⟨3967854738884452814951377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5290472985179270419935169 3967854738884452814951377)
                ·
                  refine ⟨2975891054163339611213533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3967854738884452814951377 2975891054163339611213533)
                  ·
                    refine ⟨1115959145311252354205075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2975891054163339611213533 1115959145311252354205075)
                    ·
                      rfl

theorem cell22_3259984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 2, 3].length) (baseStart_3259984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3259984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3259984 prefixEnd_3259984 := by exact prefixLift 3259984
  have htrace : WordTrace (prefixWord ++ tailWord_3259984) baseStart_3259984 baseEnd_3259984 := by
    simpa [prefixWord, tailWord_3259984, baseEnd_3259984] using wordTrace_append hprefix tailTrace_3259984
  have hstable : (prefixWord ++ tailWord_3259984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259984).length < 2 ^ (prefixWord ++ tailWord_3259984).sum := by decide
  have hdescent : baseEnd_3259984 < baseStart_3259984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259986 : List Nat := [3, 2, 2, 1, 2, 2, 4, 2, 4]
def baseStart_3259986 : Nat := 118140960795 + 3259986 * 2 ^ 59
def prefixEnd_3259986 : Nat := 4983230072969 + 3 ^ 40 * 3259986 * 2
def baseEnd_3259986 : Nat := 371986609984041671885023

theorem tailTrace_3259986 : CollatzResearch.WordTrace tailWord_3259986 prefixEnd_3259986 371986609984041671885023 := by
  unfold tailWord_3259986
  simp only [CollatzResearch.WordTrace]
  refine ⟨29725364391908739531969953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79267638378423305418586541 29725364391908739531969953)
  ·
    refine ⟨22294023293931554648977465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29725364391908739531969953 22294023293931554648977465)
    ·
      refine ⟨16720517470448665986733099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22294023293931554648977465 16720517470448665986733099)
      ·
        refine ⟨25080776205672998980099649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16720517470448665986733099 25080776205672998980099649)
        ·
          refine ⟨18810582154254749235074737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25080776205672998980099649 18810582154254749235074737)
          ·
            refine ⟨14107936615691061926306053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18810582154254749235074737 14107936615691061926306053)
            ·
              refine ⟨2645238115442074111182385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14107936615691061926306053 2645238115442074111182385)
              ·
                refine ⟨1983928586581555583386789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2645238115442074111182385 1983928586581555583386789)
                ·
                  refine ⟨371986609984041671885023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1983928586581555583386789 371986609984041671885023)
                  ·
                    rfl

theorem cell22_3259986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 2, 4].length) (baseStart_3259986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3259986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3259986 prefixEnd_3259986 := by exact prefixLift 3259986
  have htrace : WordTrace (prefixWord ++ tailWord_3259986) baseStart_3259986 baseEnd_3259986 := by
    simpa [prefixWord, tailWord_3259986, baseEnd_3259986] using wordTrace_append hprefix tailTrace_3259986
  have hstable : (prefixWord ++ tailWord_3259986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259986).length < 2 ^ (prefixWord ++ tailWord_3259986).sum := by decide
  have hdescent : baseEnd_3259986 < baseStart_3259986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260046 : List Nat := [4, 1, 1, 3, 1, 3, 2, 1, 3, 3]
def baseStart_3260046 : Nat := 118140960795 + 3260046 * 2 ^ 59
def prefixEnd_3260046 : Nat := 4983230072969 + 3 ^ 40 * 3260046 * 2
def baseEnd_3260046 : Nat := 1115980369178304859154885

theorem tailTrace_3260046 : CollatzResearch.WordTrace tailWord_3260046 prefixEnd_3260046 1115980369178304859154885 := by
  unfold tailWord_3260046
  simp only [CollatzResearch.WordTrace]
  refine ⟨14862955743427198546882999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79269097298278392250042661 14862955743427198546882999)
  ·
    refine ⟨22294433615140797820324499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14862955743427198546882999 22294433615140797820324499)
    ·
      refine ⟨33441650422711196730486749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22294433615140797820324499 33441650422711196730486749)
      ·
        refine ⟨12540618908516698773932531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33441650422711196730486749 12540618908516698773932531)
        ·
          refine ⟨18810928362775048160898797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12540618908516698773932531 18810928362775048160898797)
          ·
            refine ⟨7054098136040643060337049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18810928362775048160898797 7054098136040643060337049)
            ·
              refine ⟨5290573602030482295252787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7054098136040643060337049 5290573602030482295252787)
              ·
                refine ⟨7935860403045723442879181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5290573602030482295252787 7935860403045723442879181)
                ·
                  refine ⟨2975947651142146291079693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7935860403045723442879181 2975947651142146291079693)
                  ·
                    refine ⟨1115980369178304859154885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2975947651142146291079693 1115980369178304859154885)
                    ·
                      rfl

theorem cell22_3260046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 3, 3].length) (baseStart_3260046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3260046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3260046 prefixEnd_3260046 := by exact prefixLift 3260046
  have htrace : WordTrace (prefixWord ++ tailWord_3260046) baseStart_3260046 baseEnd_3260046 := by
    simpa [prefixWord, tailWord_3260046, baseEnd_3260046] using wordTrace_append hprefix tailTrace_3260046
  have hstable : (prefixWord ++ tailWord_3260046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260046).length < 2 ^ (prefixWord ++ tailWord_3260046).sum := by decide
  have hdescent : baseEnd_3260046 < baseStart_3260046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260089 : List Nat := [1, 2, 1, 4, 1, 1, 4, 3, 1, 4]
def baseStart_3260089 : Nat := 118140960795 + 3260089 * 2 ^ 59
def prefixEnd_3260089 : Nat := 4983230072969 + 3 ^ 40 * 3260089 * 2
def baseEnd_3260089 : Nat := 1115995088957067080329753

theorem tailTrace_3260089 : CollatzResearch.WordTrace tailWord_3260089 prefixEnd_3260089 1115995088957067080329753 := by
  unfold tailWord_3260089
  simp only [CollatzResearch.WordTrace]
  refine ⟨118905214286261806718879321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79270142857507871145919547 118905214286261806718879321)
  ·
    refine ⟨89178910714696355039159491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118905214286261806718879321 89178910714696355039159491)
    ·
      refine ⟨133768366072044532558739237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89178910714696355039159491 133768366072044532558739237)
      ·
        refine ⟨25081568638508349854763607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133768366072044532558739237 25081568638508349854763607)
        ·
          refine ⟨37622352957762524782145411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25081568638508349854763607 37622352957762524782145411)
          ·
            refine ⟨56433529436643787173218117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37622352957762524782145411 56433529436643787173218117)
            ·
              refine ⟨10581286769370710094978397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56433529436643787173218117 10581286769370710094978397)
              ·
                refine ⟨3967982538514016285616899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10581286769370710094978397 3967982538514016285616899)
                ·
                  refine ⟨5951973807771024428425349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3967982538514016285616899 5951973807771024428425349)
                  ·
                    refine ⟨1115995088957067080329753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5951973807771024428425349 1115995088957067080329753)
                    ·
                      rfl

theorem cell22_3260089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 4].length) (baseStart_3260089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3260089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3260089 prefixEnd_3260089 := by exact prefixLift 3260089
  have htrace : WordTrace (prefixWord ++ tailWord_3260089) baseStart_3260089 baseEnd_3260089 := by
    simpa [prefixWord, tailWord_3260089, baseEnd_3260089] using wordTrace_append hprefix tailTrace_3260089
  have hstable : (prefixWord ++ tailWord_3260089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260089).length < 2 ^ (prefixWord ++ tailWord_3260089).sum := by decide
  have hdescent : baseEnd_3260089 < baseStart_3260089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260132 : List Nat := [2, 3, 1, 1, 1, 3, 1, 10]
def baseStart_3260132 : Nat := 118140960795 + 3260132 * 2 ^ 59
def prefixEnd_3260132 : Nat := 4983230072969 + 3 ^ 40 * 3260132 * 2
def baseEnd_3260132 : Nat := 124001089859536589056069

theorem tailTrace_3260132 : CollatzResearch.WordTrace tailWord_3260132 prefixEnd_3260132 124001089859536589056069 := by
  unfold tailWord_3260132
  simp only [CollatzResearch.WordTrace]
  refine ⟨59453391312553012531347325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79271188416737350041796433 59453391312553012531347325)
  ·
    refine ⟨22295021742207379699255247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59453391312553012531347325 22295021742207379699255247)
    ·
      refine ⟨33442532613311069548882871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22295021742207379699255247 33442532613311069548882871)
      ·
        refine ⟨50163798919966604323324307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33442532613311069548882871 50163798919966604323324307)
        ·
          refine ⟨75245698379949906484986461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50163798919966604323324307 75245698379949906484986461)
          ·
            refine ⟨28217136892481214931869923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75245698379949906484986461 28217136892481214931869923)
            ·
              refine ⟨42325705338721822397804885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28217136892481214931869923 42325705338721822397804885)
              ·
                refine ⟨124001089859536589056069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 42325705338721822397804885 124001089859536589056069)
                ·
                  rfl

theorem cell22_3260132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 10].length) (baseStart_3260132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3260132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3260132 prefixEnd_3260132 := by exact prefixLift 3260132
  have htrace : WordTrace (prefixWord ++ tailWord_3260132) baseStart_3260132 baseEnd_3260132 := by
    simpa [prefixWord, tailWord_3260132, baseEnd_3260132] using wordTrace_append hprefix tailTrace_3260132
  have hstable : (prefixWord ++ tailWord_3260132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260132).length < 2 ^ (prefixWord ++ tailWord_3260132).sum := by decide
  have hdescent : baseEnd_3260132 < baseStart_3260132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260149 : List Nat := [1, 3, 6, 12]
def baseStart_3260149 : Nat := 118140960795 + 3260149 * 2 ^ 59
def prefixEnd_3260149 : Nat := 4983230072969 + 3 ^ 40 * 3260149 * 2
def baseEnd_3260149 : Nat := 1530885635367965601961

theorem tailTrace_3260149 : CollatzResearch.WordTrace tailWord_3260149 prefixEnd_3260149 1530885635367965601961 := by
  unfold tailWord_3260149
  simp only [CollatzResearch.WordTrace]
  refine ⟨118907402666044436966063501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79271601777362957977375667 118907402666044436966063501)
  ·
    refine ⟨44590275999766663862273813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118907402666044436966063501 44590275999766663862273813)
    ·
      refine ⟨2090169187489062368544085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44590275999766663862273813 2090169187489062368544085)
      ·
        refine ⟨1530885635367965601961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 2090169187489062368544085 1530885635367965601961)
        ·
          rfl

theorem cell22_3260149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 12].length) (baseStart_3260149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3260149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3260149 prefixEnd_3260149 := by exact prefixLift 3260149
  have htrace : WordTrace (prefixWord ++ tailWord_3260149) baseStart_3260149 baseEnd_3260149 := by
    simpa [prefixWord, tailWord_3260149, baseEnd_3260149] using wordTrace_append hprefix tailTrace_3260149
  have hstable : (prefixWord ++ tailWord_3260149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260149).length < 2 ^ (prefixWord ++ tailWord_3260149).sum := by decide
  have hdescent : baseEnd_3260149 < baseStart_3260149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260177 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 9]
def baseStart_3260177 : Nat := 118140960795 + 3260177 * 2 ^ 59
def prefixEnd_3260177 : Nat := 4983230072969 + 3 ^ 40 * 3260177 * 2
def baseEnd_3260177 : Nat := 372008404385154728043161

theorem tailTrace_3260177 : CollatzResearch.WordTrace tailWord_3260177 prefixEnd_3260177 372008404385154728043161 := by
  unfold tailWord_3260177
  simp only [CollatzResearch.WordTrace]
  refine ⟨118908423909942997748082785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79272282606628665165388523 118908423909942997748082785)
  ·
    refine ⟨89181317932457248311062089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118908423909942997748082785 89181317932457248311062089)
    ·
      refine ⟨66885988449342936233296567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89181317932457248311062089 66885988449342936233296567)
      ·
        refine ⟨100328982674014404349944851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66885988449342936233296567 100328982674014404349944851)
        ·
          refine ⟨150493474011021606524917277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100328982674014404349944851 150493474011021606524917277)
          ·
            refine ⟨56435052754133102446843979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150493474011021606524917277 56435052754133102446843979)
            ·
              refine ⟨84652579131199653670265969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56435052754133102446843979 84652579131199653670265969)
              ·
                refine ⟨63489434348399740252699477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84652579131199653670265969 63489434348399740252699477)
                ·
                  refine ⟨372008404385154728043161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 63489434348399740252699477 372008404385154728043161)
                  ·
                    rfl

theorem cell22_3260177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 9].length) (baseStart_3260177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3260177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3260177 prefixEnd_3260177 := by exact prefixLift 3260177
  have htrace : WordTrace (prefixWord ++ tailWord_3260177) baseStart_3260177 baseEnd_3260177 := by
    simpa [prefixWord, tailWord_3260177, baseEnd_3260177] using wordTrace_append hprefix tailTrace_3260177
  have hstable : (prefixWord ++ tailWord_3260177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260177).length < 2 ^ (prefixWord ++ tailWord_3260177).sum := by decide
  have hdescent : baseEnd_3260177 < baseStart_3260177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260181 : List Nat := [1, 3, 2, 1, 2, 4, 1, 2, 3, 3]
def baseStart_3260181 : Nat := 118140960795 + 3260181 * 2 ^ 59
def prefixEnd_3260181 : Nat := 4983230072969 + 3 ^ 40 * 3260181 * 2
def baseEnd_3260181 : Nat := 1116026582437209507029471

theorem tailTrace_3260181 : CollatzResearch.WordTrace tailWord_3260181 prefixEnd_3260181 1116026582437209507029471 := by
  unfold tailWord_3260181
  simp only [CollatzResearch.WordTrace]
  refine ⟨118908569801928506431228397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79272379867952337620818931 118908569801928506431228397)
  ·
    refine ⟨44590713675723189911710649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118908569801928506431228397 44590713675723189911710649)
    ·
      refine ⟨33443035256792392433782987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44590713675723189911710649 33443035256792392433782987)
      ·
        refine ⟨50164552885188588650674481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33443035256792392433782987 50164552885188588650674481)
        ·
          refine ⟨37623414663891441488005861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50164552885188588650674481 37623414663891441488005861)
          ·
            refine ⟨7054390249479645279001099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37623414663891441488005861 7054390249479645279001099)
            ·
              refine ⟨10581585374219467918501649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7054390249479645279001099 10581585374219467918501649)
              ·
                refine ⟨7936189030664600938876237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10581585374219467918501649 7936189030664600938876237)
                ·
                  refine ⟨2976070886499225352078589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7936189030664600938876237 2976070886499225352078589)
                  ·
                    refine ⟨1116026582437209507029471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2976070886499225352078589 1116026582437209507029471)
                    ·
                      rfl

theorem cell22_3260181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 3, 3].length) (baseStart_3260181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3260181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3260181 prefixEnd_3260181 := by exact prefixLift 3260181
  have htrace : WordTrace (prefixWord ++ tailWord_3260181) baseStart_3260181 baseEnd_3260181 := by
    simpa [prefixWord, tailWord_3260181, baseEnd_3260181] using wordTrace_append hprefix tailTrace_3260181
  have hstable : (prefixWord ++ tailWord_3260181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260181).length < 2 ^ (prefixWord ++ tailWord_3260181).sum := by decide
  have hdescent : baseEnd_3260181 < baseStart_3260181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260194 : List Nat := [3, 3, 1, 1, 2, 1, 2, 2, 7]
def baseStart_3260194 : Nat := 118140960795 + 3260194 * 2 ^ 59
def prefixEnd_3260194 : Nat := 4983230072969 + 3 ^ 40 * 3260194 * 2
def baseEnd_3260194 : Nat := 372010344200960602151477

theorem tailTrace_3260194 : CollatzResearch.WordTrace tailWord_3260194 prefixEnd_3260194 372010344200960602151477 := by
  unfold tailWord_3260194
  simp only [CollatzResearch.WordTrace]
  refine ⟨29727260987720352412862909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79272695967254273100967757 29727260987720352412862909)
  ·
    refine ⟨11147722870395132154823591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29727260987720352412862909 11147722870395132154823591)
    ·
      refine ⟨16721584305592698232235387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11147722870395132154823591 16721584305592698232235387)
      ·
        refine ⟨25082376458389047348353081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16721584305592698232235387 25082376458389047348353081)
        ·
          refine ⟨18811782343791785511264811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25082376458389047348353081 18811782343791785511264811)
          ·
            refine ⟨28217673515687678266897217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18811782343791785511264811 28217673515687678266897217)
            ·
              refine ⟨21163255136765758700172913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28217673515687678266897217 21163255136765758700172913)
              ·
                refine ⟨15872441352574319025129685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21163255136765758700172913 15872441352574319025129685)
                ·
                  refine ⟨372010344200960602151477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15872441352574319025129685 372010344200960602151477)
                  ·
                    rfl

theorem cell22_3260194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_3260194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3260194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3260194 prefixEnd_3260194 := by exact prefixLift 3260194
  have htrace : WordTrace (prefixWord ++ tailWord_3260194) baseStart_3260194 baseEnd_3260194 := by
    simpa [prefixWord, tailWord_3260194, baseEnd_3260194] using wordTrace_append hprefix tailTrace_3260194
  have hstable : (prefixWord ++ tailWord_3260194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260194).length < 2 ^ (prefixWord ++ tailWord_3260194).sum := by decide
  have hdescent : baseEnd_3260194 < baseStart_3260194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260209 : List Nat := [1, 2, 2, 3, 2, 2, 1, 2, 2, 5]
def baseStart_3260209 : Nat := 118140960795 + 3260209 * 2 ^ 59
def prefixEnd_3260209 : Nat := 4983230072969 + 3 ^ 40 * 3260209 * 2
def baseEnd_3260209 : Nat := 1116036167409426767329385

theorem tailTrace_3260209 : CollatzResearch.WordTrace tailWord_3260209 prefixEnd_3260209 1116036167409426767329385 := by
  unfold tailWord_3260209
  simp only [CollatzResearch.WordTrace]
  refine ⟨118909591045827067213247681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79273060697218044808831787 118909591045827067213247681)
  ·
    refine ⟨89182193284370300409935761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118909591045827067213247681 89182193284370300409935761)
    ·
      refine ⟨66886644963277725307451821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89182193284370300409935761 66886644963277725307451821)
      ·
        refine ⟨25082491861229146990294433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66886644963277725307451821 25082491861229146990294433)
        ·
          refine ⟨18811868895921860242720825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25082491861229146990294433 18811868895921860242720825)
          ·
            refine ⟨14108901671941395182040619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18811868895921860242720825 14108901671941395182040619)
            ·
              refine ⟨21163352507912092773060929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14108901671941395182040619 21163352507912092773060929)
              ·
                refine ⟨15872514380934069579795697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21163352507912092773060929 15872514380934069579795697)
                ·
                  refine ⟨11904385785700552184846773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15872514380934069579795697 11904385785700552184846773)
                  ·
                    refine ⟨1116036167409426767329385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11904385785700552184846773 1116036167409426767329385)
                    ·
                      rfl

theorem cell22_3260209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_3260209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3260209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3260209 prefixEnd_3260209 := by exact prefixLift 3260209
  have htrace : WordTrace (prefixWord ++ tailWord_3260209) baseStart_3260209 baseEnd_3260209 := by
    simpa [prefixWord, tailWord_3260209, baseEnd_3260209] using wordTrace_append hprefix tailTrace_3260209
  have hstable : (prefixWord ++ tailWord_3260209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260209).length < 2 ^ (prefixWord ++ tailWord_3260209).sum := by decide
  have hdescent : baseEnd_3260209 < baseStart_3260209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260241 : List Nat := [1, 2, 2, 1, 5, 1, 1, 4, 1, 4]
def baseStart_3260241 : Nat := 118140960795 + 3260241 * 2 ^ 59
def prefixEnd_3260241 : Nat := 4983230072969 + 3 ^ 40 * 3260241 * 2
def baseEnd_3260241 : Nat := 1116047121663389350529287

theorem tailTrace_3260241 : CollatzResearch.WordTrace tailWord_3260241 prefixEnd_3260241 1116047121663389350529287 := by
  unfold tailWord_3260241
  simp only [CollatzResearch.WordTrace]
  refine ⟨118910758181711136678412577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79273838787807424452275051 118910758181711136678412577)
  ·
    refine ⟨89183068636283352508809433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118910758181711136678412577 89183068636283352508809433)
    ·
      refine ⟨66887301477212514381607075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89183068636283352508809433 66887301477212514381607075)
      ·
        refine ⟨100330952215818771572410613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66887301477212514381607075 100330952215818771572410613)
        ·
          refine ⟨9406026770233009834913495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 100330952215818771572410613 9406026770233009834913495)
          ·
            refine ⟨14109040155349514752370243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9406026770233009834913495 14109040155349514752370243)
            ·
              refine ⟨21163560233024272128555365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14109040155349514752370243 21163560233024272128555365)
              ·
                refine ⟨3968167543692051024104131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21163560233024272128555365 3968167543692051024104131)
                ·
                  refine ⟨5952251315538076536156197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3968167543692051024104131 5952251315538076536156197)
                  ·
                    refine ⟨1116047121663389350529287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5952251315538076536156197 1116047121663389350529287)
                    ·
                      rfl

theorem cell22_3260241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 4].length) (baseStart_3260241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3260241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3260241 prefixEnd_3260241 := by exact prefixLift 3260241
  have htrace : WordTrace (prefixWord ++ tailWord_3260241) baseStart_3260241 baseEnd_3260241 := by
    simpa [prefixWord, tailWord_3260241, baseEnd_3260241] using wordTrace_append hprefix tailTrace_3260241
  have hstable : (prefixWord ++ tailWord_3260241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260241).length < 2 ^ (prefixWord ++ tailWord_3260241).sum := by decide
  have hdescent : baseEnd_3260241 < baseStart_3260241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260258 : List Nat := [3, 3, 2, 1, 2, 1, 2, 3, 1, 4]
def baseStart_3260258 : Nat := 118140960795 + 3260258 * 2 ^ 59
def prefixEnd_3260258 : Nat := 4983230072969 + 3 ^ 40 * 3260258 * 2
def baseEnd_3260258 : Nat := 1116052941110806972854235

theorem tailTrace_3260258 : CollatzResearch.WordTrace tailWord_3260258 prefixEnd_3260258 1116052941110806972854235 := by
  unfold tailWord_3260258
  simp only [CollatzResearch.WordTrace]
  refine ⟨29727844555662387145445357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79274252148433032387854285 29727844555662387145445357)
  ·
    refine ⟨11147941708373395179542009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29727844555662387145445357 11147941708373395179542009)
    ·
      refine ⟨8360956281280046384656507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11147941708373395179542009 8360956281280046384656507)
      ·
        refine ⟨12541434421920069576984761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8360956281280046384656507 12541434421920069576984761)
        ·
          refine ⟨9406075816440052182738571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12541434421920069576984761 9406075816440052182738571)
          ·
            refine ⟨14109113724660078274107857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9406075816440052182738571 14109113724660078274107857)
            ·
              refine ⟨10581835293495058705580893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14109113724660078274107857 10581835293495058705580893)
              ·
                refine ⟨3968188235060647014592835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10581835293495058705580893 3968188235060647014592835)
                ·
                  refine ⟨5952282352590970521889253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3968188235060647014592835 5952282352590970521889253)
                  ·
                    refine ⟨1116052941110806972854235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5952282352590970521889253 1116052941110806972854235)
                    ·
                      rfl

theorem cell22_3260258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_3260258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3260258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3260258 prefixEnd_3260258 := by exact prefixLift 3260258
  have htrace : WordTrace (prefixWord ++ tailWord_3260258) baseStart_3260258 baseEnd_3260258 := by
    simpa [prefixWord, tailWord_3260258, baseEnd_3260258] using wordTrace_append hprefix tailTrace_3260258
  have hstable : (prefixWord ++ tailWord_3260258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260258).length < 2 ^ (prefixWord ++ tailWord_3260258).sum := by decide
  have hdescent : baseEnd_3260258 < baseStart_3260258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260273 : List Nat := [1, 2, 2, 2, 1, 3, 5, 2, 4]
def baseStart_3260273 : Nat := 118140960795 + 3260273 * 2 ^ 59
def prefixEnd_3260273 : Nat := 4983230072969 + 3 ^ 40 * 3260273 * 2
def baseEnd_3260273 : Nat := 372019358639117311243063

theorem tailTrace_3260273 : CollatzResearch.WordTrace tailWord_3260273 prefixEnd_3260273 372019358639117311243063 := by
  unfold tailWord_3260273
  simp only [CollatzResearch.WordTrace]
  refine ⟨118911925317595206143577473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79274616878396804095718315 118911925317595206143577473)
  ·
    refine ⟨89183943988196404607683105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118911925317595206143577473 89183943988196404607683105)
    ·
      refine ⟨66887957991147303455762329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89183943988196404607683105 66887957991147303455762329)
      ·
        refine ⟨50165968493360477591821747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66887957991147303455762329 50165968493360477591821747)
        ·
          refine ⟨75248952740040716387732621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50165968493360477591821747 75248952740040716387732621)
          ·
            refine ⟨28218357277515268645399733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75248952740040716387732621 28218357277515268645399733)
            ·
              refine ⟨2645470994767056435506225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28218357277515268645399733 2645470994767056435506225)
              ·
                refine ⟨1984103246075292326629669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2645470994767056435506225 1984103246075292326629669)
                ·
                  refine ⟨372019358639117311243063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1984103246075292326629669 372019358639117311243063)
                  ·
                    rfl

theorem cell22_3260273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 2, 4].length) (baseStart_3260273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3260273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3260273 prefixEnd_3260273 := by exact prefixLift 3260273
  have htrace : WordTrace (prefixWord ++ tailWord_3260273) baseStart_3260273 baseEnd_3260273 := by
    simpa [prefixWord, tailWord_3260273, baseEnd_3260273] using wordTrace_append hprefix tailTrace_3260273
  have hstable : (prefixWord ++ tailWord_3260273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260273).length < 2 ^ (prefixWord ++ tailWord_3260273).sum := by decide
  have hdescent : baseEnd_3260273 < baseStart_3260273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260318 : List Nat := [4, 3, 1, 3, 1, 10]
def baseStart_3260318 : Nat := 118140960795 + 3260318 * 2 ^ 59
def prefixEnd_3260318 : Nat := 4983230072969 + 3 ^ 40 * 3260318 * 2
def baseEnd_3260318 : Nat := 13778684942431936004371

theorem tailTrace_3260318 : CollatzResearch.WordTrace tailWord_3260318 prefixEnd_3260318 13778684942431936004371 := by
  unfold tailWord_3260318
  simp only [CollatzResearch.WordTrace]
  refine ⟨14864195825304022353620701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79275711068288119219310405 14864195825304022353620701)
  ·
    refine ⟨5574073434489008382607763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14864195825304022353620701 5574073434489008382607763)
    ·
      refine ⟨8361110151733512573911645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5574073434489008382607763 8361110151733512573911645)
      ·
        refine ⟨3135416306900067215216867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8361110151733512573911645 3135416306900067215216867)
        ·
          refine ⟨4703124460350100822825301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3135416306900067215216867 4703124460350100822825301)
          ·
            refine ⟨13778684942431936004371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4703124460350100822825301 13778684942431936004371)
            ·
              rfl

theorem cell22_3260318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 10].length) (baseStart_3260318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3260318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3260318 prefixEnd_3260318 := by exact prefixLift 3260318
  have htrace : WordTrace (prefixWord ++ tailWord_3260318) baseStart_3260318 baseEnd_3260318 := by
    simpa [prefixWord, tailWord_3260318, baseEnd_3260318] using wordTrace_append hprefix tailTrace_3260318
  have hstable : (prefixWord ++ tailWord_3260318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260318).length < 2 ^ (prefixWord ++ tailWord_3260318).sum := by decide
  have hdescent : baseEnd_3260318 < baseStart_3260318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260397 : List Nat := [1, 5, 1, 4, 1, 1, 3, 1, 5]
def baseStart_3260397 : Nat := 118140960795 + 3260397 * 2 ^ 59
def prefixEnd_3260397 : Nat := 4983230072969 + 3 ^ 40 * 3260397 * 2
def baseEnd_3260397 : Nat := 372033507883818981209603

theorem tailTrace_3260397 : CollatzResearch.WordTrace tailWord_3260397 prefixEnd_3260397 372033507883818981209603 := by
  unfold tailWord_3260397
  simp only [CollatzResearch.WordTrace]
  refine ⟨118916447969145975321091445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79277631979430650214060963 118916447969145975321091445)
  ·
    refine ⟨11148416997107435186352323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118916447969145975321091445 11148416997107435186352323)
    ·
      refine ⟨16722625495661152779528485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11148416997107435186352323 16722625495661152779528485)
      ·
        refine ⟨3135492280436466146161591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16722625495661152779528485 3135492280436466146161591)
        ·
          refine ⟨4703238420654699219242387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3135492280436466146161591 4703238420654699219242387)
          ·
            refine ⟨7054857630982048828863581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4703238420654699219242387 7054857630982048828863581)
            ·
              refine ⟨2645571611618268310823843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7054857630982048828863581 2645571611618268310823843)
              ·
                refine ⟨3968357417427402466235765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2645571611618268310823843 3968357417427402466235765)
                ·
                  refine ⟨372033507883818981209603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3968357417427402466235765 372033507883818981209603)
                  ·
                    rfl

theorem cell22_3260397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_3260397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3260397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3260397 prefixEnd_3260397 := by exact prefixLift 3260397
  have htrace : WordTrace (prefixWord ++ tailWord_3260397) baseStart_3260397 baseEnd_3260397 := by
    simpa [prefixWord, tailWord_3260397, baseEnd_3260397] using wordTrace_append hprefix tailTrace_3260397
  have hstable : (prefixWord ++ tailWord_3260397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260397).length < 2 ^ (prefixWord ++ tailWord_3260397).sum := by decide
  have hdescent : baseEnd_3260397 < baseStart_3260397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260421 : List Nat := [1, 3, 1, 1, 2, 4, 2, 1, 1, 6]
def baseStart_3260421 : Nat := 118140960795 + 3260421 * 2 ^ 59
def prefixEnd_3260421 : Nat := 4983230072969 + 3 ^ 40 * 3260421 * 2
def baseEnd_3260421 : Nat := 1116108739341928881028735

theorem tailTrace_3260421 : CollatzResearch.WordTrace tailWord_3260421 prefixEnd_3260421 1116108739341928881028735 := by
  unfold tailWord_3260421
  simp only [CollatzResearch.WordTrace]
  refine ⟨118917323321059027419965117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79278215547372684946643411 118917323321059027419965117)
  ·
    refine ⟨44593996245397135282486919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118917323321059027419965117 44593996245397135282486919)
    ·
      refine ⟨66890994368095702923730379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44593996245397135282486919 66890994368095702923730379)
      ·
        refine ⟨100336491552143554385595569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66890994368095702923730379 100336491552143554385595569)
        ·
          refine ⟨75252368664107665789196677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100336491552143554385595569 75252368664107665789196677)
          ·
            refine ⟨14109819124520187335474377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75252368664107665789196677 14109819124520187335474377)
            ·
              refine ⟨10582364343390140501605783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14109819124520187335474377 10582364343390140501605783)
              ·
                refine ⟨15873546515085210752408675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10582364343390140501605783 15873546515085210752408675)
                ·
                  refine ⟨23810319772627816128613013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15873546515085210752408675 23810319772627816128613013)
                  ·
                    refine ⟨1116108739341928881028735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23810319772627816128613013 1116108739341928881028735)
                    ·
                      rfl

theorem cell22_3260421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 6].length) (baseStart_3260421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3260421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3260421 prefixEnd_3260421 := by exact prefixLift 3260421
  have htrace : WordTrace (prefixWord ++ tailWord_3260421) baseStart_3260421 baseEnd_3260421 := by
    simpa [prefixWord, tailWord_3260421, baseEnd_3260421] using wordTrace_append hprefix tailTrace_3260421
  have hstable : (prefixWord ++ tailWord_3260421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260421).length < 2 ^ (prefixWord ++ tailWord_3260421).sum := by decide
  have hdescent : baseEnd_3260421 < baseStart_3260421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260423 : List Nat := [1, 1, 4, 3, 1, 2, 1, 2, 4, 3]
def baseStart_3260423 : Nat := 118140960795 + 3260423 * 2 ^ 59
def prefixEnd_3260423 : Nat := 4983230072969 + 3 ^ 40 * 3260423 * 2
def baseEnd_3260423 : Nat := 1116109423982801542478729

theorem tailTrace_3260423 : CollatzResearch.WordTrace tailWord_3260423 prefixEnd_3260423 1116109423982801542478729 := by
  unfold tailWord_3260423
  simp only [CollatzResearch.WordTrace]
  refine ⟨118917396267051781761537923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79278264178034521174358615 118917396267051781761537923)
  ·
    refine ⟨178376094400577672642306885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118917396267051781761537923 178376094400577672642306885)
    ·
      refine ⟨33445517700108313620432541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178376094400577672642306885 33445517700108313620432541)
      ·
        refine ⟨12542069137540617607662203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33445517700108313620432541 12542069137540617607662203)
        ·
          refine ⟨18813103706310926411493305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12542069137540617607662203 18813103706310926411493305)
          ·
            refine ⟨14109827779733194808619979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18813103706310926411493305 14109827779733194808619979)
            ·
              refine ⟨21164741669599792212929969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14109827779733194808619979 21164741669599792212929969)
              ·
                refine ⟨15873556252199844159697477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21164741669599792212929969 15873556252199844159697477)
                ·
                  refine ⟨2976291797287470779943277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15873556252199844159697477 2976291797287470779943277)
                  ·
                    refine ⟨1116109423982801542478729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2976291797287470779943277 1116109423982801542478729)
                    ·
                      rfl

theorem cell22_3260423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 4, 3].length) (baseStart_3260423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3260423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3260423 prefixEnd_3260423 := by exact prefixLift 3260423
  have htrace : WordTrace (prefixWord ++ tailWord_3260423) baseStart_3260423 baseEnd_3260423 := by
    simpa [prefixWord, tailWord_3260423, baseEnd_3260423] using wordTrace_append hprefix tailTrace_3260423
  have hstable : (prefixWord ++ tailWord_3260423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260423).length < 2 ^ (prefixWord ++ tailWord_3260423).sum := by decide
  have hdescent : baseEnd_3260423 < baseStart_3260423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260485 : List Nat := [1, 3, 1, 1, 1, 3, 1, 7, 1, 3]
def baseStart_3260485 : Nat := 118140960795 + 3260485 * 2 ^ 59
def prefixEnd_3260485 : Nat := 4983230072969 + 3 ^ 40 * 3260485 * 2
def baseEnd_3260485 : Nat := 1116130647849854047428539

theorem tailTrace_3260485 : CollatzResearch.WordTrace tailWord_3260485 prefixEnd_3260485 1116130647849854047428539 := by
  unfold tailWord_3260485
  simp only [CollatzResearch.WordTrace]
  refine ⟨118919657592827166350294909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79279771728551444233529939 118919657592827166350294909)
  ·
    refine ⟨44594871597310187381360591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118919657592827166350294909 44594871597310187381360591)
    ·
      refine ⟨66892307395965281072040887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44594871597310187381360591 66892307395965281072040887)
      ·
        refine ⟨100338461093947921608061331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66892307395965281072040887 100338461093947921608061331)
        ·
          refine ⟨150507691640921882412091997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100338461093947921608061331 150507691640921882412091997)
          ·
            refine ⟨56440384365345705904534499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150507691640921882412091997 56440384365345705904534499)
            ·
              refine ⟨84660576548018558856801749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56440384365345705904534499 84660576548018558856801749)
              ·
                refine ⟨1984232262844184973206291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 84660576548018558856801749 1984232262844184973206291)
                ·
                  refine ⟨2976348394266277459809437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1984232262844184973206291 2976348394266277459809437)
                  ·
                    refine ⟨1116130647849854047428539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2976348394266277459809437 1116130647849854047428539)
                    ·
                      rfl

theorem cell22_3260485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 7, 1, 3].length) (baseStart_3260485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3260485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3260485 prefixEnd_3260485 := by exact prefixLift 3260485
  have htrace : WordTrace (prefixWord ++ tailWord_3260485) baseStart_3260485 baseEnd_3260485 := by
    simpa [prefixWord, tailWord_3260485, baseEnd_3260485] using wordTrace_append hprefix tailTrace_3260485
  have hstable : (prefixWord ++ tailWord_3260485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260485).length < 2 ^ (prefixWord ++ tailWord_3260485).sum := by decide
  have hdescent : baseEnd_3260485 < baseStart_3260485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260528 : List Nat := [2, 1, 1, 1, 5, 2, 2, 1, 3, 4]
def baseStart_3260528 : Nat := 118140960795 + 3260528 * 2 ^ 59
def prefixEnd_3260528 : Nat := 4983230072969 + 3 ^ 40 * 3260528 * 2
def baseEnd_3260528 : Nat := 1116145367628616268603407

theorem tailTrace_3260528 : CollatzResearch.WordTrace tailWord_3260528 prefixEnd_3260528 1116145367628616268603407 := by
  unfold tailWord_3260528
  simp only [CollatzResearch.WordTrace]
  refine ⟨59460612965835692347055119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79280817287780923129406825 59460612965835692347055119)
  ·
    refine ⟨89190919448753538520582679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59460612965835692347055119 89190919448753538520582679)
    ·
      refine ⟨133786379173130307780874019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89190919448753538520582679 133786379173130307780874019)
      ·
        refine ⟨200679568759695461671311029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133786379173130307780874019 200679568759695461671311029)
        ·
          refine ⟨18813709571221449531685409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 200679568759695461671311029 18813709571221449531685409)
          ·
            refine ⟨14110282178416087148764057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18813709571221449531685409 14110282178416087148764057)
            ·
              refine ⟨10582711633812065361573043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14110282178416087148764057 10582711633812065361573043)
              ·
                refine ⟨15874067450718098042359565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10582711633812065361573043 15874067450718098042359565)
                ·
                  refine ⟨5952775294019286765884837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15874067450718098042359565 5952775294019286765884837)
                  ·
                    refine ⟨1116145367628616268603407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5952775294019286765884837 1116145367628616268603407)
                    ·
                      rfl

theorem cell22_3260528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 3, 4].length) (baseStart_3260528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3260528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3260528 prefixEnd_3260528 := by exact prefixLift 3260528
  have htrace : WordTrace (prefixWord ++ tailWord_3260528) baseStart_3260528 baseEnd_3260528 := by
    simpa [prefixWord, tailWord_3260528, baseEnd_3260528] using wordTrace_append hprefix tailTrace_3260528
  have hstable : (prefixWord ++ tailWord_3260528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260528).length < 2 ^ (prefixWord ++ tailWord_3260528).sum := by decide
  have hdescent : baseEnd_3260528 < baseStart_3260528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260573 : List Nat := [1, 4, 2, 1, 1, 3, 1, 2, 1, 6]
def baseStart_3260573 : Nat := 118140960795 + 3260573 * 2 ^ 59
def prefixEnd_3260573 : Nat := 4983230072969 + 3 ^ 40 * 3260573 * 2
def baseEnd_3260573 : Nat := 1116160772048251151228269

theorem tailTrace_3260573 : CollatzResearch.WordTrace tailWord_3260573 prefixEnd_3260573 1116160772048251151228269 := by
  unfold tailWord_3260573
  simp only [CollatzResearch.WordTrace]
  refine ⟨118922867216508357379498373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79281911477672238252998915 118922867216508357379498373)
  ·
    refine ⟨22298037603095317008655945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118922867216508357379498373 22298037603095317008655945)
    ·
      refine ⟨16723528202321487756491959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22298037603095317008655945 16723528202321487756491959)
      ·
        refine ⟨25085292303482231634737939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16723528202321487756491959 25085292303482231634737939)
        ·
          refine ⟨37627938455223347452106909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25085292303482231634737939 37627938455223347452106909)
          ·
            refine ⟨14110476920708755294540091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37627938455223347452106909 14110476920708755294540091)
            ·
              refine ⟨21165715381063132941810137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14110476920708755294540091 21165715381063132941810137)
              ·
                refine ⟨15874286535797349706357603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21165715381063132941810137 15874286535797349706357603)
                ·
                  refine ⟨23811429803696024559536405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15874286535797349706357603 23811429803696024559536405)
                  ·
                    refine ⟨1116160772048251151228269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23811429803696024559536405 1116160772048251151228269)
                    ·
                      rfl

theorem cell22_3260573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_3260573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3260573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3260573 prefixEnd_3260573 := by exact prefixLift 3260573
  have htrace : WordTrace (prefixWord ++ tailWord_3260573) baseStart_3260573 baseEnd_3260573 := by
    simpa [prefixWord, tailWord_3260573, baseEnd_3260573] using wordTrace_append hprefix tailTrace_3260573
  have hstable : (prefixWord ++ tailWord_3260573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260573).length < 2 ^ (prefixWord ++ tailWord_3260573).sum := by decide
  have hdescent : baseEnd_3260573 < baseStart_3260573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260575 : List Nat := [1, 1, 2, 6, 1, 1, 3, 1, 1, 5]
def baseStart_3260575 : Nat := 118140960795 + 3260575 * 2 ^ 59
def prefixEnd_3260575 : Nat := 4983230072969 + 3 ^ 40 * 3260575 * 2
def baseEnd_3260575 : Nat := 1116161456689123812678263

theorem tailTrace_3260575 : CollatzResearch.WordTrace tailWord_3260575 prefixEnd_3260575 1116161456689123812678263 := by
  unfold tailWord_3260575
  simp only [CollatzResearch.WordTrace]
  refine ⟨118922940162501111721071179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79281960108334074480714119 118922940162501111721071179)
  ·
    refine ⟨178384410243751667581606769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118922940162501111721071179 178384410243751667581606769)
    ·
      refine ⟨133788307682813750686205077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178384410243751667581606769 133788307682813750686205077)
      ·
        refine ⟨6271326922631894563415863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 133788307682813750686205077 6271326922631894563415863)
        ·
          refine ⟨9406990383947841845123795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6271326922631894563415863 9406990383947841845123795)
          ·
            refine ⟨14110485575921762767685693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9406990383947841845123795 14110485575921762767685693)
            ·
              refine ⟨5291432090970661037882135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14110485575921762767685693 5291432090970661037882135)
              ·
                refine ⟨7937148136455991556823203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5291432090970661037882135 7937148136455991556823203)
                ·
                  refine ⟨11905722204683987335234805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7937148136455991556823203 11905722204683987335234805)
                  ·
                    refine ⟨1116161456689123812678263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11905722204683987335234805 1116161456689123812678263)
                    ·
                      rfl

theorem cell22_3260575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 5].length) (baseStart_3260575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3260575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3260575 prefixEnd_3260575 := by exact prefixLift 3260575
  have htrace : WordTrace (prefixWord ++ tailWord_3260575) baseStart_3260575 baseEnd_3260575 := by
    simpa [prefixWord, tailWord_3260575, baseEnd_3260575] using wordTrace_append hprefix tailTrace_3260575
  have hstable : (prefixWord ++ tailWord_3260575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260575).length < 2 ^ (prefixWord ++ tailWord_3260575).sum := by decide
  have hdescent : baseEnd_3260575 < baseStart_3260575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260618 : List Nat := [3, 1, 2, 1, 3, 1, 2, 1, 2, 6]
def baseStart_3260618 : Nat := 118140960795 + 3260618 * 2 ^ 59
def prefixEnd_3260618 : Nat := 4983230072969 + 3 ^ 40 * 3260618 * 2
def baseEnd_3260618 : Nat := 1116176176467886033853131

theorem tailTrace_3260618 : CollatzResearch.WordTrace tailWord_3260618 prefixEnd_3260618 1116176176467886033853131 := by
  unfold tailWord_3260618
  simp only [CollatzResearch.WordTrace]
  refine ⟨29731127125336332516221627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79283005667563553376591005 29731127125336332516221627)
  ·
    refine ⟨44596690688004498774332441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29731127125336332516221627 44596690688004498774332441)
    ·
      refine ⟨33447518016003374080749331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44596690688004498774332441 33447518016003374080749331)
      ·
        refine ⟨50171277024005061121123997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33447518016003374080749331 50171277024005061121123997)
        ·
          refine ⟨18814228884001897920421499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50171277024005061121123997 18814228884001897920421499)
          ·
            refine ⟨28221343326002846880632249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18814228884001897920421499 28221343326002846880632249)
            ·
              refine ⟨21166007494502135160474187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28221343326002846880632249 21166007494502135160474187)
              ·
                refine ⟨31749011241753202740711281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21166007494502135160474187 31749011241753202740711281)
                ·
                  refine ⟨23811758431314902055533461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31749011241753202740711281 23811758431314902055533461)
                  ·
                    refine ⟨1116176176467886033853131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23811758431314902055533461 1116176176467886033853131)
                    ·
                      rfl

theorem cell22_3260618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_3260618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3260618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3260618 prefixEnd_3260618 := by exact prefixLift 3260618
  have htrace : WordTrace (prefixWord ++ tailWord_3260618) baseStart_3260618 baseEnd_3260618 := by
    simpa [prefixWord, tailWord_3260618, baseEnd_3260618] using wordTrace_append hprefix tailTrace_3260618
  have hstable : (prefixWord ++ tailWord_3260618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260618).length < 2 ^ (prefixWord ++ tailWord_3260618).sum := by decide
  have hdescent : baseEnd_3260618 < baseStart_3260618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260663 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 7, 4]
def baseStart_3260663 : Nat := 118140960795 + 3260663 * 2 ^ 59
def prefixEnd_3260663 : Nat := 4983230072969 + 3 ^ 40 * 3260663 * 2
def baseEnd_3260663 : Nat := 1116191580887520916477993

theorem tailTrace_3260663 : CollatzResearch.WordTrace tailWord_3260663 prefixEnd_3260663 1116191580887520916477993 := by
  unfold tailWord_3260663
  simp only [CollatzResearch.WordTrace]
  refine ⟨118926149786182302750274643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79284099857454868500183095 118926149786182302750274643)
  ·
    refine ⟨178389224679273454125411965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118926149786182302750274643 178389224679273454125411965)
    ·
      refine ⟨66895959254727545297029487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178389224679273454125411965 66895959254727545297029487)
      ·
        refine ⟨100343938882091317945544231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66895959254727545297029487 100343938882091317945544231)
        ·
          refine ⟨150515908323136976918316347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100343938882091317945544231 150515908323136976918316347)
          ·
            refine ⟨225773862484705465377474521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150515908323136976918316347 225773862484705465377474521)
            ·
              refine ⟨169330396863529099033105891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225773862484705465377474521 169330396863529099033105891)
              ·
                refine ⟨253995595295293648549658837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169330396863529099033105891 253995595295293648549658837)
                ·
                  refine ⟨5953021764733444887882629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 253995595295293648549658837 5953021764733444887882629)
                  ·
                    refine ⟨1116191580887520916477993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5953021764733444887882629 1116191580887520916477993)
                    ·
                      rfl

theorem cell22_3260663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 4].length) (baseStart_3260663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3260663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3260663 prefixEnd_3260663 := by exact prefixLift 3260663
  have htrace : WordTrace (prefixWord ++ tailWord_3260663) baseStart_3260663 baseEnd_3260663 := by
    simpa [prefixWord, tailWord_3260663, baseEnd_3260663] using wordTrace_append hprefix tailTrace_3260663
  have hstable : (prefixWord ++ tailWord_3260663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260663).length < 2 ^ (prefixWord ++ tailWord_3260663).sum := by decide
  have hdescent : baseEnd_3260663 < baseStart_3260663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260680 : List Nat := [2, 1, 3, 2, 3, 1, 1, 2, 3, 4]
def baseStart_3260680 : Nat := 118140960795 + 3260680 * 2 ^ 59
def prefixEnd_3260680 : Nat := 4983230072969 + 3 ^ 40 * 3260680 * 2
def baseEnd_3260680 : Nat := 1116197400334938538802941

theorem tailTrace_3260680 : CollatzResearch.WordTrace tailWord_3260680 prefixEnd_3260680 1116197400334938538802941 := by
  unfold tailWord_3260680
  simp only [CollatzResearch.WordTrace]
  refine ⟨59463384913560357326821747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79284513218080476435762329 59463384913560357326821747)
  ·
    refine ⟨89195077370340535990232621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59463384913560357326821747 89195077370340535990232621)
    ·
      refine ⟨33448154013877700996337233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89195077370340535990232621 33448154013877700996337233)
      ·
        refine ⟨25086115510408275747252925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33448154013877700996337233 25086115510408275747252925)
        ·
          refine ⟨9407293316403103405219847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25086115510408275747252925 9407293316403103405219847)
          ·
            refine ⟨14110939974604655107829771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9407293316403103405219847 14110939974604655107829771)
            ·
              refine ⟨21166409961906982661744657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14110939974604655107829771 21166409961906982661744657)
              ·
                refine ⟨15874807471430236996308493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21166409961906982661744657 15874807471430236996308493)
                ·
                  refine ⟨5953052801786338873615685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15874807471430236996308493 5953052801786338873615685)
                  ·
                    refine ⟨1116197400334938538802941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5953052801786338873615685 1116197400334938538802941)
                    ·
                      rfl

theorem cell22_3260680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_3260680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3260680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3260680 prefixEnd_3260680 := by exact prefixLift 3260680
  have htrace : WordTrace (prefixWord ++ tailWord_3260680) baseStart_3260680 baseEnd_3260680 := by
    simpa [prefixWord, tailWord_3260680, baseEnd_3260680] using wordTrace_append hprefix tailTrace_3260680
  have hstable : (prefixWord ++ tailWord_3260680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260680).length < 2 ^ (prefixWord ++ tailWord_3260680).sum := by decide
  have hdescent : baseEnd_3260680 < baseStart_3260680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260695 : List Nat := [1, 1, 3, 4, 1, 3, 1, 2, 6]
def baseStart_3260695 : Nat := 118140960795 + 3260695 * 2 ^ 59
def prefixEnd_3260695 : Nat := 4983230072969 + 3 ^ 40 * 3260695 * 2
def baseEnd_3260695 : Nat := 372067511713827833225965

theorem tailTrace_3260695 : CollatzResearch.WordTrace tailWord_3260695 prefixEnd_3260695 372067511713827833225965 := by
  unfold tailWord_3260695
  simp only [CollatzResearch.WordTrace]
  refine ⟨118927316922066372215439539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79284877948044248143626359 118927316922066372215439539)
  ·
    refine ⟨178390975383099558323159309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118927316922066372215439539 178390975383099558323159309)
    ·
      refine ⟨66896615768662334371184741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178390975383099558323159309 66896615768662334371184741)
      ·
        refine ⟨12543115456624187694597139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66896615768662334371184741 12543115456624187694597139)
        ·
          refine ⟨18814673184936281541895709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12543115456624187694597139 18814673184936281541895709)
          ·
            refine ⟨7055502444351105578210891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18814673184936281541895709 7055502444351105578210891)
            ·
              refine ⟨10583253666526658367316337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7055502444351105578210891 10583253666526658367316337)
              ·
                refine ⟨7937440249894993775487253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10583253666526658367316337 7937440249894993775487253)
                ·
                  refine ⟨372067511713827833225965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7937440249894993775487253 372067511713827833225965)
                  ·
                    rfl

theorem cell22_3260695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 6].length) (baseStart_3260695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3260695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3260695 prefixEnd_3260695 := by exact prefixLift 3260695
  have htrace : WordTrace (prefixWord ++ tailWord_3260695) baseStart_3260695 baseEnd_3260695 := by
    simpa [prefixWord, tailWord_3260695, baseEnd_3260695] using wordTrace_append hprefix tailTrace_3260695
  have hstable : (prefixWord ++ tailWord_3260695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260695).length < 2 ^ (prefixWord ++ tailWord_3260695).sum := by decide
  have hdescent : baseEnd_3260695 < baseStart_3260695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260714 : List Nat := [3, 1, 4, 2, 2, 1, 1, 3, 1, 4]
def baseStart_3260714 : Nat := 118140960795 + 3260714 * 2 ^ 59
def prefixEnd_3260714 : Nat := 4983230072969 + 3 ^ 40 * 3260714 * 2
def baseEnd_3260714 : Nat := 1116209039229773783452837

theorem tailTrace_3260714 : CollatzResearch.WordTrace tailWord_3260714 prefixEnd_3260714 1116209039229773783452837 := by
  unfold tailWord_3260714
  simp only [CollatzResearch.WordTrace]
  refine ⟨29732002477249384615095299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79285339939331692306920797 29732002477249384615095299)
  ·
    refine ⟨44598003715874076922642949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29732002477249384615095299 44598003715874076922642949)
    ·
      refine ⟨8362125696726389422995553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44598003715874076922642949 8362125696726389422995553)
      ·
        refine ⟨6271594272544792067246665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8362125696726389422995553 6271594272544792067246665)
        ·
          refine ⟨4703695704408594050434999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6271594272544792067246665 4703695704408594050434999)
          ·
            refine ⟨7055543556612891075652499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4703695704408594050434999 7055543556612891075652499)
            ·
              refine ⟨10583315334919336613478749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7055543556612891075652499 10583315334919336613478749)
              ·
                refine ⟨3968743250594751230054531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10583315334919336613478749 3968743250594751230054531)
                ·
                  refine ⟨5953114875892126845081797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3968743250594751230054531 5953114875892126845081797)
                  ·
                    refine ⟨1116209039229773783452837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5953114875892126845081797 1116209039229773783452837)
                    ·
                      rfl

theorem cell22_3260714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_3260714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3260714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3260714 prefixEnd_3260714 := by exact prefixLift 3260714
  have htrace : WordTrace (prefixWord ++ tailWord_3260714) baseStart_3260714 baseEnd_3260714 := by
    simpa [prefixWord, tailWord_3260714, baseEnd_3260714] using wordTrace_append hprefix tailTrace_3260714
  have hstable : (prefixWord ++ tailWord_3260714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260714).length < 2 ^ (prefixWord ++ tailWord_3260714).sum := by decide
  have hdescent : baseEnd_3260714 < baseStart_3260714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260723 : List Nat := [1, 1, 1, 2, 5, 1, 11]
def baseStart_3260723 : Nat := 118140960795 + 3260723 * 2 ^ 59
def prefixEnd_3260723 : Nat := 4983230072969 + 3 ^ 40 * 3260723 * 2
def baseEnd_3260723 : Nat := 41341189633840768888067

theorem tailTrace_3260723 : CollatzResearch.WordTrace tailWord_3260723 prefixEnd_3260723 41341189633840768888067 := by
  unfold tailWord_3260723
  simp only [CollatzResearch.WordTrace]
  refine ⟨118928338165964932997458823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79285558777309955331639215 118928338165964932997458823)
  ·
    refine ⟨178392507248947399496188235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118928338165964932997458823 178392507248947399496188235)
    ·
      refine ⟨267588760873421099244282353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178392507248947399496188235 267588760873421099244282353)
      ·
        refine ⟨200691570655065824433211765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267588760873421099244282353 200691570655065824433211765)
        ·
          refine ⟨18814834748912421040613603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 200691570655065824433211765 18814834748912421040613603)
          ·
            refine ⟨28222252123368631560920405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18814834748912421040613603 28222252123368631560920405)
            ·
              refine ⟨41341189633840768888067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 28222252123368631560920405 41341189633840768888067)
              ·
                rfl

theorem cell22_3260723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 11].length) (baseStart_3260723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3260723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3260723 prefixEnd_3260723 := by exact prefixLift 3260723
  have htrace : WordTrace (prefixWord ++ tailWord_3260723) baseStart_3260723 baseEnd_3260723 := by
    simpa [prefixWord, tailWord_3260723, baseEnd_3260723] using wordTrace_append hprefix tailTrace_3260723
  have hstable : (prefixWord ++ tailWord_3260723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260723).length < 2 ^ (prefixWord ++ tailWord_3260723).sum := by decide
  have hdescent : baseEnd_3260723 < baseStart_3260723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260725 : List Nat := [1, 3, 3, 1, 2, 1, 2, 1, 4, 4]
def baseStart_3260725 : Nat := 118140960795 + 3260725 * 2 ^ 59
def prefixEnd_3260725 : Nat := 4983230072969 + 3 ^ 40 * 3260725 * 2
def baseEnd_3260725 : Nat := 1116212804754573421427803

theorem tailTrace_3260725 : CollatzResearch.WordTrace tailWord_3260725 prefixEnd_3260725 1116212804754573421427803 := by
  unfold tailWord_3260725
  simp only [CollatzResearch.WordTrace]
  refine ⟨118928411111957687339031629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79285607407971791559354419 118928411111957687339031629)
  ·
    refine ⟨44598154166984132752136861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118928411111957687339031629 44598154166984132752136861)
    ·
      refine ⟨16724307812619049782051323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44598154166984132752136861 16724307812619049782051323)
      ·
        refine ⟨25086461718928574673076985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16724307812619049782051323 25086461718928574673076985)
        ·
          refine ⟨18814846289196431004807739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25086461718928574673076985 18814846289196431004807739)
          ·
            refine ⟨28222269433794646507211609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18814846289196431004807739 28222269433794646507211609)
            ·
              refine ⟨21166702075345984880408707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28222269433794646507211609 21166702075345984880408707)
              ·
                refine ⟨31750053113018977320613061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21166702075345984880408707 31750053113018977320613061)
                ·
                  refine ⟨5953134958691058247614949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31750053113018977320613061 5953134958691058247614949)
                  ·
                    refine ⟨1116212804754573421427803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5953134958691058247614949 1116212804754573421427803)
                    ·
                      rfl

theorem cell22_3260725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_3260725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3260725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3260725 prefixEnd_3260725 := by exact prefixLift 3260725
  have htrace : WordTrace (prefixWord ++ tailWord_3260725) baseStart_3260725 baseEnd_3260725 := by
    simpa [prefixWord, tailWord_3260725, baseEnd_3260725] using wordTrace_append hprefix tailTrace_3260725
  have hstable : (prefixWord ++ tailWord_3260725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260725).length < 2 ^ (prefixWord ++ tailWord_3260725).sum := by decide
  have hdescent : baseEnd_3260725 < baseStart_3260725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260755 : List Nat := [1, 1, 1, 2, 1, 1, 4, 3, 5, 3]
def baseStart_3260755 : Nat := 118140960795 + 3260755 * 2 ^ 59
def prefixEnd_3260755 : Nat := 4983230072969 + 3 ^ 40 * 3260755 * 2
def baseEnd_3260755 : Nat := 1116223074367663343177711

theorem tailTrace_3260755 : CollatzResearch.WordTrace tailWord_3260755 prefixEnd_3260755 1116223074367663343177711 := by
  unfold tailWord_3260755
  simp only [CollatzResearch.WordTrace]
  refine ⟨118929505301849002462623719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79286336867899334975082479 118929505301849002462623719)
  ·
    refine ⟨178394257952773503693935579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118929505301849002462623719 178394257952773503693935579)
    ·
      refine ⟨267591386929160255540903369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178394257952773503693935579 267591386929160255540903369)
      ·
        refine ⟨200693540196870191655677527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267591386929160255540903369 200693540196870191655677527)
        ·
          refine ⟨301040310295305287483516291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200693540196870191655677527 301040310295305287483516291)
          ·
            refine ⟨451560465442957931225274437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301040310295305287483516291 451560465442957931225274437)
            ·
              refine ⟨84667587270554612104738957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 451560465442957931225274437 84667587270554612104738957)
              ·
                refine ⟨31750345226457979539277109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84667587270554612104738957 31750345226457979539277109)
                ·
                  refine ⟨2976594864980435581807229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31750345226457979539277109 2976594864980435581807229)
                  ·
                    refine ⟨1116223074367663343177711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2976594864980435581807229 1116223074367663343177711)
                    ·
                      rfl

theorem cell22_3260755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 5, 3].length) (baseStart_3260755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3260755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3260755 prefixEnd_3260755 := by exact prefixLift 3260755
  have htrace : WordTrace (prefixWord ++ tailWord_3260755) baseStart_3260755 baseEnd_3260755 := by
    simpa [prefixWord, tailWord_3260755, baseEnd_3260755] using wordTrace_append hprefix tailTrace_3260755
  have hstable : (prefixWord ++ tailWord_3260755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260755).length < 2 ^ (prefixWord ++ tailWord_3260755).sum := by decide
  have hdescent : baseEnd_3260755 < baseStart_3260755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260785 : List Nat := [1, 2, 2, 2, 1, 2, 1, 6, 5]
def baseStart_3260785 : Nat := 118140960795 + 3260785 * 2 ^ 59
def prefixEnd_3260785 : Nat := 4983230072969 + 3 ^ 40 * 3260785 * 2
def baseEnd_3260785 : Nat := 372077781326917754975873

theorem tailTrace_3260785 : CollatzResearch.WordTrace tailWord_3260785 prefixEnd_3260785 372077781326917754975873 := by
  unfold tailWord_3260785
  simp only [CollatzResearch.WordTrace]
  refine ⟨118930599491740317586215809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79287066327826878390810539 118930599491740317586215809)
  ·
    refine ⟨89197949618805238189661857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118930599491740317586215809 89197949618805238189661857)
    ·
      refine ⟨66898462214103928642246393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89197949618805238189661857 66898462214103928642246393)
      ·
        refine ⟨50173846660577946481684795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66898462214103928642246393 50173846660577946481684795)
        ·
          refine ⟨75260769990866919722527193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50173846660577946481684795 75260769990866919722527193)
          ·
            refine ⟨56445577493150189791895395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75260769990866919722527193 56445577493150189791895395)
            ·
              refine ⟨84668366239725284687843093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56445577493150189791895395 84668366239725284687843093)
              ·
                refine ⟨3968829667487122719742645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 84668366239725284687843093 3968829667487122719742645)
                ·
                  refine ⟨372077781326917754975873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3968829667487122719742645 372077781326917754975873)
                  ·
                    rfl

theorem cell22_3260785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 5].length) (baseStart_3260785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3260785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3260785 prefixEnd_3260785 := by exact prefixLift 3260785
  have htrace : WordTrace (prefixWord ++ tailWord_3260785) baseStart_3260785 baseEnd_3260785 := by
    simpa [prefixWord, tailWord_3260785, baseEnd_3260785] using wordTrace_append hprefix tailTrace_3260785
  have hstable : (prefixWord ++ tailWord_3260785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260785).length < 2 ^ (prefixWord ++ tailWord_3260785).sum := by decide
  have hdescent : baseEnd_3260785 < baseStart_3260785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260789 : List Nat := [1, 3, 4, 1, 2, 1, 3, 1, 3, 3]
def baseStart_3260789 : Nat := 118140960795 + 3260789 * 2 ^ 59
def prefixEnd_3260789 : Nat := 4983230072969 + 3 ^ 40 * 3260789 * 2
def baseEnd_3260789 : Nat := 1116234713262498587827607

theorem tailTrace_3260789 : CollatzResearch.WordTrace tailWord_3260789 prefixEnd_3260789 1116234713262498587827607 := by
  unfold tailWord_3260789
  simp only [CollatzResearch.WordTrace]
  refine ⟨118930745383725826269361421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79287163589150550846240947 118930745383725826269361421)
  ·
    refine ⟨44599029518897184851010533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118930745383725826269361421 44599029518897184851010533)
    ·
      refine ⟨8362318034793222159564475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44599029518897184851010533 8362318034793222159564475)
      ·
        refine ⟨12543477052189833239346713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8362318034793222159564475 12543477052189833239346713)
        ·
          refine ⟨9407607789142374929510035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12543477052189833239346713 9407607789142374929510035)
          ·
            refine ⟨14111411683713562394265053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9407607789142374929510035 14111411683713562394265053)
            ·
              refine ⟨5291779381392585897849395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14111411683713562394265053 5291779381392585897849395)
              ·
                refine ⟨7937669072088878846774093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5291779381392585897849395 7937669072088878846774093)
                ·
                  refine ⟨2976625902033329567540285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7937669072088878846774093 2976625902033329567540285)
                  ·
                    refine ⟨1116234713262498587827607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2976625902033329567540285 1116234713262498587827607)
                    ·
                      rfl

theorem cell22_3260789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_3260789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3260789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3260789 prefixEnd_3260789 := by exact prefixLift 3260789
  have htrace : WordTrace (prefixWord ++ tailWord_3260789) baseStart_3260789 baseEnd_3260789 := by
    simpa [prefixWord, tailWord_3260789, baseEnd_3260789] using wordTrace_append hprefix tailTrace_3260789
  have hstable : (prefixWord ++ tailWord_3260789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260789).length < 2 ^ (prefixWord ++ tailWord_3260789).sum := by decide
  have hdescent : baseEnd_3260789 < baseStart_3260789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260840 : List Nat := [2, 1, 6, 1, 1, 3, 2, 2, 1, 3]
def baseStart_3260840 : Nat := 118140960795 + 3260840 * 2 ^ 59
def prefixEnd_3260840 : Nat := 4983230072969 + 3 ^ 40 * 3260840 * 2
def baseEnd_3260840 : Nat := 1116252171604751454802451

theorem tailTrace_3260840 : CollatzResearch.WordTrace tailWord_3260840 prefixEnd_3260840 1116252171604751454802451 := by
  unfold tailWord_3260840
  simp only [CollatzResearch.WordTrace]
  refine ⟨59466302753270530989733987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79288403671027374652978649 59466302753270530989733987)
  ·
    refine ⟨89199454129905796484600981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59466302753270530989733987 89199454129905796484600981)
    ·
      refine ⟨4181224412339334210215671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 89199454129905796484600981 4181224412339334210215671)
      ·
        refine ⟨6271836618509001315323507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4181224412339334210215671 6271836618509001315323507)
        ·
          refine ⟨9407754927763501972985261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6271836618509001315323507 9407754927763501972985261)
          ·
            refine ⟨3527908097911313239869473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9407754927763501972985261 3527908097911313239869473)
            ·
              refine ⟨2645931073433484929902105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3527908097911313239869473 2645931073433484929902105)
              ·
                refine ⟨1984448305075113697426579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2645931073433484929902105 1984448305075113697426579)
                ·
                  refine ⟨2976672457612670546139869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1984448305075113697426579 2976672457612670546139869)
                  ·
                    refine ⟨1116252171604751454802451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2976672457612670546139869 1116252171604751454802451)
                    ·
                      rfl

theorem cell22_3260840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_3260840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3260840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3260840 prefixEnd_3260840 := by exact prefixLift 3260840
  have htrace : WordTrace (prefixWord ++ tailWord_3260840) baseStart_3260840 baseEnd_3260840 := by
    simpa [prefixWord, tailWord_3260840, baseEnd_3260840] using wordTrace_append hprefix tailTrace_3260840
  have hstable : (prefixWord ++ tailWord_3260840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260840).length < 2 ^ (prefixWord ++ tailWord_3260840).sum := by decide
  have hdescent : baseEnd_3260840 < baseStart_3260840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260862 : List Nat := [4, 2, 1, 1, 1, 1, 3, 3, 1, 5]
def baseStart_3260862 : Nat := 118140960795 + 3260862 * 2 ^ 59
def prefixEnd_3260862 : Nat := 4983230072969 + 3 ^ 40 * 3260862 * 2
def baseEnd_3260862 : Nat := 1116259702654350730752383

theorem tailTrace_3260862 : CollatzResearch.WordTrace tailWord_3260862 prefixEnd_3260862 1116259702654350730752383 := by
  unfold tailWord_3260862
  simp only [CollatzResearch.WordTrace]
  refine ⟨14866675989057669967096105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79288938608307573157845893 14866675989057669967096105)
  ·
    refine ⟨11150006991793252475322079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14866675989057669967096105 11150006991793252475322079)
    ·
      refine ⟨16725010487689878712983119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11150006991793252475322079 16725010487689878712983119)
      ·
        refine ⟨25087515731534818069474679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16725010487689878712983119 25087515731534818069474679)
        ·
          refine ⟨37631273597302227104212019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25087515731534818069474679 37631273597302227104212019)
          ·
            refine ⟨56446910395953340656318029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37631273597302227104212019 56446910395953340656318029)
            ·
              refine ⟨21167591398482502746119261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56446910395953340656318029 21167591398482502746119261)
              ·
                refine ⟨7937846774430938529794723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21167591398482502746119261 7937846774430938529794723)
                ·
                  refine ⟨11906770161646407794692085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7937846774430938529794723 11906770161646407794692085)
                  ·
                    refine ⟨1116259702654350730752383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11906770161646407794692085 1116259702654350730752383)
                    ·
                      rfl

theorem cell22_3260862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_3260862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3260862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3260862 prefixEnd_3260862 := by exact prefixLift 3260862
  have htrace : WordTrace (prefixWord ++ tailWord_3260862) baseStart_3260862 baseEnd_3260862 := by
    simpa [prefixWord, tailWord_3260862, baseEnd_3260862] using wordTrace_append hprefix tailTrace_3260862
  have hstable : (prefixWord ++ tailWord_3260862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260862).length < 2 ^ (prefixWord ++ tailWord_3260862).sum := by decide
  have hdescent : baseEnd_3260862 < baseStart_3260862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260905 : List Nat := [1, 2, 1, 1, 1, 2, 1, 5, 2, 6]
def baseStart_3260905 : Nat := 118140960795 + 3260905 * 2 ^ 59
def prefixEnd_3260905 : Nat := 4983230072969 + 3 ^ 40 * 3260905 * 2
def baseEnd_3260905 : Nat := 1116274422433112951927251

theorem tailTrace_3260905 : CollatzResearch.WordTrace tailWord_3260905 prefixEnd_3260905 1116274422433112951927251 := by
  unfold tailWord_3260905
  simp only [CollatzResearch.WordTrace]
  refine ⟨118934976251305578080584169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79289984167537052053722779 118934976251305578080584169)
  ·
    refine ⟨89201232188479183560438127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118934976251305578080584169 89201232188479183560438127)
    ·
      refine ⟨133801848282718775340657191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89201232188479183560438127 133801848282718775340657191)
      ·
        refine ⟨200702772424078163010985787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133801848282718775340657191 200702772424078163010985787)
        ·
          refine ⟨301054158636117244516478681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200702772424078163010985787 301054158636117244516478681)
          ·
            refine ⟨225790618977087933387359011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301054158636117244516478681 225790618977087933387359011)
            ·
              refine ⟨338685928465631900081038517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225790618977087933387359011 338685928465631900081038517)
              ·
                refine ⟨31751805793652990632597361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 338685928465631900081038517 31751805793652990632597361)
                ·
                  refine ⟨23813854345239742974448021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31751805793652990632597361 23813854345239742974448021)
                  ·
                    refine ⟨1116274422433112951927251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23813854345239742974448021 1116274422433112951927251)
                    ·
                      rfl

theorem cell22_3260905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 6].length) (baseStart_3260905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3260905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3260905 prefixEnd_3260905 := by exact prefixLift 3260905
  have htrace : WordTrace (prefixWord ++ tailWord_3260905) baseStart_3260905 baseEnd_3260905 := by
    simpa [prefixWord, tailWord_3260905, baseEnd_3260905] using wordTrace_append hprefix tailTrace_3260905
  have hstable : (prefixWord ++ tailWord_3260905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260905).length < 2 ^ (prefixWord ++ tailWord_3260905).sum := by decide
  have hdescent : baseEnd_3260905 < baseStart_3260905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260997 : List Nat := [1, 3, 1, 1, 1, 5, 1, 1, 3, 5]
def baseStart_3260997 : Nat := 118140960795 + 3260997 * 2 ^ 59
def prefixEnd_3260997 : Nat := 4983230072969 + 3 ^ 40 * 3260997 * 2
def baseEnd_3260997 : Nat := 1116305915913255378626969

theorem tailTrace_3260997 : CollatzResearch.WordTrace tailWord_3260997 prefixEnd_3260997 1116305915913255378626969 := by
  unfold tailWord_3260997
  simp only [CollatzResearch.WordTrace]
  refine ⟨118938331766972277792933245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79292221177981518528622163 118938331766972277792933245)
  ·
    refine ⟨44601874412614604172349967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118938331766972277792933245 44601874412614604172349967)
    ·
      refine ⟨66902811618921906258524951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44601874412614604172349967 66902811618921906258524951)
      ·
        refine ⟨100354217428382859387787427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66902811618921906258524951 100354217428382859387787427)
        ·
          refine ⟨150531326142574289081681141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100354217428382859387787427 150531326142574289081681141)
          ·
            refine ⟨14112311825866339601407607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150531326142574289081681141 14112311825866339601407607)
            ·
              refine ⟨21168467738799509402111411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14112311825866339601407607 21168467738799509402111411)
              ·
                refine ⟨31752701608199264103167117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21168467738799509402111411 31752701608199264103167117)
                ·
                  refine ⟨11907263103074724038687669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31752701608199264103167117 11907263103074724038687669)
                  ·
                    refine ⟨1116305915913255378626969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11907263103074724038687669 1116305915913255378626969)
                    ·
                      rfl

theorem cell22_3260997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_3260997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3260997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3260997 prefixEnd_3260997 := by exact prefixLift 3260997
  have htrace : WordTrace (prefixWord ++ tailWord_3260997) baseStart_3260997 baseEnd_3260997 := by
    simpa [prefixWord, tailWord_3260997, baseEnd_3260997] using wordTrace_append hprefix tailTrace_3260997
  have hstable : (prefixWord ++ tailWord_3260997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260997).length < 2 ^ (prefixWord ++ tailWord_3260997).sum := by decide
  have hdescent : baseEnd_3260997 < baseStart_3260997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261016 : List Nat := [2, 1, 2, 2, 1, 2, 6, 2, 4]
def baseStart_3261016 : Nat := 118140960795 + 3261016 * 2 ^ 59
def prefixEnd_3261016 : Nat := 4983230072969 + 3 ^ 40 * 3261016 * 2
def baseEnd_3261016 : Nat := 372104140000515220800637

theorem tailTrace_3261016 : CollatzResearch.WordTrace tailWord_3261016 prefixEnd_3261016 372104140000515220800637 := by
  unfold tailWord_3261016
  simp only [CollatzResearch.WordTrace]
  refine ⟨59469512376951722018937451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79292683169268962691916601 59469512376951722018937451)
  ·
    refine ⟨89204268565427583028406177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59469512376951722018937451 89204268565427583028406177)
    ·
      refine ⟨66903201424070687271304633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89204268565427583028406177 66903201424070687271304633)
      ·
        refine ⟨50177401068053015453478475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66903201424070687271304633 50177401068053015453478475)
        ·
          refine ⟨75266101602079523180217713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50177401068053015453478475 75266101602079523180217713)
          ·
            refine ⟨56449576201559642385163285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75266101602079523180217713 56449576201559642385163285)
            ·
              refine ⟨2646073884448108236804529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56449576201559642385163285 2646073884448108236804529)
              ·
                refine ⟨1984555413336081177603397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2646073884448108236804529 1984555413336081177603397)
                ·
                  refine ⟨372104140000515220800637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1984555413336081177603397 372104140000515220800637)
                  ·
                    rfl

theorem cell22_3261016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 2, 4].length) (baseStart_3261016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3261016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3261016 prefixEnd_3261016 := by exact prefixLift 3261016
  have htrace : WordTrace (prefixWord ++ tailWord_3261016) baseStart_3261016 baseEnd_3261016 := by
    simpa [prefixWord, tailWord_3261016, baseEnd_3261016] using wordTrace_append hprefix tailTrace_3261016
  have hstable : (prefixWord ++ tailWord_3261016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261016).length < 2 ^ (prefixWord ++ tailWord_3261016).sum := by decide
  have hdescent : baseEnd_3261016 < baseStart_3261016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261046 : List Nat := [5, 1, 1, 2, 3, 1, 1, 1, 1, 6]
def baseStart_3261046 : Nat := 118140960795 + 3261046 * 2 ^ 59
def prefixEnd_3261046 : Nat := 4983230072969 + 3 ^ 40 * 3261046 * 2
def baseEnd_3261046 : Nat := 1116322689614635584151819

theorem tailTrace_3261046 : CollatzResearch.WordTrace tailWord_3261046 prefixEnd_3261046 1116322689614635584151819 := by
  unfold tailWord_3261046
  simp only [CollatzResearch.WordTrace]
  refine ⟨7433757433987172447591687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79293412629196506107644661 7433757433987172447591687)
  ·
    refine ⟨11150636150980758671387531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7433757433987172447591687 11150636150980758671387531)
    ·
      refine ⟨16725954226471138007081297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11150636150980758671387531 16725954226471138007081297)
      ·
        refine ⟨12544465669853353505310973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16725954226471138007081297 12544465669853353505310973)
        ·
          refine ⟨4704174626195007564491615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12544465669853353505310973 4704174626195007564491615)
          ·
            refine ⟨7056261939292511346737423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4704174626195007564491615 7056261939292511346737423)
            ·
              refine ⟨10584392908938767020106135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7056261939292511346737423 10584392908938767020106135)
              ·
                refine ⟨15876589363408150530159203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10584392908938767020106135 15876589363408150530159203)
                ·
                  refine ⟨23814884045112225795238805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15876589363408150530159203 23814884045112225795238805)
                  ·
                    refine ⟨1116322689614635584151819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23814884045112225795238805 1116322689614635584151819)
                    ·
                      rfl

theorem cell22_3261046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_3261046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3261046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3261046 prefixEnd_3261046 := by exact prefixLift 3261046
  have htrace : WordTrace (prefixWord ++ tailWord_3261046) baseStart_3261046 baseEnd_3261046 := by
    simpa [prefixWord, tailWord_3261046, baseEnd_3261046] using wordTrace_append hprefix tailTrace_3261046
  have hstable : (prefixWord ++ tailWord_3261046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261046).length < 2 ^ (prefixWord ++ tailWord_3261046).sum := by decide
  have hdescent : baseEnd_3261046 < baseStart_3261046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261095 : List Nat := [1, 1, 6, 3, 2, 1, 2, 6]
def baseStart_3261095 : Nat := 118140960795 + 3261095 * 2 ^ 59
def prefixEnd_3261095 : Nat := 4983230072969 + 3 ^ 40 * 3261095 * 2
def baseEnd_3261095 : Nat := 124037718146223976630741

theorem tailTrace_3261095 : CollatzResearch.WordTrace tailWord_3261095 prefixEnd_3261095 124037718146223976630741 := by
  unfold tailWord_3261095
  simp only [CollatzResearch.WordTrace]
  refine ⟨118941906120617240530000739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79294604080411493686667159 118941906120617240530000739)
  ·
    refine ⟨178412859180925860795001109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118941906120617240530000739 178412859180925860795001109)
    ·
      refine ⟨8363102774105899724765677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 178412859180925860795001109 8363102774105899724765677)
      ·
        refine ⟨3136163540289712396787129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8363102774105899724765677 3136163540289712396787129)
        ·
          refine ⟨2352122655217284297590347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3136163540289712396787129 2352122655217284297590347)
          ·
            refine ⟨3528183982825926446385521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2352122655217284297590347 3528183982825926446385521)
            ·
              refine ⟨2646137987119444834789141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3528183982825926446385521 2646137987119444834789141)
              ·
                refine ⟨124037718146223976630741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2646137987119444834789141 124037718146223976630741)
                ·
                  rfl

theorem cell22_3261095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 6].length) (baseStart_3261095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3261095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3261095 prefixEnd_3261095 := by exact prefixLift 3261095
  have htrace : WordTrace (prefixWord ++ tailWord_3261095) baseStart_3261095 baseEnd_3261095 := by
    simpa [prefixWord, tailWord_3261095, baseEnd_3261095] using wordTrace_append hprefix tailTrace_3261095
  have hstable : (prefixWord ++ tailWord_3261095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261095).length < 2 ^ (prefixWord ++ tailWord_3261095).sum := by decide
  have hdescent : baseEnd_3261095 < baseStart_3261095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261140 : List Nat := [2, 4, 1, 3, 2, 2, 2, 1, 5]
def baseStart_3261140 : Nat := 118140960795 + 3261140 * 2 ^ 59
def prefixEnd_3261140 : Nat := 4983230072969 + 3 ^ 40 * 3261140 * 2
def baseEnd_3261140 : Nat := 372118289245216890767177

theorem tailTrace_3261140 : CollatzResearch.WordTrace tailWord_3261140 prefixEnd_3261140 372118289245216890767177 := by
  unfold tailWord_3261140
  simp only [CollatzResearch.WordTrace]
  refine ⟨59471773702727106607694437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79295698270302808810259249 59471773702727106607694437)
  ·
    refine ⟨11150957569261332488942707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59471773702727106607694437 11150957569261332488942707)
    ·
      refine ⟨16726436353891998733414061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11150957569261332488942707 16726436353891998733414061)
      ·
        refine ⟨6272413632709499525030273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16726436353891998733414061 6272413632709499525030273)
        ·
          refine ⟨4704310224532124643772705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6272413632709499525030273 4704310224532124643772705)
          ·
            refine ⟨3528232668399093482829529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4704310224532124643772705 3528232668399093482829529)
            ·
              refine ⟨2646174501299320112122147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3528232668399093482829529 2646174501299320112122147)
              ·
                refine ⟨3969261751948980168183221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2646174501299320112122147 3969261751948980168183221)
                ·
                  refine ⟨372118289245216890767177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3969261751948980168183221 372118289245216890767177)
                  ·
                    rfl

theorem cell22_3261140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_3261140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3261140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3261140 prefixEnd_3261140 := by exact prefixLift 3261140
  have htrace : WordTrace (prefixWord ++ tailWord_3261140) baseStart_3261140 baseEnd_3261140 := by
    simpa [prefixWord, tailWord_3261140, baseEnd_3261140] using wordTrace_append hprefix tailTrace_3261140
  have hstable : (prefixWord ++ tailWord_3261140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261140).length < 2 ^ (prefixWord ++ tailWord_3261140).sum := by decide
  have hdescent : baseEnd_3261140 < baseStart_3261140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261153 : List Nat := [1, 2, 3, 1, 4, 3, 1, 2, 1, 4]
def baseStart_3261153 : Nat := 118140960795 + 3261153 * 2 ^ 59
def prefixEnd_3261153 : Nat := 4983230072969 + 3 ^ 40 * 3261153 * 2
def baseEnd_3261153 : Nat := 1116359317901322971726491

theorem tailTrace_3261153 : CollatzResearch.WordTrace tailWord_3261153 prefixEnd_3261153 1116359317901322971726491 := by
  unfold tailWord_3261153
  simp only [CollatzResearch.WordTrace]
  refine ⟨118944021554407116435612113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79296014369604744290408075 118944021554407116435612113)
  ·
    refine ⟨89208016165805337326709085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118944021554407116435612113 89208016165805337326709085)
    ·
      refine ⟨33453006062177001497515907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89208016165805337326709085 33453006062177001497515907)
      ·
        refine ⟨50179509093265502246273861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33453006062177001497515907 50179509093265502246273861)
        ·
          refine ⟨9408657954987281671176349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50179509093265502246273861 9408657954987281671176349)
          ·
            refine ⟨3528246733120230626691131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9408657954987281671176349 3528246733120230626691131)
            ·
              refine ⟨5292370099680345940036697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3528246733120230626691131 5292370099680345940036697)
              ·
                refine ⟨3969277574760259455027523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5292370099680345940036697 3969277574760259455027523)
                ·
                  refine ⟨5953916362140389182541285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3969277574760259455027523 5953916362140389182541285)
                  ·
                    refine ⟨1116359317901322971726491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5953916362140389182541285 1116359317901322971726491)
                    ·
                      rfl

theorem cell22_3261153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 4].length) (baseStart_3261153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3261153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3261153 prefixEnd_3261153 := by exact prefixLift 3261153
  have htrace : WordTrace (prefixWord ++ tailWord_3261153) baseStart_3261153 baseEnd_3261153 := by
    simpa [prefixWord, tailWord_3261153, baseEnd_3261153] using wordTrace_append hprefix tailTrace_3261153
  have hstable : (prefixWord ++ tailWord_3261153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261153).length < 2 ^ (prefixWord ++ tailWord_3261153).sum := by decide
  have hdescent : baseEnd_3261153 < baseStart_3261153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261166 : List Nat := [4, 1, 2, 1, 1, 4, 1, 2, 1, 5]
def baseStart_3261166 : Nat := 118140960795 + 3261166 * 2 ^ 59
def prefixEnd_3261166 : Nat := 4983230072969 + 3 ^ 40 * 3261166 * 2
def baseEnd_3261166 : Nat := 1116363768066995271151451

theorem tailTrace_3261166 : CollatzResearch.WordTrace tailWord_3261166 prefixEnd_3261166 1116363768066995271151451 := by
  unfold tailWord_3261166
  simp only [CollatzResearch.WordTrace]
  refine ⟨14868061962920002456979419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79296330468906679770556901 14868061962920002456979419)
  ·
    refine ⟨22302092944380003685469129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14868061962920002456979419 22302092944380003685469129)
    ·
      refine ⟨16726569708285002764101847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22302092944380003685469129 16726569708285002764101847)
      ·
        refine ⟨25089854562427504146152771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16726569708285002764101847 25089854562427504146152771)
        ·
          refine ⟨37634781843641256219229157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25089854562427504146152771 37634781843641256219229157)
          ·
            refine ⟨7056521595682735541105467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37634781843641256219229157 7056521595682735541105467)
            ·
              refine ⟨10584782393524103311658201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7056521595682735541105467 10584782393524103311658201)
              ·
                refine ⟨7938586795143077483743651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10584782393524103311658201 7938586795143077483743651)
                ·
                  refine ⟨11907880192714616225615477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7938586795143077483743651 11907880192714616225615477)
                  ·
                    refine ⟨1116363768066995271151451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11907880192714616225615477 1116363768066995271151451)
                    ·
                      rfl

theorem cell22_3261166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_3261166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3261166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3261166 prefixEnd_3261166 := by exact prefixLift 3261166
  have htrace : WordTrace (prefixWord ++ tailWord_3261166) baseStart_3261166 baseEnd_3261166 := by
    simpa [prefixWord, tailWord_3261166, baseEnd_3261166] using wordTrace_append hprefix tailTrace_3261166
  have hstable : (prefixWord ++ tailWord_3261166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261166).length < 2 ^ (prefixWord ++ tailWord_3261166).sum := by decide
  have hdescent : baseEnd_3261166 < baseStart_3261166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261239 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 4, 5]
def baseStart_3261239 : Nat := 118140960795 + 3261239 * 2 ^ 59
def prefixEnd_3261239 : Nat := 4983230072969 + 3 ^ 40 * 3261239 * 2
def baseEnd_3261239 : Nat := 1116388757458847414076227

theorem tailTrace_3261239 : CollatzResearch.WordTrace tailWord_3261239 prefixEnd_3261239 1116388757458847414076227 := by
  unfold tailWord_3261239
  simp only [CollatzResearch.WordTrace]
  refine ⟨118947158232095553123242771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79298105488063702082161847 118947158232095553123242771)
  ·
    refine ⟨178420737348143329684864157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118947158232095553123242771 178420737348143329684864157)
    ·
      refine ⟨66907776505553748631824059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178420737348143329684864157 66907776505553748631824059)
      ·
        refine ⟨100361664758330622947736089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66907776505553748631824059 100361664758330622947736089)
        ·
          refine ⟨75271248568747967210802067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100361664758330622947736089 75271248568747967210802067)
          ·
            refine ⟨112906872853121950816203101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75271248568747967210802067 112906872853121950816203101)
            ·
              refine ⟨42340077319920731556076163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112906872853121950816203101 42340077319920731556076163)
              ·
                refine ⟨63510115979881097334114245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42340077319920731556076163 63510115979881097334114245)
                ·
                  refine ⟨11908146746227705750146421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63510115979881097334114245 11908146746227705750146421)
                  ·
                    refine ⟨1116388757458847414076227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11908146746227705750146421 1116388757458847414076227)
                    ·
                      rfl

theorem cell22_3261239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_3261239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3261239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3261239 prefixEnd_3261239 := by exact prefixLift 3261239
  have htrace : WordTrace (prefixWord ++ tailWord_3261239) baseStart_3261239 baseEnd_3261239 := by
    simpa [prefixWord, tailWord_3261239, baseEnd_3261239] using wordTrace_append hprefix tailTrace_3261239
  have hstable : (prefixWord ++ tailWord_3261239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261239).length < 2 ^ (prefixWord ++ tailWord_3261239).sum := by decide
  have hdescent : baseEnd_3261239 < baseStart_3261239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261245 : List Nat := [1, 4, 1, 4, 2, 1, 2, 1, 3, 3]
def baseStart_3261245 : Nat := 118140960795 + 3261245 * 2 ^ 59
def prefixEnd_3261245 : Nat := 4983230072969 + 3 ^ 40 * 3261245 * 2
def baseEnd_3261245 : Nat := 1116390811381465398426209

theorem tailTrace_3261245 : CollatzResearch.WordTrace tailWord_3261245 prefixEnd_3261245 1116390811381465398426209 := by
  unfold tailWord_3261245
  simp only [CollatzResearch.WordTrace]
  refine ⟨118947377070073816147961189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79298251380049210765307459 118947377070073816147961189)
  ·
    refine ⟨22302633200638840527742723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118947377070073816147961189 22302633200638840527742723)
    ·
      refine ⟨33453949800958260791614085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22302633200638840527742723 33453949800958260791614085)
      ·
        refine ⟨6272615587679673898427641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33453949800958260791614085 6272615587679673898427641)
        ·
          refine ⟨4704461690759755423820731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6272615587679673898427641 4704461690759755423820731)
          ·
            refine ⟨7056692536139633135731097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4704461690759755423820731 7056692536139633135731097)
            ·
              refine ⟨5292519402104724851798323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7056692536139633135731097 5292519402104724851798323)
              ·
                refine ⟨7938779103157087277697485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5292519402104724851798323 7938779103157087277697485)
                ·
                  refine ⟨2977042163683907729136557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7938779103157087277697485 2977042163683907729136557)
                  ·
                    refine ⟨1116390811381465398426209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2977042163683907729136557 1116390811381465398426209)
                    ·
                      rfl

theorem cell22_3261245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 3, 3].length) (baseStart_3261245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3261245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3261245 prefixEnd_3261245 := by exact prefixLift 3261245
  have htrace : WordTrace (prefixWord ++ tailWord_3261245) baseStart_3261245 baseEnd_3261245 := by
    simpa [prefixWord, tailWord_3261245, baseEnd_3261245] using wordTrace_append hprefix tailTrace_3261245
  have hstable : (prefixWord ++ tailWord_3261245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261245).length < 2 ^ (prefixWord ++ tailWord_3261245).sum := by decide
  have hdescent : baseEnd_3261245 < baseStart_3261245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261288 : List Nat := [2, 1, 4, 2, 1, 2, 2, 3, 1, 4]
def baseStart_3261288 : Nat := 118140960795 + 3261288 * 2 ^ 59
def prefixEnd_3261288 : Nat := 4983230072969 + 3 ^ 40 * 3261288 * 2
def baseEnd_3261288 : Nat := 1116405531160227619601077

theorem tailTrace_3261288 : CollatzResearch.WordTrace tailWord_3261288 prefixEnd_3261288 1116405531160227619601077 := by
  unfold tailWord_3261288
  simp only [CollatzResearch.WordTrace]
  refine ⟨59474472704459017245888259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79299296939278689661184345 59474472704459017245888259)
  ·
    refine ⟨89211709056688525868832389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59474472704459017245888259 89211709056688525868832389)
    ·
      refine ⟨16727195448129098600406073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89211709056688525868832389 16727195448129098600406073)
      ·
        refine ⟨12545396586096823950304555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16727195448129098600406073 12545396586096823950304555)
        ·
          refine ⟨18818094879145235925456833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12545396586096823950304555 18818094879145235925456833)
          ·
            refine ⟨14113571159358926944092625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18818094879145235925456833 14113571159358926944092625)
            ·
              refine ⟨10585178369519195208069469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14113571159358926944092625 10585178369519195208069469)
              ·
                refine ⟨3969441888569698203026051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10585178369519195208069469 3969441888569698203026051)
                ·
                  refine ⟨5954162832854547304539077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3969441888569698203026051 5954162832854547304539077)
                  ·
                    refine ⟨1116405531160227619601077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5954162832854547304539077 1116405531160227619601077)
                    ·
                      rfl

theorem cell22_3261288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_3261288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3261288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3261288 prefixEnd_3261288 := by exact prefixLift 3261288
  have htrace : WordTrace (prefixWord ++ tailWord_3261288) baseStart_3261288 baseEnd_3261288 := by
    simpa [prefixWord, tailWord_3261288, baseEnd_3261288] using wordTrace_append hprefix tailTrace_3261288
  have hstable : (prefixWord ++ tailWord_3261288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261288).length < 2 ^ (prefixWord ++ tailWord_3261288).sum := by decide
  have hdescent : baseEnd_3261288 < baseStart_3261288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261316 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 6, 4]
def baseStart_3261316 : Nat := 118140960795 + 3261316 * 2 ^ 59
def prefixEnd_3261316 : Nat := 4983230072969 + 3 ^ 40 * 3261316 * 2
def baseEnd_3261316 : Nat := 1116415116132444879900991

theorem tailTrace_3261316 : CollatzResearch.WordTrace tailWord_3261316 prefixEnd_3261316 1116415116132444879900991 := by
  unfold tailWord_3261316
  simp only [CollatzResearch.WordTrace]
  refine ⟨59474983326408297636897901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79299977768544396849197201 59474983326408297636897901)
  ·
    refine ⟨22303118747403111613836713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59474983326408297636897901 22303118747403111613836713)
    ·
      refine ⟨16727339060552333710377535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22303118747403111613836713 16727339060552333710377535)
      ·
        refine ⟨25091008590828500565566303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16727339060552333710377535 25091008590828500565566303)
        ·
          refine ⟨37636512886242750848349455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25091008590828500565566303 37636512886242750848349455)
          ·
            refine ⟨56454769329364126272524183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37636512886242750848349455 56454769329364126272524183)
            ·
              refine ⟨84682153994046189408786275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56454769329364126272524183 84682153994046189408786275)
              ·
                refine ⟨127023230991069284113179413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84682153994046189408786275 127023230991069284113179413)
                ·
                  refine ⟨5954213952706372692805285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 127023230991069284113179413 5954213952706372692805285)
                  ·
                    refine ⟨1116415116132444879900991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5954213952706372692805285 1116415116132444879900991)
                    ·
                      rfl

theorem cell22_3261316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_3261316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3261316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3261316 prefixEnd_3261316 := by exact prefixLift 3261316
  have htrace : WordTrace (prefixWord ++ tailWord_3261316) baseStart_3261316 baseEnd_3261316 := by
    simpa [prefixWord, tailWord_3261316, baseEnd_3261316] using wordTrace_append hprefix tailTrace_3261316
  have hstable : (prefixWord ++ tailWord_3261316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261316).length < 2 ^ (prefixWord ++ tailWord_3261316).sum := by decide
  have hdescent : baseEnd_3261316 < baseStart_3261316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261333 : List Nat := [1, 3, 2, 1, 1, 5, 2, 1, 2, 4]
def baseStart_3261333 : Nat := 118140960795 + 3261333 * 2 ^ 59
def prefixEnd_3261333 : Nat := 4983230072969 + 3 ^ 40 * 3261333 * 2
def baseEnd_3261333 : Nat := 1116420935579862502225939

theorem tailTrace_3261333 : CollatzResearch.WordTrace tailWord_3261333 prefixEnd_3261333 1116420935579862502225939 := by
  unfold tailWord_3261333
  simp only [CollatzResearch.WordTrace]
  refine ⟨118950586693755007177164653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79300391129170004784776435 118950586693755007177164653)
  ·
    refine ⟨44606470010158127691436745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118950586693755007177164653 44606470010158127691436745)
    ·
      refine ⟨33454852507618595768577559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44606470010158127691436745 33454852507618595768577559)
      ·
        refine ⟨50182278761427893652866339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33454852507618595768577559 50182278761427893652866339)
        ·
          refine ⟨75273418142141840479299509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50182278761427893652866339 75273418142141840479299509)
          ·
            refine ⟨7056882950825797544934329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75273418142141840479299509 7056882950825797544934329)
            ·
              refine ⟨5292662213119348158700747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7056882950825797544934329 5292662213119348158700747)
              ·
                refine ⟨7938993319679022238051121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5292662213119348158700747 7938993319679022238051121)
                ·
                  refine ⟨5954244989759266678538341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7938993319679022238051121 5954244989759266678538341)
                  ·
                    refine ⟨1116420935579862502225939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5954244989759266678538341 1116420935579862502225939)
                    ·
                      rfl

theorem cell22_3261333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_3261333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3261333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3261333 prefixEnd_3261333 := by exact prefixLift 3261333
  have htrace : WordTrace (prefixWord ++ tailWord_3261333) baseStart_3261333 baseEnd_3261333 := by
    simpa [prefixWord, tailWord_3261333, baseEnd_3261333] using wordTrace_append hprefix tailTrace_3261333
  have hstable : (prefixWord ++ tailWord_3261333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261333).length < 2 ^ (prefixWord ++ tailWord_3261333).sum := by decide
  have hdescent : baseEnd_3261333 < baseStart_3261333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261410 : List Nat := [3, 3, 3, 1, 1, 2, 1, 1, 7]
def baseStart_3261410 : Nat := 118140960795 + 3261410 * 2 ^ 59
def prefixEnd_3261410 : Nat := 4983230072969 + 3 ^ 40 * 3261410 * 2
def baseEnd_3261410 : Nat := 372149098084486656016901

theorem tailTrace_3261410 : CollatzResearch.WordTrace tailWord_3261410 prefixEnd_3261410 372149098084486656016901 := by
  unfold tailWord_3261410
  simp only [CollatzResearch.WordTrace]
  refine ⟨29738348778619012331929421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79302263409650699551811789 29738348778619012331929421)
  ·
    refine ⟨11151880791982129624473533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29738348778619012331929421 11151880791982129624473533)
    ·
      refine ⟨4181955296993298609177575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11151880791982129624473533 4181955296993298609177575)
      ·
        refine ⟨6272932945489947913766363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4181955296993298609177575 6272932945489947913766363)
        ·
          refine ⟨9409399418234921870649545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6272932945489947913766363 9409399418234921870649545)
          ·
            refine ⟨7057049563676191402987159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9409399418234921870649545 7057049563676191402987159)
            ·
              refine ⟨10585574345514287104480739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7057049563676191402987159 10585574345514287104480739)
              ·
                refine ⟨15878361518271430656721109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10585574345514287104480739 15878361518271430656721109)
                ·
                  refine ⟨372149098084486656016901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15878361518271430656721109 372149098084486656016901)
                  ·
                    rfl

theorem cell22_3261410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_3261410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3261410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3261410 prefixEnd_3261410 := by exact prefixLift 3261410
  have htrace : WordTrace (prefixWord ++ tailWord_3261410) baseStart_3261410 baseEnd_3261410 := by
    simpa [prefixWord, tailWord_3261410, baseEnd_3261410] using wordTrace_append hprefix tailTrace_3261410
  have hstable : (prefixWord ++ tailWord_3261410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261410).length < 2 ^ (prefixWord ++ tailWord_3261410).sum := by decide
  have hdescent : baseEnd_3261410 < baseStart_3261410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261472 : List Nat := [2, 1, 1, 7, 1, 2, 1, 1, 6]
def baseStart_3261472 : Nat := 118140960795 + 3261472 * 2 ^ 59
def prefixEnd_3261472 : Nat := 4983230072969 + 3 ^ 40 * 3261472 * 2
def baseEnd_3261472 : Nat := 372156172706837491000171

theorem tailTrace_3261472 : CollatzResearch.WordTrace tailWord_3261472 prefixEnd_3261472 372156172706837491000171 := by
  unfold tailWord_3261472
  simp only [CollatzResearch.WordTrace]
  refine ⟨59477828220125716958237335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79303770960167622610983113 59477828220125716958237335)
  ·
    refine ⟨89216742330188575437356003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59477828220125716958237335 89216742330188575437356003)
    ·
      refine ⟨133825113495282863156034005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89216742330188575437356003 133825113495282863156034005)
      ·
        refine ⟨3136526097545692105219547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 133825113495282863156034005 3136526097545692105219547)
        ·
          refine ⟨4704789146318538157829321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3136526097545692105219547 4704789146318538157829321)
          ·
            refine ⟨3528591859738903618371991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4704789146318538157829321 3528591859738903618371991)
            ·
              refine ⟨5292887789608355427557987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3528591859738903618371991 5292887789608355427557987)
              ·
                refine ⟨7939331684412533141336981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5292887789608355427557987 7939331684412533141336981)
                ·
                  refine ⟨372156172706837491000171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7939331684412533141336981 372156172706837491000171)
                  ·
                    rfl

theorem cell22_3261472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 6].length) (baseStart_3261472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3261472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3261472 prefixEnd_3261472 := by exact prefixLift 3261472
  have htrace : WordTrace (prefixWord ++ tailWord_3261472) baseStart_3261472 baseEnd_3261472 := by
    simpa [prefixWord, tailWord_3261472, baseEnd_3261472] using wordTrace_append hprefix tailTrace_3261472
  have hstable : (prefixWord ++ tailWord_3261472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261472).length < 2 ^ (prefixWord ++ tailWord_3261472).sum := by decide
  have hdescent : baseEnd_3261472 < baseStart_3261472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261502 : List Nat := [4, 2, 1, 3, 1, 2, 2, 1, 2, 4]
def baseStart_3261502 : Nat := 118140960795 + 3261502 * 2 ^ 59
def prefixEnd_3261502 : Nat := 4983230072969 + 3 ^ 40 * 3261502 * 2
def baseEnd_3261502 : Nat := 1116478787733602394750421

theorem tailTrace_3261502 : CollatzResearch.WordTrace tailWord_3261502 prefixEnd_3261502 1116478787733602394750421 := by
  unfold tailWord_3261502
  simp only [CollatzResearch.WordTrace]
  refine ⟨14869593828767843630008345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79304500420095166026711173 14869593828767843630008345)
  ·
    refine ⟨11152195371575882722506259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14869593828767843630008345 11152195371575882722506259)
    ·
      refine ⟨16728293057363824083759389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11152195371575882722506259 16728293057363824083759389)
      ·
        refine ⟨6273109896511434031409771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16728293057363824083759389 6273109896511434031409771)
        ·
          refine ⟨9409664844767151047114657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6273109896511434031409771 9409664844767151047114657)
          ·
            refine ⟨7057248633575363285335993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9409664844767151047114657 7057248633575363285335993)
            ·
              refine ⟨5292936475181522464001995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7057248633575363285335993 5292936475181522464001995)
              ·
                refine ⟨7939404712772283696002993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5292936475181522464001995 7939404712772283696002993)
                ·
                  refine ⟨5954553534579212772002245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7939404712772283696002993 5954553534579212772002245)
                  ·
                    refine ⟨1116478787733602394750421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5954553534579212772002245 1116478787733602394750421)
                    ·
                      rfl

theorem cell22_3261502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_3261502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3261502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3261502 prefixEnd_3261502 := by exact prefixLift 3261502
  have htrace : WordTrace (prefixWord ++ tailWord_3261502) baseStart_3261502 baseEnd_3261502 := by
    simpa [prefixWord, tailWord_3261502, baseEnd_3261502] using wordTrace_append hprefix tailTrace_3261502
  have hstable : (prefixWord ++ tailWord_3261502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261502).length < 2 ^ (prefixWord ++ tailWord_3261502).sum := by decide
  have hdescent : baseEnd_3261502 < baseStart_3261502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261534 : List Nat := [4, 4, 1, 1, 1, 3, 1, 7]
def baseStart_3261534 : Nat := 118140960795 + 3261534 * 2 ^ 59
def prefixEnd_3261534 : Nat := 4983230072969 + 3 ^ 40 * 3261534 * 2
def baseEnd_3261534 : Nat := 124054415776396108661147

theorem tailTrace_3261534 : CollatzResearch.WordTrace tailWord_3261534 prefixEnd_3261534 124054415776396108661147 := by
  unfold tailWord_3261534
  simp only [CollatzResearch.WordTrace]
  refine ⟨14869739720753352313153957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79305278510684545670154437 14869739720753352313153957)
  ·
    refine ⟨2788076197641253558716367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14869739720753352313153957 2788076197641253558716367)
    ·
      refine ⟨4182114296461880338074551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2788076197641253558716367 4182114296461880338074551)
      ·
        refine ⟨6273171444692820507111827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4182114296461880338074551 6273171444692820507111827)
        ·
          refine ⟨9409757167039230760667741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6273171444692820507111827 9409757167039230760667741)
          ·
            refine ⟨3528658937639711535250403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9409757167039230760667741 3528658937639711535250403)
            ·
              refine ⟨5292988406459567302875605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3528658937639711535250403 5292988406459567302875605)
              ·
                refine ⟨124054415776396108661147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5292988406459567302875605 124054415776396108661147)
                ·
                  rfl

theorem cell22_3261534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 7].length) (baseStart_3261534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3261534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3261534 prefixEnd_3261534 := by exact prefixLift 3261534
  have htrace : WordTrace (prefixWord ++ tailWord_3261534) baseStart_3261534 baseEnd_3261534 := by
    simpa [prefixWord, tailWord_3261534, baseEnd_3261534] using wordTrace_append hprefix tailTrace_3261534
  have hstable : (prefixWord ++ tailWord_3261534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261534).length < 2 ^ (prefixWord ++ tailWord_3261534).sum := by decide
  have hdescent : baseEnd_3261534 < baseStart_3261534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261543 : List Nat := [1, 1, 5, 1, 1, 3, 1, 1, 1, 7]
def baseStart_3261543 : Nat := 118140960795 + 3261543 * 2 ^ 59
def prefixEnd_3261543 : Nat := 4983230072969 + 3 ^ 40 * 3261543 * 2
def baseEnd_3261543 : Nat := 1116492822871491954475295

theorem tailTrace_3261543 : CollatzResearch.WordTrace tailWord_3261543 prefixEnd_3261543 1116492822871491954475295 := by
  unfold tailWord_3261543
  simp only [CollatzResearch.WordTrace]
  refine ⟨118958246022994213042309283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79305497348662808694872855 118958246022994213042309283)
  ·
    refine ⟨178437369034491319563463925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118958246022994213042309283 178437369034491319563463925)
    ·
      refine ⟨16728503346983561209074743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 178437369034491319563463925 16728503346983561209074743)
      ·
        refine ⟨25092755020475341813612115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16728503346983561209074743 25092755020475341813612115)
        ·
          refine ⟨37639132530713012720418173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25092755020475341813612115 37639132530713012720418173)
          ·
            refine ⟨14114674699017379770156815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37639132530713012720418173 14114674699017379770156815)
            ·
              refine ⟨21172012048526069655235223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14114674699017379770156815 21172012048526069655235223)
              ·
                refine ⟨31758018072789104482852835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21172012048526069655235223 31758018072789104482852835)
                ·
                  refine ⟨47637027109183656724279253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31758018072789104482852835 47637027109183656724279253)
                  ·
                    refine ⟨1116492822871491954475295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47637027109183656724279253 1116492822871491954475295)
                    ·
                      rfl

theorem cell22_3261543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_3261543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3261543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3261543 prefixEnd_3261543 := by exact prefixLift 3261543
  have htrace : WordTrace (prefixWord ++ tailWord_3261543) baseStart_3261543 baseEnd_3261543 := by
    simpa [prefixWord, tailWord_3261543, baseEnd_3261543] using wordTrace_append hprefix tailTrace_3261543
  have hstable : (prefixWord ++ tailWord_3261543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261543).length < 2 ^ (prefixWord ++ tailWord_3261543).sum := by decide
  have hdescent : baseEnd_3261543 < baseStart_3261543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261605 : List Nat := [1, 3, 1, 2, 1, 4, 3, 1, 1, 5]
def baseStart_3261605 : Nat := 118140960795 + 3261605 * 2 ^ 59
def prefixEnd_3261605 : Nat := 4983230072969 + 3 ^ 40 * 3261605 * 2
def baseEnd_3261605 : Nat := 1116514046738544459425105

theorem tailTrace_3261605 : CollatzResearch.WordTrace tailWord_3261605 prefixEnd_3261605 1116514046738544459425105 := by
  unfold tailWord_3261605
  simp only [CollatzResearch.WordTrace]
  refine ⟨118960507348769597631066269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79307004899179731754044179 118960507348769597631066269)
  ·
    refine ⟨44610190255788599111649851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118960507348769597631066269 44610190255788599111649851)
    ·
      refine ⟨66915285383682898667474777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44610190255788599111649851 66915285383682898667474777)
      ·
        refine ⟨50186464037762174000606083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66915285383682898667474777 50186464037762174000606083)
        ·
          refine ⟨75279696056643261000909125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50186464037762174000606083 75279696056643261000909125)
          ·
            refine ⟨14114943010620611437670461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75279696056643261000909125 14114943010620611437670461)
            ·
              refine ⟨5293103628982729289126423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14114943010620611437670461 5293103628982729289126423)
              ·
                refine ⟨7939655443474093933689635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5293103628982729289126423 7939655443474093933689635)
                ·
                  refine ⟨11909483165211140900534453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7939655443474093933689635 11909483165211140900534453)
                  ·
                    refine ⟨1116514046738544459425105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11909483165211140900534453 1116514046738544459425105)
                    ·
                      rfl

theorem cell22_3261605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 5].length) (baseStart_3261605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3261605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3261605 prefixEnd_3261605 := by exact prefixLift 3261605
  have htrace : WordTrace (prefixWord ++ tailWord_3261605) baseStart_3261605 baseEnd_3261605 := by
    simpa [prefixWord, tailWord_3261605, baseEnd_3261605] using wordTrace_append hprefix tailTrace_3261605
  have hstable : (prefixWord ++ tailWord_3261605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261605).length < 2 ^ (prefixWord ++ tailWord_3261605).sum := by decide
  have hdescent : baseEnd_3261605 < baseStart_3261605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261656 : List Nat := [2, 1, 2, 2, 5, 2, 2, 1, 2, 3]
def baseStart_3261656 : Nat := 118140960795 + 3261656 * 2 ^ 59
def prefixEnd_3261656 : Nat := 4983230072969 + 3 ^ 40 * 3261656 * 2
def baseEnd_3261656 : Nat := 1116531505080797326399949

theorem tailTrace_3261656 : CollatzResearch.WordTrace tailWord_3261656 prefixEnd_3261656 1116531505080797326399949 := by
  unfold tailWord_3261656
  simp only [CollatzResearch.WordTrace]
  refine ⟨59481183735792416670586411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79308244981056555560781881 59481183735792416670586411)
  ·
    refine ⟨89221775603688625005879617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59481183735792416670586411 89221775603688625005879617)
    ·
      refine ⟨66916331702766468754409713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89221775603688625005879617 66916331702766468754409713)
      ·
        refine ⟨50187248777074851565807285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66916331702766468754409713 50187248777074851565807285)
        ·
          refine ⟨4705054572850767334294433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50187248777074851565807285 4705054572850767334294433)
          ·
            refine ⟨3528790929638075500720825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4705054572850767334294433 3528790929638075500720825)
            ·
              refine ⟨2646593197228556625540619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3528790929638075500720825 2646593197228556625540619)
              ·
                refine ⟨3969889795842834938310929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2646593197228556625540619 3969889795842834938310929)
                ·
                  refine ⟨2977417346882126203733197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3969889795842834938310929 2977417346882126203733197)
                  ·
                    refine ⟨1116531505080797326399949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2977417346882126203733197 1116531505080797326399949)
                    ·
                      rfl

theorem cell22_3261656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 2, 3].length) (baseStart_3261656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3261656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3261656 prefixEnd_3261656 := by exact prefixLift 3261656
  have htrace : WordTrace (prefixWord ++ tailWord_3261656) baseStart_3261656 baseEnd_3261656 := by
    simpa [prefixWord, tailWord_3261656, baseEnd_3261656] using wordTrace_append hprefix tailTrace_3261656
  have hstable : (prefixWord ++ tailWord_3261656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261656).length < 2 ^ (prefixWord ++ tailWord_3261656).sum := by decide
  have hdescent : baseEnd_3261656 < baseStart_3261656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261697 : List Nat := [1, 2, 4, 1, 1, 4, 2, 2, 5]
def baseStart_3261697 : Nat := 118140960795 + 3261697 * 2 ^ 59
def prefixEnd_3261697 : Nat := 4983230072969 + 3 ^ 40 * 3261697 * 2
def baseEnd_3261697 : Nat := 372181846739562295374941

theorem tailTrace_3261697 : CollatzResearch.WordTrace tailWord_3261697 prefixEnd_3261697 372181846739562295374941 := by
  unfold tailWord_3261697
  simp only [CollatzResearch.WordTrace]
  refine ⟨118963862864436297343415345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79309241909624198228943563 118963862864436297343415345)
  ·
    refine ⟨89222897148327223007561509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118963862864436297343415345 89222897148327223007561509)
    ·
      refine ⟨16729293215311354313917783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89222897148327223007561509 16729293215311354313917783)
      ·
        refine ⟨25093939822967031470876675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16729293215311354313917783 25093939822967031470876675)
        ·
          refine ⟨37640909734450547206315013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25093939822967031470876675 37640909734450547206315013)
          ·
            refine ⟨7057670575209477601184065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37640909734450547206315013 7057670575209477601184065)
            ·
              refine ⟨5293252931407108200888049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7057670575209477601184065 5293252931407108200888049)
              ·
                refine ⟨3969939698555331150666037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5293252931407108200888049 3969939698555331150666037)
                ·
                  refine ⟨372181846739562295374941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3969939698555331150666037 372181846739562295374941)
                  ·
                    rfl

theorem cell22_3261697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 5].length) (baseStart_3261697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3261697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3261697 prefixEnd_3261697 := by exact prefixLift 3261697
  have htrace : WordTrace (prefixWord ++ tailWord_3261697) baseStart_3261697 baseEnd_3261697 := by
    simpa [prefixWord, tailWord_3261697, baseEnd_3261697] using wordTrace_append hprefix tailTrace_3261697
  have hstable : (prefixWord ++ tailWord_3261697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261697).length < 2 ^ (prefixWord ++ tailWord_3261697).sum := by decide
  have hdescent : baseEnd_3261697 < baseStart_3261697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261806 : List Nat := [4, 1, 2, 4, 1, 1, 1, 2, 2, 4]
def baseStart_3261806 : Nat := 118140960795 + 3261806 * 2 ^ 59
def prefixEnd_3261806 : Nat := 4983230072969 + 3 ^ 40 * 3261806 * 2
def baseEnd_3261806 : Nat := 1116582853146246935149489

theorem tailTrace_3261806 : CollatzResearch.WordTrace tailWord_3261806 prefixEnd_3261806 1116582853146246935149489 := by
  unfold tailWord_3261806
  simp only [CollatzResearch.WordTrace]
  refine ⟨14870979802630176119891659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79311892280694272639422181 14870979802630176119891659)
  ·
    refine ⟨22306469703945264179837489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14870979802630176119891659 22306469703945264179837489)
    ·
      refine ⟨16729852277958948134878117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22306469703945264179837489 16729852277958948134878117)
      ·
        refine ⟨3136847302117302775289647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16729852277958948134878117 3136847302117302775289647)
        ·
          refine ⟨4705270953175954162934471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3136847302117302775289647 4705270953175954162934471)
          ·
            refine ⟨7057906429763931244401707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4705270953175954162934471 7057906429763931244401707)
            ·
              refine ⟨10586859644645896866602561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7057906429763931244401707 10586859644645896866602561)
              ·
                refine ⟨7940144733484422649951921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10586859644645896866602561 7940144733484422649951921)
                ·
                  refine ⟨5955108550113316987463941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7940144733484422649951921 5955108550113316987463941)
                  ·
                    refine ⟨1116582853146246935149489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5955108550113316987463941 1116582853146246935149489)
                    ·
                      rfl

theorem cell22_3261806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_3261806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3261806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3261806 prefixEnd_3261806 := by exact prefixLift 3261806
  have htrace : WordTrace (prefixWord ++ tailWord_3261806) baseStart_3261806 baseEnd_3261806 := by
    simpa [prefixWord, tailWord_3261806, baseEnd_3261806] using wordTrace_append hprefix tailTrace_3261806
  have hstable : (prefixWord ++ tailWord_3261806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261806).length < 2 ^ (prefixWord ++ tailWord_3261806).sum := by decide
  have hdescent : baseEnd_3261806 < baseStart_3261806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261815 : List Nat := [1, 1, 3, 1, 1, 2, 3, 3, 7]
def baseStart_3261815 : Nat := 118140960795 + 3261815 * 2 ^ 59
def prefixEnd_3261815 : Nat := 4983230072969 + 3 ^ 40 * 3261815 * 2
def baseEnd_3261815 : Nat := 372195311343391303891487

theorem tailTrace_3261815 : CollatzResearch.WordTrace tailWord_3261815 prefixEnd_3261815 372195311343391303891487 := by
  unfold tailWord_3261815
  simp only [CollatzResearch.WordTrace]
  refine ⟨118968166678008803496210899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79312111118672535664140599 118968166678008803496210899)
  ·
    refine ⟨178452250017013205244316349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118968166678008803496210899 178452250017013205244316349)
    ·
      refine ⟨66919593756379951966618631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178452250017013205244316349 66919593756379951966618631)
      ·
        refine ⟨100379390634569927949927947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66919593756379951966618631 100379390634569927949927947)
        ·
          refine ⟨150569085951854891924891921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100379390634569927949927947 150569085951854891924891921)
          ·
            refine ⟨112926814463891168943668941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150569085951854891924891921 112926814463891168943668941)
            ·
              refine ⟨42347555423959188353875853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112926814463891168943668941 42347555423959188353875853)
              ·
                refine ⟨15880333283984695632703445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42347555423959188353875853 15880333283984695632703445)
                ·
                  refine ⟨372195311343391303891487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15880333283984695632703445 372195311343391303891487)
                  ·
                    rfl

theorem cell22_3261815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 7].length) (baseStart_3261815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3261815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3261815 prefixEnd_3261815 := by exact prefixLift 3261815
  have htrace : WordTrace (prefixWord ++ tailWord_3261815) baseStart_3261815 baseEnd_3261815 := by
    simpa [prefixWord, tailWord_3261815, baseEnd_3261815] using wordTrace_append hprefix tailTrace_3261815
  have hstable : (prefixWord ++ tailWord_3261815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261815).length < 2 ^ (prefixWord ++ tailWord_3261815).sum := by decide
  have hdescent : baseEnd_3261815 < baseStart_3261815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261825 : List Nat := [1, 2, 4, 3, 3, 1, 2, 1, 2, 3]
def baseStart_3261825 : Nat := 118140960795 + 3261825 * 2 ^ 59
def prefixEnd_3261825 : Nat := 4983230072969 + 3 ^ 40 * 3261825 * 2
def baseEnd_3261825 : Nat := 1116589357234537218924431

theorem tailTrace_3261825 : CollatzResearch.WordTrace tailWord_3261825 prefixEnd_3261825 1116589357234537218924431 := by
  unfold tailWord_3261825
  simp only [CollatzResearch.WordTrace]
  refine ⟨118968531407972575204074929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79312354271981716802716619 118968531407972575204074929)
  ·
    refine ⟨89226398555979431403056197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118968531407972575204074929 89226398555979431403056197)
    ·
      refine ⟨16729949729246143388073037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89226398555979431403056197 16729949729246143388073037)
      ·
        refine ⟨6273731148467303770527389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16729949729246143388073037 6273731148467303770527389)
        ·
          refine ⟨2352649180675238913947771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6273731148467303770527389 2352649180675238913947771)
          ·
            refine ⟨3528973771012858370921657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2352649180675238913947771 3528973771012858370921657)
            ·
              refine ⟨2646730328259643778191243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3528973771012858370921657 2646730328259643778191243)
              ·
                refine ⟨3970095492389465667286865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2646730328259643778191243 3970095492389465667286865)
                ·
                  refine ⟨2977571619292099250465149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3970095492389465667286865 2977571619292099250465149)
                  ·
                    refine ⟨1116589357234537218924431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2977571619292099250465149 1116589357234537218924431)
                    ·
                      rfl

theorem cell22_3261825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_3261825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3261825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3261825 prefixEnd_3261825 := by exact prefixLift 3261825
  have htrace : WordTrace (prefixWord ++ tailWord_3261825) baseStart_3261825 baseEnd_3261825 := by
    simpa [prefixWord, tailWord_3261825, baseEnd_3261825] using wordTrace_append hprefix tailTrace_3261825
  have hstable : (prefixWord ++ tailWord_3261825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261825).length < 2 ^ (prefixWord ++ tailWord_3261825).sum := by decide
  have hdescent : baseEnd_3261825 < baseStart_3261825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261909 : List Nat := [1, 3, 2, 3, 1, 1, 2, 2, 4, 3]
def baseStart_3261909 : Nat := 118140960795 + 3261909 * 2 ^ 59
def prefixEnd_3261909 : Nat := 4983230072969 + 3 ^ 40 * 3261909 * 2
def baseEnd_3261909 : Nat := 1116618112151188999824173

theorem tailTrace_3261909 : CollatzResearch.WordTrace tailWord_3261909 prefixEnd_3261909 1116618112151188999824173 := by
  unfold tailWord_3261909
  simp only [CollatzResearch.WordTrace]
  refine ⟨118971595139668257550132781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79314396759778838366755187 118971595139668257550132781)
  ·
    refine ⟨44614348177375596581299793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118971595139668257550132781 44614348177375596581299793)
    ·
      refine ⟨33460761133031697435974845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44614348177375596581299793 33460761133031697435974845)
      ·
        refine ⟨12547785424886886538490567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33460761133031697435974845 12547785424886886538490567)
        ·
          refine ⟨18821678137330329807735851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12547785424886886538490567 18821678137330329807735851)
          ·
            refine ⟨28232517205995494711603777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18821678137330329807735851 28232517205995494711603777)
            ·
              refine ⟨21174387904496621033702833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28232517205995494711603777 21174387904496621033702833)
              ·
                refine ⟨15880790928372465775277125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21174387904496621033702833 15880790928372465775277125)
                ·
                  refine ⟨2977648299069837332864461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15880790928372465775277125 2977648299069837332864461)
                  ·
                    refine ⟨1116618112151188999824173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2977648299069837332864461 1116618112151188999824173)
                    ·
                      rfl

theorem cell22_3261909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 4, 3].length) (baseStart_3261909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3261909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3261909 prefixEnd_3261909 := by exact prefixLift 3261909
  have htrace : WordTrace (prefixWord ++ tailWord_3261909) baseStart_3261909 baseEnd_3261909 := by
    simpa [prefixWord, tailWord_3261909, baseEnd_3261909] using wordTrace_append hprefix tailTrace_3261909
  have hstable : (prefixWord ++ tailWord_3261909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261909).length < 2 ^ (prefixWord ++ tailWord_3261909).sum := by decide
  have hdescent : baseEnd_3261909 < baseStart_3261909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261984 : List Nat := [2, 1, 1, 6, 1, 1, 2, 1, 7]
def baseStart_3261984 : Nat := 118140960795 + 3261984 * 2 ^ 59
def prefixEnd_3261984 : Nat := 4983230072969 + 3 ^ 40 * 3261984 * 2
def baseEnd_3261984 : Nat := 372214595394637934732981

theorem tailTrace_3261984 : CollatzResearch.WordTrace tailWord_3261984 prefixEnd_3261984 372214595394637934732981 := by
  unfold tailWord_3261984
  simp only [CollatzResearch.WordTrace]
  refine ⟨59487165307198272679556503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79316220409597696906075337 59487165307198272679556503)
  ·
    refine ⟨89230747960797409019334755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59487165307198272679556503 89230747960797409019334755)
    ·
      refine ⟨133846121941196113529002133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89230747960797409019334755 133846121941196113529002133)
      ·
        refine ⟨6274036965993567821671975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 133846121941196113529002133 6274036965993567821671975)
        ·
          refine ⟨9411055448990351732507963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6274036965993567821671975 9411055448990351732507963)
          ·
            refine ⟨14116583173485527598761945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9411055448990351732507963 14116583173485527598761945)
            ·
              refine ⟨10587437380114145699071459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14116583173485527598761945 10587437380114145699071459)
              ·
                refine ⟨15881156070171218548607189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10587437380114145699071459 15881156070171218548607189)
                ·
                  refine ⟨372214595394637934732981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15881156070171218548607189 372214595394637934732981)
                  ·
                    rfl

theorem cell22_3261984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 7].length) (baseStart_3261984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3261984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3261984 prefixEnd_3261984 := by exact prefixLift 3261984
  have htrace : WordTrace (prefixWord ++ tailWord_3261984) baseStart_3261984 baseEnd_3261984 := by
    simpa [prefixWord, tailWord_3261984, baseEnd_3261984] using wordTrace_append hprefix tailTrace_3261984
  have hstable : (prefixWord ++ tailWord_3261984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261984).length < 2 ^ (prefixWord ++ tailWord_3261984).sum := by decide
  have hdescent : baseEnd_3261984 < baseStart_3261984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262140 : List Nat := [2, 2, 2, 3, 1, 2, 3, 3, 1, 3]
def baseStart_3262140 : Nat := 118140960795 + 3262140 * 2 ^ 59
def prefixEnd_3262140 : Nat := 4983230072969 + 3 ^ 40 * 3262140 * 2
def baseEnd_3262140 : Nat := 1116697188171981397298465

theorem tailTrace_3262140 : CollatzResearch.WordTrace tailWord_3262140 prefixEnd_3262140 1116697188171981397298465 := by
  unfold tailWord_3262140
  simp only [CollatzResearch.WordTrace]
  refine ⟨59490010200915692000895937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79320013601220922667861249 59490010200915692000895937)
  ·
    refine ⟨44617507650686769000671953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59490010200915692000895937 44617507650686769000671953)
    ·
      refine ⟨33463130738015076750503965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44617507650686769000671953 33463130738015076750503965)
      ·
        refine ⟨12548674026755653781438987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33463130738015076750503965 12548674026755653781438987)
        ·
          refine ⟨18823011040133480672158481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12548674026755653781438987 18823011040133480672158481)
          ·
            refine ⟨14117258280100110504118861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18823011040133480672158481 14117258280100110504118861)
            ·
              refine ⟨5293971855037541439044573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14117258280100110504118861 5293971855037541439044573)
              ·
                refine ⟨1985239445639078039641715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5293971855037541439044573 1985239445639078039641715)
                ·
                  refine ⟨2977859168458617059462573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1985239445639078039641715 2977859168458617059462573)
                  ·
                    refine ⟨1116697188171981397298465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2977859168458617059462573 1116697188171981397298465)
                    ·
                      rfl

theorem cell22_3262140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 3, 1, 3].length) (baseStart_3262140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3262140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3262140 prefixEnd_3262140 := by exact prefixLift 3262140
  have htrace : WordTrace (prefixWord ++ tailWord_3262140) baseStart_3262140 baseEnd_3262140 := by
    simpa [prefixWord, tailWord_3262140, baseEnd_3262140] using wordTrace_append hprefix tailTrace_3262140
  have hstable : (prefixWord ++ tailWord_3262140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262140).length < 2 ^ (prefixWord ++ tailWord_3262140).sum := by decide
  have hdescent : baseEnd_3262140 < baseStart_3262140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262157 : List Nat := [1, 6, 2, 1, 1, 3, 1, 1, 3, 3]
def baseStart_3262157 : Nat := 118140960795 + 3262157 * 2 ^ 59
def prefixEnd_3262157 : Nat := 4983230072969 + 3 ^ 40 * 3262157 * 2
def baseEnd_3262157 : Nat := 1116703007619399019623413

theorem tailTrace_3262157 : CollatzResearch.WordTrace tailWord_3262157 prefixEnd_3262157 1116703007619399019623413 := by
  unfold tailWord_3262157
  simp only [CollatzResearch.WordTrace]
  refine ⟨118980640442769795905160725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79320426961846530603440483 118980640442769795905160725)
  ·
    refine ⟨5577217520754834183054409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 118980640442769795905160725 5577217520754834183054409)
    ·
      refine ⟨4182913140566125637290807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5577217520754834183054409 4182913140566125637290807)
      ·
        refine ⟨6274369710849188455936211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4182913140566125637290807 6274369710849188455936211)
        ·
          refine ⟨9411554566273782683904317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6274369710849188455936211 9411554566273782683904317)
          ·
            refine ⟨3529332962352668506464119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9411554566273782683904317 3529332962352668506464119)
            ·
              refine ⟨5293999443529002759696179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3529332962352668506464119 5293999443529002759696179)
              ·
                refine ⟨7940999165293504139544269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5293999443529002759696179 7940999165293504139544269)
                ·
                  refine ⟨2977874686985064052329101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7940999165293504139544269 2977874686985064052329101)
                  ·
                    refine ⟨1116703007619399019623413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2977874686985064052329101 1116703007619399019623413)
                    ·
                      rfl

theorem cell22_3262157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_3262157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3262157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3262157 prefixEnd_3262157 := by exact prefixLift 3262157
  have htrace : WordTrace (prefixWord ++ tailWord_3262157) baseStart_3262157 baseEnd_3262157 := by
    simpa [prefixWord, tailWord_3262157, baseEnd_3262157] using wordTrace_append hprefix tailTrace_3262157
  have hstable : (prefixWord ++ tailWord_3262157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262157).length < 2 ^ (prefixWord ++ tailWord_3262157).sum := by decide
  have hdescent : baseEnd_3262157 < baseStart_3262157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262211 : List Nat := [1, 1, 1, 3, 2, 2, 4, 2, 2, 4]
def baseStart_3262211 : Nat := 118140960795 + 3262211 * 2 ^ 59
def prefixEnd_3262211 : Nat := 4983230072969 + 3 ^ 40 * 3262211 * 2
def baseEnd_3262211 : Nat := 1116721492922960878773247

theorem tailTrace_3262211 : CollatzResearch.WordTrace tailWord_3262211 prefixEnd_3262211 1116721492922960878773247 := by
  unfold tailWord_3262211
  simp only [CollatzResearch.WordTrace]
  refine ⟨118982609984574163127626487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79321739989716108751750991 118982609984574163127626487)
  ·
    refine ⟨178473914976861244691439731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118982609984574163127626487 178473914976861244691439731)
    ·
      refine ⟨267710872465291867037159597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178473914976861244691439731 267710872465291867037159597)
      ·
        refine ⟨100391577174484450138934849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267710872465291867037159597 100391577174484450138934849)
        ·
          refine ⟨75293682880863337604201137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100391577174484450138934849 75293682880863337604201137)
          ·
            refine ⟨56470262160647503203150853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75293682880863337604201137 56470262160647503203150853)
            ·
              refine ⟨10588174155121406850590785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56470262160647503203150853 10588174155121406850590785)
              ·
                refine ⟨7941130616341055137943089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10588174155121406850590785 7941130616341055137943089)
                ·
                  refine ⟨5955847962255791353457317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7941130616341055137943089 5955847962255791353457317)
                  ·
                    refine ⟨1116721492922960878773247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5955847962255791353457317 1116721492922960878773247)
                    ·
                      rfl

theorem cell22_3262211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 4].length) (baseStart_3262211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3262211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3262211 prefixEnd_3262211 := by exact prefixLift 3262211
  have htrace : WordTrace (prefixWord ++ tailWord_3262211) baseStart_3262211 baseEnd_3262211 := by
    simpa [prefixWord, tailWord_3262211, baseEnd_3262211] using wordTrace_append hprefix tailTrace_3262211
  have hstable : (prefixWord ++ tailWord_3262211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262211).length < 2 ^ (prefixWord ++ tailWord_3262211).sum := by decide
  have hdescent : baseEnd_3262211 < baseStart_3262211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262215 : List Nat := [1, 1, 4, 4, 2, 1, 1, 4, 4]
def baseStart_3262215 : Nat := 118140960795 + 3262215 * 2 ^ 59
def prefixEnd_3262215 : Nat := 4983230072969 + 3 ^ 40 * 3262215 * 2
def baseEnd_3262215 : Nat := 372240954068235400557745

theorem tailTrace_3262215 : CollatzResearch.WordTrace tailWord_3262215 prefixEnd_3262215 372240954068235400557745 := by
  unfold tailWord_3262215
  simp only [CollatzResearch.WordTrace]
  refine ⟨118982755876559671810772099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79321837251039781207181399 118982755876559671810772099)
  ·
    refine ⟨178474133814839507716158149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118982755876559671810772099 178474133814839507716158149)
    ·
      refine ⟨33463900090282407696779653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178474133814839507716158149 33463900090282407696779653)
      ·
        refine ⟨6274481266927951443146185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33463900090282407696779653 6274481266927951443146185)
        ·
          refine ⟨4705860950195963582359639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6274481266927951443146185 4705860950195963582359639)
          ·
            refine ⟨7058791425293945373539459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4705860950195963582359639 7058791425293945373539459)
            ·
              refine ⟨10588187137940918060309189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7058791425293945373539459 10588187137940918060309189)
              ·
                refine ⟨1985285088363922136307973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10588187137940918060309189 1985285088363922136307973)
                ·
                  refine ⟨372240954068235400557745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1985285088363922136307973 372240954068235400557745)
                  ·
                    rfl

theorem cell22_3262215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 4, 4].length) (baseStart_3262215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3262215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3262215 prefixEnd_3262215 := by exact prefixLift 3262215
  have htrace : WordTrace (prefixWord ++ tailWord_3262215) baseStart_3262215 baseEnd_3262215 := by
    simpa [prefixWord, tailWord_3262215, baseEnd_3262215] using wordTrace_append hprefix tailTrace_3262215
  have hstable : (prefixWord ++ tailWord_3262215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262215).length < 2 ^ (prefixWord ++ tailWord_3262215).sum := by decide
  have hdescent : baseEnd_3262215 < baseStart_3262215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262275 : List Nat := [1, 1, 1, 3, 1, 5, 2, 4, 1, 3]
def baseStart_3262275 : Nat := 118140960795 + 3262275 * 2 ^ 59
def prefixEnd_3262275 : Nat := 4983230072969 + 3 ^ 40 * 3262275 * 2
def baseEnd_3262275 : Nat := 1116743401430886045173051

theorem tailTrace_3262275 : CollatzResearch.WordTrace tailWord_3262275 prefixEnd_3262275 1116743401430886045173051 := by
  unfold tailWord_3262275
  simp only [CollatzResearch.WordTrace]
  refine ⟨118984944256342302057956279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79323296170894868038637519 118984944256342302057956279)
  ·
    refine ⟨178477416384513453086934419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118984944256342302057956279 178477416384513453086934419)
    ·
      refine ⟨267716124576770179630401629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178477416384513453086934419 267716124576770179630401629)
      ·
        refine ⟨100393546716288817361400611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267716124576770179630401629 100393546716288817361400611)
        ·
          refine ⟨150590320074433226042100917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100393546716288817361400611 150590320074433226042100917)
          ·
            refine ⟨14117842506978114941446961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150590320074433226042100917 14117842506978114941446961)
            ·
              refine ⟨10588381880233586206085221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14117842506978114941446961 10588381880233586206085221)
              ·
                refine ⟨1985321602543797413640979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10588381880233586206085221 1985321602543797413640979)
                ·
                  refine ⟨2977982403815696120461469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1985321602543797413640979 2977982403815696120461469)
                  ·
                    refine ⟨1116743401430886045173051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2977982403815696120461469 1116743401430886045173051)
                    ·
                      rfl

theorem cell22_3262275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 4, 1, 3].length) (baseStart_3262275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3262275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3262275 prefixEnd_3262275 := by exact prefixLift 3262275
  have htrace : WordTrace (prefixWord ++ tailWord_3262275) baseStart_3262275 baseEnd_3262275 := by
    simpa [prefixWord, tailWord_3262275, baseEnd_3262275] using wordTrace_append hprefix tailTrace_3262275
  have hstable : (prefixWord ++ tailWord_3262275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262275).length < 2 ^ (prefixWord ++ tailWord_3262275).sum := by decide
  have hdescent : baseEnd_3262275 < baseStart_3262275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262326 : List Nat := [5, 1, 1, 3, 2, 1, 3, 2, 1, 3]
def baseStart_3262326 : Nat := 118140960795 + 3262326 * 2 ^ 59
def prefixEnd_3262326 : Nat := 4983230072969 + 3 ^ 40 * 3262326 * 2
def baseEnd_3262326 : Nat := 1116760859773138912147895

theorem tailTrace_3262326 : CollatzResearch.WordTrace tailWord_3262326 prefixEnd_3262326 1116760859773138912147895 := by
  unfold tailWord_3262326
  simp only [CollatzResearch.WordTrace]
  refine ⟨7436675273697346110503927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79324536252771691845375221 7436675273697346110503927)
  ·
    refine ⟨11155012910546019165755891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7436675273697346110503927 11155012910546019165755891)
    ·
      refine ⟨16732519365819028748633837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11155012910546019165755891 16732519365819028748633837)
      ·
        refine ⟨6274694762182135780737689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16732519365819028748633837 6274694762182135780737689)
        ·
          refine ⟨4706021071636601835553267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6274694762182135780737689 4706021071636601835553267)
          ·
            refine ⟨7059031607454902753329901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4706021071636601835553267 7059031607454902753329901)
            ·
              refine ⟨2647136852795588532498713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7059031607454902753329901 2647136852795588532498713)
              ·
                refine ⟨1985352639596691399374035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2647136852795588532498713 1985352639596691399374035)
                ·
                  refine ⟨2978028959395037099061053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1985352639596691399374035 2978028959395037099061053)
                  ·
                    refine ⟨1116760859773138912147895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2978028959395037099061053 1116760859773138912147895)
                    ·
                      rfl

theorem cell22_3262326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_3262326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3262326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3262326 prefixEnd_3262326 := by exact prefixLift 3262326
  have htrace : WordTrace (prefixWord ++ tailWord_3262326) baseStart_3262326 baseEnd_3262326 := by
    simpa [prefixWord, tailWord_3262326, baseEnd_3262326] using wordTrace_append hprefix tailTrace_3262326
  have hstable : (prefixWord ++ tailWord_3262326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262326).length < 2 ^ (prefixWord ++ tailWord_3262326).sum := by decide
  have hdescent : baseEnd_3262326 < baseStart_3262326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262361 : List Nat := [1, 2, 1, 2, 1, 3, 4, 8]
def baseStart_3262361 : Nat := 118140960795 + 3262361 * 2 ^ 59
def prefixEnd_3262361 : Nat := 4983230072969 + 3 ^ 40 * 3262361 * 2
def baseEnd_3262361 : Nat := 124085871220934498613643

theorem tailTrace_3262361 : CollatzResearch.WordTrace tailWord_3262361 prefixEnd_3262361 124085871220934498613643 := by
  unfold tailWord_3262361
  simp only [CollatzResearch.WordTrace]
  refine ⟨118988080934030738745586937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79325387289353825830391291 118988080934030738745586937)
  ·
    refine ⟨89241060700523054059190203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118988080934030738745586937 89241060700523054059190203)
    ·
      refine ⟨133861591050784581088785305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89241060700523054059190203 133861591050784581088785305)
      ·
        refine ⟨100396193288088435816588979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133861591050784581088785305 100396193288088435816588979)
        ·
          refine ⟨150594289932132653724883469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100396193288088435816588979 150594289932132653724883469)
          ·
            refine ⟨56472858724549745146831301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150594289932132653724883469 56472858724549745146831301)
            ·
              refine ⟨10588661010853077215030869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56472858724549745146831301 10588661010853077215030869)
              ·
                refine ⟨124085871220934498613643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10588661010853077215030869 124085871220934498613643)
                ·
                  rfl

theorem cell22_3262361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 8].length) (baseStart_3262361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3262361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3262361 prefixEnd_3262361 := by exact prefixLift 3262361
  have htrace : WordTrace (prefixWord ++ tailWord_3262361) baseStart_3262361 baseEnd_3262361 := by
    simpa [prefixWord, tailWord_3262361, baseEnd_3262361] using wordTrace_append hprefix tailTrace_3262361
  have hstable : (prefixWord ++ tailWord_3262361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262361).length < 2 ^ (prefixWord ++ tailWord_3262361).sum := by decide
  have hdescent : baseEnd_3262361 < baseStart_3262361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262483 : List Nat := [1, 1, 1, 2, 1, 4, 2, 4, 1, 5]
def baseStart_3262483 : Nat := 118140960795 + 3262483 * 2 ^ 59
def prefixEnd_3262483 : Nat := 4983230072969 + 3 ^ 40 * 3262483 * 2
def baseEnd_3262483 : Nat := 1116814604081642835972413

theorem tailTrace_3262483 : CollatzResearch.WordTrace tailWord_3262483 prefixEnd_3262483 1116814604081642835972413 := by
  unfold tailWord_3262483
  simp only [CollatzResearch.WordTrace]
  refine ⟨118992530639588753581528103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79328353759725835721018735 118992530639588753581528103)
  ·
    refine ⟨178488795959383130372292155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118992530639588753581528103 178488795959383130372292155)
    ·
      refine ⟨267733193939074695558438233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178488795959383130372292155 267733193939074695558438233)
      ·
        refine ⟨200799895454306021668828675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267733193939074695558438233 200799895454306021668828675)
        ·
          refine ⟨301199843181459032503243013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200799895454306021668828675 301199843181459032503243013)
          ·
            refine ⟨56474970596523568594358065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 301199843181459032503243013 56474970596523568594358065)
            ·
              refine ⟨42356227947392676445768549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56474970596523568594358065 42356227947392676445768549)
              ·
                refine ⟨7941792740136126833581603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42356227947392676445768549 7941792740136126833581603)
                ·
                  refine ⟨11912689110204190250372405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7941792740136126833581603 11912689110204190250372405)
                  ·
                    refine ⟨1116814604081642835972413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11912689110204190250372405 1116814604081642835972413)
                    ·
                      rfl

theorem cell22_3262483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 5].length) (baseStart_3262483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3262483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3262483 prefixEnd_3262483 := by exact prefixLift 3262483
  have htrace : WordTrace (prefixWord ++ tailWord_3262483) baseStart_3262483 baseEnd_3262483 := by
    simpa [prefixWord, tailWord_3262483, baseEnd_3262483] using wordTrace_append hprefix tailTrace_3262483
  have hstable : (prefixWord ++ tailWord_3262483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262483).length < 2 ^ (prefixWord ++ tailWord_3262483).sum := by decide
  have hdescent : baseEnd_3262483 < baseStart_3262483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262513 : List Nat := [1, 2, 2, 3, 1, 3, 1, 9]
def baseStart_3262513 : Nat := 118140960795 + 3262513 * 2 ^ 59
def prefixEnd_3262513 : Nat := 4983230072969 + 3 ^ 40 * 3262513 * 2
def baseEnd_3262513 : Nat := 124091652632748084191369

theorem tailTrace_3262513 : CollatzResearch.WordTrace tailWord_3262513 prefixEnd_3262513 124091652632748084191369 := by
  unfold tailWord_3262513
  simp only [CollatzResearch.WordTrace]
  refine ⟨118993624829480068705120193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79329083219653379136746795 118993624829480068705120193)
  ·
    refine ⟨89245218622110051528840145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118993624829480068705120193 89245218622110051528840145)
    ·
      refine ⟨66933913966582538646630109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89245218622110051528840145 66933913966582538646630109)
      ·
        refine ⟨25100217737468451992486291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66933913966582538646630109 25100217737468451992486291)
        ·
          refine ⟨37650326606202677988729437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25100217737468451992486291 37650326606202677988729437)
          ·
            refine ⟨14118872477326004245773539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37650326606202677988729437 14118872477326004245773539)
            ·
              refine ⟨21178308715989006368660309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14118872477326004245773539 21178308715989006368660309)
              ·
                refine ⟨124091652632748084191369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21178308715989006368660309 124091652632748084191369)
                ·
                  rfl

theorem cell22_3262513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 9].length) (baseStart_3262513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3262513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3262513 prefixEnd_3262513 := by exact prefixLift 3262513
  have htrace : WordTrace (prefixWord ++ tailWord_3262513) baseStart_3262513 baseEnd_3262513 := by
    simpa [prefixWord, tailWord_3262513, baseEnd_3262513] using wordTrace_append hprefix tailTrace_3262513
  have hstable : (prefixWord ++ tailWord_3262513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262513).length < 2 ^ (prefixWord ++ tailWord_3262513).sum := by decide
  have hdescent : baseEnd_3262513 < baseStart_3262513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262575 : List Nat := [1, 1, 2, 1, 3, 4, 2, 3, 5]
def baseStart_3262575 : Nat := 118140960795 + 3262575 * 2 ^ 59
def prefixEnd_3262575 : Nat := 4983230072969 + 3 ^ 40 * 3262575 * 2
def baseEnd_3262575 : Nat := 372282032520595087557377

theorem tailTrace_3262575 : CollatzResearch.WordTrace tailWord_3262575 prefixEnd_3262575 372282032520595087557377 := by
  unfold tailWord_3262575
  simp only [CollatzResearch.WordTrace]
  refine ⟨118995886155255453293877179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79330590770170302195918119 118995886155255453293877179)
  ·
    refine ⟨178493829232883179940815769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118995886155255453293877179 178493829232883179940815769)
    ·
      refine ⟨133870371924662384955611827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178493829232883179940815769 133870371924662384955611827)
      ·
        refine ⟨200805557886993577433417741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133870371924662384955611827 200805557886993577433417741)
        ·
          refine ⟨75302084207622591537531653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200805557886993577433417741 75302084207622591537531653)
          ·
            refine ⟨14119140788929235913287185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75302084207622591537531653 14119140788929235913287185)
            ·
              refine ⟨10589355591696926934965389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14119140788929235913287185 10589355591696926934965389)
              ·
                refine ⟨3971008346886347600612021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10589355591696926934965389 3971008346886347600612021)
                ·
                  refine ⟨372282032520595087557377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3971008346886347600612021 372282032520595087557377)
                  ·
                    rfl

theorem cell22_3262575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 5].length) (baseStart_3262575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3262575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3262575 prefixEnd_3262575 := by exact prefixLift 3262575
  have htrace : WordTrace (prefixWord ++ tailWord_3262575) baseStart_3262575 baseEnd_3262575 := by
    simpa [prefixWord, tailWord_3262575, baseEnd_3262575] using wordTrace_append hprefix tailTrace_3262575
  have hstable : (prefixWord ++ tailWord_3262575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262575).length < 2 ^ (prefixWord ++ tailWord_3262575).sum := by decide
  have hdescent : baseEnd_3262575 < baseStart_3262575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262637 : List Nat := [1, 5, 2, 1, 2, 1, 2, 2, 6]
def baseStart_3262637 : Nat := 118140960795 + 3262637 * 2 ^ 59
def prefixEnd_3262637 : Nat := 4983230072969 + 3 ^ 40 * 3262637 * 2
def baseEnd_3262637 : Nat := 372289107142945922540647

theorem tailTrace_3262637 : CollatzResearch.WordTrace tailWord_3262637 prefixEnd_3262637 372289107142945922540647 := by
  unfold tailWord_3262637
  simp only [CollatzResearch.WordTrace]
  refine ⟨118998147481030837882634165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79332098320687225255089443 118998147481030837882634165)
  ·
    refine ⟨11156076326346641051496953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118998147481030837882634165 11156076326346641051496953)
    ·
      refine ⟨8367057244759980788622715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11156076326346641051496953 8367057244759980788622715)
      ·
        refine ⟨12550585867139971182934073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8367057244759980788622715 12550585867139971182934073)
        ·
          refine ⟨9412939400354978387200555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12550585867139971182934073 9412939400354978387200555)
          ·
            refine ⟨14119409100532467580800833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9412939400354978387200555 14119409100532467580800833)
            ·
              refine ⟨10589556825399350685600625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14119409100532467580800833 10589556825399350685600625)
              ·
                refine ⟨7942167619049513014200469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10589556825399350685600625 7942167619049513014200469)
                ·
                  refine ⟨372289107142945922540647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7942167619049513014200469 372289107142945922540647)
                  ·
                    rfl

theorem cell22_3262637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_3262637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3262637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3262637 prefixEnd_3262637 := by exact prefixLift 3262637
  have htrace : WordTrace (prefixWord ++ tailWord_3262637) baseStart_3262637 baseEnd_3262637 := by
    simpa [prefixWord, tailWord_3262637, baseEnd_3262637] using wordTrace_append hprefix tailTrace_3262637
  have hstable : (prefixWord ++ tailWord_3262637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262637).length < 2 ^ (prefixWord ++ tailWord_3262637).sum := by decide
  have hdescent : baseEnd_3262637 < baseStart_3262637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262650 : List Nat := [3, 1, 1, 1, 2, 2, 4, 1, 1, 6]
def baseStart_3262650 : Nat := 118140960795 + 3262650 * 2 ^ 59
def prefixEnd_3262650 : Nat := 4983230072969 + 3 ^ 40 * 3262650 * 2
def baseEnd_3262650 : Nat := 1116871771594510067046901

theorem tailTrace_3262650 : CollatzResearch.WordTrace tailWord_3262650 prefixEnd_3262650 1116871771594510067046901 := by
  unfold tailWord_3262650
  simp only [CollatzResearch.WordTrace]
  refine ⟨29749655407495935275714351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79332414419989160735238269 29749655407495935275714351)
  ·
    refine ⟨44624483111243902913571527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29749655407495935275714351 44624483111243902913571527)
    ·
      refine ⟨66936724666865854370357291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44624483111243902913571527 66936724666865854370357291)
      ·
        refine ⟨100405087000298781555535937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66936724666865854370357291 100405087000298781555535937)
        ·
          refine ⟨75303815250224086166651953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100405087000298781555535937 75303815250224086166651953)
          ·
            refine ⟨56477861437668064624988965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75303815250224086166651953 56477861437668064624988965)
            ·
              refine ⟨10589599019562762117185431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56477861437668064624988965 10589599019562762117185431)
              ·
                refine ⟨15884398529344143175778147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10589599019562762117185431 15884398529344143175778147)
                ·
                  refine ⟨23826597794016214763667221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15884398529344143175778147 23826597794016214763667221)
                  ·
                    refine ⟨1116871771594510067046901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23826597794016214763667221 1116871771594510067046901)
                    ·
                      rfl

theorem cell22_3262650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 1, 6].length) (baseStart_3262650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3262650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3262650 prefixEnd_3262650 := by exact prefixLift 3262650
  have htrace : WordTrace (prefixWord ++ tailWord_3262650) baseStart_3262650 baseEnd_3262650 := by
    simpa [prefixWord, tailWord_3262650, baseEnd_3262650] using wordTrace_append hprefix tailTrace_3262650
  have hstable : (prefixWord ++ tailWord_3262650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262650).length < 2 ^ (prefixWord ++ tailWord_3262650).sum := by decide
  have hdescent : baseEnd_3262650 < baseStart_3262650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262690 : List Nat := [3, 3, 4, 1, 1, 2, 1, 2, 1, 4]
def baseStart_3262690 : Nat := 118140960795 + 3262690 * 2 ^ 59
def prefixEnd_3262690 : Nat := 4983230072969 + 3 ^ 40 * 3262690 * 2
def baseEnd_3262690 : Nat := 1116885464411963296046779

theorem tailTrace_3262690 : CollatzResearch.WordTrace tailWord_3262690 prefixEnd_3262690 1116885464411963296046779 := by
  unfold tailWord_3262690
  simp only [CollatzResearch.WordTrace]
  refine ⟨29750020137459706983578381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79333387033225885289542349 29750020137459706983578381)
  ·
    refine ⟨11156257551547390118841893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29750020137459706983578381 11156257551547390118841893)
    ·
      refine ⟨2091798290915135647282855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11156257551547390118841893 2091798290915135647282855)
      ·
        refine ⟨3137697436372703470924283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2091798290915135647282855 3137697436372703470924283)
        ·
          refine ⟨4706546154559055206386425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3137697436372703470924283 4706546154559055206386425)
          ·
            refine ⟨3529909615919291404789819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4706546154559055206386425 3529909615919291404789819)
            ·
              refine ⟨5294864423878937107184729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3529909615919291404789819 5294864423878937107184729)
              ·
                refine ⟨3971148317909202830388547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5294864423878937107184729 3971148317909202830388547)
                ·
                  refine ⟨5956722476863804245582821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3971148317909202830388547 5956722476863804245582821)
                  ·
                    refine ⟨1116885464411963296046779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5956722476863804245582821 1116885464411963296046779)
                    ·
                      rfl

theorem cell22_3262690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_3262690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3262690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3262690 prefixEnd_3262690 := by exact prefixLift 3262690
  have htrace : WordTrace (prefixWord ++ tailWord_3262690) baseStart_3262690 baseEnd_3262690 := by
    simpa [prefixWord, tailWord_3262690, baseEnd_3262690] using wordTrace_append hprefix tailTrace_3262690
  have hstable : (prefixWord ++ tailWord_3262690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262690).length < 2 ^ (prefixWord ++ tailWord_3262690).sum := by decide
  have hdescent : baseEnd_3262690 < baseStart_3262690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262765 : List Nat := [1, 5, 3, 1, 2, 1, 2, 3, 1, 3]
def baseStart_3262765 : Nat := 118140960795 + 3262765 * 2 ^ 59
def prefixEnd_3262765 : Nat := 4983230072969 + 3 ^ 40 * 3262765 * 2
def baseEnd_3262765 : Nat := 1116911138444688100421549

theorem tailTrace_3262765 : CollatzResearch.WordTrace tailWord_3262765 prefixEnd_3262765 1116911138444688100421549 := by
  unfold tailWord_3262765
  simp only [CollatzResearch.WordTrace]
  refine ⟨119002816024567115743293749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79335210683044743828862499 119002816024567115743293749)
  ·
    refine ⟨11156514002303167100933789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119002816024567115743293749 11156514002303167100933789)
    ·
      refine ⟨4183692750863687662850171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11156514002303167100933789 4183692750863687662850171)
      ·
        refine ⟨6275539126295531494275257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4183692750863687662850171 6275539126295531494275257)
        ·
          refine ⟨4706654344721648620706443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6275539126295531494275257 4706654344721648620706443)
          ·
            refine ⟨7059981517082472931059665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4706654344721648620706443 7059981517082472931059665)
            ·
              refine ⟨5294986137811854698294749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7059981517082472931059665 5294986137811854698294749)
              ·
                refine ⟨1985619801679445511860531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5294986137811854698294749 1985619801679445511860531)
                ·
                  refine ⟨2978429702519168267790797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1985619801679445511860531 2978429702519168267790797)
                  ·
                    refine ⟨1116911138444688100421549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2978429702519168267790797 1116911138444688100421549)
                    ·
                      rfl

theorem cell22_3262765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_3262765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3262765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3262765 prefixEnd_3262765 := by exact prefixLift 3262765
  have htrace : WordTrace (prefixWord ++ tailWord_3262765) baseStart_3262765 baseEnd_3262765 := by
    simpa [prefixWord, tailWord_3262765, baseEnd_3262765] using wordTrace_append hprefix tailTrace_3262765
  have hstable : (prefixWord ++ tailWord_3262765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262765).length < 2 ^ (prefixWord ++ tailWord_3262765).sum := by decide
  have hdescent : baseEnd_3262765 < baseStart_3262765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262802 : List Nat := [3, 2, 2, 1, 1, 1, 3, 2, 1, 6]
def baseStart_3262802 : Nat := 118140960795 + 3262802 * 2 ^ 59
def prefixEnd_3262802 : Nat := 4983230072969 + 3 ^ 40 * 3262802 * 2
def baseEnd_3262802 : Nat := 1116923804300832337246435

theorem tailTrace_3262802 : CollatzResearch.WordTrace tailWord_3262802 prefixEnd_3262802 1116923804300832337246435 := by
  unfold tailWord_3262802
  simp only [CollatzResearch.WordTrace]
  refine ⟨29751041381358267765597665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79336110350288714041593773 29751041381358267765597665)
  ·
    refine ⟨22313281036018700824198249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29751041381358267765597665 22313281036018700824198249)
    ·
      refine ⟨16734960777014025618148687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22313281036018700824198249 16734960777014025618148687)
      ·
        refine ⟨25102441165521038427223031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16734960777014025618148687 25102441165521038427223031)
        ·
          refine ⟨37653661748281557640834547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25102441165521038427223031 37653661748281557640834547)
          ·
            refine ⟨56480492622422336461251821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37653661748281557640834547 56480492622422336461251821)
            ·
              refine ⟨21180184733408376172969433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56480492622422336461251821 21180184733408376172969433)
              ·
                refine ⟨15885138550056282129727075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21180184733408376172969433 15885138550056282129727075)
                ·
                  refine ⟨23827707825084423194590613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15885138550056282129727075 23827707825084423194590613)
                  ·
                    refine ⟨1116923804300832337246435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23827707825084423194590613 1116923804300832337246435)
                    ·
                      rfl

theorem cell22_3262802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_3262802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3262802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3262802 prefixEnd_3262802 := by exact prefixLift 3262802
  have htrace : WordTrace (prefixWord ++ tailWord_3262802) baseStart_3262802 baseEnd_3262802 := by
    simpa [prefixWord, tailWord_3262802, baseEnd_3262802] using wordTrace_append hprefix tailTrace_3262802
  have hstable : (prefixWord ++ tailWord_3262802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262802).length < 2 ^ (prefixWord ++ tailWord_3262802).sum := by decide
  have hdescent : baseEnd_3262802 < baseStart_3262802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262804 : List Nat := [2, 4, 1, 1, 2, 2, 3, 1, 1, 5]
def baseStart_3262804 : Nat := 118140960795 + 3262804 * 2 ^ 59
def prefixEnd_3262804 : Nat := 4983230072969 + 3 ^ 40 * 3262804 * 2
def baseEnd_3262804 : Nat := 1116924488941704998696429

theorem tailTrace_3262804 : CollatzResearch.WordTrace tailWord_3262804 prefixEnd_3262804 1116924488941704998696429 := by
  unfold tailWord_3262804
  simp only [CollatzResearch.WordTrace]
  refine ⟨59502119235712912701981733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79336158980950550269308977 59502119235712912701981733)
  ·
    refine ⟨11156647356696171131621575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59502119235712912701981733 11156647356696171131621575)
    ·
      refine ⟨16734971035044256697432363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11156647356696171131621575 16734971035044256697432363)
      ·
        refine ⟨25102456552566385046148545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16734971035044256697432363 25102456552566385046148545)
        ·
          refine ⟨18826842414424788784611409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25102456552566385046148545 18826842414424788784611409)
          ·
            refine ⟨14120131810818591588458557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18826842414424788784611409 14120131810818591588458557)
            ·
              refine ⟨5295049429056971845671959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14120131810818591588458557 5295049429056971845671959)
              ·
                refine ⟨7942574143585457768507939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5295049429056971845671959 7942574143585457768507939)
                ·
                  refine ⟨11913861215378186652761909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7942574143585457768507939 11913861215378186652761909)
                  ·
                    refine ⟨1116924488941704998696429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11913861215378186652761909 1116924488941704998696429)
                    ·
                      rfl

theorem cell22_3262804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_3262804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3262804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3262804 prefixEnd_3262804 := by exact prefixLift 3262804
  have htrace : WordTrace (prefixWord ++ tailWord_3262804) baseStart_3262804 baseEnd_3262804 := by
    simpa [prefixWord, tailWord_3262804, baseEnd_3262804] using wordTrace_append hprefix tailTrace_3262804
  have hstable : (prefixWord ++ tailWord_3262804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262804).length < 2 ^ (prefixWord ++ tailWord_3262804).sum := by decide
  have hdescent : baseEnd_3262804 < baseStart_3262804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262909 : List Nat := [1, 4, 1, 2, 2, 2, 1, 2, 3, 4]
def baseStart_3262909 : Nat := 118140960795 + 3262909 * 2 ^ 59
def prefixEnd_3262909 : Nat := 4983230072969 + 3 ^ 40 * 3262909 * 2
def baseEnd_3262909 : Nat := 1116960432587519724821107

theorem tailTrace_3262909 : CollatzResearch.WordTrace tailWord_3262909 prefixEnd_3262909 1116960432587519724821107 := by
  unfold tailWord_3262909
  simp only [CollatzResearch.WordTrace]
  refine ⟨119008068136045428336535781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79338712090696952224357187 119008068136045428336535781)
  ·
    refine ⟨22314012775508517813100459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119008068136045428336535781 22314012775508517813100459)
    ·
      refine ⟨33471019163262776719650689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22314012775508517813100459 33471019163262776719650689)
      ·
        refine ⟨25103264372447082539738017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33471019163262776719650689 25103264372447082539738017)
        ·
          refine ⟨18827448279335311904803513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25103264372447082539738017 18827448279335311904803513)
          ·
            refine ⟨14120586209501483928602635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18827448279335311904803513 14120586209501483928602635)
            ·
              refine ⟨21180879314252225892903953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14120586209501483928602635 21180879314252225892903953)
              ·
                refine ⟨15885659485689169419677965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21180879314252225892903953 15885659485689169419677965)
                ·
                  refine ⟨5957122307133438532379237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15885659485689169419677965 5957122307133438532379237)
                  ·
                    refine ⟨1116960432587519724821107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5957122307133438532379237 1116960432587519724821107)
                    ·
                      rfl

theorem cell22_3262909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_3262909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3262909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3262909 prefixEnd_3262909 := by exact prefixLift 3262909
  have htrace : WordTrace (prefixWord ++ tailWord_3262909) baseStart_3262909 baseEnd_3262909 := by
    simpa [prefixWord, tailWord_3262909, baseEnd_3262909] using wordTrace_append hprefix tailTrace_3262909
  have hstable : (prefixWord ++ tailWord_3262909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262909).length < 2 ^ (prefixWord ++ tailWord_3262909).sum := by decide
  have hdescent : baseEnd_3262909 < baseStart_3262909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262943 : List Nat := [1, 1, 2, 3, 3, 4, 2, 1, 1, 4]
def baseStart_3262943 : Nat := 118140960795 + 3262943 * 2 ^ 59
def prefixEnd_3262943 : Nat := 4983230072969 + 3 ^ 40 * 3262943 * 2
def baseEnd_3262943 : Nat := 1116972071482354969471003

theorem tailTrace_3262943 : CollatzResearch.WordTrace tailWord_3262943 prefixEnd_3262943 1116972071482354969471003 := by
  unfold tailWord_3262943
  simp only [CollatzResearch.WordTrace]
  refine ⟨119009308217922252143273483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79339538811948168095515655 119009308217922252143273483)
  ·
    refine ⟨178513962326883378214910225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119009308217922252143273483 178513962326883378214910225)
    ·
      refine ⟨133885471745162533661182669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178513962326883378214910225 133885471745162533661182669)
      ·
        refine ⟨50207051904435950122943501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133885471745162533661182669 50207051904435950122943501)
        ·
          refine ⟨18827644464163481296103813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50207051904435950122943501 18827644464163481296103813)
          ·
            refine ⟨3530183337030652743019465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18827644464163481296103813 3530183337030652743019465)
            ·
              refine ⟨2647637502772989557264599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3530183337030652743019465 2647637502772989557264599)
              ·
                refine ⟨3971456254159484335896899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2647637502772989557264599 3971456254159484335896899)
                ·
                  refine ⟨5957184381239226503845349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3971456254159484335896899 5957184381239226503845349)
                  ·
                    refine ⟨1116972071482354969471003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5957184381239226503845349 1116972071482354969471003)
                    ·
                      rfl

theorem cell22_3262943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 1, 4].length) (baseStart_3262943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3262943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3262943 prefixEnd_3262943 := by exact prefixLift 3262943
  have htrace : WordTrace (prefixWord ++ tailWord_3262943) baseStart_3262943 baseEnd_3262943 := by
    simpa [prefixWord, tailWord_3262943, baseEnd_3262943] using wordTrace_append hprefix tailTrace_3262943
  have hstable : (prefixWord ++ tailWord_3262943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262943).length < 2 ^ (prefixWord ++ tailWord_3262943).sum := by decide
  have hdescent : baseEnd_3262943 < baseStart_3262943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262973 : List Nat := [1, 4, 1, 1, 1, 3, 5, 1, 2, 3]
def baseStart_3262973 : Nat := 118140960795 + 3262973 * 2 ^ 59
def prefixEnd_3262973 : Nat := 4983230072969 + 3 ^ 40 * 3262973 * 2
def baseEnd_3262973 : Nat := 1116982341095444891220911

theorem tailTrace_3262973 : CollatzResearch.WordTrace tailWord_3262973 prefixEnd_3262973 1116982341095444891220911 := by
  unfold tailWord_3262973
  simp only [CollatzResearch.WordTrace]
  refine ⟨119010402407813567266865573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79340268271875711511243715 119010402407813567266865573)
  ·
    refine ⟨22314450451465043862537295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119010402407813567266865573 22314450451465043862537295)
    ·
      refine ⟨33471675677197565793805943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22314450451465043862537295 33471675677197565793805943)
      ·
        refine ⟨50207513515796348690708915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33471675677197565793805943 50207513515796348690708915)
        ·
          refine ⟨75311270273694523036063373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50207513515796348690708915 75311270273694523036063373)
          ·
            refine ⟨28241726352635446138523765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75311270273694523036063373 28241726352635446138523765)
            ·
              refine ⟨2647661845559573075486603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28241726352635446138523765 2647661845559573075486603)
              ·
                refine ⟨3971492768339359613229905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2647661845559573075486603 3971492768339359613229905)
                ·
                  refine ⟨2978619576254519709922429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3971492768339359613229905 2978619576254519709922429)
                  ·
                    refine ⟨1116982341095444891220911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2978619576254519709922429 1116982341095444891220911)
                    ·
                      rfl

theorem cell22_3262973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 2, 3].length) (baseStart_3262973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3262973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3262973 prefixEnd_3262973 := by exact prefixLift 3262973
  have htrace : WordTrace (prefixWord ++ tailWord_3262973) baseStart_3262973 baseEnd_3262973 := by
    simpa [prefixWord, tailWord_3262973, baseEnd_3262973] using wordTrace_append hprefix tailTrace_3262973
  have hstable : (prefixWord ++ tailWord_3262973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262973).length < 2 ^ (prefixWord ++ tailWord_3262973).sum := by decide
  have hdescent : baseEnd_3262973 < baseStart_3262973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263018 : List Nat := [3, 1, 4, 1, 1, 2, 3, 1, 3, 3]
def baseStart_3263018 : Nat := 118140960795 + 3263018 * 2 ^ 59
def prefixEnd_3263018 : Nat := 4983230072969 + 3 ^ 40 * 3263018 * 2
def baseEnd_3263018 : Nat := 1116997745515079773845773

theorem tailTrace_3263018 : CollatzResearch.WordTrace tailWord_3263018 prefixEnd_3263018 1116997745515079773845773 := by
  unfold tailWord_3263018
  simp only [CollatzResearch.WordTrace]
  refine ⟨29753010923162634988063427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79341362461767026634835805 29753010923162634988063427)
  ·
    refine ⟨44629516384743952482095141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29753010923162634988063427 44629516384743952482095141)
    ·
      refine ⟨8368034322139491090392839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44629516384743952482095141 8368034322139491090392839)
      ·
        refine ⟨12552051483209236635589259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8368034322139491090392839 12552051483209236635589259)
        ·
          refine ⟨18828077224813854953383889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12552051483209236635589259 18828077224813854953383889)
          ·
            refine ⟨14121057918610391215037917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18828077224813854953383889 14121057918610391215037917)
            ·
              refine ⟨5295396719478896705639219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14121057918610391215037917 5295396719478896705639219)
              ·
                refine ⟨7943095079218345058458829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5295396719478896705639219 7943095079218345058458829)
                ·
                  refine ⟨2978660654706879396922061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7943095079218345058458829 2978660654706879396922061)
                  ·
                    refine ⟨1116997745515079773845773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2978660654706879396922061 1116997745515079773845773)
                    ·
                      rfl

theorem cell22_3263018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_3263018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3263018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3263018 prefixEnd_3263018 := by exact prefixLift 3263018
  have htrace : WordTrace (prefixWord ++ tailWord_3263018) baseStart_3263018 baseEnd_3263018 := by
    simpa [prefixWord, tailWord_3263018, baseEnd_3263018] using wordTrace_append hprefix tailTrace_3263018
  have hstable : (prefixWord ++ tailWord_3263018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263018).length < 2 ^ (prefixWord ++ tailWord_3263018).sum := by decide
  have hdescent : baseEnd_3263018 < baseStart_3263018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263029 : List Nat := [1, 3, 3, 1, 1, 2, 2, 1, 1, 7]
def baseStart_3263029 : Nat := 118140960795 + 3263029 * 2 ^ 59
def prefixEnd_3263029 : Nat := 4983230072969 + 3 ^ 40 * 3263029 * 2
def baseEnd_3263029 : Nat := 1117001511039879411820739

theorem tailTrace_3263029 : CollatzResearch.WordTrace tailWord_3263029 prefixEnd_3263029 1117001511039879411820739 := by
  unfold tailWord_3263029
  simp only [CollatzResearch.WordTrace]
  refine ⟨119012444895610688830904141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79341629930407125887269427 119012444895610688830904141)
  ·
    refine ⟨44629666835854008311589053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119012444895610688830904141 44629666835854008311589053)
    ·
      refine ⟨16736125063445253116845895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44629666835854008311589053 16736125063445253116845895)
      ·
        refine ⟨25104187595167879675268843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16736125063445253116845895 25104187595167879675268843)
        ·
          refine ⟨37656281392751819512903265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25104187595167879675268843 37656281392751819512903265)
          ·
            refine ⟨28242211044563864634677449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37656281392751819512903265 28242211044563864634677449)
            ·
              refine ⟨21181658283422898476008087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28242211044563864634677449 21181658283422898476008087)
              ·
                refine ⟨31772487425134347714012131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21181658283422898476008087 31772487425134347714012131)
                ·
                  refine ⟨47658731137701521571018197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31772487425134347714012131 47658731137701521571018197)
                  ·
                    refine ⟨1117001511039879411820739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47658731137701521571018197 1117001511039879411820739)
                    ·
                      rfl

theorem cell22_3263029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_3263029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3263029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3263029 prefixEnd_3263029 := by exact prefixLift 3263029
  have htrace : WordTrace (prefixWord ++ tailWord_3263029) baseStart_3263029 baseEnd_3263029 := by
    simpa [prefixWord, tailWord_3263029, baseEnd_3263029] using wordTrace_append hprefix tailTrace_3263029
  have hstable : (prefixWord ++ tailWord_3263029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263029).length < 2 ^ (prefixWord ++ tailWord_3263029).sum := by decide
  have hdescent : baseEnd_3263029 < baseStart_3263029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263061 : List Nat := [1, 3, 2, 2, 1, 1, 2, 5, 1, 4]
def baseStart_3263061 : Nat := 118140960795 + 3263061 * 2 ^ 59
def prefixEnd_3263061 : Nat := 4983230072969 + 3 ^ 40 * 3263061 * 2
def baseEnd_3263061 : Nat := 1117012465293841995020641

theorem tailTrace_3263061 : CollatzResearch.WordTrace tailWord_3263061 prefixEnd_3263061 1117012465293841995020641 := by
  unfold tailWord_3263061
  simp only [CollatzResearch.WordTrace]
  refine ⟨119013612031494758296069037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79342408020996505530712691 119013612031494758296069037)
  ·
    refine ⟨44630104511810534361025889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119013612031494758296069037 44630104511810534361025889)
    ·
      refine ⟨33472578383857900770769417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44630104511810534361025889 33472578383857900770769417)
      ·
        refine ⟨25104433787893425578077063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33472578383857900770769417 25104433787893425578077063)
        ·
          refine ⟨37656650681840138367115595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25104433787893425578077063 37656650681840138367115595)
          ·
            refine ⟨56484976022760207550673393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37656650681840138367115595 56484976022760207550673393)
            ·
              refine ⟨42363732017070155663005045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56484976022760207550673393 42363732017070155663005045)
              ·
                refine ⟨3971599876600327093406723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42363732017070155663005045 3971599876600327093406723)
                ·
                  refine ⟨5957399814900490640110085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3971599876600327093406723 5957399814900490640110085)
                  ·
                    refine ⟨1117012465293841995020641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5957399814900490640110085 1117012465293841995020641)
                    ·
                      rfl

theorem cell22_3263061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_3263061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3263061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3263061 prefixEnd_3263061 := by exact prefixLift 3263061
  have htrace : WordTrace (prefixWord ++ tailWord_3263061) baseStart_3263061 baseEnd_3263061 := by
    simpa [prefixWord, tailWord_3263061, baseEnd_3263061] using wordTrace_append hprefix tailTrace_3263061
  have hstable : (prefixWord ++ tailWord_3263061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263061).length < 2 ^ (prefixWord ++ tailWord_3263061).sum := by decide
  have hdescent : baseEnd_3263061 < baseStart_3263061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263093 : List Nat := [1, 3, 4, 2, 2, 1, 1, 2, 6]
def baseStart_3263093 : Nat := 118140960795 + 3263093 * 2 ^ 59
def prefixEnd_3263093 : Nat := 4983230072969 + 3 ^ 40 * 3263093 * 2
def baseEnd_3263093 : Nat := 372341139849268192740181

theorem tailTrace_3263093 : CollatzResearch.WordTrace tailWord_3263093 prefixEnd_3263093 372341139849268192740181 := by
  unfold tailWord_3263093
  simp only [CollatzResearch.WordTrace]
  refine ⟨119014779167378827761233933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79343186111585885174155955 119014779167378827761233933)
  ·
    refine ⟨44630542187767060410462725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119014779167378827761233933 44630542187767060410462725)
    ·
      refine ⟨8368226660206323826961761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44630542187767060410462725 8368226660206323826961761)
      ·
        refine ⟨6276169995154742870221321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8368226660206323826961761 6276169995154742870221321)
        ·
          refine ⟨4707127496366057152665991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6276169995154742870221321 4707127496366057152665991)
          ·
            refine ⟨7060691244549085728998987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4707127496366057152665991 7060691244549085728998987)
            ·
              refine ⟨10591036866823628593498481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7060691244549085728998987 10591036866823628593498481)
              ·
                refine ⟨7943277650117721445123861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10591036866823628593498481 7943277650117721445123861)
                ·
                  refine ⟨372341139849268192740181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7943277650117721445123861 372341139849268192740181)
                  ·
                    rfl

theorem cell22_3263093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 6].length) (baseStart_3263093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3263093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3263093 prefixEnd_3263093 := by exact prefixLift 3263093
  have htrace : WordTrace (prefixWord ++ tailWord_3263093) baseStart_3263093 baseEnd_3263093 := by
    simpa [prefixWord, tailWord_3263093, baseEnd_3263093] using wordTrace_append hprefix tailTrace_3263093
  have hstable : (prefixWord ++ tailWord_3263093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263093).length < 2 ^ (prefixWord ++ tailWord_3263093).sum := by decide
  have hdescent : baseEnd_3263093 < baseStart_3263093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263166 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 9]
def baseStart_3263166 : Nat := 118140960795 + 3263166 * 2 ^ 59
def prefixEnd_3263166 : Nat := 4983230072969 + 3 ^ 40 * 3263166 * 2
def baseEnd_3263166 : Nat := 372349469646552240381773

theorem tailTrace_3263166 : CollatzResearch.WordTrace tailWord_3263166 prefixEnd_3263166 372349469646552240381773 := by
  unfold tailWord_3263166
  simp only [CollatzResearch.WordTrace]
  refine ⟨14877180212014295153580169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79344961130742907485760901 14877180212014295153580169)
  ·
    refine ⟨11157885159010721365185127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14877180212014295153580169 11157885159010721365185127)
    ·
      refine ⟨16736827738516082047777691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11157885159010721365185127 16736827738516082047777691)
      ·
        refine ⟨25105241607774123071666537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16736827738516082047777691 25105241607774123071666537)
        ·
          refine ⟨18828931205830592303749903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25105241607774123071666537 18828931205830592303749903)
          ·
            refine ⟨28243396808745888455624855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18828931205830592303749903 28243396808745888455624855)
            ·
              refine ⟨42365095213118832683437283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28243396808745888455624855 42365095213118832683437283)
              ·
                refine ⟨63547642819678249025155925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42365095213118832683437283 63547642819678249025155925)
                ·
                  refine ⟨372349469646552240381773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 63547642819678249025155925 372349469646552240381773)
                  ·
                    rfl

theorem cell22_3263166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_3263166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3263166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3263166 prefixEnd_3263166 := by exact prefixLift 3263166
  have htrace : WordTrace (prefixWord ++ tailWord_3263166) baseStart_3263166 baseEnd_3263166 := by
    simpa [prefixWord, tailWord_3263166, baseEnd_3263166] using wordTrace_append hprefix tailTrace_3263166
  have hstable : (prefixWord ++ tailWord_3263166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263166).length < 2 ^ (prefixWord ++ tailWord_3263166).sum := by decide
  have hdescent : baseEnd_3263166 < baseStart_3263166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263213 : List Nat := [1, 5, 1, 2, 1, 1, 3, 1, 3, 4]
def baseStart_3263213 : Nat := 118140960795 + 3263213 * 2 ^ 59
def prefixEnd_3263213 : Nat := 4983230072969 + 3 ^ 40 * 3263213 * 2
def baseEnd_3263213 : Nat := 1117064498000164265220175

theorem tailTrace_3263213 : CollatzResearch.WordTrace tailWord_3263213 prefixEnd_3263213 1117064498000164265220175 := by
  unfold tailWord_3263213
  simp only [CollatzResearch.WordTrace]
  refine ⟨119019155926944088255602293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79346103951296058837068195 119019155926944088255602293)
  ·
    refine ⟨11158045868151008273962715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119019155926944088255602293 11158045868151008273962715)
    ·
      refine ⟨16737068802226512410944073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11158045868151008273962715 16737068802226512410944073)
      ·
        refine ⟨12552801601669884308208055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16737068802226512410944073 12552801601669884308208055)
        ·
          refine ⟨18829202402504826462312083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12552801601669884308208055 18829202402504826462312083)
          ·
            refine ⟨28243803603757239693468125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18829202402504826462312083 28243803603757239693468125)
            ·
              refine ⟨10591426351408964885050547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28243803603757239693468125 10591426351408964885050547)
              ·
                refine ⟨15887139527113447327575821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10591426351408964885050547 15887139527113447327575821)
                ·
                  refine ⟨5957677322667542747840933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15887139527113447327575821 5957677322667542747840933)
                  ·
                    refine ⟨1117064498000164265220175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5957677322667542747840933 1117064498000164265220175)
                    ·
                      rfl

theorem cell22_3263213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_3263213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3263213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3263213 prefixEnd_3263213 := by exact prefixLift 3263213
  have htrace : WordTrace (prefixWord ++ tailWord_3263213) baseStart_3263213 baseEnd_3263213 := by
    simpa [prefixWord, tailWord_3263213, baseEnd_3263213] using wordTrace_append hprefix tailTrace_3263213
  have hstable : (prefixWord ++ tailWord_3263213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263213).length < 2 ^ (prefixWord ++ tailWord_3263213).sum := by decide
  have hdescent : baseEnd_3263213 < baseStart_3263213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263226 : List Nat := [3, 1, 1, 1, 1, 3, 3, 1, 3, 5]
def baseStart_3263226 : Nat := 118140960795 + 3263226 * 2 ^ 59
def prefixEnd_3263226 : Nat := 4983230072969 + 3 ^ 40 * 3263226 * 2
def baseEnd_3263226 : Nat := 1117068948165836564645135

theorem tailTrace_3263226 : CollatzResearch.WordTrace tailWord_3263226 prefixEnd_3263226 1117068948165836564645135 := by
  unfold tailWord_3263226
  simp only [CollatzResearch.WordTrace]
  refine ⟨29754907518974247868956383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79346420050597994317217021 29754907518974247868956383)
  ·
    refine ⟨44632361278461371803434575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29754907518974247868956383 44632361278461371803434575)
    ·
      refine ⟨66948541917692057705151863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44632361278461371803434575 66948541917692057705151863)
      ·
        refine ⟨100422812876538086557727795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66948541917692057705151863 100422812876538086557727795)
        ·
          refine ⟨150634219314807129836591693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100422812876538086557727795 150634219314807129836591693)
          ·
            refine ⟨56487832243052673688721885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150634219314807129836591693 56487832243052673688721885)
            ·
              refine ⟨21182937091144752633270707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56487832243052673688721885 21182937091144752633270707)
              ·
                refine ⟨31774405636717128949906061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21182937091144752633270707 31774405636717128949906061)
                ·
                  refine ⟨11915402113768923356214773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31774405636717128949906061 11915402113768923356214773)
                  ·
                    refine ⟨1117068948165836564645135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11915402113768923356214773 1117068948165836564645135)
                    ·
                      rfl

theorem cell22_3263226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_3263226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3263226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3263226 prefixEnd_3263226 := by exact prefixLift 3263226
  have htrace : WordTrace (prefixWord ++ tailWord_3263226) baseStart_3263226 baseEnd_3263226 := by
    simpa [prefixWord, tailWord_3263226, baseEnd_3263226] using wordTrace_append hprefix tailTrace_3263226
  have hstable : (prefixWord ++ tailWord_3263226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263226).length < 2 ^ (prefixWord ++ tailWord_3263226).sum := by decide
  have hdescent : baseEnd_3263226 < baseStart_3263226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263260 : List Nat := [2, 2, 3, 1, 1, 3, 2, 3, 2, 3]
def baseStart_3263260 : Nat := 118140960795 + 3263260 * 2 ^ 59
def prefixEnd_3263260 : Nat := 4983230072969 + 3 ^ 40 * 3263260 * 2
def baseEnd_3263260 : Nat := 1117080587060671809295031

theorem tailTrace_3263260 : CollatzResearch.WordTrace tailWord_3263260 prefixEnd_3263260 1117080587060671809295031 := by
  unfold tailWord_3263260
  simp only [CollatzResearch.WordTrace]
  refine ⟨59510435078886907641281617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79347246771849210188375489 59510435078886907641281617)
  ·
    refine ⟨44632826309165180730961213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59510435078886907641281617 44632826309165180730961213)
    ·
      refine ⟨16737309865936942774110455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44632826309165180730961213 16737309865936942774110455)
      ·
        refine ⟨25105964798905414161165683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16737309865936942774110455 25105964798905414161165683)
        ·
          refine ⟨37658947198358121241748525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25105964798905414161165683 37658947198358121241748525)
          ·
            refine ⟨14122105199384295465655697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37658947198358121241748525 14122105199384295465655697)
            ·
              refine ⟨10591578899538221599241773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14122105199384295465655697 10591578899538221599241773)
              ·
                refine ⟨3971842087326833099715665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10591578899538221599241773 3971842087326833099715665)
                ·
                  refine ⟨2978881565495124824786749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3971842087326833099715665 2978881565495124824786749)
                  ·
                    refine ⟨1117080587060671809295031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2978881565495124824786749 1117080587060671809295031)
                    ·
                      rfl

theorem cell22_3263260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_3263260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3263260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3263260 prefixEnd_3263260 := by exact prefixLift 3263260
  have htrace : WordTrace (prefixWord ++ tailWord_3263260) baseStart_3263260 baseEnd_3263260 := by
    simpa [prefixWord, tailWord_3263260, baseEnd_3263260] using wordTrace_append hprefix tailTrace_3263260
  have hstable : (prefixWord ++ tailWord_3263260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263260).length < 2 ^ (prefixWord ++ tailWord_3263260).sum := by decide
  have hdescent : baseEnd_3263260 < baseStart_3263260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263288 : List Nat := [2, 1, 2, 1, 3, 2, 1, 2, 5, 3]
def baseStart_3263288 : Nat := 118140960795 + 3263288 * 2 ^ 59
def prefixEnd_3263288 : Nat := 4983230072969 + 3 ^ 40 * 3263288 * 2
def baseEnd_3263288 : Nat := 1117090172032889069594945

theorem tailTrace_3263288 : CollatzResearch.WordTrace tailWord_3263288 prefixEnd_3263288 1117090172032889069594945 := by
  unfold tailWord_3263288
  simp only [CollatzResearch.WordTrace]
  refine ⟨59510945700836188032291259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79347927601114917376388345 59510945700836188032291259)
  ·
    refine ⟨89266418551254282048436889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59510945700836188032291259 89266418551254282048436889)
    ·
      refine ⟨66949813913440711536327667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89266418551254282048436889 66949813913440711536327667)
      ·
        refine ⟨100424720870161067304491501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66949813913440711536327667 100424720870161067304491501)
        ·
          refine ⟨37659270326310400239184313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100424720870161067304491501 37659270326310400239184313)
          ·
            refine ⟨28244452744732800179388235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37659270326310400239184313 28244452744732800179388235)
            ·
              refine ⟨42366679117099200269082353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28244452744732800179388235 42366679117099200269082353)
              ·
                refine ⟨31775009337824400201811765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42366679117099200269082353 31775009337824400201811765)
                ·
                  refine ⟨2978907125421037518919853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31775009337824400201811765 2978907125421037518919853)
                  ·
                    refine ⟨1117090172032889069594945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2978907125421037518919853 1117090172032889069594945)
                    ·
                      rfl

theorem cell22_3263288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 5, 3].length) (baseStart_3263288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3263288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3263288 prefixEnd_3263288 := by exact prefixLift 3263288
  have htrace : WordTrace (prefixWord ++ tailWord_3263288) baseStart_3263288 baseEnd_3263288 := by
    simpa [prefixWord, tailWord_3263288, baseEnd_3263288] using wordTrace_append hprefix tailTrace_3263288
  have hstable : (prefixWord ++ tailWord_3263288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263288).length < 2 ^ (prefixWord ++ tailWord_3263288).sum := by decide
  have hdescent : baseEnd_3263288 < baseStart_3263288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263294 : List Nat := [4, 2, 1, 2, 3, 2, 1, 2, 2, 3]
def baseStart_3263294 : Nat := 118140960795 + 3263294 * 2 ^ 59
def prefixEnd_3263294 : Nat := 4983230072969 + 3 ^ 40 * 3263294 * 2
def baseEnd_3263294 : Nat := 1117092225955507053944927

theorem tailTrace_3263294 : CollatzResearch.WordTrace tailWord_3263294 prefixEnd_3263294 1117092225955507053944927 := by
  unfold tailWord_3263294
  simp only [CollatzResearch.WordTrace]
  refine ⟨14877763779956329886162617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79348073493100426059533957 14877763779956329886162617)
  ·
    refine ⟨11158322834967247414621963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14877763779956329886162617 11158322834967247414621963)
    ·
      refine ⟨16737484252450871121932945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11158322834967247414621963 16737484252450871121932945)
      ·
        refine ⟨12553113189338153341449709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16737484252450871121932945 12553113189338153341449709)
        ·
          refine ⟨4707417446001807503043641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12553113189338153341449709 4707417446001807503043641)
          ·
            refine ⟨3530563084501355627282731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4707417446001807503043641 3530563084501355627282731)
            ·
              refine ⟨5295844626752033440924097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3530563084501355627282731 5295844626752033440924097)
              ·
                refine ⟨3971883470064025080693073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5295844626752033440924097 3971883470064025080693073)
                ·
                  refine ⟨2978912602548018810519805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3971883470064025080693073 2978912602548018810519805)
                  ·
                    refine ⟨1117092225955507053944927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2978912602548018810519805 1117092225955507053944927)
                    ·
                      rfl

theorem cell22_3263294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_3263294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3263294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3263294 prefixEnd_3263294 := by exact prefixLift 3263294
  have htrace : WordTrace (prefixWord ++ tailWord_3263294) baseStart_3263294 baseEnd_3263294 := by
    simpa [prefixWord, tailWord_3263294, baseEnd_3263294] using wordTrace_append hprefix tailTrace_3263294
  have hstable : (prefixWord ++ tailWord_3263294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263294).length < 2 ^ (prefixWord ++ tailWord_3263294).sum := by decide
  have hdescent : baseEnd_3263294 < baseStart_3263294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263305 : List Nat := [1, 2, 1, 1, 2, 6, 2, 1, 3, 3]
def baseStart_3263305 : Nat := 118140960795 + 3263305 * 2 ^ 59
def prefixEnd_3263305 : Nat := 4983230072969 + 3 ^ 40 * 3263305 * 2
def baseEnd_3263305 : Nat := 1117095991480306691919893

theorem tailTrace_3263305 : CollatzResearch.WordTrace tailWord_3263305 prefixEnd_3263305 1117095991480306691919893 := by
  unfold tailWord_3263305
  simp only [CollatzResearch.WordTrace]
  refine ⟨119022511442610787967951369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79348340961740525311967579 119022511442610787967951369)
  ·
    refine ⟨89266883581958090975963527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119022511442610787967951369 89266883581958090975963527)
    ·
      refine ⟨133900325372937136463945291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89266883581958090975963527 133900325372937136463945291)
      ·
        refine ⟨200850488059405704695917937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133900325372937136463945291 200850488059405704695917937)
        ·
          refine ⟨150637866044554278521938453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200850488059405704695917937 150637866044554278521938453)
          ·
            refine ⟨7061149970838481805715865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 150637866044554278521938453 7061149970838481805715865)
            ·
              refine ⟨5295862478128861354286899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7061149970838481805715865 5295862478128861354286899)
              ·
                refine ⟨7943793717193292031430349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5295862478128861354286899 7943793717193292031430349)
                ·
                  refine ⟨2978922643947484511786381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7943793717193292031430349 2978922643947484511786381)
                  ·
                    refine ⟨1117095991480306691919893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2978922643947484511786381 1117095991480306691919893)
                    ·
                      rfl

theorem cell22_3263305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 3, 3].length) (baseStart_3263305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3263305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3263305 prefixEnd_3263305 := by exact prefixLift 3263305
  have htrace : WordTrace (prefixWord ++ tailWord_3263305) baseStart_3263305 baseEnd_3263305 := by
    simpa [prefixWord, tailWord_3263305, baseEnd_3263305] using wordTrace_append hprefix tailTrace_3263305
  have hstable : (prefixWord ++ tailWord_3263305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263305).length < 2 ^ (prefixWord ++ tailWord_3263305).sum := by decide
  have hdescent : baseEnd_3263305 < baseStart_3263305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263399 : List Nat := [1, 1, 6, 1, 3, 1, 3, 1, 1, 4]
def baseStart_3263399 : Nat := 118140960795 + 3263399 * 2 ^ 59
def prefixEnd_3263399 : Nat := 4983230072969 + 3 ^ 40 * 3263399 * 2
def baseEnd_3263399 : Nat := 1117128169601321780069605

theorem tailTrace_3263399 : CollatzResearch.WordTrace tailWord_3263399 prefixEnd_3263399 1117128169601321780069605 := by
  unfold tailWord_3263399
  simp only [CollatzResearch.WordTrace]
  refine ⟨119025939904270242021873251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79350626602846828014582167 119025939904270242021873251)
  ·
    refine ⟨178538909856405363032809877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119025939904270242021873251 178538909856405363032809877)
    ·
      refine ⟨8369011399519001392162963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 178538909856405363032809877 8369011399519001392162963)
      ·
        refine ⟨12553517099278502088244445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8369011399519001392162963 12553517099278502088244445)
        ·
          refine ⟨4707568912229438283091667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12553517099278502088244445 4707568912229438283091667)
          ·
            refine ⟨7061353368344157424637501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4707568912229438283091667 7061353368344157424637501)
            ·
              refine ⟨2648007513129059034239063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7061353368344157424637501 2648007513129059034239063)
              ·
                refine ⟨3972011269693588551358595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2648007513129059034239063 3972011269693588551358595)
                ·
                  refine ⟨5958016904540382827037893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3972011269693588551358595 5958016904540382827037893)
                  ·
                    refine ⟨1117128169601321780069605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5958016904540382827037893 1117128169601321780069605)
                    ·
                      rfl

theorem cell22_3263399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_3263399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3263399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3263399 prefixEnd_3263399 := by exact prefixLift 3263399
  have htrace : WordTrace (prefixWord ++ tailWord_3263399) baseStart_3263399 baseEnd_3263399 := by
    simpa [prefixWord, tailWord_3263399, baseEnd_3263399] using wordTrace_append hprefix tailTrace_3263399
  have hstable : (prefixWord ++ tailWord_3263399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263399).length < 2 ^ (prefixWord ++ tailWord_3263399).sum := by decide
  have hdescent : baseEnd_3263399 < baseStart_3263399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263442 : List Nat := [3, 2, 2, 3, 1, 2, 3, 6]
def baseStart_3263442 : Nat := 118140960795 + 3263442 * 2 ^ 59
def prefixEnd_3263442 : Nat := 4983230072969 + 3 ^ 40 * 3263442 * 2
def baseEnd_3263442 : Nat := 124126987708898222360497

theorem tailTrace_3263442 : CollatzResearch.WordTrace tailWord_3263442 prefixEnd_3263442 124126987708898222360497 := by
  unfold tailWord_3263442
  simp only [CollatzResearch.WordTrace]
  refine ⟨29756877060778615091422145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79351672162076306910459053 29756877060778615091422145)
  ·
    refine ⟨22317657795583961318566609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29756877060778615091422145 22317657795583961318566609)
    ·
      refine ⟨16738243346687970988924957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22317657795583961318566609 16738243346687970988924957)
      ·
        refine ⟨6276841255007989120846859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16738243346687970988924957 6276841255007989120846859)
        ·
          refine ⟨9415261882511983681270289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6276841255007989120846859 9415261882511983681270289)
          ·
            refine ⟨7061446411883987760952717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9415261882511983681270289 7061446411883987760952717)
            ·
              refine ⟨2648042404456495410357269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7061446411883987760952717 2648042404456495410357269)
              ·
                refine ⟨124126987708898222360497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2648042404456495410357269 124126987708898222360497)
                ·
                  rfl

theorem cell22_3263442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 6].length) (baseStart_3263442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3263442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3263442 prefixEnd_3263442 := by exact prefixLift 3263442
  have htrace : WordTrace (prefixWord ++ tailWord_3263442) baseStart_3263442 baseEnd_3263442 := by
    simpa [prefixWord, tailWord_3263442, baseEnd_3263442] using wordTrace_append hprefix tailTrace_3263442
  have hstable : (prefixWord ++ tailWord_3263442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263442).length < 2 ^ (prefixWord ++ tailWord_3263442).sum := by decide
  have hdescent : baseEnd_3263442 < baseStart_3263442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263609 : List Nat := [1, 2, 1, 3, 5, 1, 1, 2, 3, 3]
def baseStart_3263609 : Nat := 118140960795 + 3263609 * 2 ^ 59
def prefixEnd_3263609 : Nat := 4983230072969 + 3 ^ 40 * 3263609 * 2
def baseEnd_3263609 : Nat := 1117200056892951232318961

theorem tailTrace_3263609 : CollatzResearch.WordTrace tailWord_3263609 prefixEnd_3263609 1117200056892951232318961 := by
  unfold tailWord_3263609
  simp only [CollatzResearch.WordTrace]
  refine ⟨119033599233509447887017881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79355732822339631924678587 119033599233509447887017881)
  ·
    refine ⟨89275199425132085915263411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119033599233509447887017881 89275199425132085915263411)
    ·
      refine ⟨133912799137698128872895117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89275199425132085915263411 133912799137698128872895117)
      ·
        refine ⟨50217299676636798327335669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133912799137698128872895117 50217299676636798327335669)
        ·
          refine ⟨4707871844684699843187719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50217299676636798327335669 4707871844684699843187719)
          ·
            refine ⟨7061807767027049764781579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4707871844684699843187719 7061807767027049764781579)
            ·
              refine ⟨10592711650540574647172369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7061807767027049764781579 10592711650540574647172369)
              ·
                refine ⟨7944533737905430985379277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10592711650540574647172369 7944533737905430985379277)
                ·
                  refine ⟨2979200151714536619517229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7944533737905430985379277 2979200151714536619517229)
                  ·
                    refine ⟨1117200056892951232318961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2979200151714536619517229 1117200056892951232318961)
                    ·
                      rfl

theorem cell22_3263609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 3, 3].length) (baseStart_3263609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3263609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3263609 prefixEnd_3263609 := by exact prefixLift 3263609
  have htrace : WordTrace (prefixWord ++ tailWord_3263609) baseStart_3263609 baseEnd_3263609 := by
    simpa [prefixWord, tailWord_3263609, baseEnd_3263609] using wordTrace_append hprefix tailTrace_3263609
  have hstable : (prefixWord ++ tailWord_3263609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263609).length < 2 ^ (prefixWord ++ tailWord_3263609).sum := by decide
  have hdescent : baseEnd_3263609 < baseStart_3263609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263626 : List Nat := [3, 1, 2, 3, 1, 1, 4, 3, 1, 3]
def baseStart_3263626 : Nat := 118140960795 + 3263626 * 2 ^ 59
def prefixEnd_3263626 : Nat := 4983230072969 + 3 ^ 40 * 3263626 * 2
def baseEnd_3263626 : Nat := 1117205876340368854643909

theorem tailTrace_3263626 : CollatzResearch.WordTrace tailWord_3263626 prefixEnd_3263626 1117205876340368854643909 := by
  unfold tailWord_3263626
  simp only [CollatzResearch.WordTrace]
  refine ⟨29758554818611964947596683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79356146182965239860257821 29758554818611964947596683)
  ·
    refine ⟨44637832227917947421395025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29758554818611964947596683 44637832227917947421395025)
    ·
      refine ⟨33478374170938460566046269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44637832227917947421395025 33478374170938460566046269)
      ·
        refine ⟨12554390314101922712267351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33478374170938460566046269 12554390314101922712267351)
        ·
          refine ⟨18831585471152884068401027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12554390314101922712267351 18831585471152884068401027)
          ·
            refine ⟨28247378206729326102601541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18831585471152884068401027 28247378206729326102601541)
            ·
              refine ⟨5296383413761748644237789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28247378206729326102601541 5296383413761748644237789)
              ·
                refine ⟨1986143780160655741589171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5296383413761748644237789 1986143780160655741589171)
                ·
                  refine ⟨2979215670240983612383757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1986143780160655741589171 2979215670240983612383757)
                  ·
                    refine ⟨1117205876340368854643909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2979215670240983612383757 1117205876340368854643909)
                    ·
                      rfl

theorem cell22_3263626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 3, 1, 3].length) (baseStart_3263626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3263626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3263626 prefixEnd_3263626 := by exact prefixLift 3263626
  have htrace : WordTrace (prefixWord ++ tailWord_3263626) baseStart_3263626 baseEnd_3263626 := by
    simpa [prefixWord, tailWord_3263626, baseEnd_3263626] using wordTrace_append hprefix tailTrace_3263626
  have hstable : (prefixWord ++ tailWord_3263626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263626).length < 2 ^ (prefixWord ++ tailWord_3263626).sum := by decide
  have hdescent : baseEnd_3263626 < baseStart_3263626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263639 : List Nat := [1, 1, 3, 3, 3, 3, 1, 2, 5]
def baseStart_3263639 : Nat := 118140960795 + 3263639 * 2 ^ 59
def prefixEnd_3263639 : Nat := 4983230072969 + 3 ^ 40 * 3263639 * 2
def baseEnd_3263639 : Nat := 372403442168680384689623

theorem tailTrace_3263639 : CollatzResearch.WordTrace tailWord_3263639 prefixEnd_3263639 372403442168680384689623 := by
  unfold tailWord_3263639
  simp only [CollatzResearch.WordTrace]
  refine ⟨119034693423400763010609971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79356462282267175340406647 119034693423400763010609971)
  ·
    refine ⟨178552040135101144515914957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119034693423400763010609971 178552040135101144515914957)
    ·
      refine ⟨66957015050662929193468109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178552040135101144515914957 66957015050662929193468109)
      ·
        refine ⟨25108880643998598447550541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66957015050662929193468109 25108880643998598447550541)
        ·
          refine ⟨9415830241499474417831453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25108880643998598447550541 9415830241499474417831453)
          ·
            refine ⟨3530936340562302906686795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9415830241499474417831453 3530936340562302906686795)
            ·
              refine ⟨5296404510843454360030193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3530936340562302906686795 5296404510843454360030193)
              ·
                refine ⟨3972303383132590770022645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5296404510843454360030193 3972303383132590770022645)
                ·
                  refine ⟨372403442168680384689623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3972303383132590770022645 372403442168680384689623)
                  ·
                    rfl

theorem cell22_3263639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 5].length) (baseStart_3263639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3263639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3263639 prefixEnd_3263639 := by exact prefixLift 3263639
  have htrace : WordTrace (prefixWord ++ tailWord_3263639) baseStart_3263639 baseEnd_3263639 := by
    simpa [prefixWord, tailWord_3263639, baseEnd_3263639] using wordTrace_append hprefix tailTrace_3263639
  have hstable : (prefixWord ++ tailWord_3263639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263639).length < 2 ^ (prefixWord ++ tailWord_3263639).sum := by decide
  have hdescent : baseEnd_3263639 < baseStart_3263639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263712 : List Nat := [2, 1, 1, 3, 1, 5, 2, 7]
def baseStart_3263712 : Nat := 118140960795 + 3263712 * 2 ^ 59
def prefixEnd_3263712 : Nat := 4983230072969 + 3 ^ 40 * 3263712 * 2
def baseEnd_3263712 : Nat := 124137257321988144110405

theorem tailTrace_3263712 : CollatzResearch.WordTrace tailWord_3263712 prefixEnd_3263712 124137257321988144110405 := by
  unfold tailWord_3263712
  simp only [CollatzResearch.WordTrace]
  refine ⟨59518677976068148239008695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79358237301424197652011593 59518677976068148239008695)
  ·
    refine ⟨89278016964102222358513043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59518677976068148239008695 89278016964102222358513043)
    ·
      refine ⟨133917025446153333537769565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89278016964102222358513043 133917025446153333537769565)
      ·
        refine ⟨50218884542307500076663587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133917025446153333537769565 50218884542307500076663587)
        ·
          refine ⟨75328326813461250114995381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50218884542307500076663587 75328326813461250114995381)
          ·
            refine ⟨7062030638761992198280817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75328326813461250114995381 7062030638761992198280817)
            ·
              refine ⟨5296522979071494148710613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7062030638761992198280817 5296522979071494148710613)
              ·
                refine ⟨124137257321988144110405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5296522979071494148710613 124137257321988144110405)
                ·
                  rfl

theorem cell22_3263712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 7].length) (baseStart_3263712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3263712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3263712 prefixEnd_3263712 := by exact prefixLift 3263712
  have htrace : WordTrace (prefixWord ++ tailWord_3263712) baseStart_3263712 baseEnd_3263712 := by
    simpa [prefixWord, tailWord_3263712, baseEnd_3263712] using wordTrace_append hprefix tailTrace_3263712
  have hstable : (prefixWord ++ tailWord_3263712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263712).length < 2 ^ (prefixWord ++ tailWord_3263712).sum := by decide
  have hdescent : baseEnd_3263712 < baseStart_3263712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263716 : List Nat := [2, 3, 1, 1, 1, 2, 6, 1, 2, 3]
def baseStart_3263716 : Nat := 118140960795 + 3263716 * 2 ^ 59
def prefixEnd_3263716 : Nat := 4983230072969 + 3 ^ 40 * 3263716 * 2
def baseEnd_3263716 : Nat := 1117236685179638619893633

theorem tailTrace_3263716 : CollatzResearch.WordTrace tailWord_3263716 prefixEnd_3263716 1117236685179638619893633 := by
  unfold tailWord_3263716
  simp only [CollatzResearch.WordTrace]
  refine ⟨59518750922060902580581501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79358334562747870107442001 59518750922060902580581501)
  ·
    refine ⟨22319531595772838467718063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59518750922060902580581501 22319531595772838467718063)
    ·
      refine ⟨33479297393659257701577095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22319531595772838467718063 33479297393659257701577095)
      ·
        refine ⟨50218946090488886552365643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33479297393659257701577095 50218946090488886552365643)
        ·
          refine ⟨75328419135733329828548465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50218946090488886552365643 75328419135733329828548465)
          ·
            refine ⟨56496314351799997371411349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75328419135733329828548465 56496314351799997371411349)
            ·
              refine ⟨2648264735240624876784907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56496314351799997371411349 2648264735240624876784907)
              ·
                refine ⟨3972397102860937315177361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2648264735240624876784907 3972397102860937315177361)
                ·
                  refine ⟨2979297827145702986383021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3972397102860937315177361 2979297827145702986383021)
                  ·
                    refine ⟨1117236685179638619893633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2979297827145702986383021 1117236685179638619893633)
                    ·
                      rfl

theorem cell22_3263716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 2, 3].length) (baseStart_3263716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3263716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3263716 prefixEnd_3263716 := by exact prefixLift 3263716
  have htrace : WordTrace (prefixWord ++ tailWord_3263716) baseStart_3263716 baseEnd_3263716 := by
    simpa [prefixWord, tailWord_3263716, baseEnd_3263716] using wordTrace_append hprefix tailTrace_3263716
  have hstable : (prefixWord ++ tailWord_3263716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263716).length < 2 ^ (prefixWord ++ tailWord_3263716).sum := by decide
  have hdescent : baseEnd_3263716 < baseStart_3263716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263761 : List Nat := [1, 2, 2, 1, 1, 4, 3, 4, 1, 3]
def baseStart_3263761 : Nat := 118140960795 + 3263761 * 2 ^ 59
def prefixEnd_3263761 : Nat := 4983230072969 + 3 ^ 40 * 3263761 * 2
def baseEnd_3263761 : Nat := 1117252089599273502518495

theorem tailTrace_3263761 : CollatzResearch.WordTrace tailWord_3263761 prefixEnd_3263761 1117252089599273502518495 := by
  unfold tailWord_3263761
  simp only [CollatzResearch.WordTrace]
  refine ⟨119039143128958777846551137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79359428752639185231034091 119039143128958777846551137)
  ·
    refine ⟨89279357346719083384913353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119039143128958777846551137 89279357346719083384913353)
    ·
      refine ⟨66959518010039312538685015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89279357346719083384913353 66959518010039312538685015)
      ·
        refine ⟨100439277015058968808027523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66959518010039312538685015 100439277015058968808027523)
        ·
          refine ⟨150658915522588453212041285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100439277015058968808027523 150658915522588453212041285)
          ·
            refine ⟨28248546660485334977257741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150658915522588453212041285 28248546660485334977257741)
            ·
              refine ⟨10593204997682000616471653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28248546660485334977257741 10593204997682000616471653)
              ·
                refine ⟨1986225937065375115588435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10593204997682000616471653 1986225937065375115588435)
                ·
                  refine ⟨2979338905598062673382653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1986225937065375115588435 2979338905598062673382653)
                  ·
                    refine ⟨1117252089599273502518495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2979338905598062673382653 1117252089599273502518495)
                    ·
                      rfl

theorem cell22_3263761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 4, 1, 3].length) (baseStart_3263761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3263761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3263761 prefixEnd_3263761 := by exact prefixLift 3263761
  have htrace : WordTrace (prefixWord ++ tailWord_3263761) baseStart_3263761 baseEnd_3263761 := by
    simpa [prefixWord, tailWord_3263761, baseEnd_3263761] using wordTrace_append hprefix tailTrace_3263761
  have hstable : (prefixWord ++ tailWord_3263761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263761).length < 2 ^ (prefixWord ++ tailWord_3263761).sum := by decide
  have hdescent : baseEnd_3263761 < baseStart_3263761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263772 : List Nat := [2, 2, 3, 1, 1, 1, 3, 1, 1, 7]
def baseStart_3263772 : Nat := 118140960795 + 3263772 * 2 ^ 59
def prefixEnd_3263772 : Nat := 4983230072969 + 3 ^ 40 * 3263772 * 2
def baseEnd_3263772 : Nat := 1117255855124073140493461

theorem tailTrace_3263772 : CollatzResearch.WordTrace tailWord_3263772 prefixEnd_3263772 1117255855124073140493461 := by
  unfold tailWord_3263772
  simp only [CollatzResearch.WordTrace]
  refine ⟨59519772165959463362600785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79359696221279284483467713 59519772165959463362600785)
  ·
    refine ⟨44639829124469597521950589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59519772165959463362600785 44639829124469597521950589)
    ·
      refine ⟨16739935921676099070731471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44639829124469597521950589 16739935921676099070731471)
      ·
        refine ⟨25109903882514148606097207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16739935921676099070731471 25109903882514148606097207)
        ·
          refine ⟨37664855823771222909145811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25109903882514148606097207 37664855823771222909145811)
          ·
            refine ⟨56497283735656834363718717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37664855823771222909145811 56497283735656834363718717)
            ·
              refine ⟨21186481400871312886394519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56497283735656834363718717 21186481400871312886394519)
              ·
                refine ⟨31779722101306969329591779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21186481400871312886394519 31779722101306969329591779)
                ·
                  refine ⟨47669583151960453994387669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31779722101306969329591779 47669583151960453994387669)
                  ·
                    refine ⟨1117255855124073140493461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47669583151960453994387669 1117255855124073140493461)
                    ·
                      rfl

theorem cell22_3263772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_3263772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3263772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3263772 prefixEnd_3263772 := by exact prefixLift 3263772
  have htrace : WordTrace (prefixWord ++ tailWord_3263772) baseStart_3263772 baseEnd_3263772 := by
    simpa [prefixWord, tailWord_3263772, baseEnd_3263772] using wordTrace_append hprefix tailTrace_3263772
  have hstable : (prefixWord ++ tailWord_3263772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263772).length < 2 ^ (prefixWord ++ tailWord_3263772).sum := by decide
  have hdescent : baseEnd_3263772 < baseStart_3263772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263802 : List Nat := [3, 1, 1, 1, 4, 1, 1, 2, 8]
def baseStart_3263802 : Nat := 118140960795 + 3263802 * 2 ^ 59
def prefixEnd_3263802 : Nat := 4983230072969 + 3 ^ 40 * 3263802 * 2
def baseEnd_3263802 : Nat := 372422041579054354081123

theorem tailTrace_3263802 : CollatzResearch.WordTrace tailWord_3263802 prefixEnd_3263802 372422041579054354081123 := by
  unfold tailWord_3263802
  simp only [CollatzResearch.WordTrace]
  refine ⟨29760159630452560462198415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79360425681206827899195773 29760159630452560462198415)
  ·
    refine ⟨44640239445678840693297623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29760159630452560462198415 44640239445678840693297623)
    ·
      refine ⟨66960359168518261039946435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44640239445678840693297623 66960359168518261039946435)
      ·
        refine ⟨100440538752777391559919653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66960359168518261039946435 100440538752777391559919653)
        ·
          refine ⟨18832601016145760917484935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100440538752777391559919653 18832601016145760917484935)
          ·
            refine ⟨28248901524218641376227403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18832601016145760917484935 28248901524218641376227403)
            ·
              refine ⟨42373352286327962064341105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28248901524218641376227403 42373352286327962064341105)
              ·
                refine ⟨31780014214745971548255829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42373352286327962064341105 31780014214745971548255829)
                ·
                  refine ⟨372422041579054354081123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31780014214745971548255829 372422041579054354081123)
                  ·
                    rfl

theorem cell22_3263802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 8].length) (baseStart_3263802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3263802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3263802 prefixEnd_3263802 := by exact prefixLift 3263802
  have htrace : WordTrace (prefixWord ++ tailWord_3263802) baseStart_3263802 baseEnd_3263802 := by
    simpa [prefixWord, tailWord_3263802, baseEnd_3263802] using wordTrace_append hprefix tailTrace_3263802
  have hstable : (prefixWord ++ tailWord_3263802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263802).length < 2 ^ (prefixWord ++ tailWord_3263802).sum := by decide
  have hdescent : baseEnd_3263802 < baseStart_3263802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263817 : List Nat := [1, 2, 1, 1, 2, 3, 2, 2, 3, 5]
def baseStart_3263817 : Nat := 118140960795 + 3263817 * 2 ^ 59
def prefixEnd_3263817 : Nat := 4983230072969 + 3 ^ 40 * 3263817 * 2
def baseEnd_3263817 : Nat := 1117271259543708023118323

theorem tailTrace_3263817 : CollatzResearch.WordTrace tailWord_3263817 prefixEnd_3263817 1117271259543708023118323 := by
  unfold tailWord_3263817
  simp only [CollatzResearch.WordTrace]
  refine ⟨119041185616755899410589705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79360790411170599607059803 119041185616755899410589705)
  ·
    refine ⟨89280889212566924557942279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119041185616755899410589705 89280889212566924557942279)
    ·
      refine ⟨133921333818850386836913419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89280889212566924557942279 133921333818850386836913419)
      ·
        refine ⟨200882000728275580255370129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133921333818850386836913419 200882000728275580255370129)
        ·
          refine ⟨150661500546206685191527597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200882000728275580255370129 150661500546206685191527597)
          ·
            refine ⟨56498062704827506946822849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150661500546206685191527597 56498062704827506946822849)
            ·
              refine ⟨42373547028620630210117137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56498062704827506946822849 42373547028620630210117137)
              ·
                refine ⟨31780160271465472657587853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42373547028620630210117137 31780160271465472657587853)
                ·
                  refine ⟨11917560101799552246595445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31780160271465472657587853 11917560101799552246595445)
                  ·
                    refine ⟨1117271259543708023118323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11917560101799552246595445 1117271259543708023118323)
                    ·
                      rfl

theorem cell22_3263817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 5].length) (baseStart_3263817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3263817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3263817 prefixEnd_3263817 := by exact prefixLift 3263817
  have htrace : WordTrace (prefixWord ++ tailWord_3263817) baseStart_3263817 baseEnd_3263817 := by
    simpa [prefixWord, tailWord_3263817, baseEnd_3263817] using wordTrace_append hprefix tailTrace_3263817
  have hstable : (prefixWord ++ tailWord_3263817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263817).length < 2 ^ (prefixWord ++ tailWord_3263817).sum := by decide
  have hdescent : baseEnd_3263817 < baseStart_3263817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263832 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 3, 6]
def baseStart_3263832 : Nat := 118140960795 + 3263832 * 2 ^ 59
def prefixEnd_3263832 : Nat := 4983230072969 + 3 ^ 40 * 3263832 * 2
def baseEnd_3263832 : Nat := 1117276394350252983993277

theorem tailTrace_3263832 : CollatzResearch.WordTrace tailWord_3263832 prefixEnd_3263832 1117276394350252983993277 := by
  unfold tailWord_3263832
  simp only [CollatzResearch.WordTrace]
  refine ⟨59520866355850778486192875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79361155141134371314923833 59520866355850778486192875)
  ·
    refine ⟨89281299533776167729289313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59520866355850778486192875 89281299533776167729289313)
    ·
      refine ⟨66960974650332125796966985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89281299533776167729289313 66960974650332125796966985)
      ·
        refine ⟨50220730987749094347725239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66960974650332125796966985 50220730987749094347725239)
        ·
          refine ⟨75331096481623641521587859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50220730987749094347725239 75331096481623641521587859)
          ·
            refine ⟨112996644722435462282381789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75331096481623641521587859 112996644722435462282381789)
            ·
              refine ⟨42373741770913298355893171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112996644722435462282381789 42373741770913298355893171)
              ·
                refine ⟨63560612656369947533839757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42373741770913298355893171 63560612656369947533839757)
                ·
                  refine ⟨23835229746138730325189909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63560612656369947533839757 23835229746138730325189909)
                  ·
                    refine ⟨1117276394350252983993277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23835229746138730325189909 1117276394350252983993277)
                    ·
                      rfl

theorem cell22_3263832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_3263832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3263832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3263832 prefixEnd_3263832 := by exact prefixLift 3263832
  have htrace : WordTrace (prefixWord ++ tailWord_3263832) baseStart_3263832 baseEnd_3263832 := by
    simpa [prefixWord, tailWord_3263832, baseEnd_3263832] using wordTrace_append hprefix tailTrace_3263832
  have hstable : (prefixWord ++ tailWord_3263832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263832).length < 2 ^ (prefixWord ++ tailWord_3263832).sum := by decide
  have hdescent : baseEnd_3263832 < baseStart_3263832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263834 : List Nat := [3, 1, 1, 2, 1, 2, 5, 1, 1, 5]
def baseStart_3263834 : Nat := 118140960795 + 3263834 * 2 ^ 59
def prefixEnd_3263834 : Nat := 4983230072969 + 3 ^ 40 * 3263834 * 2
def baseEnd_3263834 : Nat := 1117277078991125645443271

theorem tailTrace_3263834 : CollatzResearch.WordTrace tailWord_3263834 prefixEnd_3263834 1117277078991125645443271 := by
  unfold tailWord_3263834
  simp only [CollatzResearch.WordTrace]
  refine ⟨29760451414423577828489639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79361203771796207542639037 29760451414423577828489639)
  ·
    refine ⟨44640677121635366742734459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29760451414423577828489639 44640677121635366742734459)
    ·
      refine ⟨66961015682453050114101689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44640677121635366742734459 66961015682453050114101689)
      ·
        refine ⟨50220761761839787585576267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66961015682453050114101689 50220761761839787585576267)
        ·
          refine ⟨75331142642759681378364401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50220761761839787585576267 75331142642759681378364401)
          ·
            refine ⟨56498356982069761033773301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75331142642759681378364401 56498356982069761033773301)
            ·
              refine ⟨5296720967069040096916247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56498356982069761033773301 5296720967069040096916247)
              ·
                refine ⟨7945081450603560145374371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5296720967069040096916247 7945081450603560145374371)
                ·
                  refine ⟨11917622175905340218061557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7945081450603560145374371 11917622175905340218061557)
                  ·
                    refine ⟨1117277078991125645443271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11917622175905340218061557 1117277078991125645443271)
                    ·
                      rfl

theorem cell22_3263834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 1, 5].length) (baseStart_3263834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3263834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3263834 prefixEnd_3263834 := by exact prefixLift 3263834
  have htrace : WordTrace (prefixWord ++ tailWord_3263834) baseStart_3263834 baseEnd_3263834 := by
    simpa [prefixWord, tailWord_3263834, baseEnd_3263834] using wordTrace_append hprefix tailTrace_3263834
  have hstable : (prefixWord ++ tailWord_3263834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263834).length < 2 ^ (prefixWord ++ tailWord_3263834).sum := by decide
  have hdescent : baseEnd_3263834 < baseStart_3263834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263853 : List Nat := [1, 5, 1, 1, 1, 5, 1, 3, 4]
def baseStart_3263853 : Nat := 118140960795 + 3263853 * 2 ^ 59
def prefixEnd_3263853 : Nat := 4983230072969 + 3 ^ 40 * 3263853 * 2
def baseEnd_3263853 : Nat := 372427861026471976406071

theorem tailTrace_3263853 : CollatzResearch.WordTrace tailWord_3263853 prefixEnd_3263853 372427861026471976406071 := by
  unfold tailWord_3263853
  simp only [CollatzResearch.WordTrace]
  refine ⟨119042498644625477558900213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79361665763083651705933475 119042498644625477558900213)
  ·
    refine ⟨11160234247933638521146895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119042498644625477558900213 11160234247933638521146895)
    ·
      refine ⟨16740351371900457781720343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11160234247933638521146895 16740351371900457781720343)
      ·
        refine ⟨25110527057850686672580515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16740351371900457781720343 25110527057850686672580515)
        ·
          refine ⟨37665790586776030008870773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25110527057850686672580515 37665790586776030008870773)
          ·
            refine ⟨3531167867510252813331635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37665790586776030008870773 3531167867510252813331635)
            ·
              refine ⟨5296751801265379219997453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3531167867510252813331635 5296751801265379219997453)
              ·
                refine ⟨1986281925474517207499045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5296751801265379219997453 1986281925474517207499045)
                ·
                  refine ⟨372427861026471976406071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1986281925474517207499045 372427861026471976406071)
                  ·
                    rfl

theorem cell22_3263853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_3263853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3263853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3263853 prefixEnd_3263853 := by exact prefixLift 3263853
  have htrace : WordTrace (prefixWord ++ tailWord_3263853) baseStart_3263853 baseEnd_3263853 := by
    simpa [prefixWord, tailWord_3263853, baseEnd_3263853] using wordTrace_append hprefix tailTrace_3263853
  have hstable : (prefixWord ++ tailWord_3263853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263853).length < 2 ^ (prefixWord ++ tailWord_3263853).sum := by decide
  have hdescent : baseEnd_3263853 < baseStart_3263853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263870 : List Nat := [4, 2, 3, 2, 1, 2, 1, 1, 6]
def baseStart_3263870 : Nat := 118140960795 + 3263870 * 2 ^ 59
def prefixEnd_3263870 : Nat := 4983230072969 + 3 ^ 40 * 3263870 * 2
def baseEnd_3263870 : Nat := 372429800842277850514387

theorem tailTrace_3263870 : CollatzResearch.WordTrace tailWord_3263870 prefixEnd_3263870 372429800842277850514387 := by
  unfold tailWord_3263870
  simp only [CollatzResearch.WordTrace]
  refine ⟨14880389835695486182783633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79362079123709259641512709 14880389835695486182783633)
  ·
    refine ⟨11160292376771614637087725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14880389835695486182783633 11160292376771614637087725)
    ·
      refine ⟨4185109641289355488907897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11160292376771614637087725 4185109641289355488907897)
      ·
        refine ⟨3138832230967016616680923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4185109641289355488907897 3138832230967016616680923)
        ·
          refine ⟨4708248346450524925021385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3138832230967016616680923 4708248346450524925021385)
          ·
            refine ⟨3531186259837893693766039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4708248346450524925021385 3531186259837893693766039)
            ·
              refine ⟨5296779389756840540649059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3531186259837893693766039 5296779389756840540649059)
              ·
                refine ⟨7945169084635260810973589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5296779389756840540649059 7945169084635260810973589)
                ·
                  refine ⟨372429800842277850514387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7945169084635260810973589 372429800842277850514387)
                  ·
                    rfl

theorem cell22_3263870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_3263870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3263870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3263870 prefixEnd_3263870 := by exact prefixLift 3263870
  have htrace : WordTrace (prefixWord ++ tailWord_3263870) baseStart_3263870 baseEnd_3263870 := by
    simpa [prefixWord, tailWord_3263870, baseEnd_3263870] using wordTrace_append hprefix tailTrace_3263870
  have hstable : (prefixWord ++ tailWord_3263870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263870).length < 2 ^ (prefixWord ++ tailWord_3263870).sum := by decide
  have hdescent : baseEnd_3263870 < baseStart_3263870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263939 : List Nat := [1, 1, 1, 3, 1, 1, 5, 2, 3, 4]
def baseStart_3263939 : Nat := 118140960795 + 3263939 * 2 ^ 59
def prefixEnd_3263939 : Nat := 4983230072969 + 3 ^ 40 * 3263939 * 2
def baseEnd_3263939 : Nat := 1117313022636940371567949

theorem tailTrace_3263939 : CollatzResearch.WordTrace tailWord_3263939 prefixEnd_3263939 1117313022636940371567949 := by
  unfold tailWord_3263939
  simp only [CollatzResearch.WordTrace]
  refine ⟨119045635322313914246530871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79363756881542609497687247 119045635322313914246530871)
  ·
    refine ⟨178568452983470871369796307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119045635322313914246530871 178568452983470871369796307)
    ·
      refine ⟨267852679475206307054694461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178568452983470871369796307 267852679475206307054694461)
      ·
        refine ⟨100444754803202365145510423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267852679475206307054694461 100444754803202365145510423)
        ·
          refine ⟨150667132204803547718265635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100444754803202365145510423 150667132204803547718265635)
          ·
            refine ⟨226000698307205321577398453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150667132204803547718265635 226000698307205321577398453)
            ·
              refine ⟨21187565466300498897881105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 226000698307205321577398453 21187565466300498897881105)
              ·
                refine ⟨15890674099725374173410829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21187565466300498897881105 15890674099725374173410829)
                ·
                  refine ⟨5959002787397015315029061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15890674099725374173410829 5959002787397015315029061)
                  ·
                    refine ⟨1117313022636940371567949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5959002787397015315029061 1117313022636940371567949)
                    ·
                      rfl

theorem cell22_3263939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 4].length) (baseStart_3263939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3263939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3263939 prefixEnd_3263939 := by exact prefixLift 3263939
  have htrace : WordTrace (prefixWord ++ tailWord_3263939) baseStart_3263939 baseEnd_3263939 := by
    simpa [prefixWord, tailWord_3263939, baseEnd_3263939] using wordTrace_append hprefix tailTrace_3263939
  have hstable : (prefixWord ++ tailWord_3263939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263939).length < 2 ^ (prefixWord ++ tailWord_3263939).sum := by decide
  have hdescent : baseEnd_3263939 < baseStart_3263939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263973 : List Nat := [1, 3, 1, 5, 1, 2, 1, 3, 1, 4]
def baseStart_3263973 : Nat := 118140960795 + 3263973 * 2 ^ 59
def prefixEnd_3263973 : Nat := 4983230072969 + 3 ^ 40 * 3263973 * 2
def baseEnd_3263973 : Nat := 1117324661531775616217845

theorem tailTrace_3263973 : CollatzResearch.WordTrace tailWord_3263973 prefixEnd_3263973 1117324661531775616217845 := by
  unfold tailWord_3263973
  simp only [CollatzResearch.WordTrace]
  refine ⟨119046875404190738053268573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79364583602793825368845715 119046875404190738053268573)
  ·
    refine ⟨44642578276571526769975715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119046875404190738053268573 44642578276571526769975715)
    ·
      refine ⟨66963867414857290154963573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44642578276571526769975715 66963867414857290154963573)
      ·
        refine ⟨6277862570142870952027835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66963867414857290154963573 6277862570142870952027835)
        ·
          refine ⟨9416793855214306428041753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6277862570142870952027835 9416793855214306428041753)
          ·
            refine ⟨7062595391410729821031315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9416793855214306428041753 7062595391410729821031315)
            ·
              refine ⟨10593893087116094731546973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7062595391410729821031315 10593893087116094731546973)
              ·
                refine ⟨3972709907668535524330115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10593893087116094731546973 3972709907668535524330115)
                ·
                  refine ⟨5959064861502803286495173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3972709907668535524330115 5959064861502803286495173)
                  ·
                    refine ⟨1117324661531775616217845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5959064861502803286495173 1117324661531775616217845)
                    ·
                      rfl

theorem cell22_3263973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 4].length) (baseStart_3263973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3263973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3263973 prefixEnd_3263973 := by exact prefixLift 3263973
  have htrace : WordTrace (prefixWord ++ tailWord_3263973) baseStart_3263973 baseEnd_3263973 := by
    simpa [prefixWord, tailWord_3263973, baseEnd_3263973] using wordTrace_append hprefix tailTrace_3263973
  have hstable : (prefixWord ++ tailWord_3263973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263973).length < 2 ^ (prefixWord ++ tailWord_3263973).sum := by decide
  have hdescent : baseEnd_3263973 < baseStart_3263973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264031 : List Nat := [1, 1, 2, 4, 1, 1, 2, 2, 5, 3]
def baseStart_3264031 : Nat := 118140960795 + 3264031 * 2 ^ 59
def prefixEnd_3264031 : Nat := 4983230072969 + 3 ^ 40 * 3264031 * 2
def baseEnd_3264031 : Nat := 1117344516117082798267667

theorem tailTrace_3264031 : CollatzResearch.WordTrace tailWord_3264031 prefixEnd_3264031 1117344516117082798267667 := by
  unfold tailWord_3264031
  simp only [CollatzResearch.WordTrace]
  refine ⟨119048990837980613958879947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79365993891987075972586631 119048990837980613958879947)
  ·
    refine ⟨178573486256970920938319921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119048990837980613958879947 178573486256970920938319921)
    ·
      refine ⟨133930114692728190703739941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178573486256970920938319921 133930114692728190703739941)
      ·
        refine ⟨25111896504886535756951239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133930114692728190703739941 25111896504886535756951239)
        ·
          refine ⟨37667844757329803635426859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25111896504886535756951239 37667844757329803635426859)
          ·
            refine ⟨56501767135994705453140289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37667844757329803635426859 56501767135994705453140289)
            ·
              refine ⟨42376325351996029089855217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56501767135994705453140289 42376325351996029089855217)
              ·
                refine ⟨31782244013997021817391413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42376325351996029089855217 31782244013997021817391413)
                ·
                  refine ⟨2979585376312220795380445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31782244013997021817391413 2979585376312220795380445)
                  ·
                    refine ⟨1117344516117082798267667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2979585376312220795380445 1117344516117082798267667)
                    ·
                      rfl

theorem cell22_3264031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 5, 3].length) (baseStart_3264031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3264031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3264031 prefixEnd_3264031 := by exact prefixLift 3264031
  have htrace : WordTrace (prefixWord ++ tailWord_3264031) baseStart_3264031 baseEnd_3264031 := by
    simpa [prefixWord, tailWord_3264031, baseEnd_3264031] using wordTrace_append hprefix tailTrace_3264031
  have hstable : (prefixWord ++ tailWord_3264031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264031).length < 2 ^ (prefixWord ++ tailWord_3264031).sum := by decide
  have hdescent : baseEnd_3264031 < baseStart_3264031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264054 : List Nat := [5, 1, 2, 1, 3, 2, 2, 1, 2, 3]
def baseStart_3264054 : Nat := 118140960795 + 3264054 * 2 ^ 59
def prefixEnd_3264054 : Nat := 4983230072969 + 3 ^ 40 * 3264054 * 2
def baseEnd_3264054 : Nat := 1117352389487118404942597

theorem tailTrace_3264054 : CollatzResearch.WordTrace tailWord_3264054 prefixEnd_3264054 1117352389487118404942597 := by
  unfold tailWord_3264054
  simp only [CollatzResearch.WordTrace]
  refine ⟨7440614357306080555435451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79366553144598192591311477 7440614357306080555435451)
  ·
    refine ⟨11160921535959120833153177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7440614357306080555435451 11160921535959120833153177)
    ·
      refine ⟨8370691151969340624864883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11160921535959120833153177 8370691151969340624864883)
      ·
        refine ⟨12556036727954010937297325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8370691151969340624864883 12556036727954010937297325)
        ·
          refine ⟨4708513772982754101486497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12556036727954010937297325 4708513772982754101486497)
          ·
            refine ⟨3531385329737065576114873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4708513772982754101486497 3531385329737065576114873)
            ·
              refine ⟨2648538997302799182086155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3531385329737065576114873 2648538997302799182086155)
              ·
                refine ⟨3972808495954198773129233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2648538997302799182086155 3972808495954198773129233)
                ·
                  refine ⟨2979606371965649079846925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3972808495954198773129233 2979606371965649079846925)
                  ·
                    refine ⟨1117352389487118404942597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2979606371965649079846925 1117352389487118404942597)
                    ·
                      rfl

theorem cell22_3264054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_3264054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3264054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3264054 prefixEnd_3264054 := by exact prefixLift 3264054
  have htrace : WordTrace (prefixWord ++ tailWord_3264054) baseStart_3264054 baseEnd_3264054 := by
    simpa [prefixWord, tailWord_3264054, baseEnd_3264054] using wordTrace_append hprefix tailTrace_3264054
  have hstable : (prefixWord ++ tailWord_3264054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264054).length < 2 ^ (prefixWord ++ tailWord_3264054).sum := by decide
  have hdescent : baseEnd_3264054 < baseStart_3264054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264138 : List Nat := [3, 1, 2, 3, 2, 1, 2, 2, 1, 5]
def baseStart_3264138 : Nat := 118140960795 + 3264138 * 2 ^ 59
def prefixEnd_3264138 : Nat := 4983230072969 + 3 ^ 40 * 3264138 * 2
def baseEnd_3264138 : Nat := 1117381144403770185842339

theorem tailTrace_3264138 : CollatzResearch.WordTrace tailWord_3264138 prefixEnd_3264138 1117381144403770185842339 := by
  unfold tailWord_3264138
  simp only [CollatzResearch.WordTrace]
  refine ⟨29763223362148242808256267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79368595632395314155350045 29763223362148242808256267)
  ·
    refine ⟨44644835043222364212384401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29763223362148242808256267 44644835043222364212384401)
    ·
      refine ⟨33483626282416773159288301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44644835043222364212384401 33483626282416773159288301)
      ·
        refine ⟨12556359855906289934733113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33483626282416773159288301 12556359855906289934733113)
        ·
          refine ⟨9417269891929717451049835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12556359855906289934733113 9417269891929717451049835)
          ·
            refine ⟨14125904837894576176574753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9417269891929717451049835 14125904837894576176574753)
            ·
              refine ⟨10594428628420932132431065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14125904837894576176574753 10594428628420932132431065)
              ·
                refine ⟨7945821471315699099323299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10594428628420932132431065 7945821471315699099323299)
                ·
                  refine ⟨11918732206973548648984949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7945821471315699099323299 11918732206973548648984949)
                  ·
                    refine ⟨1117381144403770185842339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11918732206973548648984949 1117381144403770185842339)
                    ·
                      rfl

theorem cell22_3264138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_3264138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3264138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3264138 prefixEnd_3264138 := by exact prefixLift 3264138
  have htrace : WordTrace (prefixWord ++ tailWord_3264138) baseStart_3264138 baseEnd_3264138 := by
    simpa [prefixWord, tailWord_3264138, baseEnd_3264138] using wordTrace_append hprefix tailTrace_3264138
  have hstable : (prefixWord ++ tailWord_3264138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264138).length < 2 ^ (prefixWord ++ tailWord_3264138).sum := by decide
  have hdescent : baseEnd_3264138 < baseStart_3264138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264142 : List Nat := [4, 1, 1, 3, 1, 4, 2, 1, 1, 4]
def baseStart_3264142 : Nat := 118140960795 + 3264142 * 2 ^ 59
def prefixEnd_3264142 : Nat := 4983230072969 + 3 ^ 40 * 3264142 * 2
def baseEnd_3264142 : Nat := 1117382513685515508742327

theorem tailTrace_3264142 : CollatzResearch.WordTrace tailWord_3264142 prefixEnd_3264142 1117382513685515508742327 := by
  unfold tailWord_3264142
  simp only [CollatzResearch.WordTrace]
  refine ⟨14881629917572309989521335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79368692893718986610780453 14881629917572309989521335)
  ·
    refine ⟨22322444876358464984282003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14881629917572309989521335 22322444876358464984282003)
    ·
      refine ⟨33483667314537697476423005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22322444876358464984282003 33483667314537697476423005)
      ·
        refine ⟨12556375242951636553658627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33483667314537697476423005 12556375242951636553658627)
        ·
          refine ⟨18834562864427454830487941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12556375242951636553658627 18834562864427454830487941)
          ·
            refine ⟨3531480537080147780716489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18834562864427454830487941 3531480537080147780716489)
            ·
              refine ⟨2648610402810110835537367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3531480537080147780716489 2648610402810110835537367)
              ·
                refine ⟨3972915604215166253306051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2648610402810110835537367 3972915604215166253306051)
                ·
                  refine ⟨5959373406322749379959077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3972915604215166253306051 5959373406322749379959077)
                  ·
                    refine ⟨1117382513685515508742327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5959373406322749379959077 1117382513685515508742327)
                    ·
                      rfl

theorem cell22_3264142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 1, 4].length) (baseStart_3264142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3264142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3264142 prefixEnd_3264142 := by exact prefixLift 3264142
  have htrace : WordTrace (prefixWord ++ tailWord_3264142) baseStart_3264142 baseEnd_3264142 := by
    simpa [prefixWord, tailWord_3264142, baseEnd_3264142] using wordTrace_append hprefix tailTrace_3264142
  have hstable : (prefixWord ++ tailWord_3264142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264142).length < 2 ^ (prefixWord ++ tailWord_3264142).sum := by decide
  have hdescent : baseEnd_3264142 < baseStart_3264142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264151 : List Nat := [1, 1, 3, 3, 2, 3, 9]
def baseStart_3264151 : Nat := 118140960795 + 3264151 * 2 ^ 59
def prefixEnd_3264151 : Nat := 4983230072969 + 3 ^ 40 * 3264151 * 2
def baseEnd_3264151 : Nat := 41384651650720092046937

theorem tailTrace_3264151 : CollatzResearch.WordTrace tailWord_3264151 prefixEnd_3264151 41384651650720092046937 := by
  unfold tailWord_3264151
  simp only [CollatzResearch.WordTrace]
  refine ⟨119053367597545874453248307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79368911731697249635498871 119053367597545874453248307)
  ·
    refine ⟨178580051396318811679872461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119053367597545874453248307 178580051396318811679872461)
    ·
      refine ⟨66967519273619554379952173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178580051396318811679872461 66967519273619554379952173)
      ·
        refine ⟨25112819727607332892482065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66967519273619554379952173 25112819727607332892482065)
        ·
          refine ⟨18834614795705499669361549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25112819727607332892482065 18834614795705499669361549)
          ·
            refine ⟨7062980548389562376010581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18834614795705499669361549 7062980548389562376010581)
            ·
              refine ⟨41384651650720092046937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7062980548389562376010581 41384651650720092046937)
              ·
                rfl

theorem cell22_3264151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 9].length) (baseStart_3264151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3264151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3264151 prefixEnd_3264151 := by exact prefixLift 3264151
  have htrace : WordTrace (prefixWord ++ tailWord_3264151) baseStart_3264151 baseEnd_3264151 := by
    simpa [prefixWord, tailWord_3264151, baseEnd_3264151] using wordTrace_append hprefix tailTrace_3264151
  have hstable : (prefixWord ++ tailWord_3264151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264151).length < 2 ^ (prefixWord ++ tailWord_3264151).sum := by decide
  have hdescent : baseEnd_3264151 < baseStart_3264151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264288 : List Nat := [2, 1, 1, 5, 1, 1, 2, 2, 1, 6]
def baseStart_3264288 : Nat := 118140960795 + 3264288 * 2 ^ 59
def prefixEnd_3264288 : Nat := 4983230072969 + 3 ^ 40 * 3264288 * 2
def baseEnd_3264288 : Nat := 1117432492469219794591879

theorem tailTrace_3264288 : CollatzResearch.WordTrace tailWord_3264288 prefixEnd_3264288 1117432492469219794591879 := by
  unfold tailWord_3264288
  simp only [CollatzResearch.WordTrace]
  refine ⟨59529182199024773425492759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79372242932033031233990345 59529182199024773425492759)
  ·
    refine ⟨89293773298537160138239139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59529182199024773425492759 89293773298537160138239139)
    ·
      refine ⟨133940659947805740207358709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89293773298537160138239139 133940659947805740207358709)
      ·
        refine ⟨12556936870106788144439879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133940659947805740207358709 12556936870106788144439879)
        ·
          refine ⟨18835405305160182216659819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12556936870106788144439879 18835405305160182216659819)
          ·
            refine ⟨28253107957740273324989729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18835405305160182216659819 28253107957740273324989729)
            ·
              refine ⟨21189830968305204993742297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28253107957740273324989729 21189830968305204993742297)
              ·
                refine ⟨15892373226228903745306723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21189830968305204993742297 15892373226228903745306723)
                ·
                  refine ⟨23838559839343355617960085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15892373226228903745306723 23838559839343355617960085)
                  ·
                    refine ⟨1117432492469219794591879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23838559839343355617960085 1117432492469219794591879)
                    ·
                      rfl

theorem cell22_3264288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 1, 6].length) (baseStart_3264288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3264288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3264288 prefixEnd_3264288 := by exact prefixLift 3264288
  have htrace : WordTrace (prefixWord ++ tailWord_3264288) baseStart_3264288 baseEnd_3264288 := by
    simpa [prefixWord, tailWord_3264288, baseEnd_3264288] using wordTrace_append hprefix tailTrace_3264288
  have hstable : (prefixWord ++ tailWord_3264288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264288).length < 2 ^ (prefixWord ++ tailWord_3264288).sum := by decide
  have hdescent : baseEnd_3264288 < baseStart_3264288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264290 : List Nat := [3, 3, 1, 1, 2, 1, 4, 1, 1, 5]
def baseStart_3264290 : Nat := 118140960795 + 3264290 * 2 ^ 59
def prefixEnd_3264290 : Nat := 4983230072969 + 3 ^ 40 * 3264290 * 2
def baseEnd_3264290 : Nat := 1117433177110092456041873

theorem tailTrace_3264290 : CollatzResearch.WordTrace tailWord_3264290 prefixEnd_3264290 1117433177110092456041873 := by
  unfold tailWord_3264290
  simp only [CollatzResearch.WordTrace]
  refine ⟨29764609336010575298139581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79372291562694867461705549 29764609336010575298139581)
  ·
    refine ⟨11161728501003965736802343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29764609336010575298139581 11161728501003965736802343)
    ·
      refine ⟨16742592751505948605203515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11161728501003965736802343 16742592751505948605203515)
      ·
        refine ⟨25113889127258922907805273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16742592751505948605203515 25113889127258922907805273)
        ·
          refine ⟨18835416845444192180853955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25113889127258922907805273 18835416845444192180853955)
          ·
            refine ⟨28253125268166288271280933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18835416845444192180853955 28253125268166288271280933)
            ·
              refine ⟨5297460987781179050865175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28253125268166288271280933 5297460987781179050865175)
              ·
                refine ⟨7946191481671768576297763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5297460987781179050865175 7946191481671768576297763)
                ·
                  refine ⟨11919287222507652864446645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7946191481671768576297763 11919287222507652864446645)
                  ·
                    refine ⟨1117433177110092456041873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11919287222507652864446645 1117433177110092456041873)
                    ·
                      rfl

theorem cell22_3264290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_3264290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3264290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3264290 prefixEnd_3264290 := by exact prefixLift 3264290
  have htrace : WordTrace (prefixWord ++ tailWord_3264290) baseStart_3264290 baseEnd_3264290 := by
    simpa [prefixWord, tailWord_3264290, baseEnd_3264290] using wordTrace_append hprefix tailTrace_3264290
  have hstable : (prefixWord ++ tailWord_3264290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264290).length < 2 ^ (prefixWord ++ tailWord_3264290).sum := by decide
  have hdescent : baseEnd_3264290 < baseStart_3264290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264305 : List Nat := [1, 2, 2, 3, 2, 2, 3, 1, 2, 4]
def baseStart_3264305 : Nat := 118140960795 + 3264305 * 2 ^ 59
def prefixEnd_3264305 : Nat := 4983230072969 + 3 ^ 40 * 3264305 * 2
def baseEnd_3264305 : Nat := 1117438311916637416916827

theorem tailTrace_3264305 : CollatzResearch.WordTrace tailWord_3264305 prefixEnd_3264305 1117438311916637416916827 := by
  unfold tailWord_3264305
  simp only [CollatzResearch.WordTrace]
  refine ⟨119058984438987958754354369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79372656292658639169569579 119058984438987958754354369)
  ·
    refine ⟨89294238329240969065765777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119058984438987958754354369 89294238329240969065765777)
    ·
      refine ⟨66970678746930726799324333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89294238329240969065765777 66970678746930726799324333)
      ·
        refine ⟨25114004530099022549746625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66970678746930726799324333 25114004530099022549746625)
        ·
          refine ⟨18835503397574266912309969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25114004530099022549746625 18835503397574266912309969)
          ·
            refine ⟨14126627548180700184232477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18835503397574266912309969 14126627548180700184232477)
            ·
              refine ⟨5297485330567762569087179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14126627548180700184232477 5297485330567762569087179)
              ·
                refine ⟨7946227995851643853630769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5297485330567762569087179 7946227995851643853630769)
                ·
                  refine ⟨5959670996888732890223077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7946227995851643853630769 5959670996888732890223077)
                  ·
                    refine ⟨1117438311916637416916827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5959670996888732890223077 1117438311916637416916827)
                    ·
                      rfl

theorem cell22_3264305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 4].length) (baseStart_3264305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3264305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3264305 prefixEnd_3264305 := by exact prefixLift 3264305
  have htrace : WordTrace (prefixWord ++ tailWord_3264305) baseStart_3264305 baseEnd_3264305 := by
    simpa [prefixWord, tailWord_3264305, baseEnd_3264305] using wordTrace_append hprefix tailTrace_3264305
  have hstable : (prefixWord ++ tailWord_3264305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264305).length < 2 ^ (prefixWord ++ tailWord_3264305).sum := by decide
  have hdescent : baseEnd_3264305 < baseStart_3264305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264382 : List Nat := [4, 2, 3, 1, 1, 1, 2, 1, 7]
def baseStart_3264382 : Nat := 118140960795 + 3264382 * 2 ^ 59
def prefixEnd_3264382 : Nat := 4983230072969 + 3 ^ 40 * 3264382 * 2
def baseEnd_3264382 : Nat := 372488223530078294247197

theorem tailTrace_3264382 : CollatzResearch.WordTrace tailWord_3264382 prefixEnd_3264382 372488223530078294247197 := by
  unfold tailWord_3264382
  simp only [CollatzResearch.WordTrace]
  refine ⟨14882724107463625113113425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79374528573139333936604933 14882724107463625113113425)
  ·
    refine ⟨11162043080597718834835069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14882724107463625113113425 11162043080597718834835069)
    ·
      refine ⟨4185766155224144563063151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11162043080597718834835069 4185766155224144563063151)
      ·
        refine ⟨6278649232836216844594727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4185766155224144563063151 6278649232836216844594727)
        ·
          refine ⟨9417973849254325266892091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6278649232836216844594727 9417973849254325266892091)
          ·
            refine ⟨14126960773881487900338137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9417973849254325266892091 14126960773881487900338137)
            ·
              refine ⟨10595220580411115925253603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14126960773881487900338137 10595220580411115925253603)
              ·
                refine ⟨15892830870616673887880405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10595220580411115925253603 15892830870616673887880405)
                ·
                  refine ⟨372488223530078294247197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15892830870616673887880405 372488223530078294247197)
                  ·
                    rfl

theorem cell22_3264382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_3264382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3264382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3264382 prefixEnd_3264382 := by exact prefixLift 3264382
  have htrace : WordTrace (prefixWord ++ tailWord_3264382) baseStart_3264382 baseEnd_3264382 := by
    simpa [prefixWord, tailWord_3264382, baseEnd_3264382] using wordTrace_append hprefix tailTrace_3264382
  have hstable : (prefixWord ++ tailWord_3264382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264382).length < 2 ^ (prefixWord ++ tailWord_3264382).sum := by decide
  have hdescent : baseEnd_3264382 < baseStart_3264382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264412 : List Nat := [2, 2, 3, 3, 1, 2, 1, 1, 3, 4]
def baseStart_3264412 : Nat := 118140960795 + 3264412 * 2 ^ 59
def prefixEnd_3264412 : Nat := 4983230072969 + 3 ^ 40 * 3264412 * 2
def baseEnd_3264412 : Nat := 1117474940203324804491499

theorem tailTrace_3264412 : CollatzResearch.WordTrace tailWord_3264412 prefixEnd_3264412 1117474940203324804491499 := by
  unfold tailWord_3264412
  simp only [CollatzResearch.WordTrace]
  refine ⟨59531443524800158014249745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79375258033066877352332993 59531443524800158014249745)
  ·
    refine ⟨44648582643600118510687309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59531443524800158014249745 44648582643600118510687309)
    ·
      refine ⟨16743218491350044441507741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44648582643600118510687309 16743218491350044441507741)
      ·
        refine ⟨6278706934256266665565403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16743218491350044441507741 6278706934256266665565403)
        ·
          refine ⟨9418060401384399998348105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6278706934256266665565403 9418060401384399998348105)
          ·
            refine ⟨7063545301038299998761079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9418060401384399998348105 7063545301038299998761079)
            ·
              refine ⟨10595317951557449998141619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7063545301038299998761079 10595317951557449998141619)
              ·
                refine ⟨15892976927336174997212429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10595317951557449998141619 15892976927336174997212429)
                ·
                  refine ⟨5959866347751065623954661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15892976927336174997212429 5959866347751065623954661)
                  ·
                    refine ⟨1117474940203324804491499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5959866347751065623954661 1117474940203324804491499)
                    ·
                      rfl

theorem cell22_3264412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_3264412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3264412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3264412 prefixEnd_3264412 := by exact prefixLift 3264412
  have htrace : WordTrace (prefixWord ++ tailWord_3264412) baseStart_3264412 baseEnd_3264412 := by
    simpa [prefixWord, tailWord_3264412, baseEnd_3264412] using wordTrace_append hprefix tailTrace_3264412
  have hstable : (prefixWord ++ tailWord_3264412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264412).length < 2 ^ (prefixWord ++ tailWord_3264412).sum := by decide
  have hdescent : baseEnd_3264412 < baseStart_3264412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264425 : List Nat := [1, 2, 1, 1, 1, 1, 4, 4, 4, 3]
def baseStart_3264425 : Nat := 118140960795 + 3264425 * 2 ^ 59
def prefixEnd_3264425 : Nat := 4983230072969 + 3 ^ 40 * 3264425 * 2
def baseEnd_3264425 : Nat := 1117479390368997103916459

theorem tailTrace_3264425 : CollatzResearch.WordTrace tailWord_3264425 prefixEnd_3264425 1117479390368997103916459 := by
  unfold tailWord_3264425
  simp only [CollatzResearch.WordTrace]
  refine ⟨119063361198553219248722729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79375574132368812832481819 119063361198553219248722729)
  ·
    refine ⟨89297520898914914436542047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119063361198553219248722729 89297520898914914436542047)
    ·
      refine ⟨133946281348372371654813071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89297520898914914436542047 133946281348372371654813071)
      ·
        refine ⟨200919422022558557482219607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133946281348372371654813071 200919422022558557482219607)
        ·
          refine ⟨301379133033837836223329411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200919422022558557482219607 301379133033837836223329411)
          ·
            refine ⟨452068699550756754334994117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301379133033837836223329411 452068699550756754334994117)
            ·
              refine ⟨84762881165766891437811397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 452068699550756754334994117 84762881165766891437811397)
              ·
                refine ⟨15893040218581292144589637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84762881165766891437811397 15893040218581292144589637)
                ·
                  refine ⟨2979945040983992277110557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15893040218581292144589637 2979945040983992277110557)
                  ·
                    refine ⟨1117479390368997103916459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2979945040983992277110557 1117479390368997103916459)
                    ·
                      rfl

theorem cell22_3264425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 4, 3].length) (baseStart_3264425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3264425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3264425 prefixEnd_3264425 := by exact prefixLift 3264425
  have htrace : WordTrace (prefixWord ++ tailWord_3264425) baseStart_3264425 baseEnd_3264425 := by
    simpa [prefixWord, tailWord_3264425, baseEnd_3264425] using wordTrace_append hprefix tailTrace_3264425
  have hstable : (prefixWord ++ tailWord_3264425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264425).length < 2 ^ (prefixWord ++ tailWord_3264425).sum := by decide
  have hdescent : baseEnd_3264425 < baseStart_3264425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264440 : List Nat := [2, 1, 2, 1, 2, 3, 1, 4, 2, 4]
def baseStart_3264440 : Nat := 118140960795 + 3264440 * 2 ^ 59
def prefixEnd_3264440 : Nat := 4983230072969 + 3 ^ 40 * 3264440 * 2
def baseEnd_3264440 : Nat := 1117484525175542064791413

theorem tailTrace_3264440 : CollatzResearch.WordTrace tailWord_3264440 prefixEnd_3264440 1117484525175542064791413 := by
  unfold tailWord_3264440
  simp only [CollatzResearch.WordTrace]
  refine ⟨59531954146749438405259387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79375938862332584540345849 59531954146749438405259387)
  ·
    refine ⟨89297931220124157607889081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59531954146749438405259387 89297931220124157607889081)
    ·
      refine ⟨66973448415093118205916811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89297931220124157607889081 66973448415093118205916811)
      ·
        refine ⟨100460172622639677308875217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66973448415093118205916811 100460172622639677308875217)
        ·
          refine ⟨75345129466979757981656413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100460172622639677308875217 75345129466979757981656413)
          ·
            refine ⟨28254423550117409243121155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75345129466979757981656413 28254423550117409243121155)
            ·
              refine ⟨42381635325176113864681733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28254423550117409243121155 42381635325176113864681733)
              ·
                refine ⟨7946556623470521349627825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42381635325176113864681733 7946556623470521349627825)
                ·
                  refine ⟨5959917467602891012220869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7946556623470521349627825 5959917467602891012220869)
                  ·
                    refine ⟨1117484525175542064791413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5959917467602891012220869 1117484525175542064791413)
                    ·
                      rfl

theorem cell22_3264440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 2, 4].length) (baseStart_3264440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3264440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3264440 prefixEnd_3264440 := by exact prefixLift 3264440
  have htrace : WordTrace (prefixWord ++ tailWord_3264440) baseStart_3264440 baseEnd_3264440 := by
    simpa [prefixWord, tailWord_3264440, baseEnd_3264440] using wordTrace_append hprefix tailTrace_3264440
  have hstable : (prefixWord ++ tailWord_3264440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264440).length < 2 ^ (prefixWord ++ tailWord_3264440).sum := by decide
  have hdescent : baseEnd_3264440 < baseStart_3264440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264474 : List Nat := [3, 1, 1, 2, 5, 2, 1, 1, 2, 4]
def baseStart_3264474 : Nat := 118140960795 + 3264474 * 2 ^ 59
def prefixEnd_3264474 : Nat := 4983230072969 + 3 ^ 40 * 3264474 * 2
def baseEnd_3264474 : Nat := 1117496164070377309441309

theorem tailTrace_3264474 : CollatzResearch.WordTrace tailWord_3264474 prefixEnd_3264474 1117496164070377309441309 := by
  unfold tailWord_3264474
  simp only [CollatzResearch.WordTrace]
  refine ⟨29766287093843925154314119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79376765583583800411504317 29766287093843925154314119)
  ·
    refine ⟨44649430640765887731471179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29766287093843925154314119 44649430640765887731471179)
    ·
      refine ⟨66974145961148831597206769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44649430640765887731471179 66974145961148831597206769)
      ·
        refine ⟨50230609470861623697905077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66974145961148831597206769 50230609470861623697905077)
        ·
          refine ⟨4709119637893277221678601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50230609470861623697905077 4709119637893277221678601)
          ·
            refine ⟨3531839728419957916258951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4709119637893277221678601 3531839728419957916258951)
            ·
              refine ⟨5297759592629936874388427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3531839728419957916258951 5297759592629936874388427)
              ·
                refine ⟨7946639388944905311582641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5297759592629936874388427 7946639388944905311582641)
                ·
                  refine ⟨5959979541708678983686981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7946639388944905311582641 5959979541708678983686981)
                  ·
                    refine ⟨1117496164070377309441309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5959979541708678983686981 1117496164070377309441309)
                    ·
                      rfl

theorem cell22_3264474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 2, 4].length) (baseStart_3264474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3264474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3264474 prefixEnd_3264474 := by exact prefixLift 3264474
  have htrace : WordTrace (prefixWord ++ tailWord_3264474) baseStart_3264474 baseEnd_3264474 := by
    simpa [prefixWord, tailWord_3264474, baseEnd_3264474] using wordTrace_append hprefix tailTrace_3264474
  have hstable : (prefixWord ++ tailWord_3264474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264474).length < 2 ^ (prefixWord ++ tailWord_3264474).sum := by decide
  have hdescent : baseEnd_3264474 < baseStart_3264474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264493 : List Nat := [1, 5, 1, 4, 1, 2, 1, 2, 2, 3]
def baseStart_3264493 : Nat := 118140960795 + 3264493 * 2 ^ 59
def prefixEnd_3264493 : Nat := 4983230072969 + 3 ^ 40 * 3264493 * 2
def baseEnd_3264493 : Nat := 1117502668158667593216251

theorem tailTrace_3264493 : CollatzResearch.WordTrace tailWord_3264493 prefixEnd_3264493 1117502668158667593216251 := by
  unfold tailWord_3264493
  simp only [CollatzResearch.WordTrace]
  refine ⟨119065841362306866862198133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79377227574871244574798755 119065841362306866862198133)
  ·
    refine ⟨11162422627716268768331075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119065841362306866862198133 11162422627716268768331075)
    ·
      refine ⟨16743633941574403152496613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11162422627716268768331075 16743633941574403152496613)
      ·
        refine ⟨3139431364045200591093115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16743633941574403152496613 3139431364045200591093115)
        ·
          refine ⟨4709147046067800886639673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3139431364045200591093115 4709147046067800886639673)
          ·
            refine ⟨3531860284550850664979755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4709147046067800886639673 3531860284550850664979755)
            ·
              refine ⟨5297790426826275997469633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3531860284550850664979755 5297790426826275997469633)
              ·
                refine ⟨3973342820119706998102225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5297790426826275997469633 3973342820119706998102225)
                ·
                  refine ⟨2980007115089780248576669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3973342820119706998102225 2980007115089780248576669)
                  ·
                    refine ⟨1117502668158667593216251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2980007115089780248576669 1117502668158667593216251)
                    ·
                      rfl

theorem cell22_3264493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_3264493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3264493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3264493 prefixEnd_3264493 := by exact prefixLift 3264493
  have htrace : WordTrace (prefixWord ++ tailWord_3264493) baseStart_3264493 baseEnd_3264493 := by
    simpa [prefixWord, tailWord_3264493, baseEnd_3264493] using wordTrace_append hprefix tailTrace_3264493
  have hstable : (prefixWord ++ tailWord_3264493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264493).length < 2 ^ (prefixWord ++ tailWord_3264493).sum := by decide
  have hdescent : baseEnd_3264493 < baseStart_3264493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
