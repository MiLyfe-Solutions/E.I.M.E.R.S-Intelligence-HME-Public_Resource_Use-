import V185TrunkScan23Chunk0172

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1023049 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 5, 2, 4]
def baseStart_1023049 : Nat := 118140960795 + 1023049 * 2 ^ 59
def prefixEnd_1023049 : Nat := 4983230072969 + 3 ^ 40 * 1023049 * 2
def baseEnd_1023049 : Nat := 525315870101673049782589

theorem tailTrace_1023049 : CollatzResearch.WordTrace tailWord_1023049 prefixEnd_1023049 525315870101673049782589 := by
  unfold tailWord_1023049
  simp only [CollatzResearch.WordTrace]
  refine ⟨37313662470675670703912201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24875774980450447135941467 37313662470675670703912201)
  ·
    refine ⟨27985246853006753027934151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37313662470675670703912201 27985246853006753027934151)
    ·
      refine ⟨41977870279510129541901227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27985246853006753027934151 41977870279510129541901227)
      ·
        refine ⟨62966805419265194312851841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41977870279510129541901227 62966805419265194312851841)
        ·
          refine ⟨47225104064448895734638881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62966805419265194312851841 47225104064448895734638881)
          ·
            refine ⟨35418828048336671800979161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47225104064448895734638881 35418828048336671800979161)
            ·
              refine ⟨26564121036252503850734371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35418828048336671800979161 26564121036252503850734371)
              ·
                refine ⟨39846181554378755776101557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26564121036252503850734371 39846181554378755776101557)
                ·
                  refine ⟨3735579520723008354009521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39846181554378755776101557 3735579520723008354009521)
                  ·
                    refine ⟨2801684640542256265507141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3735579520723008354009521 2801684640542256265507141)
                    ·
                      refine ⟨525315870101673049782589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2801684640542256265507141 525315870101673049782589)
                      ·
                        rfl

theorem cell23_1023049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 2, 4].length) (baseStart_1023049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023049 prefixEnd_1023049 := by exact prefixLift 1023049
  have htrace : WordTrace (prefixWord ++ tailWord_1023049) baseStart_1023049 baseEnd_1023049 := by
    simpa [prefixWord, tailWord_1023049, baseEnd_1023049] using wordTrace_append hprefix tailTrace_1023049
  have hstable : (prefixWord ++ tailWord_1023049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023049).length < 2 ^ (prefixWord ++ tailWord_1023049).sum := by decide
  have hdescent : baseEnd_1023049 < baseStart_1023049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023073 : List Nat := [1, 2, 3, 1, 1, 2, 5, 2, 1, 2, 3]
def baseStart_1023073 : Nat := 118140960795 + 1023073 * 2 ^ 59
def prefixEnd_1023073 : Nat := 4983230072969 + 3 ^ 40 * 1023073 * 2
def baseEnd_1023073 : Nat := 525328193637380955882479

theorem tailTrace_1023073 : CollatzResearch.WordTrace tailWord_1023073 prefixEnd_1023073 525328193637380955882479 := by
  unfold tailWord_1023073
  simp only [CollatzResearch.WordTrace]
  refine ⟨37314537822588722802785873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24876358548392481868523915 37314537822588722802785873)
  ·
    refine ⟨27985903366941542102089405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37314537822588722802785873 27985903366941542102089405)
    ·
      refine ⟨10494713762603078288283527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27985903366941542102089405 10494713762603078288283527)
      ·
        refine ⟨15742070643904617432425291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10494713762603078288283527 15742070643904617432425291)
        ·
          refine ⟨23613105965856926148637937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15742070643904617432425291 23613105965856926148637937)
          ·
            refine ⟨17709829474392694611478453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23613105965856926148637937 17709829474392694611478453)
            ·
              refine ⟨1660296513224315119826105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17709829474392694611478453 1660296513224315119826105)
              ·
                refine ⟨1245222384918236339869579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1660296513224315119826105 1245222384918236339869579)
                ·
                  refine ⟨1867833577377354509804369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1245222384918236339869579 1867833577377354509804369)
                  ·
                    refine ⟨1400875183033015882353277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1867833577377354509804369 1400875183033015882353277)
                    ·
                      refine ⟨525328193637380955882479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1400875183033015882353277 525328193637380955882479)
                      ·
                        rfl

theorem cell23_1023073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 2, 3].length) (baseStart_1023073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023073 prefixEnd_1023073 := by exact prefixLift 1023073
  have htrace : WordTrace (prefixWord ++ tailWord_1023073) baseStart_1023073 baseEnd_1023073 := by
    simpa [prefixWord, tailWord_1023073, baseEnd_1023073] using wordTrace_append hprefix tailTrace_1023073
  have hstable : (prefixWord ++ tailWord_1023073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023073).length < 2 ^ (prefixWord ++ tailWord_1023073).sum := by decide
  have hdescent : baseEnd_1023073 < baseStart_1023073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023090 : List Nat := [3, 2, 1, 2, 2, 1, 5, 1, 1, 2, 3]
def baseStart_1023090 : Nat := 118140960795 + 1023090 * 2 ^ 59
def prefixEnd_1023090 : Nat := 4983230072969 + 3 ^ 40 * 1023090 * 2
def baseEnd_1023090 : Nat := 525336922808507389369901

theorem tailTrace_1023090 : CollatzResearch.WordTrace tailWord_1023090 prefixEnd_1023090 525336922808507389369901 := by
  unfold tailWord_1023090
  simp only [CollatzResearch.WordTrace]
  refine ⟨9328789465881783676538681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24876771909018089804103149 9328789465881783676538681)
  ·
    refine ⟨6996592099411337757404011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9328789465881783676538681 6996592099411337757404011)
    ·
      refine ⟨10494888149117006636106017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6996592099411337757404011 10494888149117006636106017)
      ·
        refine ⟨7871166111837754977079513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10494888149117006636106017 7871166111837754977079513)
        ·
          refine ⟨5903374583878316232809635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7871166111837754977079513 5903374583878316232809635)
          ·
            refine ⟨8855061875817474349214453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5903374583878316232809635 8855061875817474349214453)
            ·
              refine ⟨830162050857888220238855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8855061875817474349214453 830162050857888220238855)
              ·
                refine ⟨1245243076286832330358283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 830162050857888220238855 1245243076286832330358283)
                ·
                  refine ⟨1867864614430248495537425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1245243076286832330358283 1867864614430248495537425)
                  ·
                    refine ⟨1400898460822686371653069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1867864614430248495537425 1400898460822686371653069)
                    ·
                      refine ⟨525336922808507389369901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1400898460822686371653069 525336922808507389369901)
                      ·
                        rfl

theorem cell23_1023090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_1023090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023090 prefixEnd_1023090 := by exact prefixLift 1023090
  have htrace : WordTrace (prefixWord ++ tailWord_1023090) baseStart_1023090 baseEnd_1023090 := by
    simpa [prefixWord, tailWord_1023090, baseEnd_1023090] using wordTrace_append hprefix tailTrace_1023090
  have hstable : (prefixWord ++ tailWord_1023090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023090).length < 2 ^ (prefixWord ++ tailWord_1023090).sum := by decide
  have hdescent : baseEnd_1023090 < baseStart_1023090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023093 : List Nat := [1, 3, 4, 3, 2, 10]
def baseStart_1023093 : Nat := 118140960795 + 1023093 * 2 ^ 59
def prefixEnd_1023093 : Nat := 4983230072969 + 3 ^ 40 * 1023093 * 2
def baseEnd_1023093 : Nat := 2161886680043090031409

theorem tailTrace_1023093 : CollatzResearch.WordTrace tailWord_1023093 prefixEnd_1023093 2161886680043090031409 := by
  unfold tailWord_1023093
  simp only [CollatzResearch.WordTrace]
  refine ⟨37315267282516266218513933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24876844855010844145675955 37315267282516266218513933)
  ·
    refine ⟨13993225230943599831942725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37315267282516266218513933 13993225230943599831942725)
    ·
      refine ⟨2623729730801924968489261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13993225230943599831942725 2623729730801924968489261)
      ·
        refine ⟨983898649050721863183473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2623729730801924968489261 983898649050721863183473)
        ·
          refine ⟨737923986788041397387605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 983898649050721863183473 737923986788041397387605)
          ·
            refine ⟨2161886680043090031409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 737923986788041397387605 2161886680043090031409)
            ·
              rfl

theorem cell23_1023093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 10].length) (baseStart_1023093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023093 prefixEnd_1023093 := by exact prefixLift 1023093
  have htrace : WordTrace (prefixWord ++ tailWord_1023093) baseStart_1023093 baseEnd_1023093 := by
    simpa [prefixWord, tailWord_1023093, baseEnd_1023093] using wordTrace_append hprefix tailTrace_1023093
  have hstable : (prefixWord ++ tailWord_1023093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023093).length < 2 ^ (prefixWord ++ tailWord_1023093).sum := by decide
  have hdescent : baseEnd_1023093 < baseStart_1023093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023099 : List Nat := [1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 5]
def baseStart_1023099 : Nat := 118140960795 + 1023099 * 2 ^ 59
def prefixEnd_1023099 : Nat := 4983230072969 + 3 ^ 40 * 1023099 * 2
def baseEnd_1023099 : Nat := 525341544134397854157359

theorem tailTrace_1023099 : CollatzResearch.WordTrace tailWord_1023099 prefixEnd_1023099 525341544134397854157359 := by
  unfold tailWord_1023099
  simp only [CollatzResearch.WordTrace]
  refine ⟨37315486120494529243232351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24876990746996352828821567 37315486120494529243232351)
  ·
    refine ⟨55973229180741793864848527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37315486120494529243232351 55973229180741793864848527)
    ·
      refine ⟨83959843771112690797272791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55973229180741793864848527 83959843771112690797272791)
      ·
        refine ⟨125939765656669036195909187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83959843771112690797272791 125939765656669036195909187)
        ·
          refine ⟨188909648485003554293863781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125939765656669036195909187 188909648485003554293863781)
          ·
            refine ⟨35420559090938166430099459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188909648485003554293863781 35420559090938166430099459)
            ·
              refine ⟨53130838636407249645149189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35420559090938166430099459 53130838636407249645149189)
              ·
                refine ⟨9962032244326359308465473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53130838636407249645149189 9962032244326359308465473)
                ·
                  refine ⟨7471524183244769481349105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9962032244326359308465473 7471524183244769481349105)
                  ·
                    refine ⟨5603643137433577111011829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7471524183244769481349105 5603643137433577111011829)
                    ·
                      refine ⟨525341544134397854157359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5603643137433577111011829 525341544134397854157359)
                      ·
                        rfl

theorem cell23_1023099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 5].length) (baseStart_1023099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023099 prefixEnd_1023099 := by exact prefixLift 1023099
  have htrace : WordTrace (prefixWord ++ tailWord_1023099) baseStart_1023099 baseEnd_1023099 := by
    simpa [prefixWord, tailWord_1023099, baseEnd_1023099] using wordTrace_append hprefix tailTrace_1023099
  have hstable : (prefixWord ++ tailWord_1023099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023099).length < 2 ^ (prefixWord ++ tailWord_1023099).sum := by decide
  have hdescent : baseEnd_1023099 < baseStart_1023099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023113 : List Nat := [1, 2, 1, 1, 4, 3, 1, 2, 3, 3, 2]
def baseStart_1023113 : Nat := 118140960795 + 1023113 * 2 ^ 59
def prefixEnd_1023113 : Nat := 4983230072969 + 3 ^ 40 * 1023113 * 2
def baseEnd_1023113 : Nat := 525348732863560799382295

theorem tailTrace_1023113 : CollatzResearch.WordTrace tailWord_1023113 prefixEnd_1023113 525348732863560799382295 := by
  unfold tailWord_1023113
  simp only [CollatzResearch.WordTrace]
  refine ⟨37315996742443809634241993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24877331161629206422827995 37315996742443809634241993)
  ·
    refine ⟨27986997556832857225681495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37315996742443809634241993 27986997556832857225681495)
    ·
      refine ⟨41980496335249285838522243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27986997556832857225681495 41980496335249285838522243)
      ·
        refine ⟨62970744502873928757783365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41980496335249285838522243 62970744502873928757783365)
        ·
          refine ⟨11807014594288861642084381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62970744502873928757783365 11807014594288861642084381)
          ·
            refine ⟨4427630472858323115781643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11807014594288861642084381 4427630472858323115781643)
            ·
              refine ⟨6641445709287484673672465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4427630472858323115781643 6641445709287484673672465)
              ·
                refine ⟨4981084281965613505254349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6641445709287484673672465 4981084281965613505254349)
                ·
                  refine ⟨1867906605737105064470381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4981084281965613505254349 1867906605737105064470381)
                  ·
                    refine ⟨700464977151414399176393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1867906605737105064470381 700464977151414399176393)
                    ·
                      refine ⟨525348732863560799382295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 700464977151414399176393 525348732863560799382295)
                      ·
                        rfl

theorem cell23_1023113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 3, 2].length) (baseStart_1023113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023113 prefixEnd_1023113 := by exact prefixLift 1023113
  have htrace : WordTrace (prefixWord ++ tailWord_1023113) baseStart_1023113 baseEnd_1023113 := by
    simpa [prefixWord, tailWord_1023113, baseEnd_1023113] using wordTrace_append hprefix tailTrace_1023113
  have hstable : (prefixWord ++ tailWord_1023113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023113).length < 2 ^ (prefixWord ++ tailWord_1023113).sum := by decide
  have hdescent : baseEnd_1023113 < baseStart_1023113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023130 : List Nat := [3, 1, 1, 5, 1, 1, 2, 1, 3, 3, 2]
def baseStart_1023130 : Nat := 118140960795 + 1023130 * 2 ^ 59
def prefixEnd_1023130 : Nat := 4983230072969 + 3 ^ 40 * 1023130 * 2
def baseEnd_1023130 : Nat := 525357462034687232869717

theorem tailTrace_1023130 : CollatzResearch.WordTrace tailWord_1023130 prefixEnd_1023130 525357462034687232869717 := by
  unfold tailWord_1023130
  simp only [CollatzResearch.WordTrace]
  refine ⟨9329154195845555384402711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24877744522254814358407229 9329154195845555384402711)
  ·
    refine ⟨13993731293768333076604067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9329154195845555384402711 13993731293768333076604067)
    ·
      refine ⟨20990596940652499614906101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13993731293768333076604067 20990596940652499614906101)
      ·
        refine ⟨1967868463186171838897447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20990596940652499614906101 1967868463186171838897447)
        ·
          refine ⟨2951802694779257758346171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1967868463186171838897447 2951802694779257758346171)
          ·
            refine ⟨4427704042168886637519257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2951802694779257758346171 4427704042168886637519257)
            ·
              refine ⟨3320778031626664978139443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4427704042168886637519257 3320778031626664978139443)
              ·
                refine ⟨4981167047439997467209165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3320778031626664978139443 4981167047439997467209165)
                ·
                  refine ⟨1867937642789999050203437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4981167047439997467209165 1867937642789999050203437)
                  ·
                    refine ⟨700476616046249643826289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1867937642789999050203437 700476616046249643826289)
                    ·
                      refine ⟨525357462034687232869717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 700476616046249643826289 525357462034687232869717)
                      ·
                        rfl

theorem cell23_1023130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_1023130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023130 prefixEnd_1023130 := by exact prefixLift 1023130
  have htrace : WordTrace (prefixWord ++ tailWord_1023130) baseStart_1023130 baseEnd_1023130 := by
    simpa [prefixWord, tailWord_1023130, baseEnd_1023130] using wordTrace_append hprefix tailTrace_1023130
  have hstable : (prefixWord ++ tailWord_1023130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023130).length < 2 ^ (prefixWord ++ tailWord_1023130).sum := by decide
  have hdescent : baseEnd_1023130 < baseStart_1023130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023160 : List Nat := [2, 1, 2, 1, 2, 1, 2, 6, 2, 2, 2]
def baseStart_1023160 : Nat := 118140960795 + 1023160 * 2 ^ 59
def prefixEnd_1023160 : Nat := 4983230072969 + 3 ^ 40 * 1023160 * 2
def baseEnd_1023160 : Nat := 525372866454322115494579

theorem tailTrace_1023160 : CollatzResearch.WordTrace tailWord_1023160 prefixEnd_1023160 525372866454322115494579 := by
  unfold tailWord_1023160
  simp only [CollatzResearch.WordTrace]
  refine ⟨18658855486636768330601467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24878473982182357774135289 18658855486636768330601467)
  ·
    refine ⟨27988283229955152495902201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18658855486636768330601467 27988283229955152495902201)
    ·
      refine ⟨20991212422466364371926651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27988283229955152495902201 20991212422466364371926651)
      ·
        refine ⟨31486818633699546557889977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20991212422466364371926651 31486818633699546557889977)
        ·
          refine ⟨23615113975274659918417483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31486818633699546557889977 23615113975274659918417483)
          ·
            refine ⟨35422670962911989877626225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23615113975274659918417483 35422670962911989877626225)
            ·
              refine ⟨26567003222183992408219669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35422670962911989877626225 26567003222183992408219669)
              ·
                refine ⟨1245328276039874644135297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26567003222183992408219669 1245328276039874644135297)
                ·
                  refine ⟨933996207029905983101473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1245328276039874644135297 933996207029905983101473)
                  ·
                    refine ⟨700497155272429487326105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 933996207029905983101473 700497155272429487326105)
                    ·
                      refine ⟨525372866454322115494579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 700497155272429487326105 525372866454322115494579)
                      ·
                        rfl

theorem cell23_1023160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 2, 2, 2].length) (baseStart_1023160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023160 prefixEnd_1023160 := by exact prefixLift 1023160
  have htrace : WordTrace (prefixWord ++ tailWord_1023160) baseStart_1023160 baseEnd_1023160 := by
    simpa [prefixWord, tailWord_1023160, baseEnd_1023160] using wordTrace_append hprefix tailTrace_1023160
  have hstable : (prefixWord ++ tailWord_1023160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023160).length < 2 ^ (prefixWord ++ tailWord_1023160).sum := by decide
  have hdescent : baseEnd_1023160 < baseStart_1023160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023181 : List Nat := [1, 6, 2, 2, 1, 1, 2, 2, 1, 3, 2]
def baseStart_1023181 : Nat := 118140960795 + 1023181 * 2 ^ 59
def prefixEnd_1023181 : Nat := 4983230072969 + 3 ^ 40 * 1023181 * 2
def baseEnd_1023181 : Nat := 525383649548066533331983

theorem tailTrace_1023181 : CollatzResearch.WordTrace tailWord_1023181 prefixEnd_1023181 525383649548066533331983 := by
  unfold tailWord_1023181
  simp only [CollatzResearch.WordTrace]
  refine ⟨37318476906197457247717397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24878984604131638165144931 37318476906197457247717397)
  ·
    refine ⟨1749303604978005808486753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37318476906197457247717397 1749303604978005808486753)
    ·
      refine ⟨1311977703733504356365065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1749303604978005808486753 1311977703733504356365065)
      ·
        refine ⟨983983277800128267273799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1311977703733504356365065 983983277800128267273799)
        ·
          refine ⟨1475974916700192400910699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 983983277800128267273799 1475974916700192400910699)
          ·
            refine ⟨2213962375050288601366049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1475974916700192400910699 2213962375050288601366049)
            ·
              refine ⟨1660471781287716451024537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2213962375050288601366049 1660471781287716451024537)
              ·
                refine ⟨1245353835965787338268403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1660471781287716451024537 1245353835965787338268403)
                ·
                  refine ⟨1868030753948681007402605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1245353835965787338268403 1868030753948681007402605)
                  ·
                    refine ⟨700511532730755377775977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1868030753948681007402605 700511532730755377775977)
                    ·
                      refine ⟨525383649548066533331983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 700511532730755377775977 525383649548066533331983)
                      ·
                        rfl

theorem cell23_1023181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_1023181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023181 prefixEnd_1023181 := by exact prefixLift 1023181
  have htrace : WordTrace (prefixWord ++ tailWord_1023181) baseStart_1023181 baseEnd_1023181 := by
    simpa [prefixWord, tailWord_1023181, baseEnd_1023181] using wordTrace_append hprefix tailTrace_1023181
  have hstable : (prefixWord ++ tailWord_1023181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023181).length < 2 ^ (prefixWord ++ tailWord_1023181).sum := by decide
  have hdescent : baseEnd_1023181 < baseStart_1023181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023200 : List Nat := [2, 1, 1, 3, 1, 6, 1, 3, 5]
def baseStart_1023200 : Nat := 118140960795 + 1023200 * 2 ^ 59
def prefixEnd_1023200 : Nat := 4983230072969 + 3 ^ 40 * 1023200 * 2
def baseEnd_1023200 : Nat := 58377045075611328777155

theorem tailTrace_1023200 : CollatzResearch.WordTrace tailWord_1023200 prefixEnd_1023200 58377045075611328777155 := by
  unfold tailWord_1023200
  simp only [CollatzResearch.WordTrace]
  refine ⟨18659584946564311746329527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24879446595419082328439369 18659584946564311746329527)
  ·
    refine ⟨27989377419846467619494291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18659584946564311746329527 27989377419846467619494291)
    ·
      refine ⟨41984066129769701429241437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27989377419846467619494291 41984066129769701429241437)
      ·
        refine ⟨15744024798663638035965539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41984066129769701429241437 15744024798663638035965539)
        ·
          refine ⟨23616037197995457053948309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15744024798663638035965539 23616037197995457053948309)
          ·
            refine ⟨1107001743656037049403827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23616037197995457053948309 1107001743656037049403827)
            ·
              refine ⟨1660502615484055574105741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1107001743656037049403827 1660502615484055574105741)
              ·
                refine ⟨622688480806520840289653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1660502615484055574105741 622688480806520840289653)
                ·
                  refine ⟨58377045075611328777155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 622688480806520840289653 58377045075611328777155)
                  ·
                    rfl

theorem cell23_1023200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 3, 5].length) (baseStart_1023200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023200 prefixEnd_1023200 := by exact prefixLift 1023200
  have htrace : WordTrace (prefixWord ++ tailWord_1023200) baseStart_1023200 baseEnd_1023200 := by
    simpa [prefixWord, tailWord_1023200, baseEnd_1023200] using wordTrace_append hprefix tailTrace_1023200
  have hstable : (prefixWord ++ tailWord_1023200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023200).length < 2 ^ (prefixWord ++ tailWord_1023200).sum := by decide
  have hdescent : baseEnd_1023200 < baseStart_1023200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023213 : List Nat := [1, 5, 1, 2, 2, 1, 1, 1, 4, 5]
def baseStart_1023213 : Nat := 118140960795 + 1023213 * 2 ^ 59
def prefixEnd_1023213 : Nat := 4983230072969 + 3 ^ 40 * 1023213 * 2
def baseEnd_1023213 : Nat := 175133360309670136043945

theorem tailTrace_1023213 : CollatzResearch.WordTrace tailWord_1023213 prefixEnd_1023213 175133360309670136043945 := by
  unfold tailWord_1023213
  simp only [CollatzResearch.WordTrace]
  refine ⟨37319644042081526712882293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24879762694721017808588195 37319644042081526712882293)
  ·
    refine ⟨3498716628945143129332715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37319644042081526712882293 3498716628945143129332715)
    ·
      refine ⟨5248074943417714693999073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3498716628945143129332715 5248074943417714693999073)
      ·
        refine ⟨3936056207563286020499305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5248074943417714693999073 3936056207563286020499305)
        ·
          refine ⟨2952042155672464515374479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3936056207563286020499305 2952042155672464515374479)
          ·
            refine ⟨4428063233508696773061719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2952042155672464515374479 4428063233508696773061719)
            ·
              refine ⟨6642094850263045159592579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4428063233508696773061719 6642094850263045159592579)
              ·
                refine ⟨9963142275394567739388869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6642094850263045159592579 9963142275394567739388869)
                ·
                  refine ⟨1868089176636481451135413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9963142275394567739388869 1868089176636481451135413)
                  ·
                    refine ⟨175133360309670136043945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1868089176636481451135413 175133360309670136043945)
                    ·
                      rfl

theorem cell23_1023213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_1023213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023213 prefixEnd_1023213 := by exact prefixLift 1023213
  have htrace : WordTrace (prefixWord ++ tailWord_1023213) baseStart_1023213 baseEnd_1023213 := by
    simpa [prefixWord, tailWord_1023213, baseEnd_1023213] using wordTrace_append hprefix tailTrace_1023213
  have hstable : (prefixWord ++ tailWord_1023213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023213).length < 2 ^ (prefixWord ++ tailWord_1023213).sum := by decide
  have hdescent : baseEnd_1023213 < baseStart_1023213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023276 : List Nat := [2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 6]
def baseStart_1023276 : Nat := 118140960795 + 1023276 * 2 ^ 59
def prefixEnd_1023276 : Nat := 4983230072969 + 3 ^ 40 * 1023276 * 2
def baseEnd_1023276 : Nat := 525432430210243661644045

theorem tailTrace_1023276 : CollatzResearch.WordTrace tailWord_1023276 prefixEnd_1023276 525432430210243661644045 := by
  unfold tailWord_1023276
  simp only [CollatzResearch.WordTrace]
  refine ⟨18660970920426644236212841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24881294560568858981617121 18660970920426644236212841)
  ·
    refine ⟨13995728190319983177159631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18660970920426644236212841 13995728190319983177159631)
    ·
      refine ⟨20993592285479974765739447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13995728190319983177159631 20993592285479974765739447)
      ·
        refine ⟨31490388428219962148609171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20993592285479974765739447 31490388428219962148609171)
        ·
          refine ⟨47235582642329943222913757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31490388428219962148609171 47235582642329943222913757)
          ·
            refine ⟨17713343490873728708592659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47235582642329943222913757 17713343490873728708592659)
            ·
              refine ⟨26570015236310593062888989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17713343490873728708592659 26570015236310593062888989)
              ·
                refine ⟨9963755713616472398583371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26570015236310593062888989 9963755713616472398583371)
                ·
                  refine ⟨14945633570424708597875057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9963755713616472398583371 14945633570424708597875057)
                  ·
                    refine ⟨11209225177818531448406293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14945633570424708597875057 11209225177818531448406293)
                    ·
                      refine ⟨525432430210243661644045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11209225177818531448406293 525432430210243661644045)
                      ·
                        rfl

theorem cell23_1023276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_1023276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023276 prefixEnd_1023276 := by exact prefixLift 1023276
  have htrace : WordTrace (prefixWord ++ tailWord_1023276) baseStart_1023276 baseEnd_1023276 := by
    simpa [prefixWord, tailWord_1023276, baseEnd_1023276] using wordTrace_append hprefix tailTrace_1023276
  have hstable : (prefixWord ++ tailWord_1023276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023276).length < 2 ^ (prefixWord ++ tailWord_1023276).sum := by decide
  have hdescent : baseEnd_1023276 < baseStart_1023276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023296 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 7]
def baseStart_1023296 : Nat := 118140960795 + 1023296 * 2 ^ 59
def prefixEnd_1023296 : Nat := 4983230072969 + 3 ^ 40 * 1023296 * 2
def baseEnd_1023296 : Nat := 525442699823333583393953

theorem tailTrace_1023296 : CollatzResearch.WordTrace tailWord_1023296 prefixEnd_1023296 525442699823333583393953 := by
  unfold tailWord_1023296
  simp only [CollatzResearch.WordTrace]
  refine ⟨18661335650390415944076871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24881780867187221258769161 18661335650390415944076871)
  ·
    refine ⟨27992003475585623916115307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18661335650390415944076871 27992003475585623916115307)
    ·
      refine ⟨41988005213378435874172961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27992003475585623916115307 41988005213378435874172961)
      ·
        refine ⟨31491003910033826905629721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41988005213378435874172961 31491003910033826905629721)
        ·
          refine ⟨23618252932525370179222291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31491003910033826905629721 23618252932525370179222291)
          ·
            refine ⟨35427379398788055268833437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23618252932525370179222291 35427379398788055268833437)
            ·
              refine ⟨13285267274545520725812539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35427379398788055268833437 13285267274545520725812539)
              ·
                refine ⟨19927900911818281088718809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13285267274545520725812539 19927900911818281088718809)
                ·
                  refine ⟨14945925683863710816539107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19927900911818281088718809 14945925683863710816539107)
                  ·
                    refine ⟨22418888525795566224808661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14945925683863710816539107 22418888525795566224808661)
                    ·
                      refine ⟨525442699823333583393953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 22418888525795566224808661 525442699823333583393953)
                      ·
                        rfl

theorem cell23_1023296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_1023296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023296 prefixEnd_1023296 := by exact prefixLift 1023296
  have htrace : WordTrace (prefixWord ++ tailWord_1023296) baseStart_1023296 baseEnd_1023296 := by
    simpa [prefixWord, tailWord_1023296, baseEnd_1023296] using wordTrace_append hprefix tailTrace_1023296
  have hstable : (prefixWord ++ tailWord_1023296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023296).length < 2 ^ (prefixWord ++ tailWord_1023296).sum := by decide
  have hdescent : baseEnd_1023296 < baseStart_1023296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023303 : List Nat := [1, 1, 4, 1, 2, 3, 2, 1, 3, 5]
def baseStart_1023303 : Nat := 118140960795 + 1023303 * 2 ^ 59
def prefixEnd_1023303 : Nat := 4983230072969 + 3 ^ 40 * 1023303 * 2
def baseEnd_1023303 : Nat := 175148764729305018668807

theorem tailTrace_1023303 : CollatzResearch.WordTrace tailWord_1023303 prefixEnd_1023303 175148764729305018668807 := by
  unfold tailWord_1023303
  simp only [CollatzResearch.WordTrace]
  refine ⟨37322926611755472083658563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24881951074503648055772375 37322926611755472083658563)
  ·
    refine ⟨55984389917633208125487845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37322926611755472083658563 55984389917633208125487845)
    ·
      refine ⟨10497073109556226523528971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55984389917633208125487845 10497073109556226523528971)
      ·
        refine ⟨15745609664334339785293457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10497073109556226523528971 15745609664334339785293457)
        ·
          refine ⟨11809207248250754838970093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15745609664334339785293457 11809207248250754838970093)
          ·
            refine ⟨4428452718094033064613785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11809207248250754838970093 4428452718094033064613785)
            ·
              refine ⟨3321339538570524798460339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4428452718094033064613785 3321339538570524798460339)
              ·
                refine ⟨4982009307855787197690509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3321339538570524798460339 4982009307855787197690509)
                ·
                  refine ⟨1868253490445920199133941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4982009307855787197690509 1868253490445920199133941)
                  ·
                    refine ⟨175148764729305018668807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1868253490445920199133941 175148764729305018668807)
                    ·
                      rfl

theorem cell23_1023303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_1023303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023303 prefixEnd_1023303 := by exact prefixLift 1023303
  have htrace : WordTrace (prefixWord ++ tailWord_1023303) baseStart_1023303 baseEnd_1023303 := by
    simpa [prefixWord, tailWord_1023303, baseEnd_1023303] using wordTrace_append hprefix tailTrace_1023303
  have hstable : (prefixWord ++ tailWord_1023303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023303).length < 2 ^ (prefixWord ++ tailWord_1023303).sum := by decide
  have hdescent : baseEnd_1023303 < baseStart_1023303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023310 : List Nat := [4, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2]
def baseStart_1023310 : Nat := 118140960795 + 1023310 * 2 ^ 59
def prefixEnd_1023310 : Nat := 4983230072969 + 3 ^ 40 * 1023310 * 2
def baseEnd_1023310 : Nat := 525449888552496528618889

theorem tailTrace_1023310 : CollatzResearch.WordTrace tailWord_1023310 prefixEnd_1023310 525449888552496528618889 := by
  unfold tailWord_1023310
  simp only [CollatzResearch.WordTrace]
  refine ⟨4665397740341264034895423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24882121281820074852775589 4665397740341264034895423)
  ·
    refine ⟨6998096610511896052343135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4665397740341264034895423 6998096610511896052343135)
    ·
      refine ⟨10497144915767844078514703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6998096610511896052343135 10497144915767844078514703)
      ·
        refine ⟨15745717373651766117772055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10497144915767844078514703 15745717373651766117772055)
        ·
          refine ⟨23618576060477649176658083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15745717373651766117772055 23618576060477649176658083)
          ·
            refine ⟨35427864090716473764987125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23618576060477649176658083 35427864090716473764987125)
            ·
              refine ⟨3321362258504669415467543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35427864090716473764987125 3321362258504669415467543)
              ·
                refine ⟨4982043387757004123201315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3321362258504669415467543 4982043387757004123201315)
                ·
                  refine ⟨7473065081635506184801973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4982043387757004123201315 7473065081635506184801973)
                  ·
                    refine ⟨700599851403328704825185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7473065081635506184801973 700599851403328704825185)
                    ·
                      refine ⟨525449888552496528618889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 700599851403328704825185 525449888552496528618889)
                      ·
                        rfl

theorem cell23_1023310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2].length) (baseStart_1023310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023310 prefixEnd_1023310 := by exact prefixLift 1023310
  have htrace : WordTrace (prefixWord ++ tailWord_1023310) baseStart_1023310 baseEnd_1023310 := by
    simpa [prefixWord, tailWord_1023310, baseEnd_1023310] using wordTrace_append hprefix tailTrace_1023310
  have hstable : (prefixWord ++ tailWord_1023310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023310).length < 2 ^ (prefixWord ++ tailWord_1023310).sum := by decide
  have hdescent : baseEnd_1023310 < baseStart_1023310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023343 : List Nat := [1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 5]
def baseStart_1023343 : Nat := 118140960795 + 1023343 * 2 ^ 59
def prefixEnd_1023343 : Nat := 4983230072969 + 3 ^ 40 * 1023343 * 2
def baseEnd_1023343 : Nat := 525466833414094899506237

theorem tailTrace_1023343 : CollatzResearch.WordTrace tailWord_1023343 prefixEnd_1023343 525466833414094899506237 := by
  unfold tailWord_1023343
  simp only [CollatzResearch.WordTrace]
  refine ⟨37324385531610558915114683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24882923687740372610076455 37324385531610558915114683)
  ·
    refine ⟨55986578297415838372672025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37324385531610558915114683 55986578297415838372672025)
    ·
      refine ⟨41989933723061878779504019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55986578297415838372672025 41989933723061878779504019)
      ·
        refine ⟨62984900584592818169256029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41989933723061878779504019 62984900584592818169256029)
        ·
          refine ⟨23619337719222306813471011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62984900584592818169256029 23619337719222306813471011)
          ·
            refine ⟨35429006578833460220206517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23619337719222306813471011 35429006578833460220206517)
            ·
              refine ⟨3321469366765636895644361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35429006578833460220206517 3321469366765636895644361)
              ·
                refine ⟨2491102025074227671733271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3321469366765636895644361 2491102025074227671733271)
                ·
                  refine ⟨3736653037611341507599907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2491102025074227671733271 3736653037611341507599907)
                  ·
                    refine ⟨5604979556417012261399861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3736653037611341507599907 5604979556417012261399861)
                    ·
                      refine ⟨525466833414094899506237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5604979556417012261399861 525466833414094899506237)
                      ·
                        rfl

theorem cell23_1023343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 5].length) (baseStart_1023343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023343 prefixEnd_1023343 := by exact prefixLift 1023343
  have htrace : WordTrace (prefixWord ++ tailWord_1023343) baseStart_1023343 baseEnd_1023343 := by
    simpa [prefixWord, tailWord_1023343, baseEnd_1023343] using wordTrace_append hprefix tailTrace_1023343
  have hstable : (prefixWord ++ tailWord_1023343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023343).length < 2 ^ (prefixWord ++ tailWord_1023343).sum := by decide
  have hdescent : baseEnd_1023343 < baseStart_1023343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023357 : List Nat := [1, 4, 1, 1, 2, 2, 1, 4, 3, 2, 2]
def baseStart_1023357 : Nat := 118140960795 + 1023357 * 2 ^ 59
def prefixEnd_1023357 : Nat := 4983230072969 + 3 ^ 40 * 1023357 * 2
def baseEnd_1023357 : Nat := 525474022143257844731173

theorem tailTrace_1023357 : CollatzResearch.WordTrace tailWord_1023357 prefixEnd_1023357 525474022143257844731173 := by
  unfold tailWord_1023357
  simp only [CollatzResearch.WordTrace]
  refine ⟨37324896153559839306124325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24883264102373226204082883 37324896153559839306124325)
  ·
    refine ⟨6998418028792469869898311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37324896153559839306124325 6998418028792469869898311)
    ·
      refine ⟨10497627043188704804847467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6998418028792469869898311 10497627043188704804847467)
      ·
        refine ⟨15746440564783057207271201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10497627043188704804847467 15746440564783057207271201)
        ·
          refine ⟨11809830423587292905453401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15746440564783057207271201 11809830423587292905453401)
          ·
            refine ⟨8857372817690469679090051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11809830423587292905453401 8857372817690469679090051)
            ·
              refine ⟨13286059226535704518635077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8857372817690469679090051 13286059226535704518635077)
              ·
                refine ⟨2491136104975444597244077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13286059226535704518635077 2491136104975444597244077)
                ·
                  refine ⟨934176039365791723966529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2491136104975444597244077 934176039365791723966529)
                  ·
                    refine ⟨700632029524343792974897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 934176039365791723966529 700632029524343792974897)
                    ·
                      refine ⟨525474022143257844731173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 700632029524343792974897 525474022143257844731173)
                      ·
                        rfl

theorem cell23_1023357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 3, 2, 2].length) (baseStart_1023357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023357 prefixEnd_1023357 := by exact prefixLift 1023357
  have htrace : WordTrace (prefixWord ++ tailWord_1023357) baseStart_1023357 baseEnd_1023357 := by
    simpa [prefixWord, tailWord_1023357, baseEnd_1023357] using wordTrace_append hprefix tailTrace_1023357
  have hstable : (prefixWord ++ tailWord_1023357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023357).length < 2 ^ (prefixWord ++ tailWord_1023357).sum := by decide
  have hdescent : baseEnd_1023357 < baseStart_1023357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023363 : List Nat := [1, 1, 1, 3, 5, 2, 1, 9]
def baseStart_1023363 : Nat := 118140960795 + 1023363 * 2 ^ 59
def prefixEnd_1023363 : Nat := 4983230072969 + 3 ^ 40 * 1023363 * 2
def baseEnd_1023363 : Nat := 19462114926932771157635

theorem tailTrace_1023363 : CollatzResearch.WordTrace tailWord_1023363 prefixEnd_1023363 19462114926932771157635 := by
  unfold tailWord_1023363
  simp only [CollatzResearch.WordTrace]
  refine ⟨37325114991538102330842743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24883409994358734887228495 37325114991538102330842743)
  ·
    refine ⟨55987672487307153496264115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37325114991538102330842743 55987672487307153496264115)
    ·
      refine ⟨83981508730960730244396173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55987672487307153496264115 83981508730960730244396173)
      ·
        refine ⟨31493065774110273841648565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83981508730960730244396173 31493065774110273841648565)
        ·
          refine ⟨2952474916322838172654553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31493065774110273841648565 2952474916322838172654553)
          ·
            refine ⟨2214356187242128629490915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2952474916322838172654553 2214356187242128629490915)
            ·
              refine ⟨3321534280863192944236373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2214356187242128629490915 3321534280863192944236373)
              ·
                refine ⟨19462114926932771157635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3321534280863192944236373 19462114926932771157635)
                ·
                  rfl

theorem cell23_1023363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 9].length) (baseStart_1023363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023363 prefixEnd_1023363 := by exact prefixLift 1023363
  have htrace : WordTrace (prefixWord ++ tailWord_1023363) baseStart_1023363 baseEnd_1023363 := by
    simpa [prefixWord, tailWord_1023363, baseEnd_1023363] using wordTrace_append hprefix tailTrace_1023363
  have hstable : (prefixWord ++ tailWord_1023363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023363).length < 2 ^ (prefixWord ++ tailWord_1023363).sum := by decide
  have hdescent : baseEnd_1023363 < baseStart_1023363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023380 : List Nat := [2, 4, 2, 1, 2, 3, 9]
def baseStart_1023380 : Nat := 118140960795 + 1023380 * 2 ^ 59
def prefixEnd_1023380 : Nat := 4983230072969 + 3 ^ 40 * 1023380 * 2
def baseEnd_1023380 : Nat := 6487479409855694503007

theorem tailTrace_1023380 : CollatzResearch.WordTrace tailWord_1023380 prefixEnd_1023380 6487479409855694503007 := by
  unfold tailWord_1023380
  simp only [CollatzResearch.WordTrace]
  refine ⟨18662867516238257117105797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24883823354984342822807729 18662867516238257117105797)
  ·
    refine ⟨3499287659294673209457337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18662867516238257117105797 3499287659294673209457337)
    ·
      refine ⟨2624465744471004907093003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3499287659294673209457337 2624465744471004907093003)
      ·
        refine ⟨3936698616706507360639505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2624465744471004907093003 3936698616706507360639505)
        ·
          refine ⟨2952523962529880520479629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3936698616706507360639505 2952523962529880520479629)
          ·
            refine ⟨1107196485948705195179861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2952523962529880520479629 1107196485948705195179861)
            ·
              refine ⟨6487479409855694503007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1107196485948705195179861 6487479409855694503007)
              ·
                rfl

theorem cell23_1023380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 9].length) (baseStart_1023380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023380 prefixEnd_1023380 := by exact prefixLift 1023380
  have htrace : WordTrace (prefixWord ++ tailWord_1023380) baseStart_1023380 baseEnd_1023380 := by
    simpa [prefixWord, tailWord_1023380, baseEnd_1023380] using wordTrace_append hprefix tailTrace_1023380
  have hstable : (prefixWord ++ tailWord_1023380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023380).length < 2 ^ (prefixWord ++ tailWord_1023380).sum := by decide
  have hdescent : baseEnd_1023380 < baseStart_1023380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023447 : List Nat := [1, 1, 3, 2, 1, 1, 1, 5, 4, 2, 2]
def baseStart_1023447 : Nat := 118140960795 + 1023447 * 2 ^ 59
def prefixEnd_1023447 : Nat := 4983230072969 + 3 ^ 40 * 1023447 * 2
def baseEnd_1023447 : Nat := 525520235402162492605759

theorem tailTrace_1023447 : CollatzResearch.WordTrace tailWord_1023447 prefixEnd_1023447 525520235402162492605759 := by
  unfold tailWord_1023447
  simp only [CollatzResearch.WordTrace]
  refine ⟨37328178723233784676900595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24885452482155856451267063 37328178723233784676900595)
  ·
    refine ⟨55992268084850677015350893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37328178723233784676900595 55992268084850677015350893)
    ·
      refine ⟨20997100531819003880756585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55992268084850677015350893 20997100531819003880756585)
      ·
        refine ⟨15747825398864252910567439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20997100531819003880756585 15747825398864252910567439)
        ·
          refine ⟨23621738098296379365851159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15747825398864252910567439 23621738098296379365851159)
          ·
            refine ⟨35432607147444569048776739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23621738098296379365851159 35432607147444569048776739)
            ·
              refine ⟨53148910721166853573165109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35432607147444569048776739 53148910721166853573165109)
              ·
                refine ⟨4982710380109392522484229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53148910721166853573165109 4982710380109392522484229)
                ·
                  refine ⟨934258196270511097965793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4982710380109392522484229 934258196270511097965793)
                  ·
                    refine ⟨700693647202883323474345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 934258196270511097965793 700693647202883323474345)
                    ·
                      refine ⟨525520235402162492605759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 700693647202883323474345 525520235402162492605759)
                      ·
                        rfl

theorem cell23_1023447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 4, 2, 2].length) (baseStart_1023447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023447 prefixEnd_1023447 := by exact prefixLift 1023447
  have htrace : WordTrace (prefixWord ++ tailWord_1023447) baseStart_1023447 baseEnd_1023447 := by
    simpa [prefixWord, tailWord_1023447, baseEnd_1023447] using wordTrace_append hprefix tailTrace_1023447
  have hstable : (prefixWord ++ tailWord_1023447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023447).length < 2 ^ (prefixWord ++ tailWord_1023447).sum := by decide
  have hdescent : baseEnd_1023447 < baseStart_1023447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023450 : List Nat := [3, 1, 1, 2, 3, 2, 1, 1, 2, 4, 3]
def baseStart_1023450 : Nat := 118140960795 + 1023450 * 2 ^ 59
def prefixEnd_1023450 : Nat := 4983230072969 + 3 ^ 40 * 1023450 * 2
def baseEnd_1023450 : Nat := 525521775844125980868245

theorem tailTrace_1023450 : CollatzResearch.WordTrace tailWord_1023450 prefixEnd_1023450 525521775844125980868245 := by
  unfold tailWord_1023450
  simp only [CollatzResearch.WordTrace]
  refine ⟨9332072035555729047314951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24885525428148610792839869 9332072035555729047314951)
  ·
    refine ⟨13998108053333593570972427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9332072035555729047314951 13998108053333593570972427)
    ·
      refine ⟨20997162080000390356458641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13998108053333593570972427 20997162080000390356458641)
      ·
        refine ⟨15747871560000292767343981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20997162080000390356458641 15747871560000292767343981)
        ·
          refine ⟨5905451835000109787753993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15747871560000292767343981 5905451835000109787753993)
          ·
            refine ⟨4429088876250082340815495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5905451835000109787753993 4429088876250082340815495)
            ·
              refine ⟨6643633314375123511223243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4429088876250082340815495 6643633314375123511223243)
              ·
                refine ⟨9965449971562685266834865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6643633314375123511223243 9965449971562685266834865)
                ·
                  refine ⟨7474087478672013950126149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9965449971562685266834865 7474087478672013950126149)
                  ·
                    refine ⟨1401391402251002615648653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7474087478672013950126149 1401391402251002615648653)
                    ·
                      refine ⟨525521775844125980868245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1401391402251002615648653 525521775844125980868245)
                      ·
                        rfl

theorem cell23_1023450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 2, 4, 3].length) (baseStart_1023450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023450 prefixEnd_1023450 := by exact prefixLift 1023450
  have htrace : WordTrace (prefixWord ++ tailWord_1023450) baseStart_1023450 baseEnd_1023450 := by
    simpa [prefixWord, tailWord_1023450, baseEnd_1023450] using wordTrace_append hprefix tailTrace_1023450
  have hstable : (prefixWord ++ tailWord_1023450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023450).length < 2 ^ (prefixWord ++ tailWord_1023450).sum := by decide
  have hdescent : baseEnd_1023450 < baseStart_1023450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023464 : List Nat := [2, 1, 4, 1, 1, 2, 1, 5, 2, 2, 2]
def baseStart_1023464 : Nat := 118140960795 + 1023464 * 2 ^ 59
def prefixEnd_1023464 : Nat := 4983230072969 + 3 ^ 40 * 1023464 * 2
def baseEnd_1023464 : Nat := 525528964573288926093181

theorem tailTrace_1023464 : CollatzResearch.WordTrace tailWord_1023464 prefixEnd_1023464 525528964573288926093181 := by
  unfold tailWord_1023464
  simp only [CollatzResearch.WordTrace]
  refine ⟨18664399382086098290134723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24885865842781464386846297 18664399382086098290134723)
  ·
    refine ⟨27996599073129147435202085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18664399382086098290134723 27996599073129147435202085)
    ·
      refine ⟨5249362326211715144100391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27996599073129147435202085 5249362326211715144100391)
      ·
        refine ⟨7874043489317572716150587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5249362326211715144100391 7874043489317572716150587)
        ·
          refine ⟨11811065233976359074225881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7874043489317572716150587 11811065233976359074225881)
          ·
            refine ⟨8858298925482269305669411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11811065233976359074225881 8858298925482269305669411)
            ·
              refine ⟨13287448388223403958504117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8858298925482269305669411 13287448388223403958504117)
              ·
                refine ⟨1245698286395944121109761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13287448388223403958504117 1245698286395944121109761)
                ·
                  refine ⟨934273714796958090832321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1245698286395944121109761 934273714796958090832321)
                  ·
                    refine ⟨700705286097718568124241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 934273714796958090832321 700705286097718568124241)
                    ·
                      refine ⟨525528964573288926093181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 700705286097718568124241 525528964573288926093181)
                      ·
                        rfl

theorem cell23_1023464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_1023464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023464 prefixEnd_1023464 := by exact prefixLift 1023464
  have htrace : WordTrace (prefixWord ++ tailWord_1023464) baseStart_1023464 baseEnd_1023464 := by
    simpa [prefixWord, tailWord_1023464, baseEnd_1023464] using wordTrace_append hprefix tailTrace_1023464
  have hstable : (prefixWord ++ tailWord_1023464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023464).length < 2 ^ (prefixWord ++ tailWord_1023464).sum := by decide
  have hdescent : baseEnd_1023464 < baseStart_1023464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023470 : List Nat := [4, 1, 2, 1, 2, 1, 3, 2, 7]
def baseStart_1023470 : Nat := 118140960795 + 1023470 * 2 ^ 59
def prefixEnd_1023470 : Nat := 4983230072969 + 3 ^ 40 * 1023470 * 2
def baseEnd_1023470 : Nat := 58392449495246211402017

theorem tailTrace_1023470 : CollatzResearch.WordTrace tailWord_1023470 prefixEnd_1023470 58392449495246211402017 := by
  unfold tailWord_1023470
  simp only [CollatzResearch.WordTrace]
  refine ⟨4666127200268807450623483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24886011734766973069991909 4666127200268807450623483)
  ·
    refine ⟨6999190800403211175935225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4666127200268807450623483 6999190800403211175935225)
    ·
      refine ⟨5249393100302408381951419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6999190800403211175935225 5249393100302408381951419)
      ·
        refine ⟨7874089650453612572927129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5249393100302408381951419 7874089650453612572927129)
        ·
          refine ⟨5905567237840209429695347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7874089650453612572927129 5905567237840209429695347)
          ·
            refine ⟨8858350856760314144543021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5905567237840209429695347 8858350856760314144543021)
            ·
              refine ⟨3321881571285117804203633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8858350856760314144543021 3321881571285117804203633)
              ·
                refine ⟨2491411178463838353152725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3321881571285117804203633 2491411178463838353152725)
                ·
                  refine ⟨58392449495246211402017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2491411178463838353152725 58392449495246211402017)
                  ·
                    rfl

theorem cell23_1023470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 7].length) (baseStart_1023470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023470 prefixEnd_1023470 := by exact prefixLift 1023470
  have htrace : WordTrace (prefixWord ++ tailWord_1023470) baseStart_1023470 baseEnd_1023470 := by
    simpa [prefixWord, tailWord_1023470, baseEnd_1023470] using wordTrace_append hprefix tailTrace_1023470
  have hstable : (prefixWord ++ tailWord_1023470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023470).length < 2 ^ (prefixWord ++ tailWord_1023470).sum := by decide
  have hdescent : baseEnd_1023470 < baseStart_1023470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023483 : List Nat := [1, 1, 1, 1, 1, 3, 2, 5, 1, 7]
def baseStart_1023483 : Nat := 118140960795 + 1023483 * 2 ^ 59
def prefixEnd_1023483 : Nat := 4983230072969 + 3 ^ 40 * 1023483 * 2
def baseEnd_1023483 : Nat := 175179573568574783918531

theorem tailTrace_1023483 : CollatzResearch.WordTrace tailWord_1023483 prefixEnd_1023483 175179573568574783918531 := by
  unfold tailWord_1023483
  simp only [CollatzResearch.WordTrace]
  refine ⟨37329491751103362825211103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24886327834068908550140735 37329491751103362825211103)
  ·
    refine ⟨55994237626655044237816655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37329491751103362825211103 55994237626655044237816655)
    ·
      refine ⟨83991356439982566356724983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55994237626655044237816655 83991356439982566356724983)
      ·
        refine ⟨125987034659973849535087475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83991356439982566356724983 125987034659973849535087475)
        ·
          refine ⟨188980551989960774302631213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125987034659973849535087475 188980551989960774302631213)
          ·
            refine ⟨70867706996235290363486705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188980551989960774302631213 70867706996235290363486705)
            ·
              refine ⟨53150780247176467772615029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70867706996235290363486705 53150780247176467772615029)
              ·
                refine ⟨4982885648172793853682659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53150780247176467772615029 4982885648172793853682659)
                ·
                  refine ⟨7474328472259190780523989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4982885648172793853682659 7474328472259190780523989)
                  ·
                    refine ⟨175179573568574783918531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7474328472259190780523989 175179573568574783918531)
                    ·
                      rfl

theorem cell23_1023483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 7].length) (baseStart_1023483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023483 prefixEnd_1023483 := by exact prefixLift 1023483
  have htrace : WordTrace (prefixWord ++ tailWord_1023483) baseStart_1023483 baseEnd_1023483 := by
    simpa [prefixWord, tailWord_1023483, baseEnd_1023483] using wordTrace_append hprefix tailTrace_1023483
  have hstable : (prefixWord ++ tailWord_1023483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023483).length < 2 ^ (prefixWord ++ tailWord_1023483).sum := by decide
  have hdescent : baseEnd_1023483 < baseStart_1023483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023513 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 4, 8]
def baseStart_1023513 : Nat := 118140960795 + 1023513 * 2 ^ 59
def prefixEnd_1023513 : Nat := 4983230072969 + 3 ^ 40 * 1023513 * 2
def baseEnd_1023513 : Nat := 175184708375119744793485

theorem tailTrace_1023513 : CollatzResearch.WordTrace tailWord_1023513 prefixEnd_1023513 175184708375119744793485 := by
  unfold tailWord_1023513
  simp only [CollatzResearch.WordTrace]
  refine ⟨37330585940994677948803193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24887057293996451965868795 37330585940994677948803193)
  ·
    refine ⟨27997939455746008461602395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37330585940994677948803193 27997939455746008461602395)
    ·
      refine ⟨41996909183619012692403593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27997939455746008461602395 41996909183619012692403593)
      ·
        refine ⟨31497681887714259519302695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41996909183619012692403593 31497681887714259519302695)
        ·
          refine ⟨47246522831571389278954043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31497681887714259519302695 47246522831571389278954043)
          ·
            refine ⟨70869784247357083918431065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47246522831571389278954043 70869784247357083918431065)
            ·
              refine ⟨53152338185517812938823299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70869784247357083918431065 53152338185517812938823299)
              ·
                refine ⟨79728507278276719408234949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53152338185517812938823299 79728507278276719408234949)
                ·
                  refine ⟨14949095114676884889044053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79728507278276719408234949 14949095114676884889044053)
                  ·
                    refine ⟨175184708375119744793485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14949095114676884889044053 175184708375119744793485)
                    ·
                      rfl

theorem cell23_1023513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 8].length) (baseStart_1023513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023513 prefixEnd_1023513 := by exact prefixLift 1023513
  have htrace : WordTrace (prefixWord ++ tailWord_1023513) baseStart_1023513 baseEnd_1023513 := by
    simpa [prefixWord, tailWord_1023513, baseEnd_1023513] using wordTrace_append hprefix tailTrace_1023513
  have hstable : (prefixWord ++ tailWord_1023513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023513).length < 2 ^ (prefixWord ++ tailWord_1023513).sum := by decide
  have hdescent : baseEnd_1023513 < baseStart_1023513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023530 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 2, 8]
def baseStart_1023530 : Nat := 118140960795 + 1023530 * 2 ^ 59
def prefixEnd_1023530 : Nat := 4983230072969 + 3 ^ 40 * 1023530 * 2
def baseEnd_1023530 : Nat := 175187618098828555955959

theorem tailTrace_1023530 : CollatzResearch.WordTrace tailWord_1023530 prefixEnd_1023530 175187618098828555955959 := by
  unfold tailWord_1023530
  simp only [CollatzResearch.WordTrace]
  refine ⟨9332801495483272463043011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24887470654622059901448029 9332801495483272463043011)
  ·
    refine ⟨13999202243224908694564517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9332801495483272463043011 13999202243224908694564517)
    ·
      refine ⟨2624850420604670380230847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13999202243224908694564517 2624850420604670380230847)
      ·
        refine ⟨3937275630907005570346271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2624850420604670380230847 3937275630907005570346271)
        ·
          refine ⟨5905913446360508355519407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3937275630907005570346271 5905913446360508355519407)
          ·
            refine ⟨8858870169540762533279111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5905913446360508355519407 8858870169540762533279111)
            ·
              refine ⟨13288305254311143799918667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8858870169540762533279111 13288305254311143799918667)
              ·
                refine ⟨19932457881466715699878001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13288305254311143799918667 19932457881466715699878001)
                ·
                  refine ⟨14949343411100036774908501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19932457881466715699878001 14949343411100036774908501)
                  ·
                    refine ⟨175187618098828555955959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14949343411100036774908501 175187618098828555955959)
                    ·
                      rfl

theorem cell23_1023530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_1023530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023530 prefixEnd_1023530 := by exact prefixLift 1023530
  have htrace : WordTrace (prefixWord ++ tailWord_1023530) baseStart_1023530 baseEnd_1023530 := by
    simpa [prefixWord, tailWord_1023530, baseEnd_1023530] using wordTrace_append hprefix tailTrace_1023530
  have hstable : (prefixWord ++ tailWord_1023530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023530).length < 2 ^ (prefixWord ++ tailWord_1023530).sum := by decide
  have hdescent : baseEnd_1023530 < baseStart_1023530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023557 : List Nat := [1, 3, 1, 1, 1, 4, 3, 2, 2, 2, 3]
def baseStart_1023557 : Nat := 118140960795 + 1023557 * 2 ^ 59
def prefixEnd_1023557 : Nat := 4983230072969 + 3 ^ 40 * 1023557 * 2
def baseEnd_1023557 : Nat := 525576718274157062230253

theorem tailTrace_1023557 : CollatzResearch.WordTrace tailWord_1023557 prefixEnd_1023557 525576718274157062230253 := by
  unfold tailWord_1023557
  simp only [CollatzResearch.WordTrace]
  refine ⟨37332190752835273463404925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24888127168556848975603283 37332190752835273463404925)
  ·
    refine ⟨13999571532313227548776847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37332190752835273463404925 13999571532313227548776847)
    ·
      refine ⟨20999357298469841323165271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13999571532313227548776847 20999357298469841323165271)
      ·
        refine ⟨31499035947704761984747907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20999357298469841323165271 31499035947704761984747907)
        ·
          refine ⟨47248553921557142977121861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31499035947704761984747907 47248553921557142977121861)
          ·
            refine ⟨8859103860291964308210349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47248553921557142977121861 8859103860291964308210349)
            ·
              refine ⟨3322163947609486615578881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8859103860291964308210349 3322163947609486615578881)
              ·
                refine ⟨2491622960707114961684161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3322163947609486615578881 2491622960707114961684161)
                ·
                  refine ⟨1868717220530336221263121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2491622960707114961684161 1868717220530336221263121)
                  ·
                    refine ⟨1401537915397752165947341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1868717220530336221263121 1401537915397752165947341)
                    ·
                      refine ⟨525576718274157062230253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1401537915397752165947341 525576718274157062230253)
                      ·
                        rfl

theorem cell23_1023557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 2, 3].length) (baseStart_1023557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023557 prefixEnd_1023557 := by exact prefixLift 1023557
  have htrace : WordTrace (prefixWord ++ tailWord_1023557) baseStart_1023557 baseEnd_1023557 := by
    simpa [prefixWord, tailWord_1023557, baseEnd_1023557] using wordTrace_append hprefix tailTrace_1023557
  have hstable : (prefixWord ++ tailWord_1023557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023557).length < 2 ^ (prefixWord ++ tailWord_1023557).sum := by decide
  have hdescent : baseEnd_1023557 < baseStart_1023557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023564 : List Nat := [2, 2, 1, 3, 1, 5, 1, 1, 3, 4]
def baseStart_1023564 : Nat := 118140960795 + 1023564 * 2 ^ 59
def prefixEnd_1023564 : Nat := 4983230072969 + 3 ^ 40 * 1023564 * 2
def baseEnd_1023564 : Nat := 175193437546246178280907

theorem tailTrace_1023564 : CollatzResearch.WordTrace tailWord_1023564 prefixEnd_1023564 175193437546246178280907 := by
  unfold tailWord_1023564
  simp only [CollatzResearch.WordTrace]
  refine ⟨18666223031904956829454873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24888297375873275772606497 18666223031904956829454873)
  ·
    refine ⟨13999667273928717622091155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18666223031904956829454873 13999667273928717622091155)
    ·
      refine ⟨20999500910893076433136733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13999667273928717622091155 20999500910893076433136733)
      ·
        refine ⟨7874812841584903662426275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20999500910893076433136733 7874812841584903662426275)
        ·
          refine ⟨11812219262377355493639413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7874812841584903662426275 11812219262377355493639413)
          ·
            refine ⟨1107395555847877077528695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11812219262377355493639413 1107395555847877077528695)
            ·
              refine ⟨1661093333771815616293043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1107395555847877077528695 1661093333771815616293043)
              ·
                refine ⟨2491640000657723424439565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1661093333771815616293043 2491640000657723424439565)
                ·
                  refine ⟨934365000246646284164837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2491640000657723424439565 934365000246646284164837)
                  ·
                    refine ⟨175193437546246178280907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 934365000246646284164837 175193437546246178280907)
                    ·
                      rfl

theorem cell23_1023564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 3, 4].length) (baseStart_1023564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023564 prefixEnd_1023564 := by exact prefixLift 1023564
  have htrace : WordTrace (prefixWord ++ tailWord_1023564) baseStart_1023564 baseEnd_1023564 := by
    simpa [prefixWord, tailWord_1023564, baseEnd_1023564] using wordTrace_append hprefix tailTrace_1023564
  have hstable : (prefixWord ++ tailWord_1023564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023564).length < 2 ^ (prefixWord ++ tailWord_1023564).sum := by decide
  have hdescent : baseEnd_1023564 < baseStart_1023564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023621 : List Nat := [1, 3, 1, 1, 4, 1, 3, 4, 1, 1, 3]
def baseStart_1023621 : Nat := 118140960795 + 1023621 * 2 ^ 59
def prefixEnd_1023621 : Nat := 4983230072969 + 3 ^ 40 * 1023621 * 2
def baseEnd_1023621 : Nat := 525609581036044811829959

theorem tailTrace_1023621 : CollatzResearch.WordTrace tailWord_1023621 prefixEnd_1023621 525609581036044811829959 := by
  unfold tailWord_1023621
  simp only [CollatzResearch.WordTrace]
  refine ⟨37334525024603412393734717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24889683349735608262489811 37334525024603412393734717)
  ·
    refine ⟨14000446884226279647650519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37334525024603412393734717 14000446884226279647650519)
    ·
      refine ⟨21000670326339419471475779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14000446884226279647650519 21000670326339419471475779)
      ·
        refine ⟨31501005489509129207213669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21000670326339419471475779 31501005489509129207213669)
        ·
          refine ⟨5906438529282961726352563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31501005489509129207213669 5906438529282961726352563)
          ·
            refine ⟨8859657793924442589528845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5906438529282961726352563 8859657793924442589528845)
            ·
              refine ⟨3322371672721665971073317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8859657793924442589528845 3322371672721665971073317)
              ·
                refine ⟨622944688635312369576247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3322371672721665971073317 622944688635312369576247)
                ·
                  refine ⟨934417032952968554364371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 622944688635312369576247 934417032952968554364371)
                  ·
                    refine ⟨1401625549429452831546557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 934417032952968554364371 1401625549429452831546557)
                    ·
                      refine ⟨525609581036044811829959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1401625549429452831546557 525609581036044811829959)
                      ·
                        rfl

theorem cell23_1023621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 4, 1, 1, 3].length) (baseStart_1023621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023621 prefixEnd_1023621 := by exact prefixLift 1023621
  have htrace : WordTrace (prefixWord ++ tailWord_1023621) baseStart_1023621 baseEnd_1023621 := by
    simpa [prefixWord, tailWord_1023621, baseEnd_1023621] using wordTrace_append hprefix tailTrace_1023621
  have hstable : (prefixWord ++ tailWord_1023621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023621).length < 2 ^ (prefixWord ++ tailWord_1023621).sum := by decide
  have hdescent : baseEnd_1023621 < baseStart_1023621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023661 : List Nat := [1, 5, 2, 1, 1, 1, 1, 2, 5, 2, 2]
def baseStart_1023661 : Nat := 118140960795 + 1023661 * 2 ^ 59
def prefixEnd_1023661 : Nat := 4983230072969 + 3 ^ 40 * 1023661 * 2
def baseEnd_1023661 : Nat := 525630120262224655329775

theorem tailTrace_1023661 : CollatzResearch.WordTrace tailWord_1023661 prefixEnd_1023661 525630120262224655329775 := by
  unfold tailWord_1023661
  simp only [CollatzResearch.WordTrace]
  refine ⟨37335983944458499225190837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24890655962972332816793891 37335983944458499225190837)
  ·
    refine ⟨3500248494792984302361641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37335983944458499225190837 3500248494792984302361641)
    ·
      refine ⟨2625186371094738226771231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3500248494792984302361641 2625186371094738226771231)
      ·
        refine ⟨3937779556642107340156847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2625186371094738226771231 3937779556642107340156847)
        ·
          refine ⟨5906669334963161010235271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3937779556642107340156847 5906669334963161010235271)
          ·
            refine ⟨8860004002444741515352907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5906669334963161010235271 8860004002444741515352907)
            ·
              refine ⟨13290006003667112273029361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8860004002444741515352907 13290006003667112273029361)
              ·
                refine ⟨9967504502750334204772021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13290006003667112273029361 9967504502750334204772021)
                ·
                  refine ⟨934453547132843831697377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9967504502750334204772021 934453547132843831697377)
                  ·
                    refine ⟨700840160349632873773033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 934453547132843831697377 700840160349632873773033)
                    ·
                      refine ⟨525630120262224655329775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 700840160349632873773033 525630120262224655329775)
                      ·
                        rfl

theorem cell23_1023661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_1023661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023661 prefixEnd_1023661 := by exact prefixLift 1023661
  have htrace : WordTrace (prefixWord ++ tailWord_1023661) baseStart_1023661 baseEnd_1023661 := by
    simpa [prefixWord, tailWord_1023661, baseEnd_1023661] using wordTrace_append hprefix tailTrace_1023661
  have hstable : (prefixWord ++ tailWord_1023661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023661).length < 2 ^ (prefixWord ++ tailWord_1023661).sum := by decide
  have hdescent : baseEnd_1023661 < baseStart_1023661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023671 : List Nat := [1, 1, 3, 1, 5, 3, 1, 2, 2, 4]
def baseStart_1023671 : Nat := 118140960795 + 1023671 * 2 ^ 59
def prefixEnd_1023671 : Nat := 4983230072969 + 3 ^ 40 * 1023671 * 2
def baseEnd_1023671 : Nat := 175211751689589872068243

theorem tailTrace_1023671 : CollatzResearch.WordTrace tailWord_1023671 prefixEnd_1023671 175211751689589872068243 := by
  unfold tailWord_1023671
  simp only [CollatzResearch.WordTrace]
  refine ⟨37336348674422270933054867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24890899116281513955369911 37336348674422270933054867)
  ·
    refine ⟨56004523011633406399582301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37336348674422270933054867 56004523011633406399582301)
    ·
      refine ⟨21001696129362527399843363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56004523011633406399582301 21001696129362527399843363)
      ·
        refine ⟨31502544194043791099765045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21001696129362527399843363 31502544194043791099765045)
        ·
          refine ⟨2953363518191605415602973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31502544194043791099765045 2953363518191605415602973)
          ·
            refine ⟨1107511319321852030851115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2953363518191605415602973 1107511319321852030851115)
            ·
              refine ⟨1661266978982778046276673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1107511319321852030851115 1661266978982778046276673)
              ·
                refine ⟨1245950234237083534707505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1661266978982778046276673 1245950234237083534707505)
                ·
                  refine ⟨934462675677812651030629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1245950234237083534707505 934462675677812651030629)
                  ·
                    refine ⟨175211751689589872068243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 934462675677812651030629 175211751689589872068243)
                    ·
                      rfl

theorem cell23_1023671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 2, 4].length) (baseStart_1023671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023671 prefixEnd_1023671 := by exact prefixLift 1023671
  have htrace : WordTrace (prefixWord ++ tailWord_1023671) baseStart_1023671 baseEnd_1023671 := by
    simpa [prefixWord, tailWord_1023671, baseEnd_1023671] using wordTrace_append hprefix tailTrace_1023671
  have hstable : (prefixWord ++ tailWord_1023671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023671).length < 2 ^ (prefixWord ++ tailWord_1023671).sum := by decide
  have hdescent : baseEnd_1023671 < baseStart_1023671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023678 : List Nat := [4, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2]
def baseStart_1023678 : Nat := 118140960795 + 1023678 * 2 ^ 59
def prefixEnd_1023678 : Nat := 4983230072969 + 3 ^ 40 * 1023678 * 2
def baseEnd_1023678 : Nat := 525638849433351088817197

theorem tailTrace_1023678 : CollatzResearch.WordTrace tailWord_1023678 prefixEnd_1023678 525638849433351088817197 := by
  unfold tailWord_1023678
  simp only [CollatzResearch.WordTrace]
  refine ⟨4667075498174613891069961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24891069323597940752373125 4667075498174613891069961)
  ·
    refine ⟨3500306623630960418302471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4667075498174613891069961 3500306623630960418302471)
    ·
      refine ⟨5250459935446440627453707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3500306623630960418302471 5250459935446440627453707)
      ·
        refine ⟨7875689903169660941180561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5250459935446440627453707 7875689903169660941180561)
        ·
          refine ⟨5906767427377245705885421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7875689903169660941180561 5906767427377245705885421)
          ·
            refine ⟨2215037785266467139707033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5906767427377245705885421 2215037785266467139707033)
            ·
              refine ⟨1661278338949850354780275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2215037785266467139707033 1661278338949850354780275)
              ·
                refine ⟨2491917508424775532170413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1661278338949850354780275 2491917508424775532170413)
                ·
                  refine ⟨934469065659290824563905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2491917508424775532170413 934469065659290824563905)
                  ·
                    refine ⟨700851799244468118422929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 934469065659290824563905 700851799244468118422929)
                    ·
                      refine ⟨525638849433351088817197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 700851799244468118422929 525638849433351088817197)
                      ·
                        rfl

theorem cell23_1023678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_1023678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023678 prefixEnd_1023678 := by exact prefixLift 1023678
  have htrace : WordTrace (prefixWord ++ tailWord_1023678) baseStart_1023678 baseEnd_1023678 := by
    simpa [prefixWord, tailWord_1023678, baseEnd_1023678] using wordTrace_append hprefix tailTrace_1023678
  have hstable : (prefixWord ++ tailWord_1023678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023678).length < 2 ^ (prefixWord ++ tailWord_1023678).sum := by decide
  have hdescent : baseEnd_1023678 < baseStart_1023678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023747 : List Nat := [1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 4]
def baseStart_1023747 : Nat := 118140960795 + 1023747 * 2 ^ 59
def prefixEnd_1023747 : Nat := 4983230072969 + 3 ^ 40 * 1023747 * 2
def baseEnd_1023747 : Nat := 525674279598511318854379

theorem tailTrace_1023747 : CollatzResearch.WordTrace tailWord_1023747 prefixEnd_1023747 525674279598511318854379 := by
  unfold tailWord_1023747
  simp only [CollatzResearch.WordTrace]
  refine ⟨37339120622146935912821495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24892747081431290608547663 37339120622146935912821495)
  ·
    refine ⟨56008680933220403869232243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37339120622146935912821495 56008680933220403869232243)
    ·
      refine ⟨84013021399830605803848365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56008680933220403869232243 84013021399830605803848365)
      ·
        refine ⟨31504883024936477176443137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84013021399830605803848365 31504883024936477176443137)
        ·
          refine ⟨23628662268702357882332353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31504883024936477176443137 23628662268702357882332353)
          ·
            refine ⟨17721496701526768411749265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23628662268702357882332353 17721496701526768411749265)
            ·
              refine ⟨13291122526145076308811949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17721496701526768411749265 13291122526145076308811949)
              ·
                refine ⟨4984170947304403615804481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13291122526145076308811949 4984170947304403615804481)
                ·
                  refine ⟨3738128210478302711853361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4984170947304403615804481 3738128210478302711853361)
                  ·
                    refine ⟨2803596157858727033890021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3738128210478302711853361 2803596157858727033890021)
                    ·
                      refine ⟨525674279598511318854379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2803596157858727033890021 525674279598511318854379)
                      ·
                        rfl

theorem cell23_1023747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 4].length) (baseStart_1023747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023747 prefixEnd_1023747 := by exact prefixLift 1023747
  have htrace : WordTrace (prefixWord ++ tailWord_1023747) baseStart_1023747 baseEnd_1023747 := by
    simpa [prefixWord, tailWord_1023747, baseEnd_1023747] using wordTrace_append hprefix tailTrace_1023747
  have hstable : (prefixWord ++ tailWord_1023747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023747).length < 2 ^ (prefixWord ++ tailWord_1023747).sum := by decide
  have hdescent : baseEnd_1023747 < baseStart_1023747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023821 : List Nat := [1, 6, 1, 2, 1, 2, 1, 1, 1, 7]
def baseStart_1023821 : Nat := 118140960795 + 1023821 * 2 ^ 59
def prefixEnd_1023821 : Nat := 4983230072969 + 3 ^ 40 * 1023821 * 2
def baseEnd_1023821 : Nat := 175237425722314676443013

theorem tailTrace_1023821 : CollatzResearch.WordTrace tailWord_1023821 prefixEnd_1023821 175237425722314676443013 := by
  unfold tailWord_1023821
  simp only [CollatzResearch.WordTrace]
  refine ⟨37341819623878846551015317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24894546415919231034010211 37341819623878846551015317)
  ·
    refine ⟨1750397794869320932078843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37341819623878846551015317 1750397794869320932078843)
    ·
      refine ⟨2625596692303981398118265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1750397794869320932078843 2625596692303981398118265)
      ·
        refine ⟨1969197519227986048588699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2625596692303981398118265 1969197519227986048588699)
        ·
          refine ⟨2953796278841979072883049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1969197519227986048588699 2953796278841979072883049)
          ·
            refine ⟨2215347209131484304662287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2953796278841979072883049 2215347209131484304662287)
            ·
              refine ⟨3323020813697226456993431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2215347209131484304662287 3323020813697226456993431)
              ·
                refine ⟨4984531220545839685490147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3323020813697226456993431 4984531220545839685490147)
                ·
                  refine ⟨7476796830818759528235221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4984531220545839685490147 7476796830818759528235221)
                  ·
                    refine ⟨175237425722314676443013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7476796830818759528235221 175237425722314676443013)
                    ·
                      rfl

theorem cell23_1023821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_1023821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023821 prefixEnd_1023821 := by exact prefixLift 1023821
  have htrace : WordTrace (prefixWord ++ tailWord_1023821) baseStart_1023821 baseEnd_1023821 := by
    simpa [prefixWord, tailWord_1023821, baseEnd_1023821] using wordTrace_append hprefix tailTrace_1023821
  have hstable : (prefixWord ++ tailWord_1023821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023821).length < 2 ^ (prefixWord ++ tailWord_1023821).sum := by decide
  have hdescent : baseEnd_1023821 < baseStart_1023821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023824 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 3, 6, 2]
def baseStart_1023824 : Nat := 118140960795 + 1023824 * 2 ^ 59
def prefixEnd_1023824 : Nat := 4983230072969 + 3 ^ 40 * 1023824 * 2
def baseEnd_1023824 : Nat := 525713817608907517591525

theorem tailTrace_1023824 : CollatzResearch.WordTrace tailWord_1023824 prefixEnd_1023824 525713817608907517591525 := by
  unfold tailWord_1023824
  simp only [CollatzResearch.WordTrace]
  refine ⟨18670964521433989031687263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24894619361911985375583017 18670964521433989031687263)
  ·
    refine ⟨28006446782150983547530895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18670964521433989031687263 28006446782150983547530895)
    ·
      refine ⟨42009670173226475321296343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28006446782150983547530895 42009670173226475321296343)
      ·
        refine ⟨63014505259839712981944515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42009670173226475321296343 63014505259839712981944515)
        ·
          refine ⟨94521757889759569472916773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63014505259839712981944515 94521757889759569472916773)
          ·
            refine ⟨17722829604329919276171895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94521757889759569472916773 17722829604329919276171895)
            ·
              refine ⟨26584244406494878914257843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17722829604329919276171895 26584244406494878914257843)
              ·
                refine ⟨39876366609742318371386765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26584244406494878914257843 39876366609742318371386765)
                ·
                  refine ⟨14953637478653369389270037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39876366609742318371386765 14953637478653369389270037)
                  ·
                    refine ⟨700951756811876690122033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14953637478653369389270037 700951756811876690122033)
                    ·
                      refine ⟨525713817608907517591525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 700951756811876690122033 525713817608907517591525)
                      ·
                        rfl

theorem cell23_1023824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 3, 6, 2].length) (baseStart_1023824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023824 prefixEnd_1023824 := by exact prefixLift 1023824
  have htrace : WordTrace (prefixWord ++ tailWord_1023824) baseStart_1023824 baseEnd_1023824 := by
    simpa [prefixWord, tailWord_1023824, baseEnd_1023824] using wordTrace_append hprefix tailTrace_1023824
  have hstable : (prefixWord ++ tailWord_1023824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023824).length < 2 ^ (prefixWord ++ tailWord_1023824).sum := by decide
  have hdescent : baseEnd_1023824 < baseStart_1023824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023834 : List Nat := [3, 1, 1, 2, 1, 3, 1, 2, 5, 4]
def baseStart_1023834 : Nat := 118140960795 + 1023834 * 2 ^ 59
def prefixEnd_1023834 : Nat := 4983230072969 + 3 ^ 40 * 1023834 * 2
def baseEnd_1023834 : Nat := 175239650805150826155493

theorem tailTrace_1023834 : CollatzResearch.WordTrace tailWord_1023834 prefixEnd_1023834 175239650805150826155493 := by
  unfold tailWord_1023834
  simp only [CollatzResearch.WordTrace]
  refine ⟨9335573443207937442809639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24894862515221166514159037 9335573443207937442809639)
  ·
    refine ⟨14003360164811906164214459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9335573443207937442809639 14003360164811906164214459)
    ·
      refine ⟨21005040247217859246321689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14003360164811906164214459 21005040247217859246321689)
      ·
        refine ⟨15753780185413394434741267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21005040247217859246321689 15753780185413394434741267)
        ·
          refine ⟨23630670278120091652111901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15753780185413394434741267 23630670278120091652111901)
          ·
            refine ⟨8861501354295034369541963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23630670278120091652111901 8861501354295034369541963)
            ·
              refine ⟨13292252031442551554312945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8861501354295034369541963 13292252031442551554312945)
              ·
                refine ⟨9969189023581913665734709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13292252031442551554312945 9969189023581913665734709)
                ·
                  refine ⟨934611470960804406162629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9969189023581913665734709 934611470960804406162629)
                  ·
                    refine ⟨175239650805150826155493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 934611470960804406162629 175239650805150826155493)
                    ·
                      rfl

theorem cell23_1023834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 5, 4].length) (baseStart_1023834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023834 prefixEnd_1023834 := by exact prefixLift 1023834
  have htrace : WordTrace (prefixWord ++ tailWord_1023834) baseStart_1023834 baseEnd_1023834 := by
    simpa [prefixWord, tailWord_1023834, baseEnd_1023834] using wordTrace_append hprefix tailTrace_1023834
  have hstable : (prefixWord ++ tailWord_1023834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023834).length < 2 ^ (prefixWord ++ tailWord_1023834).sum := by decide
  have hdescent : baseEnd_1023834 < baseStart_1023834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023867 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 6]
def baseStart_1023867 : Nat := 118140960795 + 1023867 * 2 ^ 59
def prefixEnd_1023867 : Nat := 4983230072969 + 3 ^ 40 * 1023867 * 2
def baseEnd_1023867 : Nat := 525735897277050849353827

theorem tailTrace_1023867 : CollatzResearch.WordTrace tailWord_1023867 prefixEnd_1023867 525735897277050849353827 := by
  unfold tailWord_1023867
  simp only [CollatzResearch.WordTrace]
  refine ⟨37343497381712196407189855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24895664921141464271459903 37343497381712196407189855)
  ·
    refine ⟨56015246072568294610784783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37343497381712196407189855 56015246072568294610784783)
    ·
      refine ⟨84022869108852441916177175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56015246072568294610784783 84022869108852441916177175)
      ·
        refine ⟨126034303663278662874265763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84022869108852441916177175 126034303663278662874265763)
        ·
          refine ⟨189051455494917994311398645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126034303663278662874265763 189051455494917994311398645)
          ·
            refine ⟨17723573952648561966693623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 189051455494917994311398645 17723573952648561966693623)
            ·
              refine ⟨26585360928972842950040435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17723573952648561966693623 26585360928972842950040435)
              ·
                refine ⟨39878041393459264425060653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26585360928972842950040435 39878041393459264425060653)
                ·
                  refine ⟨14954265522547224159397745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39878041393459264425060653 14954265522547224159397745)
                  ·
                    refine ⟨11215699141910418119548309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14954265522547224159397745 11215699141910418119548309)
                    ·
                      refine ⟨525735897277050849353827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11215699141910418119548309 525735897277050849353827)
                      ·
                        rfl

theorem cell23_1023867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 6].length) (baseStart_1023867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023867 prefixEnd_1023867 := by exact prefixLift 1023867
  have htrace : WordTrace (prefixWord ++ tailWord_1023867) baseStart_1023867 baseEnd_1023867 := by
    simpa [prefixWord, tailWord_1023867, baseEnd_1023867] using wordTrace_append hprefix tailTrace_1023867
  have hstable : (prefixWord ++ tailWord_1023867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023867).length < 2 ^ (prefixWord ++ tailWord_1023867).sum := by decide
  have hdescent : baseEnd_1023867 < baseStart_1023867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023887 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 7]
def baseStart_1023887 : Nat := 118140960795 + 1023887 * 2 ^ 59
def prefixEnd_1023887 : Nat := 4983230072969 + 3 ^ 40 * 1023887 * 2
def baseEnd_1023887 : Nat := 525746166890140771103735

theorem tailTrace_1023887 : CollatzResearch.WordTrace tailWord_1023887 prefixEnd_1023887 525746166890140771103735 := by
  unfold tailWord_1023887
  simp only [CollatzResearch.WordTrace]
  refine ⟨37344226841639739822917915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24896151227759826548611943 37344226841639739822917915)
  ·
    refine ⟨56016340262459609734376873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37344226841639739822917915 56016340262459609734376873)
    ·
      refine ⟨42012255196844707300782655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56016340262459609734376873 42012255196844707300782655)
      ·
        refine ⟨63018382795267060951173983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42012255196844707300782655 63018382795267060951173983)
        ·
          refine ⟨94527574192900591426760975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63018382795267060951173983 94527574192900591426760975)
          ·
            refine ⟨141791361289350887140141463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94527574192900591426760975 141791361289350887140141463)
            ·
              refine ⟨212687041934026330710212195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141791361289350887140141463 212687041934026330710212195)
              ·
                refine ⟨319030562901039496065318293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212687041934026330710212195 319030562901039496065318293)
                ·
                  refine ⟨14954557635986226378061795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 319030562901039496065318293 14954557635986226378061795)
                  ·
                    refine ⟨22431836453979339567092693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14954557635986226378061795 22431836453979339567092693)
                    ·
                      refine ⟨525746166890140771103735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 22431836453979339567092693 525746166890140771103735)
                      ·
                        rfl

theorem cell23_1023887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 7].length) (baseStart_1023887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023887 prefixEnd_1023887 := by exact prefixLift 1023887
  have htrace : WordTrace (prefixWord ++ tailWord_1023887) baseStart_1023887 baseEnd_1023887 := by
    simpa [prefixWord, tailWord_1023887, baseEnd_1023887] using wordTrace_append hprefix tailTrace_1023887
  have hstable : (prefixWord ++ tailWord_1023887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023887).length < 2 ^ (prefixWord ++ tailWord_1023887).sum := by decide
  have hdescent : baseEnd_1023887 < baseStart_1023887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023902 : List Nat := [4, 3, 1, 3, 1, 2, 1, 1, 3, 4]
def baseStart_1023902 : Nat := 118140960795 + 1023902 * 2 ^ 59
def prefixEnd_1023902 : Nat := 4983230072969 + 3 ^ 40 * 1023902 * 2
def baseEnd_1023902 : Nat := 175251289699986070805389

theorem tailTrace_1023902 : CollatzResearch.WordTrace tailWord_1023902 prefixEnd_1023902 175251289699986070805389 := by
  unfold tailWord_1023902
  simp only [CollatzResearch.WordTrace]
  refine ⟨4668096742073174673089245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24896515957723598256475973 4668096742073174673089245)
  ·
    refine ⟨1750536278277440502408467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4668096742073174673089245 1750536278277440502408467)
    ·
      refine ⟨2625804417416160753612701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1750536278277440502408467 2625804417416160753612701)
      ·
        refine ⟨984676656531060282604763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2625804417416160753612701 984676656531060282604763)
        ·
          refine ⟨1477014984796590423907145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 984676656531060282604763 1477014984796590423907145)
          ·
            refine ⟨1107761238597442817930359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1477014984796590423907145 1107761238597442817930359)
            ·
              refine ⟨1661641857896164226895539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1107761238597442817930359 1661641857896164226895539)
              ·
                refine ⟨2492462786844246340343309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1661641857896164226895539 2492462786844246340343309)
                ·
                  refine ⟨934673545066592377628741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2492462786844246340343309 934673545066592377628741)
                  ·
                    refine ⟨175251289699986070805389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 934673545066592377628741 175251289699986070805389)
                    ·
                      rfl

theorem cell23_1023902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_1023902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023902 prefixEnd_1023902 := by exact prefixLift 1023902
  have htrace : WordTrace (prefixWord ++ tailWord_1023902) baseStart_1023902 baseEnd_1023902 := by
    simpa [prefixWord, tailWord_1023902, baseEnd_1023902] using wordTrace_append hprefix tailTrace_1023902
  have hstable : (prefixWord ++ tailWord_1023902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023902).length < 2 ^ (prefixWord ++ tailWord_1023902).sum := by decide
  have hdescent : baseEnd_1023902 < baseStart_1023902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023908 : List Nat := [2, 3, 1, 2, 1, 3, 3, 1, 3, 1, 3]
def baseStart_1023908 : Nat := 118140960795 + 1023908 * 2 ^ 59
def prefixEnd_1023908 : Nat := 4983230072969 + 3 ^ 40 * 1023908 * 2
def baseEnd_1023908 : Nat := 525756949983885188941139

theorem tailTrace_1023908 : CollatzResearch.WordTrace tailWord_1023908 prefixEnd_1023908 525756949983885188941139 := by
  unfold tailWord_1023908
  simp only [CollatzResearch.WordTrace]
  refine ⟨18672496387281830204716189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24896661849709106939621585 18672496387281830204716189)
  ·
    refine ⟨7002186145230686326768571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18672496387281830204716189 7002186145230686326768571)
    ·
      refine ⟨10503279217846029490152857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7002186145230686326768571 10503279217846029490152857)
      ·
        refine ⟨7877459413384522117614643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10503279217846029490152857 7877459413384522117614643)
        ·
          refine ⟨11816189120076783176421965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7877459413384522117614643 11816189120076783176421965)
          ·
            refine ⟨4431070920028793691158237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11816189120076783176421965 4431070920028793691158237)
            ·
              refine ⟨1661651595010797634184339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4431070920028793691158237 1661651595010797634184339)
              ·
                refine ⟨2492477392516196451276509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1661651595010797634184339 2492477392516196451276509)
                ·
                  refine ⟨934679022193573669228691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2492477392516196451276509 934679022193573669228691)
                  ·
                    refine ⟨1402018533290360503843037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 934679022193573669228691 1402018533290360503843037)
                    ·
                      refine ⟨525756949983885188941139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1402018533290360503843037 525756949983885188941139)
                      ·
                        rfl

theorem cell23_1023908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_1023908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023908 prefixEnd_1023908 := by exact prefixLift 1023908
  have htrace : WordTrace (prefixWord ++ tailWord_1023908) baseStart_1023908 baseEnd_1023908 := by
    simpa [prefixWord, tailWord_1023908, baseEnd_1023908] using wordTrace_append hprefix tailTrace_1023908
  have hstable : (prefixWord ++ tailWord_1023908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023908).length < 2 ^ (prefixWord ++ tailWord_1023908).sum := by decide
  have hdescent : baseEnd_1023908 < baseStart_1023908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023954 : List Nat := [3, 2, 2, 3, 13]
def baseStart_1023954 : Nat := 118140960795 + 1023954 * 2 ^ 59
def prefixEnd_1023954 : Nat := 4983230072969 + 3 ^ 40 * 1023954 * 2
def baseEnd_1023954 : Nat := 721235349923171480063

theorem tailTrace_1023954 : CollatzResearch.WordTrace tailWord_1023954 prefixEnd_1023954 721235349923171480063 := by
  unfold tailWord_1023954
  simp only [CollatzResearch.WordTrace]
  refine ⟨9336667633099252566401729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24897780354931340177071277 9336667633099252566401729)
  ·
    refine ⟨7002500724824439424801297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9336667633099252566401729 7002500724824439424801297)
    ·
      refine ⟨5251875543618329568600973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7002500724824439424801297 5251875543618329568600973)
      ·
        refine ⟨1969453328856873588225365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5251875543618329568600973 1969453328856873588225365)
        ·
          refine ⟨721235349923171480063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 1969453328856873588225365 721235349923171480063)
          ·
            rfl

theorem cell23_1023954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 13].length) (baseStart_1023954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023954 prefixEnd_1023954 := by exact prefixLift 1023954
  have htrace : WordTrace (prefixWord ++ tailWord_1023954) baseStart_1023954 baseEnd_1023954 := by
    simpa [prefixWord, tailWord_1023954, baseEnd_1023954] using wordTrace_append hprefix tailTrace_1023954
  have hstable : (prefixWord ++ tailWord_1023954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023954).length < 2 ^ (prefixWord ++ tailWord_1023954).sum := by decide
  have hdescent : baseEnd_1023954 < baseStart_1023954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023971 : List Nat := [1, 1, 1, 6, 1, 4, 1, 8]
def baseStart_1023971 : Nat := 118140960795 + 1023971 * 2 ^ 59
def prefixEnd_1023971 : Nat := 4983230072969 + 3 ^ 40 * 1023971 * 2
def baseEnd_1023971 : Nat := 19473677750559942313087

theorem tailTrace_1023971 : CollatzResearch.WordTrace tailWord_1023971 prefixEnd_1023971 19473677750559942313087 := by
  unfold tailWord_1023971
  simp only [CollatzResearch.WordTrace]
  refine ⟨37347290573335422168975767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24898193715556948112650511 37347290573335422168975767)
  ·
    refine ⟨56020935860003133253463651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37347290573335422168975767 56020935860003133253463651)
    ·
      refine ⟨84031403790004699880195477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56020935860003133253463651 84031403790004699880195477)
      ·
        refine ⟨3938972052656470306884163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 84031403790004699880195477 3938972052656470306884163)
        ·
          refine ⟨5908458078984705460326245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3938972052656470306884163 5908458078984705460326245)
          ·
            refine ⟨1107835889809632273811171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5908458078984705460326245 1107835889809632273811171)
            ·
              refine ⟨1661753834714448410716757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1107835889809632273811171 1661753834714448410716757)
              ·
                refine ⟨19473677750559942313087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1661753834714448410716757 19473677750559942313087)
                ·
                  rfl

theorem cell23_1023971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 8].length) (baseStart_1023971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023971 prefixEnd_1023971 := by exact prefixLift 1023971
  have htrace : WordTrace (prefixWord ++ tailWord_1023971) baseStart_1023971 baseEnd_1023971 := by
    simpa [prefixWord, tailWord_1023971, baseEnd_1023971] using wordTrace_append hprefix tailTrace_1023971
  have hstable : (prefixWord ++ tailWord_1023971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023971).length < 2 ^ (prefixWord ++ tailWord_1023971).sum := by decide
  have hdescent : baseEnd_1023971 < baseStart_1023971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024042 : List Nat := [3, 1, 4, 1, 2, 2, 2, 2, 1, 3, 2]
def baseStart_1024042 : Nat := 118140960795 + 1024042 * 2 ^ 59
def prefixEnd_1024042 : Nat := 4983230072969 + 3 ^ 40 * 1024042 * 2
def baseEnd_1024042 : Nat := 525825756391587664665523

theorem tailTrace_1024042 : CollatzResearch.WordTrace tailWord_1024042 prefixEnd_1024042 525825756391587664665523 := by
  unfold tailWord_1024042
  simp only [CollatzResearch.WordTrace]
  refine ⟨9337470039019550323702595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24899920104052134196540253 9337470039019550323702595)
  ·
    refine ⟨14006205058529325485553893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9337470039019550323702595 14006205058529325485553893)
    ·
      refine ⟨2626163448474248528541355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14006205058529325485553893 2626163448474248528541355)
      ·
        refine ⟨3939245172711372792812033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2626163448474248528541355 3939245172711372792812033)
        ·
          refine ⟨2954433879533529594609025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3939245172711372792812033 2954433879533529594609025)
          ·
            refine ⟨2215825409650147195956769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2954433879533529594609025 2215825409650147195956769)
            ·
              refine ⟨1661869057237610396967577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2215825409650147195956769 1661869057237610396967577)
              ·
                refine ⟨1246401792928207797725683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1661869057237610396967577 1246401792928207797725683)
                ·
                  refine ⟨1869602689392311696588525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1246401792928207797725683 1869602689392311696588525)
                  ·
                    refine ⟨701101008522116886220697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1869602689392311696588525 701101008522116886220697)
                    ·
                      refine ⟨525825756391587664665523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 701101008522116886220697 525825756391587664665523)
                      ·
                        rfl

theorem cell23_1024042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_1024042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1024042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1024042 prefixEnd_1024042 := by exact prefixLift 1024042
  have htrace : WordTrace (prefixWord ++ tailWord_1024042) baseStart_1024042 baseEnd_1024042 := by
    simpa [prefixWord, tailWord_1024042, baseEnd_1024042] using wordTrace_append hprefix tailTrace_1024042
  have hstable : (prefixWord ++ tailWord_1024042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024042).length < 2 ^ (prefixWord ++ tailWord_1024042).sum := by decide
  have hdescent : baseEnd_1024042 < baseStart_1024042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024044 : List Nat := [2, 2, 1, 1, 1, 2, 2, 3, 9]
def baseStart_1024044 : Nat := 118140960795 + 1024044 * 2 ^ 59
def prefixEnd_1024044 : Nat := 4983230072969 + 3 ^ 40 * 1024044 * 2
def baseEnd_1024044 : Nat := 58425198150321850760057

theorem tailTrace_1024044 : CollatzResearch.WordTrace tailWord_1024044 prefixEnd_1024044 58425198150321850760057 := by
  unfold tailWord_1024044
  simp only [CollatzResearch.WordTrace]
  refine ⟨18674976551035477818191593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24899968734713970424255457 18674976551035477818191593)
  ·
    refine ⟨14006232413276608363643695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18674976551035477818191593 14006232413276608363643695)
    ·
      refine ⟨21009348619914912545465543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14006232413276608363643695 21009348619914912545465543)
      ·
        refine ⟨31514022929872368818198315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21009348619914912545465543 31514022929872368818198315)
        ·
          refine ⟨47271034394808553227297473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31514022929872368818198315 47271034394808553227297473)
          ·
            refine ⟨35453275796106414920473105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47271034394808553227297473 35453275796106414920473105)
            ·
              refine ⟨26589956847079811190354829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35453275796106414920473105 26589956847079811190354829)
              ·
                refine ⟨9971233817654929196383061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26589956847079811190354829 9971233817654929196383061)
                ·
                  refine ⟨58425198150321850760057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9971233817654929196383061 58425198150321850760057)
                  ·
                    rfl

theorem cell23_1024044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 9].length) (baseStart_1024044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1024044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1024044 prefixEnd_1024044 := by exact prefixLift 1024044
  have htrace : WordTrace (prefixWord ++ tailWord_1024044) baseStart_1024044 baseEnd_1024044 := by
    simpa [prefixWord, tailWord_1024044, baseEnd_1024044] using wordTrace_append hprefix tailTrace_1024044
  have hstable : (prefixWord ++ tailWord_1024044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024044).length < 2 ^ (prefixWord ++ tailWord_1024044).sum := by decide
  have hdescent : baseEnd_1024044 < baseStart_1024044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024078 : List Nat := [4, 1, 1, 1, 1, 6, 1, 1, 7]
def baseStart_1024078 : Nat := 118140960795 + 1024078 * 2 ^ 59
def prefixEnd_1024078 : Nat := 4983230072969 + 3 ^ 40 * 1024078 * 2
def baseEnd_1024078 : Nat := 58427137966127724868373

theorem tailTrace_1024078 : CollatzResearch.WordTrace tailWord_1024078 prefixEnd_1024078 58427137966127724868373 := by
  unfold tailWord_1024078
  simp only [CollatzResearch.WordTrace]
  refine ⟨4668899147993472430390111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24900795455965186295413925 4668899147993472430390111)
  ·
    refine ⟨7003348721990208645585167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4668899147993472430390111 7003348721990208645585167)
    ·
      refine ⟨10505023082985312968377751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7003348721990208645585167 10505023082985312968377751)
      ·
        refine ⟨15757534624477969452566627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10505023082985312968377751 15757534624477969452566627)
        ·
          refine ⟨23636301936716954178849941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15757534624477969452566627 23636301936716954178849941)
          ·
            refine ⟨1107951653283607227133591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23636301936716954178849941 1107951653283607227133591)
            ·
              refine ⟨1661927479925410840700387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1107951653283607227133591 1661927479925410840700387)
              ·
                refine ⟨2492891219888116261050581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1661927479925410840700387 2492891219888116261050581)
                ·
                  refine ⟨58427137966127724868373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2492891219888116261050581 58427137966127724868373)
                  ·
                    rfl

theorem cell23_1024078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 7].length) (baseStart_1024078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1024078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1024078 prefixEnd_1024078 := by exact prefixLift 1024078
  have htrace : WordTrace (prefixWord ++ tailWord_1024078) baseStart_1024078 baseEnd_1024078 := by
    simpa [prefixWord, tailWord_1024078, baseEnd_1024078] using wordTrace_append hprefix tailTrace_1024078
  have hstable : (prefixWord ++ tailWord_1024078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024078).length < 2 ^ (prefixWord ++ tailWord_1024078).sum := by decide
  have hdescent : baseEnd_1024078 < baseStart_1024078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024108 : List Nat := [2, 2, 1, 1, 3, 4, 2, 1, 2, 5]
def baseStart_1024108 : Nat := 118140960795 + 1024108 * 2 ^ 59
def prefixEnd_1024108 : Nat := 4983230072969 + 3 ^ 40 * 1024108 * 2
def baseEnd_1024108 : Nat := 175286548704928135480073

theorem tailTrace_1024108 : CollatzResearch.WordTrace tailWord_1024108 prefixEnd_1024108 175286548704928135480073 := by
  unfold tailWord_1024108
  simp only [CollatzResearch.WordTrace]
  refine ⟨18676143686919547283356489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24901524915892729711141985 18676143686919547283356489)
  ·
    refine ⟨14007107765189660462517367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18676143686919547283356489 14007107765189660462517367)
    ·
      refine ⟨21010661647784490693776051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14007107765189660462517367 21010661647784490693776051)
      ·
        refine ⟨31515992471676736040664077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21010661647784490693776051 31515992471676736040664077)
        ·
          refine ⟨11818497176878776015249029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31515992471676736040664077 11818497176878776015249029)
          ·
            refine ⟨2215968220664770502859193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11818497176878776015249029 2215968220664770502859193)
            ·
              refine ⟨1661976165498577877144395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2215968220664770502859193 1661976165498577877144395)
              ·
                refine ⟨2492964248247866815716593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1661976165498577877144395 2492964248247866815716593)
                ·
                  refine ⟨1869723186185900111787445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2492964248247866815716593 1869723186185900111787445)
                  ·
                    refine ⟨175286548704928135480073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1869723186185900111787445 175286548704928135480073)
                    ·
                      rfl

theorem cell23_1024108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 5].length) (baseStart_1024108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1024108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1024108 prefixEnd_1024108 := by exact prefixLift 1024108
  have htrace : WordTrace (prefixWord ++ tailWord_1024108) baseStart_1024108 baseEnd_1024108 := by
    simpa [prefixWord, tailWord_1024108, baseEnd_1024108] using wordTrace_append hprefix tailTrace_1024108
  have hstable : (prefixWord ++ tailWord_1024108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024108).length < 2 ^ (prefixWord ++ tailWord_1024108).sum := by decide
  have hdescent : baseEnd_1024108 < baseStart_1024108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024118 : List Nat := [5, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5]
def baseStart_1024118 : Nat := 118140960795 + 1024118 * 2 ^ 59
def prefixEnd_1024118 : Nat := 4983230072969 + 3 ^ 40 * 1024118 * 2
def baseEnd_1024118 : Nat := 525864780921329367315173

theorem tailTrace_1024118 : CollatzResearch.WordTrace tailWord_1024118 prefixEnd_1024118 525864780921329367315173 := by
  unfold tailWord_1024118
  simp only [CollatzResearch.WordTrace]
  refine ⟨2334540756487679142161063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24901768069201910849718005 2334540756487679142161063)
  ·
    refine ⟨3501811134731518713241595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2334540756487679142161063 3501811134731518713241595)
    ·
      refine ⟨5252716702097278069862393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3501811134731518713241595 5252716702097278069862393)
      ·
        refine ⟨3939537526572958552396795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5252716702097278069862393 3939537526572958552396795)
        ·
          refine ⟨5909306289859437828595193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3939537526572958552396795 5909306289859437828595193)
          ·
            refine ⟨4431979717394578371446395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5909306289859437828595193 4431979717394578371446395)
            ·
              refine ⟨6647969576091867557169593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4431979717394578371446395 6647969576091867557169593)
              ·
                refine ⟨4985977182068900667877195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6647969576091867557169593 4985977182068900667877195)
                ·
                  refine ⟨7478965773103351001815793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4985977182068900667877195 7478965773103351001815793)
                  ·
                    refine ⟨5609224329827513251361845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7478965773103351001815793 5609224329827513251361845)
                    ·
                      refine ⟨525864780921329367315173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5609224329827513251361845 525864780921329367315173)
                      ·
                        rfl

theorem cell23_1024118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_1024118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1024118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1024118 prefixEnd_1024118 := by exact prefixLift 1024118
  have htrace : WordTrace (prefixWord ++ tailWord_1024118) baseStart_1024118 baseEnd_1024118 := by
    simpa [prefixWord, tailWord_1024118, baseEnd_1024118] using wordTrace_append hprefix tailTrace_1024118
  have hstable : (prefixWord ++ tailWord_1024118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024118).length < 2 ^ (prefixWord ++ tailWord_1024118).sum := by decide
  have hdescent : baseEnd_1024118 < baseStart_1024118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024128 : List Nat := [2, 1, 1, 2, 1, 3, 1, 4, 2, 4, 2]
def baseStart_1024128 : Nat := 118140960795 + 1024128 * 2 ^ 59
def prefixEnd_1024128 : Nat := 4983230072969 + 3 ^ 40 * 1024128 * 2
def baseEnd_1024128 : Nat := 525869915727874328190127

theorem tailTrace_1024128 : CollatzResearch.WordTrace tailWord_1024128 prefixEnd_1024128 525869915727874328190127 := by
  unfold tailWord_1024128
  simp only [CollatzResearch.WordTrace]
  refine ⟨18676508416883318991220519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24902011222511091988294025 18676508416883318991220519)
  ·
    refine ⟨28014762625324978486830779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18676508416883318991220519 28014762625324978486830779)
    ·
      refine ⟨42022143937987467730246169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28014762625324978486830779 42022143937987467730246169)
      ·
        refine ⟨31516607953490600797684627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42022143937987467730246169 31516607953490600797684627)
        ·
          refine ⟨47274911930235901196526941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31516607953490600797684627 47274911930235901196526941)
          ·
            refine ⟨17728091973838462948697603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47274911930235901196526941 17728091973838462948697603)
            ·
              refine ⟨26592137960757694423046405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17728091973838462948697603 26592137960757694423046405)
              ·
                refine ⟨4986025867642067704321201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26592137960757694423046405 4986025867642067704321201)
                ·
                  refine ⟨3739519400731550778240901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4986025867642067704321201 3739519400731550778240901)
                  ·
                    refine ⟨701159887637165770920169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3739519400731550778240901 701159887637165770920169)
                    ·
                      refine ⟨525869915727874328190127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 701159887637165770920169 525869915727874328190127)
                      ·
                        rfl

theorem cell23_1024128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 2, 4, 2].length) (baseStart_1024128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1024128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1024128 prefixEnd_1024128 := by exact prefixLift 1024128
  have htrace : WordTrace (prefixWord ++ tailWord_1024128) baseStart_1024128 baseEnd_1024128 := by
    simpa [prefixWord, tailWord_1024128, baseEnd_1024128] using wordTrace_append hprefix tailTrace_1024128
  have hstable : (prefixWord ++ tailWord_1024128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024128).length < 2 ^ (prefixWord ++ tailWord_1024128).sum := by decide
  have hdescent : baseEnd_1024128 < baseStart_1024128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024129 : List Nat := [1, 2, 4, 2, 4, 1, 2, 2, 5]
def baseStart_1024129 : Nat := 118140960795 + 1024129 * 2 ^ 59
def prefixEnd_1024129 : Nat := 4983230072969 + 3 ^ 40 * 1024129 * 2
def baseEnd_1024129 : Nat := 58430047689836536030847

theorem tailTrace_1024129 : CollatzResearch.WordTrace tailWord_1024129 prefixEnd_1024129 58430047689836536030847 := by
  unfold tailWord_1024129
  simp only [CollatzResearch.WordTrace]
  refine ⟨37353053306763015153227441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24902035537842010102151627 37353053306763015153227441)
  ·
    refine ⟨28014789980072261364920581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37353053306763015153227441 28014789980072261364920581)
    ·
      refine ⟨5252773121263549005922609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28014789980072261364920581 5252773121263549005922609)
      ·
        refine ⟨3939579840947661754441957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5252773121263549005922609 3939579840947661754441957)
        ·
          refine ⟨738671220177686578957867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3939579840947661754441957 738671220177686578957867)
          ·
            refine ⟨1108006830266529868436801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738671220177686578957867 1108006830266529868436801)
            ·
              refine ⟨831005122699897401327601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1108006830266529868436801 831005122699897401327601)
              ·
                refine ⟨623253842024923050995701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 831005122699897401327601 623253842024923050995701)
                ·
                  refine ⟨58430047689836536030847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 623253842024923050995701 58430047689836536030847)
                  ·
                    rfl

theorem cell23_1024129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 2, 5].length) (baseStart_1024129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1024129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1024129 prefixEnd_1024129 := by exact prefixLift 1024129
  have htrace : WordTrace (prefixWord ++ tailWord_1024129) baseStart_1024129 baseEnd_1024129 := by
    simpa [prefixWord, tailWord_1024129, baseEnd_1024129] using wordTrace_append hprefix tailTrace_1024129
  have hstable : (prefixWord ++ tailWord_1024129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024129).length < 2 ^ (prefixWord ++ tailWord_1024129).sum := by decide
  have hdescent : baseEnd_1024129 < baseStart_1024129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024162 : List Nat := [3, 3, 1, 3, 1, 3, 1, 1, 2, 1, 4]
def baseStart_1024162 : Nat := 118140960795 + 1024162 * 2 ^ 59
def prefixEnd_1024162 : Nat := 4983230072969 + 3 ^ 40 * 1024162 * 2
def baseEnd_1024162 : Nat := 525887374070127195164971

theorem tailTrace_1024162 : CollatzResearch.WordTrace tailWord_1024162 prefixEnd_1024162 525887374070127195164971 := by
  unfold tailWord_1024162
  simp only [CollatzResearch.WordTrace]
  refine ⟨9338564228910865447294685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24902837943762307859452493 9338564228910865447294685)
  ·
    refine ⟨3501961585841574542735507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9338564228910865447294685 3501961585841574542735507)
    ·
      refine ⟨5252942378762361814103261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3501961585841574542735507 5252942378762361814103261)
      ·
        refine ⟨1969853392035885680288723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5252942378762361814103261 1969853392035885680288723)
        ·
          refine ⟨2954780088053828520433085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1969853392035885680288723 2954780088053828520433085)
          ·
            refine ⟨1108042533020185695162407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2954780088053828520433085 1108042533020185695162407)
            ·
              refine ⟨1662063799530278542743611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1108042533020185695162407 1662063799530278542743611)
              ·
                refine ⟨2493095699295417814115417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1662063799530278542743611 2493095699295417814115417)
                ·
                  refine ⟨1869821774471563360586563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2493095699295417814115417 1869821774471563360586563)
                  ·
                    refine ⟨2804732661707345040879845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1869821774471563360586563 2804732661707345040879845)
                    ·
                      refine ⟨525887374070127195164971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2804732661707345040879845 525887374070127195164971)
                      ·
                        rfl

theorem cell23_1024162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_1024162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1024162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1024162 prefixEnd_1024162 := by exact prefixLift 1024162
  have htrace : WordTrace (prefixWord ++ tailWord_1024162) baseStart_1024162 baseEnd_1024162 := by
    simpa [prefixWord, tailWord_1024162, baseEnd_1024162] using wordTrace_append hprefix tailTrace_1024162
  have hstable : (prefixWord ++ tailWord_1024162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024162).length < 2 ^ (prefixWord ++ tailWord_1024162).sum := by decide
  have hdescent : baseEnd_1024162 < baseStart_1024162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024201 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 2, 5, 4]
def baseStart_1024201 : Nat := 118140960795 + 1024201 * 2 ^ 59
def prefixEnd_1024201 : Nat := 4983230072969 + 3 ^ 40 * 1024201 * 2
def baseEnd_1024201 : Nat := 525907399815652542577291

theorem tailTrace_1024201 : CollatzResearch.WordTrace tailWord_1024201 prefixEnd_1024201 525907399815652542577291 := by
  unfold tailWord_1024201
  simp only [CollatzResearch.WordTrace]
  refine ⟨37355679362502171449848457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24903786241668114299898971 37355679362502171449848457)
  ·
    refine ⟨28016759521876628587386343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37355679362502171449848457 28016759521876628587386343)
    ·
      refine ⟨42025139282814942881079515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28016759521876628587386343 42025139282814942881079515)
      ·
        refine ⟨63037708924222414321619273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42025139282814942881079515 63037708924222414321619273)
        ·
          refine ⟨47278281693166810741214455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63037708924222414321619273 47278281693166810741214455)
          ·
            refine ⟨70917422539750216111821683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47278281693166810741214455 70917422539750216111821683)
            ·
              refine ⟨106376133809625324167732525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70917422539750216111821683 106376133809625324167732525)
              ·
                refine ⟨39891050178609496562899697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106376133809625324167732525 39891050178609496562899697)
                ·
                  refine ⟨29918287633957122422174773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39891050178609496562899697 29918287633957122422174773)
                  ·
                    refine ⟨2804839465683480227078885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29918287633957122422174773 2804839465683480227078885)
                    ·
                      refine ⟨525907399815652542577291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2804839465683480227078885 525907399815652542577291)
                      ·
                        rfl

theorem cell23_1024201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 5, 4].length) (baseStart_1024201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1024201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1024201 prefixEnd_1024201 := by exact prefixLift 1024201
  have htrace : WordTrace (prefixWord ++ tailWord_1024201) baseStart_1024201 baseEnd_1024201 := by
    simpa [prefixWord, tailWord_1024201, baseEnd_1024201] using wordTrace_append hprefix tailTrace_1024201
  have hstable : (prefixWord ++ tailWord_1024201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024201).length < 2 ^ (prefixWord ++ tailWord_1024201).sum := by decide
  have hdescent : baseEnd_1024201 < baseStart_1024201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024218 : List Nat := [3, 1, 1, 2, 2, 1, 2, 3, 3, 1, 4]
def baseStart_1024218 : Nat := 118140960795 + 1024218 * 2 ^ 59
def prefixEnd_1024218 : Nat := 4983230072969 + 3 ^ 40 * 1024218 * 2
def baseEnd_1024218 : Nat := 525916128986778976064713

theorem tailTrace_1024218 : CollatzResearch.WordTrace tailWord_1024218 prefixEnd_1024218 525916128986778976064713 := by
  unfold tailWord_1024218
  simp only [CollatzResearch.WordTrace]
  refine ⟨9339074850860145838304327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24904199602293722235478205 9339074850860145838304327)
  ·
    refine ⟨14008612276290218757456491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9339074850860145838304327 14008612276290218757456491)
    ·
      refine ⟨21012918414435328136184737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14008612276290218757456491 21012918414435328136184737)
      ·
        refine ⟨15759688810826496102138553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21012918414435328136184737 15759688810826496102138553)
        ·
          refine ⟨11819766608119872076603915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15759688810826496102138553 11819766608119872076603915)
          ·
            refine ⟨17729649912179808114905873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11819766608119872076603915 17729649912179808114905873)
            ·
              refine ⟨13297237434134856086179405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17729649912179808114905873 13297237434134856086179405)
              ·
                refine ⟨4986464037800571032317277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13297237434134856086179405 4986464037800571032317277)
                ·
                  refine ⟨1869924014175214137118979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4986464037800571032317277 1869924014175214137118979)
                  ·
                    refine ⟨2804886021262821205678469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1869924014175214137118979 2804886021262821205678469)
                    ·
                      refine ⟨525916128986778976064713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2804886021262821205678469 525916128986778976064713)
                      ·
                        rfl

theorem cell23_1024218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_1024218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1024218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1024218 prefixEnd_1024218 := by exact prefixLift 1024218
  have htrace : WordTrace (prefixWord ++ tailWord_1024218) baseStart_1024218 baseEnd_1024218 := by
    simpa [prefixWord, tailWord_1024218, baseEnd_1024218] using wordTrace_append hprefix tailTrace_1024218
  have hstable : (prefixWord ++ tailWord_1024218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024218).length < 2 ^ (prefixWord ++ tailWord_1024218).sum := by decide
  have hdescent : baseEnd_1024218 < baseStart_1024218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024229 : List Nat := [1, 3, 1, 4, 2, 1, 3, 3, 1, 1, 3]
def baseStart_1024229 : Nat := 118140960795 + 1024229 * 2 ^ 59
def prefixEnd_1024229 : Nat := 4983230072969 + 3 ^ 40 * 1024229 * 2
def baseEnd_1024229 : Nat := 525921777273978433027163

theorem tailTrace_1024229 : CollatzResearch.WordTrace tailWord_1024229 prefixEnd_1024229 525921777273978433027163 := by
  unfold tailWord_1024229
  simp only [CollatzResearch.WordTrace]
  refine ⟨37356700606400732231867741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24904467070933821487911827 37356700606400732231867741)
  ·
    refine ⟨14008762727400274586950403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37356700606400732231867741 14008762727400274586950403)
    ·
      refine ⟨21013144091100411880425605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14008762727400274586950403 21013144091100411880425605)
      ·
        refine ⟨3939964517081327227579801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21013144091100411880425605 3939964517081327227579801)
        ·
          refine ⟨2954973387810995420684851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3939964517081327227579801 2954973387810995420684851)
          ·
            refine ⟨4432460081716493131027277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2954973387810995420684851 4432460081716493131027277)
            ·
              refine ⟨1662172530643684924135229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4432460081716493131027277 1662172530643684924135229)
              ·
                refine ⟨623314698991381846550711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1662172530643684924135229 623314698991381846550711)
                ·
                  refine ⟨934972048487072769826067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 623314698991381846550711 934972048487072769826067)
                  ·
                    refine ⟨1402458072730609154739101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 934972048487072769826067 1402458072730609154739101)
                    ·
                      refine ⟨525921777273978433027163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1402458072730609154739101 525921777273978433027163)
                      ·
                        rfl

theorem cell23_1024229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_1024229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1024229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1024229 prefixEnd_1024229 := by exact prefixLift 1024229
  have htrace : WordTrace (prefixWord ++ tailWord_1024229) baseStart_1024229 baseEnd_1024229 := by
    simpa [prefixWord, tailWord_1024229, baseEnd_1024229] using wordTrace_append hprefix tailTrace_1024229
  have hstable : (prefixWord ++ tailWord_1024229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024229).length < 2 ^ (prefixWord ++ tailWord_1024229).sum := by decide
  have hdescent : baseEnd_1024229 < baseStart_1024229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024241 : List Nat := [1, 2, 2, 2, 2, 1, 13]
def baseStart_1024241 : Nat := 118140960795 + 1024241 * 2 ^ 59
def prefixEnd_1024241 : Nat := 4983230072969 + 3 ^ 40 * 1024241 * 2
def baseEnd_1024241 : Nat := 6492937519034967729347

theorem tailTrace_1024241 : CollatzResearch.WordTrace tailWord_1024241 prefixEnd_1024241 6492937519034967729347 := by
  unfold tailWord_1024241
  simp only [CollatzResearch.WordTrace]
  refine ⟨37357138282357258281304577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24904758854904838854203051 37357138282357258281304577)
  ·
    refine ⟨28017853711767943710978433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37357138282357258281304577 28017853711767943710978433)
    ·
      refine ⟨21013390283825957783233825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28017853711767943710978433 21013390283825957783233825)
      ·
        refine ⟨15760042712869468337425369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21013390283825957783233825 15760042712869468337425369)
        ·
          refine ⟨11820032034652101253069027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15760042712869468337425369 11820032034652101253069027)
          ·
            refine ⟨17730048051978151879603541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11820032034652101253069027 17730048051978151879603541)
            ·
              refine ⟨6492937519034967729347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 17730048051978151879603541 6492937519034967729347)
              ·
                rfl

theorem cell23_1024241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 13].length) (baseStart_1024241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1024241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1024241 prefixEnd_1024241 := by exact prefixLift 1024241
  have htrace : WordTrace (prefixWord ++ tailWord_1024241) baseStart_1024241 baseEnd_1024241 := by
    simpa [prefixWord, tailWord_1024241, baseEnd_1024241] using wordTrace_append hprefix tailTrace_1024241
  have hstable : (prefixWord ++ tailWord_1024241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024241).length < 2 ^ (prefixWord ++ tailWord_1024241).sum := by decide
  have hdescent : baseEnd_1024241 < baseStart_1024241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024286 : List Nat := [4, 3, 2, 1, 1, 2, 3, 1, 1, 1, 4]
def baseStart_1024286 : Nat := 118140960795 + 1024286 * 2 ^ 59
def prefixEnd_1024286 : Nat := 4983230072969 + 3 ^ 40 * 1024286 * 2
def baseEnd_1024286 : Nat := 525951045671284710014401

theorem tailTrace_1024286 : CollatzResearch.WordTrace tailWord_1024286 prefixEnd_1024286 525951045671284710014401 := by
  unfold tailWord_1024286
  simp only [CollatzResearch.WordTrace]
  refine ⟨4669847445899278870836589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24905853044796153977795141 4669847445899278870836589)
  ·
    refine ⟨1751192792212229576563721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4669847445899278870836589 1751192792212229576563721)
    ·
      refine ⟨1313394594159172182422791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1751192792212229576563721 1313394594159172182422791)
      ·
        refine ⟨1970091891238758273634187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1313394594159172182422791 1970091891238758273634187)
        ·
          refine ⟨2955137836858137410451281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1970091891238758273634187 2955137836858137410451281)
          ·
            refine ⟨2216353377643603057838461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2955137836858137410451281 2216353377643603057838461)
            ·
              refine ⟨831132516616351146689423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2216353377643603057838461 831132516616351146689423)
              ·
                refine ⟨1246698774924526720034135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 831132516616351146689423 1246698774924526720034135)
                ·
                  refine ⟨1870048162386790080051203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1246698774924526720034135 1870048162386790080051203)
                  ·
                    refine ⟨2805072243580185120076805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1870048162386790080051203 2805072243580185120076805)
                    ·
                      refine ⟨525951045671284710014401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2805072243580185120076805 525951045671284710014401)
                      ·
                        rfl

theorem cell23_1024286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_1024286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1024286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1024286 prefixEnd_1024286 := by exact prefixLift 1024286
  have htrace : WordTrace (prefixWord ++ tailWord_1024286) baseStart_1024286 baseEnd_1024286 := by
    simpa [prefixWord, tailWord_1024286, baseEnd_1024286] using wordTrace_append hprefix tailTrace_1024286
  have hstable : (prefixWord ++ tailWord_1024286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024286).length < 2 ^ (prefixWord ++ tailWord_1024286).sum := by decide
  have hdescent : baseEnd_1024286 < baseStart_1024286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024328 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 4, 1, 5]
def baseStart_1024328 : Nat := 118140960795 + 1024328 * 2 ^ 59
def prefixEnd_1024328 : Nat := 4983230072969 + 3 ^ 40 * 1024328 * 2
def baseEnd_1024328 : Nat := 525972611858773545689207

theorem tailTrace_1024328 : CollatzResearch.WordTrace tailWord_1024328 prefixEnd_1024328 525972611858773545689207 := by
  unfold tailWord_1024328
  simp only [CollatzResearch.WordTrace]
  refine ⟨18680155716521036069860819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24906874288694714759814425 18680155716521036069860819)
  ·
    refine ⟨28020233574781554104791229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18680155716521036069860819 28020233574781554104791229)
    ·
      refine ⟨10507587590543082789296711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28020233574781554104791229 10507587590543082789296711)
      ·
        refine ⟨15761381385814624183945067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10507587590543082789296711 15761381385814624183945067)
        ·
          refine ⟨23642072078721936275917601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15761381385814624183945067 23642072078721936275917601)
          ·
            refine ⟨17731554059041452206938201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23642072078721936275917601 17731554059041452206938201)
            ·
              refine ⟨13298665544281089155203651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17731554059041452206938201 13298665544281089155203651)
              ·
                refine ⟨19947998316421633732805477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13298665544281089155203651 19947998316421633732805477)
                ·
                  refine ⟨3740249684329056324901027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19947998316421633732805477 3740249684329056324901027)
                  ·
                    refine ⟨5610374526493584487351541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3740249684329056324901027 5610374526493584487351541)
                    ·
                      refine ⟨525972611858773545689207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5610374526493584487351541 525972611858773545689207)
                      ·
                        rfl

theorem cell23_1024328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_1024328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1024328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1024328 prefixEnd_1024328 := by exact prefixLift 1024328
  have htrace : WordTrace (prefixWord ++ tailWord_1024328) baseStart_1024328 baseEnd_1024328 := by
    simpa [prefixWord, tailWord_1024328, baseEnd_1024328] using wordTrace_append hprefix tailTrace_1024328
  have hstable : (prefixWord ++ tailWord_1024328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024328).length < 2 ^ (prefixWord ++ tailWord_1024328).sum := by decide
  have hdescent : baseEnd_1024328 < baseStart_1024328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024359 : List Nat := [1, 1, 5, 1, 3, 2, 1, 1, 4, 2, 2]
def baseStart_1024359 : Nat := 118140960795 + 1024359 * 2 ^ 59
def prefixEnd_1024359 : Nat := 4983230072969 + 3 ^ 40 * 1024359 * 2
def baseEnd_1024359 : Nat := 525988529759062924401565

theorem tailTrace_1024359 : CollatzResearch.WordTrace tailWord_1024359 prefixEnd_1024359 525988529759062924401565 := by
  unfold tailWord_1024359
  simp only [CollatzResearch.WordTrace]
  refine ⟨37361442095929764434100131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24907628063953176289400087 37361442095929764434100131)
  ·
    refine ⟨56042163143894646651150197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37361442095929764434100131 56042163143894646651150197)
    ·
      refine ⟨5253952794740123123545331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56042163143894646651150197 5253952794740123123545331)
      ·
        refine ⟨7880929192110184685317997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5253952794740123123545331 7880929192110184685317997)
        ·
          refine ⟨2955348447041319256994249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7880929192110184685317997 2955348447041319256994249)
          ·
            refine ⟨2216511335280989442745687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2955348447041319256994249 2216511335280989442745687)
            ·
              refine ⟨3324767002921484164118531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2216511335280989442745687 3324767002921484164118531)
              ·
                refine ⟨4987150504382226246177797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3324767002921484164118531 4987150504382226246177797)
                ·
                  refine ⟨935090719571667421158337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4987150504382226246177797 935090719571667421158337)
                  ·
                    refine ⟨701318039678750565868753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 935090719571667421158337 701318039678750565868753)
                    ·
                      refine ⟨525988529759062924401565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 701318039678750565868753 525988529759062924401565)
                      ·
                        rfl

theorem cell23_1024359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_1024359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1024359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1024359 prefixEnd_1024359 := by exact prefixLift 1024359
  have htrace : WordTrace (prefixWord ++ tailWord_1024359) baseStart_1024359 baseEnd_1024359 := by
    simpa [prefixWord, tailWord_1024359, baseEnd_1024359] using wordTrace_append hprefix tailTrace_1024359
  have hstable : (prefixWord ++ tailWord_1024359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024359).length < 2 ^ (prefixWord ++ tailWord_1024359).sum := by decide
  have hdescent : baseEnd_1024359 < baseStart_1024359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024365 : List Nat := [1, 5, 1, 1, 1, 2, 4, 1, 7]
def baseStart_1024365 : Nat := 118140960795 + 1024365 * 2 ^ 59
def prefixEnd_1024365 : Nat := 4983230072969 + 3 ^ 40 * 1024365 * 2
def baseEnd_1024365 : Nat := 58443512293665544547393

theorem tailTrace_1024365 : CollatzResearch.WordTrace tailWord_1024365 prefixEnd_1024365 58443512293665544547393 := by
  unfold tailWord_1024365
  simp only [CollatzResearch.WordTrace]
  refine ⟨37361660933908027458818549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24907773955938684972545699 37361660933908027458818549)
  ·
    refine ⟨3502655712553877574264239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37361660933908027458818549 3502655712553877574264239)
    ·
      refine ⟨5253983568830816361396359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3502655712553877574264239 5253983568830816361396359)
      ·
        refine ⟨7880975353246224542094539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5253983568830816361396359 7880975353246224542094539)
        ·
          refine ⟨11821463029869336813141809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7880975353246224542094539 11821463029869336813141809)
          ·
            refine ⟨8866097272402002609856357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11821463029869336813141809 8866097272402002609856357)
            ·
              refine ⟨1662393238575375489348067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8866097272402002609856357 1662393238575375489348067)
              ·
                refine ⟨2493589857863063234022101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1662393238575375489348067 2493589857863063234022101)
                ·
                  refine ⟨58443512293665544547393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2493589857863063234022101 58443512293665544547393)
                  ·
                    rfl

theorem cell23_1024365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_1024365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1024365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1024365 prefixEnd_1024365 := by exact prefixLift 1024365
  have htrace : WordTrace (prefixWord ++ tailWord_1024365) baseStart_1024365 baseEnd_1024365 := by
    simpa [prefixWord, tailWord_1024365, baseEnd_1024365] using wordTrace_append hprefix tailTrace_1024365
  have hstable : (prefixWord ++ tailWord_1024365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024365).length < 2 ^ (prefixWord ++ tailWord_1024365).sum := by decide
  have hdescent : baseEnd_1024365 < baseStart_1024365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024492 : List Nat := [2, 2, 1, 1, 2, 1, 4, 2, 1, 5, 2]
def baseStart_1024492 : Nat := 118140960795 + 1024492 * 2 ^ 59
def prefixEnd_1024492 : Nat := 4983230072969 + 3 ^ 40 * 1024492 * 2
def baseEnd_1024492 : Nat := 526056822686110904038453

theorem tailTrace_1024492 : CollatzResearch.WordTrace tailWord_1024492 prefixEnd_1024492 526056822686110904038453 := by
  unfold tailWord_1024492
  simp only [CollatzResearch.WordTrace]
  refine ⟨18683146502223964074345865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24910862002965285432461153 18683146502223964074345865)
  ·
    refine ⟨14012359876667973055759399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18683146502223964074345865 14012359876667973055759399)
    ·
      refine ⟨21018539815001959583639099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14012359876667973055759399 21018539815001959583639099)
      ·
        refine ⟨31527809722502939375458649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21018539815001959583639099 31527809722502939375458649)
        ·
          refine ⟨23645857291877204531593987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31527809722502939375458649 23645857291877204531593987)
          ·
            refine ⟨35468785937815806797390981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23645857291877204531593987 35468785937815806797390981)
            ·
              refine ⟨6650397363340463774510809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35468785937815806797390981 6650397363340463774510809)
              ·
                refine ⟨4987798022505347830883107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6650397363340463774510809 4987798022505347830883107)
                ·
                  refine ⟨7481697033758021746324661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4987798022505347830883107 7481697033758021746324661)
                  ·
                    refine ⟨701409096914814538717937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7481697033758021746324661 701409096914814538717937)
                    ·
                      refine ⟨526056822686110904038453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 701409096914814538717937 526056822686110904038453)
                      ·
                        rfl

theorem cell23_1024492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 5, 2].length) (baseStart_1024492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1024492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1024492 prefixEnd_1024492 := by exact prefixLift 1024492
  have htrace : WordTrace (prefixWord ++ tailWord_1024492) baseStart_1024492 baseEnd_1024492 := by
    simpa [prefixWord, tailWord_1024492, baseEnd_1024492] using wordTrace_append hprefix tailTrace_1024492
  have hstable : (prefixWord ++ tailWord_1024492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024492).length < 2 ^ (prefixWord ++ tailWord_1024492).sum := by decide
  have hdescent : baseEnd_1024492 < baseStart_1024492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024502 : List Nat := [5, 1, 1, 1, 2, 1, 1, 3, 3, 5]
def baseStart_1024502 : Nat := 118140960795 + 1024502 * 2 ^ 59
def prefixEnd_1024502 : Nat := 4983230072969 + 3 ^ 40 * 1024502 * 2
def baseEnd_1024502 : Nat := 175353985830885288304469

theorem tailTrace_1024502 : CollatzResearch.WordTrace tailWord_1024502 prefixEnd_1024502 175353985830885288304469 := by
  unfold tailWord_1024502
  simp only [CollatzResearch.WordTrace]
  refine ⟨2335416108400731241034735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24911105156274466571037173 2335416108400731241034735)
  ·
    refine ⟨3503124162601096861552103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2335416108400731241034735 3503124162601096861552103)
    ·
      refine ⟨5254686243901645292328155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3503124162601096861552103 5254686243901645292328155)
      ·
        refine ⟨7882029365852467938492233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5254686243901645292328155 7882029365852467938492233)
        ·
          refine ⟨5911522024389350953869175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7882029365852467938492233 5911522024389350953869175)
          ·
            refine ⟨8867283036584026430803763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5911522024389350953869175 8867283036584026430803763)
            ·
              refine ⟨13300924554876039646205645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8867283036584026430803763 13300924554876039646205645)
              ·
                refine ⟨4987846708078514867327117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13300924554876039646205645 4987846708078514867327117)
                ·
                  refine ⟨1870442515529443075247669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4987846708078514867327117 1870442515529443075247669)
                  ·
                    refine ⟨175353985830885288304469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1870442515529443075247669 175353985830885288304469)
                    ·
                      rfl

theorem cell23_1024502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_1024502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1024502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1024502 prefixEnd_1024502 := by exact prefixLift 1024502
  have htrace : WordTrace (prefixWord ++ tailWord_1024502) baseStart_1024502 baseEnd_1024502 := by
    simpa [prefixWord, tailWord_1024502, baseEnd_1024502] using wordTrace_append hprefix tailTrace_1024502
  have hstable : (prefixWord ++ tailWord_1024502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024502).length < 2 ^ (prefixWord ++ tailWord_1024502).sum := by decide
  have hdescent : baseEnd_1024502 < baseStart_1024502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024515 : List Nat := [1, 1, 1, 3, 2, 1, 3, 4, 1, 6]
def baseStart_1024515 : Nat := 118140960795 + 1024515 * 2 ^ 59
def prefixEnd_1024515 : Nat := 4983230072969 + 3 ^ 40 * 1024515 * 2
def baseEnd_1024515 : Nat := 175356210913721438016949

theorem tailTrace_1024515 : CollatzResearch.WordTrace tailWord_1024515 prefixEnd_1024515 175356210913721438016949 := by
  unfold tailWord_1024515
  simp only [CollatzResearch.WordTrace]
  refine ⟨37367131883364603076778999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24911421255576402051185999 37367131883364603076778999)
  ·
    refine ⟨56050697825046904615168499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37367131883364603076778999 56050697825046904615168499)
    ·
      refine ⟨84076046737570356922752749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56050697825046904615168499 84076046737570356922752749)
      ·
        refine ⟨31528517526588883846032281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84076046737570356922752749 31528517526588883846032281)
        ·
          refine ⟨23646388144941662884524211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31528517526588883846032281 23646388144941662884524211)
          ·
            refine ⟨35469582217412494326786317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23646388144941662884524211 35469582217412494326786317)
            ·
              refine ⟨13301093331529685372544869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35469582217412494326786317 13301093331529685372544869)
              ·
                refine ⟨2493954999661816007352163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13301093331529685372544869 2493954999661816007352163)
                ·
                  refine ⟨3740932499492724011028245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2493954999661816007352163 3740932499492724011028245)
                  ·
                    refine ⟨175356210913721438016949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3740932499492724011028245 175356210913721438016949)
                    ·
                      rfl

theorem cell23_1024515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 6].length) (baseStart_1024515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1024515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1024515 prefixEnd_1024515 := by exact prefixLift 1024515
  have htrace : WordTrace (prefixWord ++ tailWord_1024515) baseStart_1024515 baseEnd_1024515 := by
    simpa [prefixWord, tailWord_1024515, baseEnd_1024515] using wordTrace_append hprefix tailTrace_1024515
  have hstable : (prefixWord ++ tailWord_1024515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024515).length < 2 ^ (prefixWord ++ tailWord_1024515).sum := by decide
  have hdescent : baseEnd_1024515 < baseStart_1024515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024519 : List Nat := [1, 1, 4, 3, 3, 1, 1, 3, 1, 5]
def baseStart_1024519 : Nat := 118140960795 + 1024519 * 2 ^ 59
def prefixEnd_1024519 : Nat := 4983230072969 + 3 ^ 40 * 1024519 * 2
def baseEnd_1024519 : Nat := 175356895554594099466943

theorem tailTrace_1024519 : CollatzResearch.WordTrace tailWord_1024519 prefixEnd_1024519 175356895554594099466943 := by
  unfold tailWord_1024519
  simp only [CollatzResearch.WordTrace]
  refine ⟨37367277775350111759924611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24911518516900074506616407 37367277775350111759924611)
  ·
    refine ⟨56050916663025167639886917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37367277775350111759924611 56050916663025167639886917)
    ·
      refine ⟨10509546874317218932478797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56050916663025167639886917 10509546874317218932478797)
      ·
        refine ⟨3941080077868957099679549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10509546874317218932478797 3941080077868957099679549)
        ·
          refine ⟨1477905029200858912379831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3941080077868957099679549 1477905029200858912379831)
          ·
            refine ⟨2216857543801288368569747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1477905029200858912379831 2216857543801288368569747)
            ·
              refine ⟨3325286315701932552854621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2216857543801288368569747 3325286315701932552854621)
              ·
                refine ⟨1246982368388224707320483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3325286315701932552854621 1246982368388224707320483)
                ·
                  refine ⟨1870473552582337060980725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1246982368388224707320483 1870473552582337060980725)
                  ·
                    refine ⟨175356895554594099466943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1870473552582337060980725 175356895554594099466943)
                    ·
                      rfl

theorem cell23_1024519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 5].length) (baseStart_1024519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1024519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1024519 prefixEnd_1024519 := by exact prefixLift 1024519
  have htrace : WordTrace (prefixWord ++ tailWord_1024519) baseStart_1024519 baseEnd_1024519 := by
    simpa [prefixWord, tailWord_1024519, baseEnd_1024519] using wordTrace_append hprefix tailTrace_1024519
  have hstable : (prefixWord ++ tailWord_1024519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024519).length < 2 ^ (prefixWord ++ tailWord_1024519).sum := by decide
  have hdescent : baseEnd_1024519 < baseStart_1024519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024545 : List Nat := [1, 2, 3, 2, 2, 1, 2, 10]
def baseStart_1024545 : Nat := 118140960795 + 1024545 * 2 ^ 59
def prefixEnd_1024545 : Nat := 4983230072969 + 3 ^ 40 * 1024545 * 2
def baseEnd_1024545 : Nat := 19484593968918488765767

theorem tailTrace_1024545 : CollatzResearch.WordTrace tailWord_1024545 prefixEnd_1024545 19484593968918488765767 := by
  unfold tailWord_1024545
  simp only [CollatzResearch.WordTrace]
  refine ⟨37368226073255918200371089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24912150715503945466914059 37368226073255918200371089)
  ·
    refine ⟨28026169554941938650278317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37368226073255918200371089 28026169554941938650278317)
    ·
      refine ⟨10509813583103226993854369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28026169554941938650278317 10509813583103226993854369)
      ·
        refine ⟨7882360187327420245390777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10509813583103226993854369 7882360187327420245390777)
        ·
          refine ⟨5911770140495565184043083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7882360187327420245390777 5911770140495565184043083)
          ·
            refine ⟨8867655210743347776064625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5911770140495565184043083 8867655210743347776064625)
            ·
              refine ⟨6650741408057510832048469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8867655210743347776064625 6650741408057510832048469)
              ·
                refine ⟨19484593968918488765767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 6650741408057510832048469 19484593968918488765767)
                ·
                  rfl

theorem cell23_1024545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 10].length) (baseStart_1024545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1024545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1024545 prefixEnd_1024545 := by exact prefixLift 1024545
  have htrace : WordTrace (prefixWord ++ tailWord_1024545) baseStart_1024545 baseEnd_1024545 := by
    simpa [prefixWord, tailWord_1024545, baseEnd_1024545] using wordTrace_append hprefix tailTrace_1024545
  have hstable : (prefixWord ++ tailWord_1024545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024545).length < 2 ^ (prefixWord ++ tailWord_1024545).sum := by decide
  have hdescent : baseEnd_1024545 < baseStart_1024545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024562 : List Nat := [3, 2, 1, 1, 2, 1, 6, 7]
def baseStart_1024562 : Nat := 118140960795 + 1024562 * 2 ^ 59
def prefixEnd_1024562 : Nat := 4983230072969 + 3 ^ 40 * 1024562 * 2
def baseEnd_1024562 : Nat := 19484917271552801117153

theorem tailTrace_1024562 : CollatzResearch.WordTrace tailWord_1024562 prefixEnd_1024562 19484917271552801117153 := by
  unfold tailWord_1024562
  simp only [CollatzResearch.WordTrace]
  refine ⟨9342211528548582525934985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24912564076129553402493293 9342211528548582525934985)
  ·
    refine ⟨7006658646411436894451239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9342211528548582525934985 7006658646411436894451239)
    ·
      refine ⟨10509987969617155341676859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7006658646411436894451239 10509987969617155341676859)
      ·
        refine ⟨15764981954425733012515289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10509987969617155341676859 15764981954425733012515289)
        ·
          refine ⟨11823736465819299759386467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15764981954425733012515289 11823736465819299759386467)
          ·
            refine ⟨17735604698728949639079701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11823736465819299759386467 17735604698728949639079701)
            ·
              refine ⟨831356470252919514331861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17735604698728949639079701 831356470252919514331861)
              ·
                refine ⟨19484917271552801117153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 831356470252919514331861 19484917271552801117153)
                ·
                  rfl

theorem cell23_1024562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 7].length) (baseStart_1024562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1024562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1024562 prefixEnd_1024562 := by exact prefixLift 1024562
  have htrace : WordTrace (prefixWord ++ tailWord_1024562) baseStart_1024562 baseEnd_1024562 := by
    simpa [prefixWord, tailWord_1024562, baseEnd_1024562] using wordTrace_append hprefix tailTrace_1024562
  have hstable : (prefixWord ++ tailWord_1024562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024562).length < 2 ^ (prefixWord ++ tailWord_1024562).sum := by decide
  have hdescent : baseEnd_1024562 < baseStart_1024562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024599 : List Nat := [1, 1, 3, 2, 2, 2, 2, 2, 3, 3, 2]
def baseStart_1024599 : Nat := 118140960795 + 1024599 * 2 ^ 59
def prefixEnd_1024599 : Nat := 4983230072969 + 3 ^ 40 * 1024599 * 2
def baseEnd_1024599 : Nat := 526111765116141985400461

theorem tailTrace_1024599 : CollatzResearch.WordTrace tailWord_1024599 prefixEnd_1024599 526111765116141985400461 := by
  unfold tailWord_1024599
  simp only [CollatzResearch.WordTrace]
  refine ⟨37370195615060285422836851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24913463743373523615224567 37370195615060285422836851)
  ·
    refine ⟨56055293422590428134255277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37370195615060285422836851 56055293422590428134255277)
    ·
      refine ⟨21020735033471410550345729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56055293422590428134255277 21020735033471410550345729)
      ·
        refine ⟨15765551275103557912759297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21020735033471410550345729 15765551275103557912759297)
        ·
          refine ⟨11824163456327668434569473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15765551275103557912759297 11824163456327668434569473)
          ·
            refine ⟨8868122592245751325927105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11824163456327668434569473 8868122592245751325927105)
            ·
              refine ⟨6651091944184313494445329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8868122592245751325927105 6651091944184313494445329)
              ·
                refine ⟨4988318958138235120833997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6651091944184313494445329 4988318958138235120833997)
                ·
                  refine ⟨1870619609301838170312749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4988318958138235120833997 1870619609301838170312749)
                  ·
                    refine ⟨701482353488189313867281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1870619609301838170312749 701482353488189313867281)
                    ·
                      refine ⟨526111765116141985400461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 701482353488189313867281 526111765116141985400461)
                      ·
                        rfl

theorem cell23_1024599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 3, 2].length) (baseStart_1024599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1024599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1024599 prefixEnd_1024599 := by exact prefixLift 1024599
  have htrace : WordTrace (prefixWord ++ tailWord_1024599) baseStart_1024599 baseEnd_1024599 := by
    simpa [prefixWord, tailWord_1024599, baseEnd_1024599] using wordTrace_append hprefix tailTrace_1024599
  have hstable : (prefixWord ++ tailWord_1024599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024599).length < 2 ^ (prefixWord ++ tailWord_1024599).sum := by decide
  have hdescent : baseEnd_1024599 < baseStart_1024599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024610 : List Nat := [3, 3, 2, 3, 1, 2, 1, 2, 1, 2, 3]
def baseStart_1024610 : Nat := 118140960795 + 1024610 * 2 ^ 59
def prefixEnd_1024610 : Nat := 4983230072969 + 3 ^ 40 * 1024610 * 2
def baseEnd_1024610 : Nat := 526117413403341442362911

theorem tailTrace_1024610 : CollatzResearch.WordTrace tailWord_1024610 prefixEnd_1024610 526117413403341442362911 := by
  unfold tailWord_1024610
  simp only [CollatzResearch.WordTrace]
  refine ⟨9342649204505108575371821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24913731212013622867658189 9342649204505108575371821)
  ·
    refine ⟨3503493451689415715764433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9342649204505108575371821 3503493451689415715764433)
    ·
      refine ⟨2627620088767061786823325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3503493451689415715764433 2627620088767061786823325)
      ·
        refine ⟨985357533287648170058747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2627620088767061786823325 985357533287648170058747)
        ·
          refine ⟨1478036299931472255088121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 985357533287648170058747 1478036299931472255088121)
          ·
            refine ⟨1108527224948604191316091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1478036299931472255088121 1108527224948604191316091)
            ·
              refine ⟨1662790837422906286974137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1108527224948604191316091 1662790837422906286974137)
              ·
                refine ⟨1247093128067179715230603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1662790837422906286974137 1247093128067179715230603)
                ·
                  refine ⟨1870639692100769572845905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1247093128067179715230603 1870639692100769572845905)
                  ·
                    refine ⟨1402979769075577179634429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1870639692100769572845905 1402979769075577179634429)
                    ·
                      refine ⟨526117413403341442362911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1402979769075577179634429 526117413403341442362911)
                      ·
                        rfl

theorem cell23_1024610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_1024610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1024610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1024610 prefixEnd_1024610 := by exact prefixLift 1024610
  have htrace : WordTrace (prefixWord ++ tailWord_1024610) baseStart_1024610 baseEnd_1024610 := by
    simpa [prefixWord, tailWord_1024610, baseEnd_1024610] using wordTrace_append hprefix tailTrace_1024610
  have hstable : (prefixWord ++ tailWord_1024610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024610).length < 2 ^ (prefixWord ++ tailWord_1024610).sum := by decide
  have hdescent : baseEnd_1024610 < baseStart_1024610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024633 : List Nat := [1, 2, 1, 3, 3, 3, 3, 1, 1, 3, 2]
def baseStart_1024633 : Nat := 118140960795 + 1024633 * 2 ^ 59
def prefixEnd_1024633 : Nat := 4983230072969 + 3 ^ 40 * 1024633 * 2
def baseEnd_1024633 : Nat := 526129223458394852375305

theorem tailTrace_1024633 : CollatzResearch.WordTrace tailWord_1024633 prefixEnd_1024633 526129223458394852375305 := by
  unfold tailWord_1024633
  simp only [CollatzResearch.WordTrace]
  refine ⟨37371435696937109229574553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24914290464624739486383035 37371435696937109229574553)
  ·
    refine ⟨28028576772702831922180915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37371435696937109229574553 28028576772702831922180915)
    ·
      refine ⟨42042865159054247883271373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28028576772702831922180915 42042865159054247883271373)
      ·
        refine ⟨15766074434645342956226765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42042865159054247883271373 15766074434645342956226765)
        ·
          refine ⟨5912277912992003608585037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15766074434645342956226765 5912277912992003608585037)
          ·
            refine ⟨2217104217372001353219389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5912277912992003608585037 2217104217372001353219389)
            ·
              refine ⟨831414081514500507457271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2217104217372001353219389 831414081514500507457271)
              ·
                refine ⟨1247121122271750761185907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 831414081514500507457271 1247121122271750761185907)
                ·
                  refine ⟨1870681683407626141778861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1247121122271750761185907 1870681683407626141778861)
                  ·
                    refine ⟨701505631277859803167073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1870681683407626141778861 701505631277859803167073)
                    ·
                      refine ⟨526129223458394852375305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 701505631277859803167073 526129223458394852375305)
                      ·
                        rfl

theorem cell23_1024633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 1, 3, 2].length) (baseStart_1024633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1024633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1024633 prefixEnd_1024633 := by exact prefixLift 1024633
  have htrace : WordTrace (prefixWord ++ tailWord_1024633) baseStart_1024633 baseEnd_1024633 := by
    simpa [prefixWord, tailWord_1024633, baseEnd_1024633] using wordTrace_append hprefix tailTrace_1024633
  have hstable : (prefixWord ++ tailWord_1024633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024633).length < 2 ^ (prefixWord ++ tailWord_1024633).sum := by decide
  have hdescent : baseEnd_1024633 < baseStart_1024633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024635 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 11]
def baseStart_1024635 : Nat := 118140960795 + 1024635 * 2 ^ 59
def prefixEnd_1024635 : Nat := 4983230072969 + 3 ^ 40 * 1024635 * 2
def baseEnd_1024635 : Nat := 58458916713300427172255

theorem tailTrace_1024635 : CollatzResearch.WordTrace tailWord_1024635 prefixEnd_1024635 58458916713300427172255 := by
  unfold tailWord_1024635
  simp only [CollatzResearch.WordTrace]
  refine ⟨37371508642929863571147359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24914339095286575714098239 37371508642929863571147359)
  ·
    refine ⟨56057262964394795356721039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37371508642929863571147359 56057262964394795356721039)
    ·
      refine ⟨84085894446592193035081559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56057262964394795356721039 84085894446592193035081559)
      ·
        refine ⟨126128841669888289552622339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84085894446592193035081559 126128841669888289552622339)
        ·
          refine ⟨189193262504832434328933509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126128841669888289552622339 189193262504832434328933509)
          ·
            refine ⟨35473736719656081436675033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189193262504832434328933509 35473736719656081436675033)
            ·
              refine ⟨26605302539742061077506275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35473736719656081436675033 26605302539742061077506275)
              ·
                refine ⟨39907953809613091616259413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26605302539742061077506275 39907953809613091616259413)
                ·
                  refine ⟨58458916713300427172255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 39907953809613091616259413 58458916713300427172255)
                  ·
                    rfl

theorem cell23_1024635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 11].length) (baseStart_1024635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1024635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1024635 prefixEnd_1024635 := by exact prefixLift 1024635
  have htrace : WordTrace (prefixWord ++ tailWord_1024635) baseStart_1024635 baseEnd_1024635 := by
    simpa [prefixWord, tailWord_1024635, baseEnd_1024635] using wordTrace_append hprefix tailTrace_1024635
  have hstable : (prefixWord ++ tailWord_1024635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024635).length < 2 ^ (prefixWord ++ tailWord_1024635).sum := by decide
  have hdescent : baseEnd_1024635 < baseStart_1024635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024729 : List Nat := [1, 2, 1, 2, 3, 2, 1, 4, 3, 4]
def baseStart_1024729 : Nat := 118140960795 + 1024729 * 2 ^ 59
def prefixEnd_1024729 : Nat := 4983230072969 + 3 ^ 40 * 1024729 * 2
def baseEnd_1024729 : Nat := 175392839200408825591621

theorem tailTrace_1024729 : CollatzResearch.WordTrace tailWord_1024729 prefixEnd_1024729 175392839200408825591621 := by
  unfold tailWord_1024729
  simp only [CollatzResearch.WordTrace]
  refine ⟨37374937104589317625069241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24916624736392878416712827 37374937104589317625069241)
  ·
    refine ⟨28031202828441988218801931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37374937104589317625069241 28031202828441988218801931)
    ·
      refine ⟨42046804242662982328202897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28031202828441988218801931 42046804242662982328202897)
      ·
        refine ⟨31535103181997236746152173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42046804242662982328202897 31535103181997236746152173)
        ·
          refine ⟨11825663693248963779807065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31535103181997236746152173 11825663693248963779807065)
          ·
            refine ⟨8869247769936722834855299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11825663693248963779807065 8869247769936722834855299)
            ·
              refine ⟨13303871654905084252282949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8869247769936722834855299 13303871654905084252282949)
              ·
                refine ⟨2494475935294703297303053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13303871654905084252282949 2494475935294703297303053)
                ·
                  refine ⟨935428475735513736488645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2494475935294703297303053 935428475735513736488645)
                  ·
                    refine ⟨175392839200408825591621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 935428475735513736488645 175392839200408825591621)
                    ·
                      rfl

theorem cell23_1024729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 3, 4].length) (baseStart_1024729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1024729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1024729 prefixEnd_1024729 := by exact prefixLift 1024729
  have htrace : WordTrace (prefixWord ++ tailWord_1024729) baseStart_1024729 baseEnd_1024729 := by
    simpa [prefixWord, tailWord_1024729, baseEnd_1024729] using wordTrace_append hprefix tailTrace_1024729
  have hstable : (prefixWord ++ tailWord_1024729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024729).length < 2 ^ (prefixWord ++ tailWord_1024729).sum := by decide
  have hdescent : baseEnd_1024729 < baseStart_1024729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024762 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 1, 1, 8]
def baseStart_1024762 : Nat := 118140960795 + 1024762 * 2 ^ 59
def prefixEnd_1024762 : Nat := 4983230072969 + 3 ^ 40 * 1024762 * 2
def baseEnd_1024762 : Nat := 526195462462824847662211

theorem tailTrace_1024762 : CollatzResearch.WordTrace tailWord_1024762 prefixEnd_1024762 526195462462824847662211 := by
  unfold tailWord_1024762
  simp only [CollatzResearch.WordTrace]
  refine ⟨9344035178367441065255135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24917427142313176174013693 9344035178367441065255135)
  ·
    refine ⟨14016052767551161597882703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9344035178367441065255135 14016052767551161597882703)
    ·
      refine ⟨21024079151326742396824055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14016052767551161597882703 21024079151326742396824055)
      ·
        refine ⟨31536118726990113595236083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21024079151326742396824055 31536118726990113595236083)
        ·
          refine ⟨47304178090485170392854125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31536118726990113595236083 47304178090485170392854125)
          ·
            refine ⟨17739066783931938897320297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47304178090485170392854125 17739066783931938897320297)
            ·
              refine ⟨13304300087948954172990223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17739066783931938897320297 13304300087948954172990223)
              ·
                refine ⟨19956450131923431259485335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13304300087948954172990223 19956450131923431259485335)
                ·
                  refine ⟨29934675197885146889228003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19956450131923431259485335 29934675197885146889228003)
                  ·
                    refine ⟨44902012796827720333842005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29934675197885146889228003 44902012796827720333842005)
                    ·
                      refine ⟨526195462462824847662211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 44902012796827720333842005 526195462462824847662211)
                      ·
                        rfl

theorem cell23_1024762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_1024762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1024762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1024762 prefixEnd_1024762 := by exact prefixLift 1024762
  have htrace : WordTrace (prefixWord ++ tailWord_1024762) baseStart_1024762 baseEnd_1024762 := by
    simpa [prefixWord, tailWord_1024762, baseEnd_1024762] using wordTrace_append hprefix tailTrace_1024762
  have hstable : (prefixWord ++ tailWord_1024762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024762).length < 2 ^ (prefixWord ++ tailWord_1024762).sum := by decide
  have hdescent : baseEnd_1024762 < baseStart_1024762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024776 : List Nat := [2, 1, 3, 2, 2, 2, 4, 1, 6]
def baseStart_1024776 : Nat := 118140960795 + 1024776 * 2 ^ 59
def prefixEnd_1024776 : Nat := 4983230072969 + 3 ^ 40 * 1024776 * 2
def baseEnd_1024776 : Nat := 58466961243554199209683

theorem tailTrace_1024776 : CollatzResearch.WordTrace tailWord_1024776 prefixEnd_1024776 58466961243554199209683 := by
  unfold tailWord_1024776
  simp only [CollatzResearch.WordTrace]
  refine ⟨18688325667709522326015091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24917767556946029768020121 18688325667709522326015091)
  ·
    refine ⟨28032488501564283489022637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18688325667709522326015091 28032488501564283489022637)
    ·
      refine ⟨10512183188086606308383489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28032488501564283489022637 10512183188086606308383489)
      ·
        refine ⟨7884137391064954731287617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10512183188086606308383489 7884137391064954731287617)
        ·
          refine ⟨5913103043298716048465713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7884137391064954731287617 5913103043298716048465713)
          ·
            refine ⟨4434827282474037036349285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5913103043298716048465713 4434827282474037036349285)
            ·
              refine ⟨831530115463881944315491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4434827282474037036349285 831530115463881944315491)
              ·
                refine ⟨1247295173195822916473237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 831530115463881944315491 1247295173195822916473237)
                ·
                  refine ⟨58466961243554199209683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1247295173195822916473237 58466961243554199209683)
                  ·
                    rfl

theorem cell23_1024776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 6].length) (baseStart_1024776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1024776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1024776 prefixEnd_1024776 := by exact prefixLift 1024776
  have htrace : WordTrace (prefixWord ++ tailWord_1024776) baseStart_1024776 baseEnd_1024776 := by
    simpa [prefixWord, tailWord_1024776, baseEnd_1024776] using wordTrace_append hprefix tailTrace_1024776
  have hstable : (prefixWord ++ tailWord_1024776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024776).length < 2 ^ (prefixWord ++ tailWord_1024776).sum := by decide
  have hdescent : baseEnd_1024776 < baseStart_1024776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024789 : List Nat := [1, 3, 2, 1, 2, 2, 3, 1, 3, 5]
def baseStart_1024789 : Nat := 118140960795 + 1024789 * 2 ^ 59
def prefixEnd_1024789 : Nat := 4983230072969 + 3 ^ 40 * 1024789 * 2
def baseEnd_1024789 : Nat := 175403108813498747341529

theorem tailTrace_1024789 : CollatzResearch.WordTrace tailWord_1024789 prefixEnd_1024789 175403108813498747341529 := by
  unfold tailWord_1024789
  simp only [CollatzResearch.WordTrace]
  refine ⟨37377125484371947872253421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24918083656247965248168947 37377125484371947872253421)
  ·
    refine ⟨14016422056639480452095033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37377125484371947872253421 14016422056639480452095033)
    ·
      refine ⟨10512316542479610339071275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14016422056639480452095033 10512316542479610339071275)
      ·
        refine ⟨15768474813719415508606913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10512316542479610339071275 15768474813719415508606913)
        ·
          refine ⟨11826356110289561631455185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15768474813719415508606913 11826356110289561631455185)
          ·
            refine ⟨8869767082717171223591389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11826356110289561631455185 8869767082717171223591389)
            ·
              refine ⟨3326162656018939208846771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8869767082717171223591389 3326162656018939208846771)
              ·
                refine ⟨4989243984028408813270157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3326162656018939208846771 4989243984028408813270157)
                ·
                  refine ⟨1870966494010653304976309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4989243984028408813270157 1870966494010653304976309)
                  ·
                    refine ⟨175403108813498747341529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1870966494010653304976309 175403108813498747341529)
                    ·
                      rfl

theorem cell23_1024789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_1024789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1024789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1024789 prefixEnd_1024789 := by exact prefixLift 1024789
  have htrace : WordTrace (prefixWord ++ tailWord_1024789) baseStart_1024789 baseEnd_1024789 := by
    simpa [prefixWord, tailWord_1024789, baseEnd_1024789] using wordTrace_append hprefix tailTrace_1024789
  have hstable : (prefixWord ++ tailWord_1024789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024789).length < 2 ^ (prefixWord ++ tailWord_1024789).sum := by decide
  have hdescent : baseEnd_1024789 < baseStart_1024789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024803 : List Nat := [1, 1, 1, 4, 2, 1, 1, 7, 1, 1, 3]
def baseStart_1024803 : Nat := 118140960795 + 1024803 * 2 ^ 59
def prefixEnd_1024803 : Nat := 4983230072969 + 3 ^ 40 * 1024803 * 2
def baseEnd_1024803 : Nat := 526216515169659187249523

theorem tailTrace_1024803 : CollatzResearch.WordTrace tailWord_1024803 prefixEnd_1024803 526216515169659187249523 := by
  unfold tailWord_1024803
  simp only [CollatzResearch.WordTrace]
  refine ⟨37377636106321228263263063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24918424070880818842175375 37377636106321228263263063)
  ·
    refine ⟨56066454159481842394894595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37377636106321228263263063 56066454159481842394894595)
    ·
      refine ⟨84099681239222763592341893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56066454159481842394894595 84099681239222763592341893)
      ·
        refine ⟨15768690232354268173564105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84099681239222763592341893 15768690232354268173564105)
        ·
          refine ⟨11826517674265701130173079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15768690232354268173564105 11826517674265701130173079)
          ·
            refine ⟨17739776511398551695259619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11826517674265701130173079 17739776511398551695259619)
            ·
              refine ⟨26609664767097827542889429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17739776511398551695259619 26609664767097827542889429)
              ·
                refine ⟨623664017978855333036471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 26609664767097827542889429 623664017978855333036471)
                ·
                  refine ⟨935496026968282999554707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 623664017978855333036471 935496026968282999554707)
                  ·
                    refine ⟨1403244040452424499332061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 935496026968282999554707 1403244040452424499332061)
                    ·
                      refine ⟨526216515169659187249523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1403244040452424499332061 526216515169659187249523)
                      ·
                        rfl

theorem cell23_1024803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 7, 1, 1, 3].length) (baseStart_1024803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1024803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1024803 prefixEnd_1024803 := by exact prefixLift 1024803
  have htrace : WordTrace (prefixWord ++ tailWord_1024803) baseStart_1024803 baseEnd_1024803 := by
    simpa [prefixWord, tailWord_1024803, baseEnd_1024803] using wordTrace_append hprefix tailTrace_1024803
  have hstable : (prefixWord ++ tailWord_1024803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024803).length < 2 ^ (prefixWord ++ tailWord_1024803).sum := by decide
  have hdescent : baseEnd_1024803 < baseStart_1024803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024859 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 9, 3, 3]
def baseStart_1024859 : Nat := 118140960795 + 1024859 * 2 ^ 59
def prefixEnd_1024859 : Nat := 4983230072969 + 3 ^ 40 * 1024859 * 2
def baseEnd_1024859 : Nat := 526245270086310968149265

theorem tailTrace_1024859 : CollatzResearch.WordTrace tailWord_1024859 prefixEnd_1024859 526245270086310968149265 := by
  unfold tailWord_1024859
  simp only [CollatzResearch.WordTrace]
  refine ⟨37379678594118349827301631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24919785729412233218201087 37379678594118349827301631)
  ·
    refine ⟨56069517891177524740952447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37379678594118349827301631 56069517891177524740952447)
    ·
      refine ⟨84104276836766287111428671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56069517891177524740952447 84104276836766287111428671)
      ·
        refine ⟨126156415255149430667143007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84104276836766287111428671 126156415255149430667143007)
        ·
          refine ⟨189234622882724146000714511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126156415255149430667143007 189234622882724146000714511)
          ·
            refine ⟨283851934324086219001071767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189234622882724146000714511 283851934324086219001071767)
            ·
              refine ⟨425777901486129328501607651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283851934324086219001071767 425777901486129328501607651)
              ·
                refine ⟨638666852229193992752411477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 425777901486129328501607651 638666852229193992752411477)
                ·
                  refine ⟨3742188587280433551283661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 638666852229193992752411477 3742188587280433551283661)
                  ·
                    refine ⟨1403320720230162581731373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3742188587280433551283661 1403320720230162581731373)
                    ·
                      refine ⟨526245270086310968149265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1403320720230162581731373 526245270086310968149265)
                      ·
                        rfl

theorem cell23_1024859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 3, 3].length) (baseStart_1024859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1024859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1024859 prefixEnd_1024859 := by exact prefixLift 1024859
  have htrace : WordTrace (prefixWord ++ tailWord_1024859) baseStart_1024859 baseEnd_1024859 := by
    simpa [prefixWord, tailWord_1024859, baseEnd_1024859] using wordTrace_append hprefix tailTrace_1024859
  have hstable : (prefixWord ++ tailWord_1024859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024859).length < 2 ^ (prefixWord ++ tailWord_1024859).sum := by decide
  have hdescent : baseEnd_1024859 < baseStart_1024859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024860 : List Nat := [2, 2, 4, 2, 1, 1, 4, 1, 1, 1, 4]
def baseStart_1024860 : Nat := 118140960795 + 1024860 * 2 ^ 59
def prefixEnd_1024860 : Nat := 4983230072969 + 3 ^ 40 * 1024860 * 2
def baseEnd_1024860 : Nat := 526245783566965464236761

theorem tailTrace_1024860 : CollatzResearch.WordTrace tailWord_1024860 prefixEnd_1024860 526245783566965464236761 := by
  unfold tailWord_1024860
  simp only [CollatzResearch.WordTrace]
  refine ⟨18689857533557363499044017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24919810044743151332058689 18689857533557363499044017)
  ·
    refine ⟨14017393150168022624283013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18689857533557363499044017 14017393150168022624283013)
    ·
      refine ⟨2628261215656504242053065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14017393150168022624283013 2628261215656504242053065)
      ·
        refine ⟨1971195911742378181539799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2628261215656504242053065 1971195911742378181539799)
        ·
          refine ⟨2956793867613567272309699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1971195911742378181539799 2956793867613567272309699)
          ·
            refine ⟨4435190801420350908464549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2956793867613567272309699 4435190801420350908464549)
            ·
              refine ⟨831598275266315795337103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4435190801420350908464549 831598275266315795337103)
              ·
                refine ⟨1247397412899473693005655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 831598275266315795337103 1247397412899473693005655)
                ·
                  refine ⟨1871096119349210539508483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1247397412899473693005655 1871096119349210539508483)
                  ·
                    refine ⟨2806644179023815809262725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1871096119349210539508483 2806644179023815809262725)
                    ·
                      refine ⟨526245783566965464236761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2806644179023815809262725 526245783566965464236761)
                      ·
                        rfl

theorem cell23_1024860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_1024860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1024860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1024860 prefixEnd_1024860 := by exact prefixLift 1024860
  have htrace : WordTrace (prefixWord ++ tailWord_1024860) baseStart_1024860 baseEnd_1024860 := by
    simpa [prefixWord, tailWord_1024860, baseEnd_1024860] using wordTrace_append hprefix tailTrace_1024860
  have hstable : (prefixWord ++ tailWord_1024860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024860).length < 2 ^ (prefixWord ++ tailWord_1024860).sum := by decide
  have hdescent : baseEnd_1024860 < baseStart_1024860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024866 : List Nat := [3, 3, 2, 1, 3, 1, 10]
def baseStart_1024866 : Nat := 118140960795 + 1024866 * 2 ^ 59
def prefixEnd_1024866 : Nat := 4983230072969 + 3 ^ 40 * 1024866 * 2
def baseEnd_1024866 : Nat := 6496899561122128898293

theorem tailTrace_1024866 : CollatzResearch.WordTrace tailWord_1024866 prefixEnd_1024866 6496899561122128898293 := by
  unfold tailWord_1024866
  simp only [CollatzResearch.WordTrace]
  refine ⟨9344983476273247505701613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24919955936728660015204301 9344983476273247505701613)
  ·
    refine ⟨3504368803602467814638105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9344983476273247505701613 3504368803602467814638105)
    ·
      refine ⟨2628276602701850860978579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3504368803602467814638105 2628276602701850860978579)
      ·
        refine ⟨3942414904052776291467869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2628276602701850860978579 3942414904052776291467869)
        ·
          refine ⟨1478405589019791109300451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3942414904052776291467869 1478405589019791109300451)
          ·
            refine ⟨2217608383529686663950677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1478405589019791109300451 2217608383529686663950677)
            ·
              refine ⟨6496899561122128898293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2217608383529686663950677 6496899561122128898293)
              ·
                rfl

theorem cell23_1024866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 10].length) (baseStart_1024866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1024866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1024866 prefixEnd_1024866 := by exact prefixLift 1024866
  have htrace : WordTrace (prefixWord ++ tailWord_1024866) baseStart_1024866 baseEnd_1024866 := by
    simpa [prefixWord, tailWord_1024866, baseEnd_1024866] using wordTrace_append hprefix tailTrace_1024866
  have hstable : (prefixWord ++ tailWord_1024866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024866).length < 2 ^ (prefixWord ++ tailWord_1024866).sum := by decide
  have hdescent : baseEnd_1024866 < baseStart_1024866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024893 : List Nat := [1, 4, 1, 1, 2, 1, 2, 5, 2, 1, 3]
def baseStart_1024893 : Nat := 118140960795 + 1024893 * 2 ^ 59
def prefixEnd_1024893 : Nat := 4983230072969 + 3 ^ 40 * 1024893 * 2
def baseEnd_1024893 : Nat := 526262728428563835124109

theorem tailTrace_1024893 : CollatzResearch.WordTrace tailWord_1024893 prefixEnd_1024893 526262728428563835124109 := by
  unfold tailWord_1024893
  simp only [CollatzResearch.WordTrace]
  refine ⟨37380918675995173634039333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24920612450663449089359555 37380918675995173634039333)
  ·
    refine ⟨7008922251749095056382375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37380918675995173634039333 7008922251749095056382375)
    ·
      refine ⟨10513383377623642584573563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7008922251749095056382375 10513383377623642584573563)
      ·
        refine ⟨15770075066435463876860345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10513383377623642584573563 15770075066435463876860345)
        ·
          refine ⟨11827556299826597907645259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15770075066435463876860345 11827556299826597907645259)
          ·
            refine ⟨17741334449739896861467889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11827556299826597907645259 17741334449739896861467889)
            ·
              refine ⟨13306000837304922646100917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17741334449739896861467889 13306000837304922646100917)
              ·
                refine ⟨1247437578497336498071961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13306000837304922646100917 1247437578497336498071961)
                ·
                  refine ⟨935578183873002373553971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1247437578497336498071961 935578183873002373553971)
                  ·
                    refine ⟨1403367275809503560330957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 935578183873002373553971 1403367275809503560330957)
                    ·
                      refine ⟨526262728428563835124109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1403367275809503560330957 526262728428563835124109)
                      ·
                        rfl

theorem cell23_1024893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 2, 1, 3].length) (baseStart_1024893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1024893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1024893 prefixEnd_1024893 := by exact prefixLift 1024893
  have htrace : WordTrace (prefixWord ++ tailWord_1024893) baseStart_1024893 baseEnd_1024893 := by
    simpa [prefixWord, tailWord_1024893, baseEnd_1024893] using wordTrace_append hprefix tailTrace_1024893
  have hstable : (prefixWord ++ tailWord_1024893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024893).length < 2 ^ (prefixWord ++ tailWord_1024893).sum := by decide
  have hdescent : baseEnd_1024893 < baseStart_1024893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024906 : List Nat := [3, 1, 2, 4, 1, 1, 1, 1, 2, 2, 5]
def baseStart_1024906 : Nat := 118140960795 + 1024906 * 2 ^ 59
def prefixEnd_1024906 : Nat := 4983230072969 + 3 ^ 40 * 1024906 * 2
def baseEnd_1024906 : Nat := 526269403677072284261549

theorem tailTrace_1024906 : CollatzResearch.WordTrace tailWord_1024906 prefixEnd_1024906 526269403677072284261549 := by
  unfold tailWord_1024906
  simp only [CollatzResearch.WordTrace]
  refine ⟨9345348206237019213565643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24920928549965384569508381 9345348206237019213565643)
  ·
    refine ⟨14018022309355528820348465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9345348206237019213565643 14018022309355528820348465)
    ·
      refine ⟨10513516732016646615261349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14018022309355528820348465 10513516732016646615261349)
      ·
        refine ⟨1971284387253121240361503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10513516732016646615261349 1971284387253121240361503)
        ·
          refine ⟨2956926580879681860542255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1971284387253121240361503 2956926580879681860542255)
          ·
            refine ⟨4435389871319522790813383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2956926580879681860542255 4435389871319522790813383)
            ·
              refine ⟨6653084806979284186220075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4435389871319522790813383 6653084806979284186220075)
              ·
                refine ⟨9979627210468926279330113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6653084806979284186220075 9979627210468926279330113)
                ·
                  refine ⟨7484720407851694709497585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9979627210468926279330113 7484720407851694709497585)
                  ·
                    refine ⟨5613540305888771032123189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7484720407851694709497585 5613540305888771032123189)
                    ·
                      refine ⟨526269403677072284261549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5613540305888771032123189 526269403677072284261549)
                      ·
                        rfl

theorem cell23_1024906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_1024906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1024906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1024906 prefixEnd_1024906 := by exact prefixLift 1024906
  have htrace : WordTrace (prefixWord ++ tailWord_1024906) baseStart_1024906 baseEnd_1024906 := by
    simpa [prefixWord, tailWord_1024906, baseEnd_1024906] using wordTrace_append hprefix tailTrace_1024906
  have hstable : (prefixWord ++ tailWord_1024906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024906).length < 2 ^ (prefixWord ++ tailWord_1024906).sum := by decide
  have hdescent : baseEnd_1024906 < baseStart_1024906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025036 : List Nat := [2, 2, 1, 2, 3, 2, 1, 1, 2, 1, 6]
def baseStart_1025036 : Nat := 118140960795 + 1025036 * 2 ^ 59
def prefixEnd_1025036 : Nat := 4983230072969 + 3 ^ 40 * 1025036 * 2
def baseEnd_1025036 : Nat := 526336156162156775635951

theorem tailTrace_1025036 : CollatzResearch.WordTrace tailWord_1025036 prefixEnd_1025036 526336156162156775635951 := by
  unfold tailWord_1025036
  simp only [CollatzResearch.WordTrace]
  refine ⟨18693067157238554528247481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24924089542984739370996641 18693067157238554528247481)
  ·
    refine ⟨14019800367928915896185611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18693067157238554528247481 14019800367928915896185611)
    ·
      refine ⟨21029700551893373844278417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14019800367928915896185611 21029700551893373844278417)
      ·
        refine ⟨15772275413920030383208813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21029700551893373844278417 15772275413920030383208813)
        ·
          refine ⟨5914603280220011393703305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15772275413920030383208813 5914603280220011393703305)
          ·
            refine ⟨4435952460165008545277479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5914603280220011393703305 4435952460165008545277479)
            ·
              refine ⟨6653928690247512817916219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4435952460165008545277479 6653928690247512817916219)
              ·
                refine ⟨9980893035371269226874329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6653928690247512817916219 9980893035371269226874329)
                ·
                  refine ⟨7485669776528451920155747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9980893035371269226874329 7485669776528451920155747)
                  ·
                    refine ⟨11228504664792677880233621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7485669776528451920155747 11228504664792677880233621)
                    ·
                      refine ⟨526336156162156775635951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11228504664792677880233621 526336156162156775635951)
                      ·
                        rfl

theorem cell23_1025036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_1025036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025036 prefixEnd_1025036 := by exact prefixLift 1025036
  have htrace : WordTrace (prefixWord ++ tailWord_1025036) baseStart_1025036 baseEnd_1025036 := by
    simpa [prefixWord, tailWord_1025036, baseEnd_1025036] using wordTrace_append hprefix tailTrace_1025036
  have hstable : (prefixWord ++ tailWord_1025036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025036).length < 2 ^ (prefixWord ++ tailWord_1025036).sum := by decide
  have hdescent : baseEnd_1025036 < baseStart_1025036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025050 : List Nat := [3, 1, 1, 3, 1, 2, 1, 6, 1, 4]
def baseStart_1025050 : Nat := 118140960795 + 1025050 * 2 ^ 59
def prefixEnd_1025050 : Nat := 4983230072969 + 3 ^ 40 * 1025050 * 2
def baseEnd_1025050 : Nat := 175447781630439906953629

theorem tailTrace_1025050 : CollatzResearch.WordTrace tailWord_1025050 prefixEnd_1025050 175447781630439906953629 := by
  unfold tailWord_1025050
  simp only [CollatzResearch.WordTrace]
  refine ⟨9346661234106597361876151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24924429957617592965003069 9346661234106597361876151)
  ·
    refine ⟨14019991851159896042814227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9346661234106597361876151 14019991851159896042814227)
    ·
      refine ⟨21029987776739844064221341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14019991851159896042814227 21029987776739844064221341)
      ·
        refine ⟨7886245416277441524083003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21029987776739844064221341 7886245416277441524083003)
        ·
          refine ⟨11829368124416162286124505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7886245416277441524083003 11829368124416162286124505)
          ·
            refine ⟨8872026093312121714593379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11829368124416162286124505 8872026093312121714593379)
            ·
              refine ⟨13308039139968182571890069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8872026093312121714593379 13308039139968182571890069)
              ·
                refine ⟨623814334686008558057347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13308039139968182571890069 623814334686008558057347)
                ·
                  refine ⟨935721502029012837086021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 623814334686008558057347 935721502029012837086021)
                  ·
                    refine ⟨175447781630439906953629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 935721502029012837086021 175447781630439906953629)
                    ·
                      rfl

theorem cell23_1025050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 6, 1, 4].length) (baseStart_1025050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025050 prefixEnd_1025050 := by exact prefixLift 1025050
  have htrace : WordTrace (prefixWord ++ tailWord_1025050) baseStart_1025050 baseEnd_1025050 := by
    simpa [prefixWord, tailWord_1025050, baseEnd_1025050] using wordTrace_append hprefix tailTrace_1025050
  have hstable : (prefixWord ++ tailWord_1025050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025050).length < 2 ^ (prefixWord ++ tailWord_1025050).sum := by decide
  have hdescent : baseEnd_1025050 < baseStart_1025050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025093 : List Nat := [1, 3, 1, 1, 1, 3, 4, 3, 1, 5]
def baseStart_1025093 : Nat := 118140960795 + 1025093 * 2 ^ 59
def prefixEnd_1025093 : Nat := 4983230072969 + 3 ^ 40 * 1025093 * 2
def baseEnd_1025093 : Nat := 175455141519821017541063

theorem tailTrace_1025093 : CollatzResearch.WordTrace tailWord_1025093 prefixEnd_1025093 175455141519821017541063 := by
  unfold tailWord_1025093
  simp only [CollatzResearch.WordTrace]
  refine ⟨37388213275270607791319933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24925475516847071860879955 37388213275270607791319933)
  ·
    refine ⟨14020579978226477921744975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37388213275270607791319933 14020579978226477921744975)
    ·
      refine ⟨21030869967339716882617463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14020579978226477921744975 21030869967339716882617463)
      ·
        refine ⟨31546304951009575323926195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21030869967339716882617463 31546304951009575323926195)
        ·
          refine ⟨47319457426514362985889293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31546304951009575323926195 47319457426514362985889293)
          ·
            refine ⟨17744796534942886119708485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47319457426514362985889293 17744796534942886119708485)
            ·
              refine ⟨3327149350301791147445341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17744796534942886119708485 3327149350301791147445341)
              ·
                refine ⟨1247681006363171680292003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3327149350301791147445341 1247681006363171680292003)
                ·
                  refine ⟨1871521509544757520438005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1247681006363171680292003 1871521509544757520438005)
                  ·
                    refine ⟨175455141519821017541063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1871521509544757520438005 175455141519821017541063)
                    ·
                      rfl

theorem cell23_1025093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 5].length) (baseStart_1025093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025093 prefixEnd_1025093 := by exact prefixLift 1025093
  have htrace : WordTrace (prefixWord ++ tailWord_1025093) baseStart_1025093 baseEnd_1025093 := by
    simpa [prefixWord, tailWord_1025093, baseEnd_1025093] using wordTrace_append hprefix tailTrace_1025093
  have hstable : (prefixWord ++ tailWord_1025093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025093).length < 2 ^ (prefixWord ++ tailWord_1025093).sum := by decide
  have hdescent : baseEnd_1025093 < baseStart_1025093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025113 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 2, 6, 2]
def baseStart_1025113 : Nat := 118140960795 + 1025113 * 2 ^ 59
def prefixEnd_1025113 : Nat := 4983230072969 + 3 ^ 40 * 1025113 * 2
def baseEnd_1025113 : Nat := 526375694172552974373097

theorem tailTrace_1025113 : CollatzResearch.WordTrace tailWord_1025113 prefixEnd_1025113 526375694172552974373097 := by
  unfold tailWord_1025113
  simp only [CollatzResearch.WordTrace]
  refine ⟨37388942735198151207047993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24925961823465434138031995 37388942735198151207047993)
  ·
    refine ⟨28041707051398613405285995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37388942735198151207047993 28041707051398613405285995)
    ·
      refine ⟨42062560577097920107928993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28041707051398613405285995 42062560577097920107928993)
      ·
        refine ⟨31546920432823440080946745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42062560577097920107928993 31546920432823440080946745)
        ·
          refine ⟨23660190324617580060710059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31546920432823440080946745 23660190324617580060710059)
          ·
            refine ⟨35490285486926370091065089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23660190324617580060710059 35490285486926370091065089)
            ·
              refine ⟨26617714115194777568298817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35490285486926370091065089 26617714115194777568298817)
              ·
                refine ⟨19963285586396083176224113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26617714115194777568298817 19963285586396083176224113)
                ·
                  refine ⟨14972464189797062382168085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19963285586396083176224113 14972464189797062382168085)
                  ·
                    refine ⟨701834258896737299164129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14972464189797062382168085 701834258896737299164129)
                    ·
                      refine ⟨526375694172552974373097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 701834258896737299164129 526375694172552974373097)
                      ·
                        rfl

theorem cell23_1025113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 6, 2].length) (baseStart_1025113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025113 prefixEnd_1025113 := by exact prefixLift 1025113
  have htrace : WordTrace (prefixWord ++ tailWord_1025113) baseStart_1025113 baseEnd_1025113 := by
    simpa [prefixWord, tailWord_1025113, baseEnd_1025113] using wordTrace_append hprefix tailTrace_1025113
  have hstable : (prefixWord ++ tailWord_1025113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025113).length < 2 ^ (prefixWord ++ tailWord_1025113).sum := by decide
  have hdescent : baseEnd_1025113 < baseStart_1025113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025130 : List Nat := [3, 1, 3, 2, 2, 2, 1, 1, 3, 1, 4]
def baseStart_1025130 : Nat := 118140960795 + 1025130 * 2 ^ 59
def prefixEnd_1025130 : Nat := 4983230072969 + 3 ^ 40 * 1025130 * 2
def baseEnd_1025130 : Nat := 526384423343679407860519

theorem tailTrace_1025130 : CollatzResearch.WordTrace tailWord_1025130 prefixEnd_1025130 526384423343679407860519 := by
  unfold tailWord_1025130
  simp only [CollatzResearch.WordTrace]
  refine ⟨9347390694034140777604211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24926375184091042073611229 9347390694034140777604211)
  ·
    refine ⟨14021086041051211166406317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9347390694034140777604211 14021086041051211166406317)
    ·
      refine ⟨5257907265394204187402369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14021086041051211166406317 5257907265394204187402369)
      ·
        refine ⟨3943430449045653140551777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5257907265394204187402369 3943430449045653140551777)
        ·
          refine ⟨2957572836784239855413833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3943430449045653140551777 2957572836784239855413833)
          ·
            refine ⟨2218179627588179891560375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2957572836784239855413833 2218179627588179891560375)
            ·
              refine ⟨3327269441382269837340563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2218179627588179891560375 3327269441382269837340563)
              ·
                refine ⟨4990904162073404756010845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3327269441382269837340563 4990904162073404756010845)
                ·
                  refine ⟨1871589060777526783504067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4990904162073404756010845 1871589060777526783504067)
                  ·
                    refine ⟨2807383591166290175256101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1871589060777526783504067 2807383591166290175256101)
                    ·
                      refine ⟨526384423343679407860519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2807383591166290175256101 526384423343679407860519)
                      ·
                        rfl

theorem cell23_1025130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_1025130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025130 prefixEnd_1025130 := by exact prefixLift 1025130
  have htrace : WordTrace (prefixWord ++ tailWord_1025130) baseStart_1025130 baseEnd_1025130 := by
    simpa [prefixWord, tailWord_1025130, baseEnd_1025130] using wordTrace_append hprefix tailTrace_1025130
  have hstable : (prefixWord ++ tailWord_1025130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025130).length < 2 ^ (prefixWord ++ tailWord_1025130).sum := by decide
  have hdescent : baseEnd_1025130 < baseStart_1025130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025136 : List Nat := [2, 1, 1, 1, 5, 1, 1, 11]
def baseStart_1025136 : Nat := 118140960795 + 1025136 * 2 ^ 59
def prefixEnd_1025136 : Nat := 4983230072969 + 3 ^ 40 * 1025136 * 2
def baseEnd_1025136 : Nat := 19495833489911347569833

theorem tailTrace_1025136 : CollatzResearch.WordTrace tailWord_1025136 prefixEnd_1025136 19495833489911347569833 := by
  unfold tailWord_1025136
  simp only [CollatzResearch.WordTrace]
  refine ⟨18694890807057413067567631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24926521076076550756756841 18694890807057413067567631)
  ·
    refine ⟨28042336210586119601351447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18694890807057413067567631 28042336210586119601351447)
    ·
      refine ⟨42063504315879179402027171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28042336210586119601351447 42063504315879179402027171)
      ·
        refine ⟨63095256473818769103040757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42063504315879179402027171 63095256473818769103040757)
        ·
          refine ⟨5915180294420509603410071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63095256473818769103040757 5915180294420509603410071)
          ·
            refine ⟨8872770441630764405115107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5915180294420509603410071 8872770441630764405115107)
            ·
              refine ⟨13309155662446146607672661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8872770441630764405115107 13309155662446146607672661)
              ·
                refine ⟨19495833489911347569833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 13309155662446146607672661 19495833489911347569833)
                ·
                  rfl

theorem cell23_1025136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 11].length) (baseStart_1025136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025136 prefixEnd_1025136 := by exact prefixLift 1025136
  have htrace : WordTrace (prefixWord ++ tailWord_1025136) baseStart_1025136 baseEnd_1025136 := by
    simpa [prefixWord, tailWord_1025136, baseEnd_1025136] using wordTrace_append hprefix tailTrace_1025136
  have hstable : (prefixWord ++ tailWord_1025136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025136).length < 2 ^ (prefixWord ++ tailWord_1025136).sum := by decide
  have hdescent : baseEnd_1025136 < baseStart_1025136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025143 : List Nat := [1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 4]
def baseStart_1025143 : Nat := 118140960795 + 1025143 * 2 ^ 59
def prefixEnd_1025143 : Nat := 4983230072969 + 3 ^ 40 * 1025143 * 2
def baseEnd_1025143 : Nat := 526391098592187856997959

theorem tailTrace_1025143 : CollatzResearch.WordTrace tailWord_1025143 prefixEnd_1025143 526391098592187856997959 := by
  unfold tailWord_1025143
  simp only [CollatzResearch.WordTrace]
  refine ⟨37390036925089466330640083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24926691283392977553760055 37390036925089466330640083)
  ·
    refine ⟨56085055387634199495960125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37390036925089466330640083 56085055387634199495960125)
    ·
      refine ⟨21031895770362824810985047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56085055387634199495960125 21031895770362824810985047)
      ·
        refine ⟨31547843655544237216477571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21031895770362824810985047 31547843655544237216477571)
        ·
          refine ⟨47321765483316355824716357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31547843655544237216477571 47321765483316355824716357)
          ·
            refine ⟨8872831028121816717134317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47321765483316355824716357 8872831028121816717134317)
            ·
              refine ⟨3327311635545681268925369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8872831028121816717134317 3327311635545681268925369)
              ·
                refine ⟨2495483726659260951694027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3327311635545681268925369 2495483726659260951694027)
                ·
                  refine ⟨3743225589988891427541041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2495483726659260951694027 3743225589988891427541041)
                  ·
                    refine ⟨2807419192491668570655781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3743225589988891427541041 2807419192491668570655781)
                    ·
                      refine ⟨526391098592187856997959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2807419192491668570655781 526391098592187856997959)
                      ·
                        rfl

theorem cell23_1025143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 4].length) (baseStart_1025143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025143 prefixEnd_1025143 := by exact prefixLift 1025143
  have htrace : WordTrace (prefixWord ++ tailWord_1025143) baseStart_1025143 baseEnd_1025143 := by
    simpa [prefixWord, tailWord_1025143, baseEnd_1025143] using wordTrace_append hprefix tailTrace_1025143
  have hstable : (prefixWord ++ tailWord_1025143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025143).length < 2 ^ (prefixWord ++ tailWord_1025143).sum := by decide
  have hdescent : baseEnd_1025143 < baseStart_1025143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025157 : List Nat := [1, 3, 1, 1, 6, 1, 2, 2, 2, 4]
def baseStart_1025157 : Nat := 118140960795 + 1025157 * 2 ^ 59
def prefixEnd_1025157 : Nat := 4983230072969 + 3 ^ 40 * 1025157 * 2
def baseEnd_1025157 : Nat := 175466095773783600740965

theorem tailTrace_1025157 : CollatzResearch.WordTrace tailWord_1025157 prefixEnd_1025157 175466095773783600740965 := by
  unfold tailWord_1025157
  simp only [CollatzResearch.WordTrace]
  refine ⟨37390547547038746721649725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24927031698025831147766483 37390547547038746721649725)
  ·
    refine ⟨14021455330139530020618647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37390547547038746721649725 14021455330139530020618647)
    ·
      refine ⟨21032182995209295030927971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14021455330139530020618647 21032182995209295030927971)
      ·
        refine ⟨31548274492813942546391957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21032182995209295030927971 31548274492813942546391957)
        ·
          refine ⟨1478825366850653556862123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31548274492813942546391957 1478825366850653556862123)
          ·
            refine ⟨2218238050275980335293185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1478825366850653556862123 2218238050275980335293185)
            ·
              refine ⟨1663678537706985251469889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2218238050275980335293185 1663678537706985251469889)
              ·
                refine ⟨1247758903280238938602417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1663678537706985251469889 1247758903280238938602417)
                ·
                  refine ⟨935819177460179203951813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1247758903280238938602417 935819177460179203951813)
                  ·
                    refine ⟨175466095773783600740965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 935819177460179203951813 175466095773783600740965)
                    ·
                      rfl

theorem cell23_1025157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 2, 4].length) (baseStart_1025157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025157 prefixEnd_1025157 := by exact prefixLift 1025157
  have htrace : WordTrace (prefixWord ++ tailWord_1025157) baseStart_1025157 baseEnd_1025157 := by
    simpa [prefixWord, tailWord_1025157, baseEnd_1025157] using wordTrace_append hprefix tailTrace_1025157
  have hstable : (prefixWord ++ tailWord_1025157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025157).length < 2 ^ (prefixWord ++ tailWord_1025157).sum := by decide
  have hdescent : baseEnd_1025157 < baseStart_1025157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025170 : List Nat := [3, 2, 3, 1, 1, 4, 1, 8]
def baseStart_1025170 : Nat := 118140960795 + 1025170 * 2 ^ 59
def prefixEnd_1025170 : Nat := 4983230072969 + 3 ^ 40 * 1025170 * 2
def baseEnd_1025170 : Nat := 19496480095179972272605

theorem tailTrace_1025170 : CollatzResearch.WordTrace tailWord_1025170 prefixEnd_1025170 19496480095179972272605 := by
  unfold tailWord_1025170
  simp only [CollatzResearch.WordTrace]
  refine ⟨9347755423997912485468241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24927347797327766627915309 9347755423997912485468241)
  ·
    refine ⟨7010816567998434364101181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9347755423997912485468241 7010816567998434364101181)
    ·
      refine ⟨2629056212999412886537943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7010816567998434364101181 2629056212999412886537943)
      ·
        refine ⟨3943584319499119329806915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2629056212999412886537943 3943584319499119329806915)
        ·
          refine ⟨5915376479248678994710373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3943584319499119329806915 5915376479248678994710373)
          ·
            refine ⟨1109133089859127311508195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5915376479248678994710373 1109133089859127311508195)
            ·
              refine ⟨1663699634788690967262293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1109133089859127311508195 1663699634788690967262293)
              ·
                refine ⟨19496480095179972272605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1663699634788690967262293 19496480095179972272605)
                ·
                  rfl

theorem cell23_1025170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 8].length) (baseStart_1025170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025170 prefixEnd_1025170 := by exact prefixLift 1025170
  have htrace : WordTrace (prefixWord ++ tailWord_1025170) baseStart_1025170 baseEnd_1025170 := by
    simpa [prefixWord, tailWord_1025170, baseEnd_1025170] using wordTrace_append hprefix tailTrace_1025170
  have hstable : (prefixWord ++ tailWord_1025170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025170).length < 2 ^ (prefixWord ++ tailWord_1025170).sum := by decide
  have hdescent : baseEnd_1025170 < baseStart_1025170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025180 : List Nat := [2, 2, 3, 2, 1, 2, 1, 3, 1, 3, 3]
def baseStart_1025180 : Nat := 118140960795 + 1025180 * 2 ^ 59
def prefixEnd_1025180 : Nat := 4983230072969 + 3 ^ 40 * 1025180 * 2
def baseEnd_1025180 : Nat := 526410097376404212235289

theorem tailTrace_1025180 : CollatzResearch.WordTrace tailWord_1025180 prefixEnd_1025180 526410097376404212235289 := by
  unfold tailWord_1025180
  simp only [CollatzResearch.WordTrace]
  refine ⟨18695693212977710824868497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24927590950636947766491329 18695693212977710824868497)
  ·
    refine ⟨14021769909733283118651373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18695693212977710824868497 14021769909733283118651373)
    ·
      refine ⟨5258163716149981169494265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14021769909733283118651373 5258163716149981169494265)
      ·
        refine ⟨3943622787112485877120699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5258163716149981169494265 3943622787112485877120699)
        ·
          refine ⟨5915434180668728815681049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3943622787112485877120699 5915434180668728815681049)
          ·
            refine ⟨4436575635501546611760787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5915434180668728815681049 4436575635501546611760787)
            ·
              refine ⟨6654863453252319917641181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4436575635501546611760787 6654863453252319917641181)
              ·
                refine ⟨2495573794969619969115443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6654863453252319917641181 2495573794969619969115443)
                ·
                  refine ⟨3743360692454429953673165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2495573794969619969115443 3743360692454429953673165)
                  ·
                    refine ⟨1403760259670411232627437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3743360692454429953673165 1403760259670411232627437)
                    ·
                      refine ⟨526410097376404212235289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1403760259670411232627437 526410097376404212235289)
                      ·
                        rfl

theorem cell23_1025180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_1025180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025180 prefixEnd_1025180 := by exact prefixLift 1025180
  have htrace : WordTrace (prefixWord ++ tailWord_1025180) baseStart_1025180 baseEnd_1025180 := by
    simpa [prefixWord, tailWord_1025180, baseEnd_1025180] using wordTrace_append hprefix tailTrace_1025180
  have hstable : (prefixWord ++ tailWord_1025180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025180).length < 2 ^ (prefixWord ++ tailWord_1025180).sum := by decide
  have hdescent : baseEnd_1025180 < baseStart_1025180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025207 : List Nat := [1, 1, 3, 1, 4, 1, 3, 3, 1, 3, 2]
def baseStart_1025207 : Nat := 118140960795 + 1025207 * 2 ^ 59
def prefixEnd_1025207 : Nat := 4983230072969 + 3 ^ 40 * 1025207 * 2
def baseEnd_1025207 : Nat := 526423961354075606597665

theorem tailTrace_1025207 : CollatzResearch.WordTrace tailWord_1025207 prefixEnd_1025207 526423961354075606597665 := by
  unfold tailWord_1025207
  simp only [CollatzResearch.WordTrace]
  refine ⟨37392371196857605260969875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24928247464571736840646583 37392371196857605260969875)
  ·
    refine ⟨56088556795286407891454813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37392371196857605260969875 56088556795286407891454813)
    ·
      refine ⟨21033208798232402959295555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56088556795286407891454813 21033208798232402959295555)
      ·
        refine ⟨31549813197348604438943333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21033208798232402959295555 31549813197348604438943333)
        ·
          refine ⟨5915589974502863332301875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31549813197348604438943333 5915589974502863332301875)
          ·
            refine ⟨8873384961754294998452813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5915589974502863332301875 8873384961754294998452813)
            ·
              refine ⟨3327519360657860624419805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8873384961754294998452813 3327519360657860624419805)
              ·
                refine ⟨1247819760246697734157427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3327519360657860624419805 1247819760246697734157427)
                ·
                  refine ⟨1871729640370046601236141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1247819760246697734157427 1871729640370046601236141)
                  ·
                    refine ⟨701898615138767475463553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1871729640370046601236141 701898615138767475463553)
                    ·
                      refine ⟨526423961354075606597665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 701898615138767475463553 526423961354075606597665)
                      ·
                        rfl

theorem cell23_1025207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 3, 2].length) (baseStart_1025207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025207 prefixEnd_1025207 := by exact prefixLift 1025207
  have htrace : WordTrace (prefixWord ++ tailWord_1025207) baseStart_1025207 baseEnd_1025207 := by
    simpa [prefixWord, tailWord_1025207, baseEnd_1025207] using wordTrace_append hprefix tailTrace_1025207
  have hstable : (prefixWord ++ tailWord_1025207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025207).length < 2 ^ (prefixWord ++ tailWord_1025207).sum := by decide
  have hdescent : baseEnd_1025207 < baseStart_1025207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025213 : List Nat := [1, 4, 1, 2, 1, 1, 3, 2, 2, 6]
def baseStart_1025213 : Nat := 118140960795 + 1025213 * 2 ^ 59
def prefixEnd_1025213 : Nat := 4983230072969 + 3 ^ 40 * 1025213 * 2
def baseEnd_1025213 : Nat := 175475680746000861040879

theorem tailTrace_1025213 : CollatzResearch.WordTrace tailWord_1025213 prefixEnd_1025213 175475680746000861040879 := by
  unfold tailWord_1025213
  simp only [CollatzResearch.WordTrace]
  refine ⟨37392590034835868285688293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24928393356557245523792195 37392590034835868285688293)
  ·
    refine ⟨7011110631531725303566555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37392590034835868285688293 7011110631531725303566555)
    ·
      refine ⟨10516665947297587955349833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7011110631531725303566555 10516665947297587955349833)
      ·
        refine ⟨7887499460473190966512375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10516665947297587955349833 7887499460473190966512375)
        ·
          refine ⟨11831249190709786449768563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7887499460473190966512375 11831249190709786449768563)
          ·
            refine ⟨17746873786064679674652845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11831249190709786449768563 17746873786064679674652845)
            ·
              refine ⟨6655077669774254877994817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17746873786064679674652845 6655077669774254877994817)
              ·
                refine ⟨4991308252330691158496113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6655077669774254877994817 4991308252330691158496113)
                ·
                  refine ⟨3743481189248018368872085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4991308252330691158496113 3743481189248018368872085)
                  ·
                    refine ⟨175475680746000861040879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3743481189248018368872085 175475680746000861040879)
                    ·
                      rfl

theorem cell23_1025213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_1025213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025213 prefixEnd_1025213 := by exact prefixLift 1025213
  have htrace : WordTrace (prefixWord ++ tailWord_1025213) baseStart_1025213 baseEnd_1025213 := by
    simpa [prefixWord, tailWord_1025213, baseEnd_1025213] using wordTrace_append hprefix tailTrace_1025213
  have hstable : (prefixWord ++ tailWord_1025213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025213).length < 2 ^ (prefixWord ++ tailWord_1025213).sum := by decide
  have hdescent : baseEnd_1025213 < baseStart_1025213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025214 : List Nat := [4, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3]
def baseStart_1025214 : Nat := 118140960795 + 1025214 * 2 ^ 59
def prefixEnd_1025214 : Nat := 4983230072969 + 3 ^ 40 * 1025214 * 2
def baseEnd_1025214 : Nat := 526427555718657079210133

theorem tailTrace_1025214 : CollatzResearch.WordTrace tailWord_1025214 prefixEnd_1025214 526427555718657079210133 := by
  unfold tailWord_1025214
  simp only [CollatzResearch.WordTrace]
  refine ⟨4674078313479030682059337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24928417671888163637649797 4674078313479030682059337)
  ·
    refine ⟨3505558735109273011544503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4674078313479030682059337 3505558735109273011544503)
    ·
      refine ⟨5258338102663909517316755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3505558735109273011544503 5258338102663909517316755)
      ·
        refine ⟨7887507153995864275975133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5258338102663909517316755 7887507153995864275975133)
        ·
          refine ⟨2957815182748449103490675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7887507153995864275975133 2957815182748449103490675)
          ·
            refine ⟨4436722774122673655236013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2957815182748449103490675 4436722774122673655236013)
            ·
              refine ⟨1663771040296002620713505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4436722774122673655236013 1663771040296002620713505)
              ·
                refine ⟨1247828280222001965535129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1663771040296002620713505 1247828280222001965535129)
                ·
                  refine ⟨935871210166501474151347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1247828280222001965535129 935871210166501474151347)
                  ·
                    refine ⟨1403806815249752211227021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 935871210166501474151347 1403806815249752211227021)
                    ·
                      refine ⟨526427555718657079210133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1403806815249752211227021 526427555718657079210133)
                      ·
                        rfl

theorem cell23_1025214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_1025214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025214 prefixEnd_1025214 := by exact prefixLift 1025214
  have htrace : WordTrace (prefixWord ++ tailWord_1025214) baseStart_1025214 baseEnd_1025214 := by
    simpa [prefixWord, tailWord_1025214, baseEnd_1025214] using wordTrace_append hprefix tailTrace_1025214
  have hstable : (prefixWord ++ tailWord_1025214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025214).length < 2 ^ (prefixWord ++ tailWord_1025214).sum := by decide
  have hdescent : baseEnd_1025214 < baseStart_1025214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025223 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 1, 6, 3]
def baseStart_1025223 : Nat := 118140960795 + 1025223 * 2 ^ 59
def prefixEnd_1025223 : Nat := 4983230072969 + 3 ^ 40 * 1025223 * 2
def baseEnd_1025223 : Nat := 526432177044547543997591

theorem tailTrace_1025223 : CollatzResearch.WordTrace tailWord_1025223 prefixEnd_1025223 526432177044547543997591 := by
  unfold tailWord_1025223
  simp only [CollatzResearch.WordTrace]
  refine ⟨37392954764799639993552323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24928636509866426662368215 37392954764799639993552323)
  ·
    refine ⟨56089432147199459990328485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37392954764799639993552323 56089432147199459990328485)
    ·
      refine ⟨10516768527599898748186591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56089432147199459990328485 10516768527599898748186591)
      ·
        refine ⟨15775152791399848122279887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10516768527599898748186591 15775152791399848122279887)
        ·
          refine ⟨23662729187099772183419831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15775152791399848122279887 23662729187099772183419831)
          ·
            refine ⟨35494093780649658275129747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23662729187099772183419831 35494093780649658275129747)
            ·
              refine ⟨53241140670974487412694621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35494093780649658275129747 53241140670974487412694621)
              ·
                refine ⟨19965427751615432779760483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53241140670974487412694621 19965427751615432779760483)
                ·
                  refine ⟨29948141627423149169640725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19965427751615432779760483 29948141627423149169640725)
                  ·
                    refine ⟨1403819138785460117326909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29948141627423149169640725 1403819138785460117326909)
                    ·
                      refine ⟨526432177044547543997591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1403819138785460117326909 526432177044547543997591)
                      ·
                        rfl

theorem cell23_1025223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 6, 3].length) (baseStart_1025223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025223 prefixEnd_1025223 := by exact prefixLift 1025223
  have htrace : WordTrace (prefixWord ++ tailWord_1025223) baseStart_1025223 baseEnd_1025223 := by
    simpa [prefixWord, tailWord_1025223, baseEnd_1025223] using wordTrace_append hprefix tailTrace_1025223
  have hstable : (prefixWord ++ tailWord_1025223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025223).length < 2 ^ (prefixWord ++ tailWord_1025223).sum := by decide
  have hdescent : baseEnd_1025223 < baseStart_1025223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025280 : List Nat := [2, 1, 1, 2, 1, 1, 3, 3, 2, 5, 2]
def baseStart_1025280 : Nat := 118140960795 + 1025280 * 2 ^ 59
def prefixEnd_1025280 : Nat := 4983230072969 + 3 ^ 40 * 1025280 * 2
def baseEnd_1025280 : Nat := 526461445441853820984829

theorem tailTrace_1025280 : CollatzResearch.WordTrace tailWord_1025280 prefixEnd_1025280 526461445441853820984829 := by
  unfold tailWord_1025280
  simp only [CollatzResearch.WordTrace]
  refine ⟨18697516862796569364188647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24930022483728759152251529 18697516862796569364188647)
  ·
    refine ⟨28046275294194854046282971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18697516862796569364188647 28046275294194854046282971)
    ·
      refine ⟨42069412941292281069424457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28046275294194854046282971 42069412941292281069424457)
      ·
        refine ⟨31552059705969210802068343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42069412941292281069424457 31552059705969210802068343)
        ·
          refine ⟨47328089558953816203102515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31552059705969210802068343 47328089558953816203102515)
          ·
            refine ⟨70992134338430724304653773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47328089558953816203102515 70992134338430724304653773)
            ·
              refine ⟨26622050376911521614245165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70992134338430724304653773 26622050376911521614245165)
              ·
                refine ⟨9983268891341820605341937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26622050376911521614245165 9983268891341820605341937)
                ·
                  refine ⟨7487451668506365454006453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9983268891341820605341937 7487451668506365454006453)
                  ·
                    refine ⟨701948593922471761313105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7487451668506365454006453 701948593922471761313105)
                    ·
                      refine ⟨526461445441853820984829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 701948593922471761313105 526461445441853820984829)
                      ·
                        rfl

theorem cell23_1025280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 2, 5, 2].length) (baseStart_1025280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025280 prefixEnd_1025280 := by exact prefixLift 1025280
  have htrace : WordTrace (prefixWord ++ tailWord_1025280) baseStart_1025280 baseEnd_1025280 := by
    simpa [prefixWord, tailWord_1025280, baseEnd_1025280] using wordTrace_append hprefix tailTrace_1025280
  have hstable : (prefixWord ++ tailWord_1025280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025280).length < 2 ^ (prefixWord ++ tailWord_1025280).sum := by decide
  have hdescent : baseEnd_1025280 < baseStart_1025280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025283 : List Nat := [1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 7]
def baseStart_1025283 : Nat := 118140960795 + 1025283 * 2 ^ 59
def prefixEnd_1025283 : Nat := 4983230072969 + 3 ^ 40 * 1025283 * 2
def baseEnd_1025283 : Nat := 526462985883817309247315

theorem tailTrace_1025283 : CollatzResearch.WordTrace tailWord_1025283 prefixEnd_1025283 526462985883817309247315 := by
  unfold tailWord_1025283
  simp only [CollatzResearch.WordTrace]
  refine ⟨37395143144582270240736503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24930095429721513493824335 37395143144582270240736503)
  ·
    refine ⟨56092714716873405361104755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37395143144582270240736503 56092714716873405361104755)
    ·
      refine ⟨84139072075310108041657133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56092714716873405361104755 84139072075310108041657133)
      ·
        refine ⟨31552152028241290515621425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84139072075310108041657133 31552152028241290515621425)
        ·
          refine ⟨23664114021180967886716069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31552152028241290515621425 23664114021180967886716069)
          ·
            refine ⟨4437021378971431478759263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23664114021180967886716069 4437021378971431478759263)
            ·
              refine ⟨6655532068457147218138895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4437021378971431478759263 6655532068457147218138895)
              ·
                refine ⟨9983298102685720827208343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6655532068457147218138895 9983298102685720827208343)
                ·
                  refine ⟨14974947154028581240812515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9983298102685720827208343 14974947154028581240812515)
                  ·
                    refine ⟨22462420731042871861218773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14974947154028581240812515 22462420731042871861218773)
                    ·
                      refine ⟨526462985883817309247315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 22462420731042871861218773 526462985883817309247315)
                      ·
                        rfl

theorem cell23_1025283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 7].length) (baseStart_1025283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025283 prefixEnd_1025283 := by exact prefixLift 1025283
  have htrace : WordTrace (prefixWord ++ tailWord_1025283) baseStart_1025283 baseEnd_1025283 := by
    simpa [prefixWord, tailWord_1025283, baseEnd_1025283] using wordTrace_append hprefix tailTrace_1025283
  have hstable : (prefixWord ++ tailWord_1025283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025283).length < 2 ^ (prefixWord ++ tailWord_1025283).sum := by decide
  have hdescent : baseEnd_1025283 < baseStart_1025283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025288 : List Nat := [2, 1, 3, 2, 4, 2, 2, 1, 2, 2, 2]
def baseStart_1025288 : Nat := 118140960795 + 1025288 * 2 ^ 59
def prefixEnd_1025288 : Nat := 4983230072969 + 3 ^ 40 * 1025288 * 2
def baseEnd_1025288 : Nat := 526465553287089789684793

theorem tailTrace_1025288 : CollatzResearch.WordTrace tailWord_1025288 prefixEnd_1025288 526465553287089789684793 := by
  unfold tailWord_1025288
  simp only [CollatzResearch.WordTrace]
  refine ⟨18697662754782078047334259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24930217006376104063112345 18697662754782078047334259)
  ·
    refine ⟨28046494132173117071001389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18697662754782078047334259 28046494132173117071001389)
    ·
      refine ⟨10517435299564918901625521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28046494132173117071001389 10517435299564918901625521)
      ·
        refine ⟨7888076474673689176219141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10517435299564918901625521 7888076474673689176219141)
        ·
          refine ⟨1479014339001316720541089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7888076474673689176219141 1479014339001316720541089)
          ·
            refine ⟨1109260754250987540405817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1479014339001316720541089 1109260754250987540405817)
            ·
              refine ⟨831945565688240655304363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1109260754250987540405817 831945565688240655304363)
              ·
                refine ⟨1247918348532360982956545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 831945565688240655304363 1247918348532360982956545)
                ·
                  refine ⟨935938761399270737217409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1247918348532360982956545 935938761399270737217409)
                  ·
                    refine ⟨701954071049453052913057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 935938761399270737217409 701954071049453052913057)
                    ·
                      refine ⟨526465553287089789684793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 701954071049453052913057 526465553287089789684793)
                      ·
                        rfl

theorem cell23_1025288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_1025288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025288 prefixEnd_1025288 := by exact prefixLift 1025288
  have htrace : WordTrace (prefixWord ++ tailWord_1025288) baseStart_1025288 baseEnd_1025288 := by
    simpa [prefixWord, tailWord_1025288, baseEnd_1025288] using wordTrace_append hprefix tailTrace_1025288
  have hstable : (prefixWord ++ tailWord_1025288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025288).length < 2 ^ (prefixWord ++ tailWord_1025288).sum := by decide
  have hdescent : baseEnd_1025288 < baseStart_1025288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025323 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 4]
def baseStart_1025323 : Nat := 118140960795 + 1025323 * 2 ^ 59
def prefixEnd_1025323 : Nat := 4983230072969 + 3 ^ 40 * 1025323 * 2
def baseEnd_1025323 : Nat := 526483525109997152747131

theorem tailTrace_1025323 : CollatzResearch.WordTrace tailWord_1025323 prefixEnd_1025323 526483525109997152747131 := by
  unfold tailWord_1025323
  simp only [CollatzResearch.WordTrace]
  refine ⟨37396602064437357072192623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24931068042958238048128415 37396602064437357072192623)
  ·
    refine ⟨56094903096656035608288935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37396602064437357072192623 56094903096656035608288935)
    ·
      refine ⟨84142354644984053412433403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56094903096656035608288935 84142354644984053412433403)
      ·
        refine ⟨126213531967476080118650105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84142354644984053412433403 126213531967476080118650105)
        ·
          refine ⟨94660148975607060088987579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126213531967476080118650105 94660148975607060088987579)
          ·
            refine ⟨141990223463410590133481369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94660148975607060088987579 141990223463410590133481369)
            ·
              refine ⟨106492667597557942600111027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141990223463410590133481369 106492667597557942600111027)
              ·
                refine ⟨159739001396336913900166541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106492667597557942600111027 159739001396336913900166541)
                ·
                  refine ⟨59902125523626342712562453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159739001396336913900166541 59902125523626342712562453)
                  ·
                    refine ⟨2807912133919984814651365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 59902125523626342712562453 2807912133919984814651365)
                    ·
                      refine ⟨526483525109997152747131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2807912133919984814651365 526483525109997152747131)
                      ·
                        rfl

theorem cell23_1025323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 4].length) (baseStart_1025323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025323 prefixEnd_1025323 := by exact prefixLift 1025323
  have htrace : WordTrace (prefixWord ++ tailWord_1025323) baseStart_1025323 baseEnd_1025323 := by
    simpa [prefixWord, tailWord_1025323, baseEnd_1025323] using wordTrace_append hprefix tailTrace_1025323
  have hstable : (prefixWord ++ tailWord_1025323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025323).length < 2 ^ (prefixWord ++ tailWord_1025323).sum := by decide
  have hdescent : baseEnd_1025323 < baseStart_1025323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025384 : List Nat := [2, 1, 4, 2, 3, 2, 1, 2, 6]
def baseStart_1025384 : Nat := 118140960795 + 1025384 * 2 ^ 59
def prefixEnd_1025384 : Nat := 4983230072969 + 3 ^ 40 * 1025384 * 2
def baseEnd_1025384 : Nat := 58501649714435712676039

theorem tailTrace_1025384 : CollatzResearch.WordTrace tailWord_1025384 prefixEnd_1025384 58501649714435712676039 := by
  unfold tailWord_1025384
  simp only [CollatzResearch.WordTrace]
  refine ⟨18699413458608182245081603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24932551278144242993442137 18699413458608182245081603)
  ·
    refine ⟨28049120187912273367622405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18699413458608182245081603 28049120187912273367622405)
    ·
      refine ⟨5259210035233551256429201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28049120187912273367622405 5259210035233551256429201)
      ·
        refine ⟨3944407526425163442321901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5259210035233551256429201 3944407526425163442321901)
        ·
          refine ⟨1479152822409436290870713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3944407526425163442321901 1479152822409436290870713)
          ·
            refine ⟨1109364616807077218153035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1479152822409436290870713 1109364616807077218153035)
            ·
              refine ⟨1664046925210615827229553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1109364616807077218153035 1664046925210615827229553)
              ·
                refine ⟨1248035193907961870422165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1664046925210615827229553 1248035193907961870422165)
                ·
                  refine ⟨58501649714435712676039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1248035193907961870422165 58501649714435712676039)
                  ·
                    rfl

theorem cell23_1025384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 6].length) (baseStart_1025384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025384 prefixEnd_1025384 := by exact prefixLift 1025384
  have htrace : WordTrace (prefixWord ++ tailWord_1025384) baseStart_1025384 baseEnd_1025384 := by
    simpa [prefixWord, tailWord_1025384, baseEnd_1025384] using wordTrace_append hprefix tailTrace_1025384
  have hstable : (prefixWord ++ tailWord_1025384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025384).length < 2 ^ (prefixWord ++ tailWord_1025384).sum := by decide
  have hdescent : baseEnd_1025384 < baseStart_1025384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025394 : List Nat := [3, 2, 1, 2, 1, 2, 4, 1, 3, 1, 3]
def baseStart_1025394 : Nat := 118140960795 + 1025394 * 2 ^ 59
def prefixEnd_1025394 : Nat := 4983230072969 + 3 ^ 40 * 1025394 * 2
def baseEnd_1025394 : Nat := 526519982236466374959305

theorem tailTrace_1025394 : CollatzResearch.WordTrace tailWord_1025394 prefixEnd_1025394 526519982236466374959305 := by
  unfold tailWord_1025394
  simp only [CollatzResearch.WordTrace]
  refine ⟨9349797911795034049506809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24932794431453424132018157 9349797911795034049506809)
  ·
    refine ⟨7012348433846275537130107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9349797911795034049506809 7012348433846275537130107)
    ·
      refine ⟨10518522650769413305695161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7012348433846275537130107 10518522650769413305695161)
      ·
        refine ⟨7888891988077059979271371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10518522650769413305695161 7888891988077059979271371)
        ·
          refine ⟨11833337982115589968907057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7888891988077059979271371 11833337982115589968907057)
          ·
            refine ⟨8875003486586692476680293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11833337982115589968907057 8875003486586692476680293)
            ·
              refine ⟨1664063153735004839377555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8875003486586692476680293 1664063153735004839377555)
              ·
                refine ⟨2496094730602507259066333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1664063153735004839377555 2496094730602507259066333)
                ·
                  refine ⟨936035523975940222149875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2496094730602507259066333 936035523975940222149875)
                  ·
                    refine ⟨1404053285963910333224813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 936035523975940222149875 1404053285963910333224813)
                    ·
                      refine ⟨526519982236466374959305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1404053285963910333224813 526519982236466374959305)
                      ·
                        rfl

theorem cell23_1025394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_1025394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025394 prefixEnd_1025394 := by exact prefixLift 1025394
  have htrace : WordTrace (prefixWord ++ tailWord_1025394) baseStart_1025394 baseEnd_1025394 := by
    simpa [prefixWord, tailWord_1025394, baseEnd_1025394] using wordTrace_append hprefix tailTrace_1025394
  have hstable : (prefixWord ++ tailWord_1025394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025394).length < 2 ^ (prefixWord ++ tailWord_1025394).sum := by decide
  have hdescent : baseEnd_1025394 < baseStart_1025394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025420 : List Nat := [2, 2, 1, 2, 1, 3, 1, 2, 3, 1, 5]
def baseStart_1025420 : Nat := 118140960795 + 1025420 * 2 ^ 59
def prefixEnd_1025420 : Nat := 4983230072969 + 3 ^ 40 * 1025420 * 2
def baseEnd_1025420 : Nat := 526533332733483273234185

theorem tailTrace_1025420 : CollatzResearch.WordTrace tailWord_1025420 prefixEnd_1025420 526533332733483273234185 := by
  unfold tailWord_1025420
  simp only [CollatzResearch.WordTrace]
  refine ⟨18700069972542971319236857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24933426630057295092315809 18700069972542971319236857)
  ·
    refine ⟨14025052479407228489427643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18700069972542971319236857 14025052479407228489427643)
    ·
      refine ⟨21037578719110842734141465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14025052479407228489427643 21037578719110842734141465)
      ·
        refine ⟨15778184039333132050606099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21037578719110842734141465 15778184039333132050606099)
        ·
          refine ⟨23667276058999698075909149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15778184039333132050606099 23667276058999698075909149)
          ·
            refine ⟨8875228522124886778465931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23667276058999698075909149 8875228522124886778465931)
            ·
              refine ⟨13312842783187330167698897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8875228522124886778465931 13312842783187330167698897)
              ·
                refine ⟨9984632087390497625774173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13312842783187330167698897 9984632087390497625774173)
                ·
                  refine ⟨3744237032771436609665315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9984632087390497625774173 3744237032771436609665315)
                  ·
                    refine ⟨5616355549157154914497973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3744237032771436609665315 5616355549157154914497973)
                    ·
                      refine ⟨526533332733483273234185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5616355549157154914497973 526533332733483273234185)
                      ·
                        rfl

theorem cell23_1025420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_1025420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025420 prefixEnd_1025420 := by exact prefixLift 1025420
  have htrace : WordTrace (prefixWord ++ tailWord_1025420) baseStart_1025420 baseEnd_1025420 := by
    simpa [prefixWord, tailWord_1025420, baseEnd_1025420] using wordTrace_append hprefix tailTrace_1025420
  have hstable : (prefixWord ++ tailWord_1025420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025420).length < 2 ^ (prefixWord ++ tailWord_1025420).sum := by decide
  have hdescent : baseEnd_1025420 < baseStart_1025420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025428 : List Nat := [2, 4, 2, 1, 2, 1, 3, 3, 1, 1, 3]
def baseStart_1025428 : Nat := 118140960795 + 1025428 * 2 ^ 59
def prefixEnd_1025428 : Nat := 4983230072969 + 3 ^ 40 * 1025428 * 2
def baseEnd_1025428 : Nat := 526537440578719241934149

theorem tailTrace_1025428 : CollatzResearch.WordTrace tailWord_1025428 prefixEnd_1025428 526537440578719241934149 := by
  unfold tailWord_1025428
  simp only [CollatzResearch.WordTrace]
  refine ⟨18700215864528480002382469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24933621152704640003176625 18700215864528480002382469)
  ·
    refine ⟨3506290474599090000446713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18700215864528480002382469 3506290474599090000446713)
    ·
      refine ⟨2629717855949317500335035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3506290474599090000446713 2629717855949317500335035)
      ·
        refine ⟨3944576783923976250502553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2629717855949317500335035 3944576783923976250502553)
        ·
          refine ⟨2958432587942982187876915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3944576783923976250502553 2958432587942982187876915)
          ·
            refine ⟨4437648881914473281815373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2958432587942982187876915 4437648881914473281815373)
            ·
              refine ⟨1664118330717927480680765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4437648881914473281815373 1664118330717927480680765)
              ·
                refine ⟨624044374019222805255287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1664118330717927480680765 624044374019222805255287)
                ·
                  refine ⟨936066561028834207882931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 624044374019222805255287 936066561028834207882931)
                  ·
                    refine ⟨1404099841543251311824397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 936066561028834207882931 1404099841543251311824397)
                    ·
                      refine ⟨526537440578719241934149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1404099841543251311824397 526537440578719241934149)
                      ·
                        rfl

theorem cell23_1025428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_1025428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025428 prefixEnd_1025428 := by exact prefixLift 1025428
  have htrace : WordTrace (prefixWord ++ tailWord_1025428) baseStart_1025428 baseEnd_1025428 := by
    simpa [prefixWord, tailWord_1025428, baseEnd_1025428] using wordTrace_append hprefix tailTrace_1025428
  have hstable : (prefixWord ++ tailWord_1025428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025428).length < 2 ^ (prefixWord ++ tailWord_1025428).sum := by decide
  have hdescent : baseEnd_1025428 < baseStart_1025428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025437 : List Nat := [1, 4, 2, 1, 3, 1, 1, 3, 1, 1, 5]
def baseStart_1025437 : Nat := 118140960795 + 1025437 * 2 ^ 59
def prefixEnd_1025437 : Nat := 4983230072969 + 3 ^ 40 * 1025437 * 2
def baseEnd_1025437 : Nat := 526542061904609706721607

theorem tailTrace_1025437 : CollatzResearch.WordTrace tailWord_1025437 prefixEnd_1025437 526542061904609706721607 := by
  unfold tailWord_1025437
  simp only [CollatzResearch.WordTrace]
  refine ⟨37400759986024354541842565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24933839990682903027895043 37400759986024354541842565)
  ·
    refine ⟨7012642497379566476595481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37400759986024354541842565 7012642497379566476595481)
    ·
      refine ⟨5259481873034674857446611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7012642497379566476595481 5259481873034674857446611)
      ·
        refine ⟨7889222809552012286169917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5259481873034674857446611 7889222809552012286169917)
        ·
          refine ⟨2958458553582004607313719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7889222809552012286169917 2958458553582004607313719)
          ·
            refine ⟨4437687830373006910970579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2958458553582004607313719 4437687830373006910970579)
            ·
              refine ⟨6656531745559510366455869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4437687830373006910970579 6656531745559510366455869)
              ·
                refine ⟨2496199404584816387420951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6656531745559510366455869 2496199404584816387420951)
                ·
                  refine ⟨3744299106877224581131427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2496199404584816387420951 3744299106877224581131427)
                  ·
                    refine ⟨5616448660315836871697141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3744299106877224581131427 5616448660315836871697141)
                    ·
                      refine ⟨526542061904609706721607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5616448660315836871697141 526542061904609706721607)
                      ·
                        rfl

theorem cell23_1025437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_1025437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025437 prefixEnd_1025437 := by exact prefixLift 1025437
  have htrace : WordTrace (prefixWord ++ tailWord_1025437) baseStart_1025437 baseEnd_1025437 := by
    simpa [prefixWord, tailWord_1025437, baseEnd_1025437] using wordTrace_append hprefix tailTrace_1025437
  have hstable : (prefixWord ++ tailWord_1025437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025437).length < 2 ^ (prefixWord ++ tailWord_1025437).sum := by decide
  have hdescent : baseEnd_1025437 < baseStart_1025437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025438 : List Nat := [4, 3, 1, 2, 2, 1, 1, 2, 2, 3, 2]
def baseStart_1025438 : Nat := 118140960795 + 1025438 * 2 ^ 59
def prefixEnd_1025438 : Nat := 4983230072969 + 3 ^ 40 * 1025438 * 2
def baseEnd_1025438 : Nat := 526542575385264202809103

theorem tailTrace_1025438 : CollatzResearch.WordTrace tailWord_1025438 prefixEnd_1025438 526542575385264202809103 := by
  unfold tailWord_1025438
  simp only [CollatzResearch.WordTrace]
  refine ⟨4675099557377591464078621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24933864306013821141752645 4675099557377591464078621)
  ·
    refine ⟨1753162334016596799029483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4675099557377591464078621 1753162334016596799029483)
    ·
      refine ⟨2629743501024895198544225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1753162334016596799029483 2629743501024895198544225)
      ·
        refine ⟨1972307625768671398908169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2629743501024895198544225 1972307625768671398908169)
        ·
          refine ⟨1479230719326503549181127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1972307625768671398908169 1479230719326503549181127)
          ·
            refine ⟨2218846078989755323771691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1479230719326503549181127 2218846078989755323771691)
            ·
              refine ⟨3328269118484632985657537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2218846078989755323771691 3328269118484632985657537)
              ·
                refine ⟨2496201838863474739243153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3328269118484632985657537 2496201838863474739243153)
                ·
                  refine ⟨1872151379147606054432365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2496201838863474739243153 1872151379147606054432365)
                  ·
                    refine ⟨702056767180352270412137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1872151379147606054432365 702056767180352270412137)
                    ·
                      refine ⟨526542575385264202809103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 702056767180352270412137 526542575385264202809103)
                      ·
                        rfl

theorem cell23_1025438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_1025438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025438 prefixEnd_1025438 := by exact prefixLift 1025438
  have htrace : WordTrace (prefixWord ++ tailWord_1025438) baseStart_1025438 baseEnd_1025438 := by
    simpa [prefixWord, tailWord_1025438, baseEnd_1025438] using wordTrace_append hprefix tailTrace_1025438
  have hstable : (prefixWord ++ tailWord_1025438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025438).length < 2 ^ (prefixWord ++ tailWord_1025438).sum := by decide
  have hdescent : baseEnd_1025438 < baseStart_1025438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025461 : List Nat := [1, 3, 3, 2, 2, 1, 4, 1, 2, 4]
def baseStart_1025461 : Nat := 118140960795 + 1025461 * 2 ^ 59
def prefixEnd_1025461 : Nat := 4983230072969 + 3 ^ 40 * 1025461 * 2
def baseEnd_1025461 : Nat := 175518128480105870940499

theorem tailTrace_1025461 : CollatzResearch.WordTrace tailWord_1025461 prefixEnd_1025461 175518128480105870940499 := by
  unfold tailWord_1025461
  simp only [CollatzResearch.WordTrace]
  refine ⟨37401635337937406640716237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24934423558624937760477491 37401635337937406640716237)
  ·
    refine ⟨14025613251726527490268589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37401635337937406640716237 14025613251726527490268589)
    ·
      refine ⟨5259604969397447808850721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14025613251726527490268589 5259604969397447808850721)
      ·
        refine ⟨3944703727048085856638041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5259604969397447808850721 3944703727048085856638041)
        ·
          refine ⟨2958527795286064392478531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3944703727048085856638041 2958527795286064392478531)
          ·
            refine ⟨4437791692929096588717797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2958527795286064392478531 4437791692929096588717797)
            ·
              refine ⟨832085942424205610384587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4437791692929096588717797 832085942424205610384587)
              ·
                refine ⟨1248128913636308415576881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 832085942424205610384587 1248128913636308415576881)
                ·
                  refine ⟨936096685227231311682661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1248128913636308415576881 936096685227231311682661)
                  ·
                    refine ⟨175518128480105870940499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 936096685227231311682661 175518128480105870940499)
                    ·
                      rfl

theorem cell23_1025461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_1025461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025461 prefixEnd_1025461 := by exact prefixLift 1025461
  have htrace : WordTrace (prefixWord ++ tailWord_1025461) baseStart_1025461 baseEnd_1025461 := by
    simpa [prefixWord, tailWord_1025461, baseEnd_1025461] using wordTrace_append hprefix tailTrace_1025461
  have hstable : (prefixWord ++ tailWord_1025461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025461).length < 2 ^ (prefixWord ++ tailWord_1025461).sum := by decide
  have hdescent : baseEnd_1025461 < baseStart_1025461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025468 : List Nat := [2, 2, 2, 4, 3, 1, 1, 2, 1, 1, 4]
def baseStart_1025468 : Nat := 118140960795 + 1025468 * 2 ^ 59
def prefixEnd_1025468 : Nat := 4983230072969 + 3 ^ 40 * 1025468 * 2
def baseEnd_1025468 : Nat := 526557979804899085433965

theorem tailTrace_1025468 : CollatzResearch.WordTrace tailWord_1025468 prefixEnd_1025468 526557979804899085433965 := by
  unfold tailWord_1025468
  simp only [CollatzResearch.WordTrace]
  refine ⟨18700945324456023418110529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24934593765941364557480705 18700945324456023418110529)
  ·
    refine ⟨14025708993342017563582897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18700945324456023418110529 14025708993342017563582897)
    ·
      refine ⟨10519281745006513172687173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14025708993342017563582897 10519281745006513172687173)
      ·
        refine ⟨1972365327188721219878845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10519281745006513172687173 1972365327188721219878845)
        ·
          refine ⟨739636997695770457454567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1972365327188721219878845 739636997695770457454567)
          ·
            refine ⟨1109455496543655686181851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 739636997695770457454567 1109455496543655686181851)
            ·
              refine ⟨1664183244815483529272777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1109455496543655686181851 1664183244815483529272777)
              ·
                refine ⟨1248137433611612646954583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1664183244815483529272777 1248137433611612646954583)
                ·
                  refine ⟨1872206150417418970431875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1248137433611612646954583 1872206150417418970431875)
                  ·
                    refine ⟨2808309225626128455647813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1872206150417418970431875 2808309225626128455647813)
                    ·
                      refine ⟨526557979804899085433965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2808309225626128455647813 526557979804899085433965)
                      ·
                        rfl

theorem cell23_1025468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_1025468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025468 prefixEnd_1025468 := by exact prefixLift 1025468
  have htrace : WordTrace (prefixWord ++ tailWord_1025468) baseStart_1025468 baseEnd_1025468 := by
    simpa [prefixWord, tailWord_1025468, baseEnd_1025468] using wordTrace_append hprefix tailTrace_1025468
  have hstable : (prefixWord ++ tailWord_1025468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025468).length < 2 ^ (prefixWord ++ tailWord_1025468).sum := by decide
  have hdescent : baseEnd_1025468 < baseStart_1025468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025484 : List Nat := [2, 2, 1, 4, 2, 2, 1, 2, 1, 3, 3]
def baseStart_1025484 : Nat := 118140960795 + 1025484 * 2 ^ 59
def prefixEnd_1025484 : Nat := 4983230072969 + 3 ^ 40 * 1025484 * 2
def baseEnd_1025484 : Nat := 526566195495371022833891

theorem tailTrace_1025484 : CollatzResearch.WordTrace tailWord_1025484 prefixEnd_1025484 526566195495371022833891 := by
  unfold tailWord_1025484
  simp only [CollatzResearch.WordTrace]
  refine ⟨18701237108427040784401753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24934982811236054379202337 18701237108427040784401753)
  ·
    refine ⟨14025927831320280588301315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18701237108427040784401753 14025927831320280588301315)
    ·
      refine ⟨21038891746980420882451973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14025927831320280588301315 21038891746980420882451973)
      ·
        refine ⟨3944792202558828915459745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21038891746980420882451973 3944792202558828915459745)
        ·
          refine ⟨2958594151919121686594809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3944792202558828915459745 2958594151919121686594809)
          ·
            refine ⟨2218945613939341264946107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2958594151919121686594809 2218945613939341264946107)
            ·
              refine ⟨3328418420909011897419161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2218945613939341264946107 3328418420909011897419161)
              ·
                refine ⟨2496313815681758923064371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3328418420909011897419161 2496313815681758923064371)
                ·
                  refine ⟨3744470723522638384596557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2496313815681758923064371 3744470723522638384596557)
                  ·
                    refine ⟨1404176521320989394223709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3744470723522638384596557 1404176521320989394223709)
                    ·
                      refine ⟨526566195495371022833891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1404176521320989394223709 526566195495371022833891)
                      ·
                        rfl

theorem cell23_1025484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_1025484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025484 prefixEnd_1025484 := by exact prefixLift 1025484
  have htrace : WordTrace (prefixWord ++ tailWord_1025484) baseStart_1025484 baseEnd_1025484 := by
    simpa [prefixWord, tailWord_1025484, baseEnd_1025484] using wordTrace_append hprefix tailTrace_1025484
  have hstable : (prefixWord ++ tailWord_1025484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025484).length < 2 ^ (prefixWord ++ tailWord_1025484).sum := by decide
  have hdescent : baseEnd_1025484 < baseStart_1025484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025501 : List Nat := [1, 4, 3, 1, 1, 2, 1, 4, 2, 1, 3]
def baseStart_1025501 : Nat := 118140960795 + 1025501 * 2 ^ 59
def prefixEnd_1025501 : Nat := 4983230072969 + 3 ^ 40 * 1025501 * 2
def baseEnd_1025501 : Nat := 526574924666497456321313

theorem tailTrace_1025501 : CollatzResearch.WordTrace tailWord_1025501 prefixEnd_1025501 526574924666497456321313 := by
  unfold tailWord_1025501
  simp only [CollatzResearch.WordTrace]
  refine ⟨37403094257792493472172357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24935396171861662314781571 37403094257792493472172357)
  ·
    refine ⟨7013080173336092526032317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37403094257792493472172357 7013080173336092526032317)
    ·
      refine ⟨2629905065001034697262119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7013080173336092526032317 2629905065001034697262119)
      ·
        refine ⟨3944857597501552045893179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2629905065001034697262119 3944857597501552045893179)
        ·
          refine ⟨5917286396252328068839769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3944857597501552045893179 5917286396252328068839769)
          ·
            refine ⟨4437964797189246051629827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5917286396252328068839769 4437964797189246051629827)
            ·
              refine ⟨6656947195783869077444741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4437964797189246051629827 6656947195783869077444741)
              ·
                refine ⟨1248177599209475452020889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6656947195783869077444741 1248177599209475452020889)
                ·
                  refine ⟨936133199407106589015667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1248177599209475452020889 936133199407106589015667)
                  ·
                    refine ⟨1404199799110659883523501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 936133199407106589015667 1404199799110659883523501)
                    ·
                      refine ⟨526574924666497456321313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1404199799110659883523501 526574924666497456321313)
                      ·
                        rfl

theorem cell23_1025501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_1025501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025501 prefixEnd_1025501 := by exact prefixLift 1025501
  have htrace : WordTrace (prefixWord ++ tailWord_1025501) baseStart_1025501 baseEnd_1025501 := by
    simpa [prefixWord, tailWord_1025501, baseEnd_1025501] using wordTrace_append hprefix tailTrace_1025501
  have hstable : (prefixWord ++ tailWord_1025501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025501).length < 2 ^ (prefixWord ++ tailWord_1025501).sum := by decide
  have hdescent : baseEnd_1025501 < baseStart_1025501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025507 : List Nat := [1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 4]
def baseStart_1025507 : Nat := 118140960795 + 1025507 * 2 ^ 59
def prefixEnd_1025507 : Nat := 4983230072969 + 3 ^ 40 * 1025507 * 2
def baseEnd_1025507 : Nat := 526578005550424432846285

theorem tailTrace_1025507 : CollatzResearch.WordTrace tailWord_1025507 prefixEnd_1025507 526578005550424432846285 := by
  unfold tailWord_1025507
  simp only [CollatzResearch.WordTrace]
  refine ⟨37403313095770756496890775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24935542063847170997927183 37403313095770756496890775)
  ·
    refine ⟨56104969643656134745336163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37403313095770756496890775 56104969643656134745336163)
    ·
      refine ⟨84157454465484202118004245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56104969643656134745336163 84157454465484202118004245)
      ·
        refine ⟨3944880678069571974281449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 84157454465484202118004245 3944880678069571974281449)
        ·
          refine ⟨2958660508552178980711087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3944880678069571974281449 2958660508552178980711087)
          ·
            refine ⟨4437990762828268471066631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2958660508552178980711087 4437990762828268471066631)
            ·
              refine ⟨6656986144242402706599947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4437990762828268471066631 6656986144242402706599947)
              ·
                refine ⟨9985479216363604059899921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6656986144242402706599947 9985479216363604059899921)
                ·
                  refine ⟨7489109412272703044924941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9985479216363604059899921 7489109412272703044924941)
                  ·
                    refine ⟨2808416029602263641846853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7489109412272703044924941 2808416029602263641846853)
                    ·
                      refine ⟨526578005550424432846285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2808416029602263641846853 526578005550424432846285)
                      ·
                        rfl

theorem cell23_1025507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_1025507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025507 prefixEnd_1025507 := by exact prefixLift 1025507
  have htrace : WordTrace (prefixWord ++ tailWord_1025507) baseStart_1025507 baseEnd_1025507 := by
    simpa [prefixWord, tailWord_1025507, baseEnd_1025507] using wordTrace_append hprefix tailTrace_1025507
  have hstable : (prefixWord ++ tailWord_1025507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025507).length < 2 ^ (prefixWord ++ tailWord_1025507).sum := by decide
  have hdescent : baseEnd_1025507 < baseStart_1025507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025564 : List Nat := [2, 2, 3, 1, 2, 1, 1, 6, 5]
def baseStart_1025564 : Nat := 118140960795 + 1025564 * 2 ^ 59
def prefixEnd_1025564 : Nat := 4983230072969 + 3 ^ 40 * 1025564 * 2
def baseEnd_1025564 : Nat := 58511919327525634425947

theorem tailTrace_1025564 : CollatzResearch.WordTrace tailWord_1025564 prefixEnd_1025564 58511919327525634425947 := by
  unfold tailWord_1025564
  simp only [CollatzResearch.WordTrace]
  refine ⟨18702696028282127615857873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24936928037709503487810497 18702696028282127615857873)
  ·
    refine ⟨14027022021211595711893405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18702696028282127615857873 14027022021211595711893405)
    ·
      refine ⟨5260133257954348391960027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14027022021211595711893405 5260133257954348391960027)
      ·
        refine ⟨7890199886931522587940041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5260133257954348391960027 7890199886931522587940041)
        ·
          refine ⟨5917649915198641940955031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7890199886931522587940041 5917649915198641940955031)
          ·
            refine ⟨8876474872797962911432547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5917649915198641940955031 8876474872797962911432547)
            ·
              refine ⟨13314712309196944367148821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8876474872797962911432547 13314712309196944367148821)
              ·
                refine ⟨624127139493606767210101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13314712309196944367148821 624127139493606767210101)
                ·
                  refine ⟨58511919327525634425947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 624127139493606767210101 58511919327525634425947)
                  ·
                    rfl

theorem cell23_1025564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 6, 5].length) (baseStart_1025564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025564 prefixEnd_1025564 := by exact prefixLift 1025564
  have htrace : WordTrace (prefixWord ++ tailWord_1025564) baseStart_1025564 baseEnd_1025564 := by
    simpa [prefixWord, tailWord_1025564, baseEnd_1025564] using wordTrace_append hprefix tailTrace_1025564
  have hstable : (prefixWord ++ tailWord_1025564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025564).length < 2 ^ (prefixWord ++ tailWord_1025564).sum := by decide
  have hdescent : baseEnd_1025564 < baseStart_1025564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025714 : List Nat := [3, 2, 1, 1, 1, 2, 4, 2, 1, 6]
def baseStart_1025714 : Nat := 118140960795 + 1025714 * 2 ^ 59
def prefixEnd_1025714 : Nat := 4983230072969 + 3 ^ 40 * 1025714 * 2
def baseEnd_1025714 : Nat := 175561432015301707652611

theorem tailTrace_1025714 : CollatzResearch.WordTrace tailWord_1025714 prefixEnd_1025714 175561432015301707652611 := by
  unfold tailWord_1025714
  simp only [CollatzResearch.WordTrace]
  refine ⟨9352715751505207712419049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24940575337347220566450797 9352715751505207712419049)
  ·
    refine ⟨7014536813628905784314287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9352715751505207712419049 7014536813628905784314287)
    ·
      refine ⟨10521805220443358676471431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7014536813628905784314287 10521805220443358676471431)
      ·
        refine ⟨15782707830665038014707147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10521805220443358676471431 15782707830665038014707147)
        ·
          refine ⟨23674061745997557022060721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15782707830665038014707147 23674061745997557022060721)
          ·
            refine ⟨17755546309498167766545541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23674061745997557022060721 17755546309498167766545541)
            ·
              refine ⟨3329164933030906456227289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17755546309498167766545541 3329164933030906456227289)
              ·
                refine ⟨2496873699773179842170467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3329164933030906456227289 2496873699773179842170467)
                ·
                  refine ⟨3745310549659769763255701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2496873699773179842170467 3745310549659769763255701)
                  ·
                    refine ⟨175561432015301707652611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3745310549659769763255701 175561432015301707652611)
                    ·
                      rfl

theorem cell23_1025714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_1025714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025714 prefixEnd_1025714 := by exact prefixLift 1025714
  have htrace : WordTrace (prefixWord ++ tailWord_1025714) baseStart_1025714 baseEnd_1025714 := by
    simpa [prefixWord, tailWord_1025714, baseEnd_1025714] using wordTrace_append hprefix tailTrace_1025714
  have hstable : (prefixWord ++ tailWord_1025714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025714).length < 2 ^ (prefixWord ++ tailWord_1025714).sum := by decide
  have hdescent : baseEnd_1025714 < baseStart_1025714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025727 : List Nat := [1, 1, 2, 2, 2, 3, 12]
def baseStart_1025727 : Nat := 118140960795 + 1025727 * 2 ^ 59
def prefixEnd_1025727 : Nat := 4983230072969 + 3 ^ 40 * 1025727 * 2
def baseEnd_1025727 : Nat := 6502357670301402124633

theorem tailTrace_1025727 : CollatzResearch.WordTrace tailWord_1025727 prefixEnd_1025727 6502357670301402124633 := by
  unfold tailWord_1025727
  simp only [CollatzResearch.WordTrace]
  refine ⟨37411337154973734069899435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24940891436649156046599623 37411337154973734069899435)
  ·
    refine ⟨56117005732460601104849153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37411337154973734069899435 56117005732460601104849153)
    ·
      refine ⟨42087754299345450828636865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56117005732460601104849153 42087754299345450828636865)
      ·
        refine ⟨31565815724509088121477649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42087754299345450828636865 31565815724509088121477649)
        ·
          refine ⟨23674361793381816091108237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31565815724509088121477649 23674361793381816091108237)
          ·
            refine ⟨8877885672518181034165589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23674361793381816091108237 8877885672518181034165589)
            ·
              refine ⟨6502357670301402124633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 8877885672518181034165589 6502357670301402124633)
              ·
                rfl

theorem cell23_1025727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 12].length) (baseStart_1025727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025727 prefixEnd_1025727 := by exact prefixLift 1025727
  have htrace : WordTrace (prefixWord ++ tailWord_1025727) baseStart_1025727 baseEnd_1025727 := by
    simpa [prefixWord, tailWord_1025727, baseEnd_1025727] using wordTrace_append hprefix tailTrace_1025727
  have hstable : (prefixWord ++ tailWord_1025727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025727).length < 2 ^ (prefixWord ++ tailWord_1025727).sum := by decide
  have hdescent : baseEnd_1025727 < baseStart_1025727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025747 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 8]
def baseStart_1025747 : Nat := 118140960795 + 1025747 * 2 ^ 59
def prefixEnd_1025747 : Nat := 4983230072969 + 3 ^ 40 * 1025747 * 2
def baseEnd_1025747 : Nat := 526701240907503493845181

theorem tailTrace_1025747 : CollatzResearch.WordTrace tailWord_1025747 prefixEnd_1025747 526701240907503493845181 := by
  unfold tailWord_1025747
  simp only [CollatzResearch.WordTrace]
  refine ⟨37412066614901277485627495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24941377743267518323751663 37412066614901277485627495)
  ·
    refine ⟨56118099922351916228441243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37412066614901277485627495 56118099922351916228441243)
    ·
      refine ⟨84177149883527874342661865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56118099922351916228441243 84177149883527874342661865)
      ·
        refine ⟨63132862412645905756996399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84177149883527874342661865 63132862412645905756996399)
        ·
          refine ⟨94699293618968858635494599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63132862412645905756996399 94699293618968858635494599)
          ·
            refine ⟨142048940428453287953241899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94699293618968858635494599 142048940428453287953241899)
            ·
              refine ⟨213073410642679931929862849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142048940428453287953241899 213073410642679931929862849)
              ·
                refine ⟨159805057982009948947397137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213073410642679931929862849 159805057982009948947397137)
                ·
                  refine ⟨119853793486507461710547853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159805057982009948947397137 119853793486507461710547853)
                  ·
                    refine ⟨44945172557440298141455445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119853793486507461710547853 44945172557440298141455445)
                    ·
                      refine ⟨526701240907503493845181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 44945172557440298141455445 526701240907503493845181)
                      ·
                        rfl

theorem cell23_1025747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 8].length) (baseStart_1025747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025747 prefixEnd_1025747 := by exact prefixLift 1025747
  have htrace : WordTrace (prefixWord ++ tailWord_1025747) baseStart_1025747 baseEnd_1025747 := by
    simpa [prefixWord, tailWord_1025747, baseEnd_1025747] using wordTrace_append hprefix tailTrace_1025747
  have hstable : (prefixWord ++ tailWord_1025747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025747).length < 2 ^ (prefixWord ++ tailWord_1025747).sum := by decide
  have hdescent : baseEnd_1025747 < baseStart_1025747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025748 : List Nat := [2, 4, 1, 3, 1, 3, 1, 1, 1, 6]
def baseStart_1025748 : Nat := 118140960795 + 1025748 * 2 ^ 59
def prefixEnd_1025748 : Nat := 4983230072969 + 3 ^ 40 * 1025748 * 2
def baseEnd_1025748 : Nat := 175567251462719329977559

theorem tailTrace_1025748 : CollatzResearch.WordTrace tailWord_1025748 prefixEnd_1025748 175567251462719329977559 := by
  unfold tailWord_1025748
  simp only [CollatzResearch.WordTrace]
  refine ⟨18706051543948827328206949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24941402058598436437609265 18706051543948827328206949)
  ·
    refine ⟨3507384664490405124038803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18706051543948827328206949 3507384664490405124038803)
    ·
      refine ⟨5261076996735607686058205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3507384664490405124038803 5261076996735607686058205)
      ·
        refine ⟨1972903873775852882271827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5261076996735607686058205 1972903873775852882271827)
        ·
          refine ⟨2959355810663779323407741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1972903873775852882271827 2959355810663779323407741)
          ·
            refine ⟨1109758428998917246277903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2959355810663779323407741 1109758428998917246277903)
            ·
              refine ⟨1664637643498375869416855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1109758428998917246277903 1664637643498375869416855)
              ·
                refine ⟨2496956465247563804125283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1664637643498375869416855 2496956465247563804125283)
                ·
                  refine ⟨3745434697871345706187925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2496956465247563804125283 3745434697871345706187925)
                  ·
                    refine ⟨175567251462719329977559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3745434697871345706187925 175567251462719329977559)
                    ·
                      rfl

theorem cell23_1025748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_1025748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025748 prefixEnd_1025748 := by exact prefixLift 1025748
  have htrace : WordTrace (prefixWord ++ tailWord_1025748) baseStart_1025748 baseEnd_1025748 := by
    simpa [prefixWord, tailWord_1025748, baseEnd_1025748] using wordTrace_append hprefix tailTrace_1025748
  have hstable : (prefixWord ++ tailWord_1025748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025748).length < 2 ^ (prefixWord ++ tailWord_1025748).sum := by decide
  have hdescent : baseEnd_1025748 < baseStart_1025748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025771 : List Nat := [1, 1, 1, 1, 2, 4, 3, 2, 4, 1, 3]
def baseStart_1025771 : Nat := 118140960795 + 1025771 * 2 ^ 59
def prefixEnd_1025771 : Nat := 4983230072969 + 3 ^ 40 * 1025771 * 2
def baseEnd_1025771 : Nat := 526713564443211399945071

theorem tailTrace_1025771 : CollatzResearch.WordTrace tailWord_1025771 prefixEnd_1025771 526713564443211399945071 := by
  unfold tailWord_1025771
  simp only [CollatzResearch.WordTrace]
  refine ⟨37412941966814329584501167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24941961311209553056334111 37412941966814329584501167)
  ·
    refine ⟨56119412950221494376751751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37412941966814329584501167 56119412950221494376751751)
    ·
      refine ⟨84179119425332241565127627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56119412950221494376751751 84179119425332241565127627)
      ·
        refine ⟨126268679137998362347691441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84179119425332241565127627 126268679137998362347691441)
        ·
          refine ⟨94701509353498771760768581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126268679137998362347691441 94701509353498771760768581)
          ·
            refine ⟨17756533003781019705144109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94701509353498771760768581 17756533003781019705144109)
            ·
              refine ⟨6658699876417882389429041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17756533003781019705144109 6658699876417882389429041)
              ·
                refine ⟨4994024907313411792071781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6658699876417882389429041 4994024907313411792071781)
                ·
                  refine ⟨936379670121264711013459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4994024907313411792071781 936379670121264711013459)
                  ·
                    refine ⟨1404569505181897066520189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 936379670121264711013459 1404569505181897066520189)
                    ·
                      refine ⟨526713564443211399945071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1404569505181897066520189 526713564443211399945071)
                      ·
                        rfl

theorem cell23_1025771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 4, 1, 3].length) (baseStart_1025771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025771 prefixEnd_1025771 := by exact prefixLift 1025771
  have htrace : WordTrace (prefixWord ++ tailWord_1025771) baseStart_1025771 baseEnd_1025771 := by
    simpa [prefixWord, tailWord_1025771, baseEnd_1025771] using wordTrace_append hprefix tailTrace_1025771
  have hstable : (prefixWord ++ tailWord_1025771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025771).length < 2 ^ (prefixWord ++ tailWord_1025771).sum := by decide
  have hdescent : baseEnd_1025771 < baseStart_1025771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025788 : List Nat := [2, 2, 2, 1, 3, 1, 2, 4, 2, 1, 3]
def baseStart_1025788 : Nat := 118140960795 + 1025788 * 2 ^ 59
def prefixEnd_1025788 : Nat := 4983230072969 + 3 ^ 40 * 1025788 * 2
def baseEnd_1025788 : Nat := 526722293614337833432493

theorem tailTrace_1025788 : CollatzResearch.WordTrace tailWord_1025788 prefixEnd_1025788 526722293614337833432493 := by
  unfold tailWord_1025788
  simp only [CollatzResearch.WordTrace]
  refine ⟨18706781003876370743935009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24942374671835160991913345 18706781003876370743935009)
  ·
    refine ⟨14030085752907278057951257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18706781003876370743935009 14030085752907278057951257)
    ·
      refine ⟨10522564314680458543463443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14030085752907278057951257 10522564314680458543463443)
      ·
        refine ⟨15783846472020687815195165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10522564314680458543463443 15783846472020687815195165)
        ·
          refine ⟨5918942427007757930698187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15783846472020687815195165 5918942427007757930698187)
          ·
            refine ⟨8878413640511636896047281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5918942427007757930698187 8878413640511636896047281)
            ·
              refine ⟨6658810230383727672035461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8878413640511636896047281 6658810230383727672035461)
              ·
                refine ⟨1248526918196948938506649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6658810230383727672035461 1248526918196948938506649)
                ·
                  refine ⟨936395188647711703879987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1248526918196948938506649 936395188647711703879987)
                  ·
                    refine ⟨1404592782971567555819981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 936395188647711703879987 1404592782971567555819981)
                    ·
                      refine ⟨526722293614337833432493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1404592782971567555819981 526722293614337833432493)
                      ·
                        rfl

theorem cell23_1025788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 2, 1, 3].length) (baseStart_1025788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025788 prefixEnd_1025788 := by exact prefixLift 1025788
  have htrace : WordTrace (prefixWord ++ tailWord_1025788) baseStart_1025788 baseEnd_1025788 := by
    simpa [prefixWord, tailWord_1025788, baseEnd_1025788] using wordTrace_append hprefix tailTrace_1025788
  have hstable : (prefixWord ++ tailWord_1025788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025788).length < 2 ^ (prefixWord ++ tailWord_1025788).sum := by decide
  have hdescent : baseEnd_1025788 < baseStart_1025788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025804 : List Nat := [2, 2, 1, 2, 2, 1, 2, 3, 2, 6]
def baseStart_1025804 : Nat := 118140960795 + 1025804 * 2 ^ 59
def prefixEnd_1025804 : Nat := 4983230072969 + 3 ^ 40 * 1025804 * 2
def baseEnd_1025804 : Nat := 175576836434936590277473

theorem tailTrace_1025804 : CollatzResearch.WordTrace tailWord_1025804 prefixEnd_1025804 175576836434936590277473 := by
  unfold tailWord_1025804
  simp only [CollatzResearch.WordTrace]
  refine ⟨18707072787847388110226233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24942763717129850813634977 18707072787847388110226233)
  ·
    refine ⟨14030304590885541082669675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18707072787847388110226233 14030304590885541082669675)
    ·
      refine ⟨21045456886328311624004513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14030304590885541082669675 21045456886328311624004513)
      ·
        refine ⟨15784092664746233718003385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21045456886328311624004513 15784092664746233718003385)
        ·
          refine ⟨11838069498559675288502539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15784092664746233718003385 11838069498559675288502539)
          ·
            refine ⟨17757104247839512932753809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11838069498559675288502539 17757104247839512932753809)
            ·
              refine ⟨13317828185879634699565357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17757104247839512932753809 13317828185879634699565357)
              ·
                refine ⟨4994185569704863012337009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13317828185879634699565357 4994185569704863012337009)
                ·
                  refine ⟨3745639177278647259252757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4994185569704863012337009 3745639177278647259252757)
                  ·
                    refine ⟨175576836434936590277473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3745639177278647259252757 175576836434936590277473)
                    ·
                      rfl

theorem cell23_1025804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 2, 6].length) (baseStart_1025804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025804 prefixEnd_1025804 := by exact prefixLift 1025804
  have htrace : WordTrace (prefixWord ++ tailWord_1025804) baseStart_1025804 baseEnd_1025804 := by
    simpa [prefixWord, tailWord_1025804, baseEnd_1025804] using wordTrace_append hprefix tailTrace_1025804
  have hstable : (prefixWord ++ tailWord_1025804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025804).length < 2 ^ (prefixWord ++ tailWord_1025804).sum := by decide
  have hdescent : baseEnd_1025804 < baseStart_1025804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025815 : List Nat := [1, 1, 3, 4, 2, 1, 3, 2, 1, 3, 2]
def baseStart_1025815 : Nat := 118140960795 + 1025815 * 2 ^ 59
def prefixEnd_1025815 : Nat := 4983230072969 + 3 ^ 40 * 1025815 * 2
def baseEnd_1025815 : Nat := 526736157592009227794869

theorem tailTrace_1025815 : CollatzResearch.WordTrace tailWord_1025815 prefixEnd_1025815 526736157592009227794869 := by
  unfold tailWord_1025815
  simp only [CollatzResearch.WordTrace]
  refine ⟨37414546778654925099102899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24943031185769950066068599 37414546778654925099102899)
  ·
    refine ⟨56121820167982387648654349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37414546778654925099102899 56121820167982387648654349)
    ·
      refine ⟨21045682562993395368245381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56121820167982387648654349 21045682562993395368245381)
      ·
        refine ⟨3946065480561261631546009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21045682562993395368245381 3946065480561261631546009)
        ·
          refine ⟨2959549110420946223659507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3946065480561261631546009 2959549110420946223659507)
          ·
            refine ⟨4439323665631419335489261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2959549110420946223659507 4439323665631419335489261)
            ·
              refine ⟨1664746374611782250808473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4439323665631419335489261 1664746374611782250808473)
              ·
                refine ⟨1248559780958836688106355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1664746374611782250808473 1248559780958836688106355)
                ·
                  refine ⟨1872839671438255032159533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1248559780958836688106355 1872839671438255032159533)
                  ·
                    refine ⟨702314876789345637059825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1872839671438255032159533 702314876789345637059825)
                    ·
                      refine ⟨526736157592009227794869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 702314876789345637059825 526736157592009227794869)
                      ·
                        rfl

theorem cell23_1025815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_1025815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025815 prefixEnd_1025815 := by exact prefixLift 1025815
  have htrace : WordTrace (prefixWord ++ tailWord_1025815) baseStart_1025815 baseEnd_1025815 := by
    simpa [prefixWord, tailWord_1025815, baseEnd_1025815] using wordTrace_append hprefix tailTrace_1025815
  have hstable : (prefixWord ++ tailWord_1025815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025815).length < 2 ^ (prefixWord ++ tailWord_1025815).sum := by decide
  have hdescent : baseEnd_1025815 < baseStart_1025815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025822 : List Nat := [4, 3, 2, 2, 1, 1, 1, 2, 1, 3, 3]
def baseStart_1025822 : Nat := 118140960795 + 1025822 * 2 ^ 59
def prefixEnd_1025822 : Nat := 4983230072969 + 3 ^ 40 * 1025822 * 2
def baseEnd_1025822 : Nat := 526739751956590700407337

theorem tailTrace_1025822 : CollatzResearch.WordTrace tailWord_1025822 prefixEnd_1025822 526739751956590700407337 := by
  unfold tailWord_1025822
  simp only [CollatzResearch.WordTrace]
  refine ⟨4676850261203695661825965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24943201393086376863071813 4676850261203695661825965)
  ·
    refine ⟨1753818847951385873184737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4676850261203695661825965 1753818847951385873184737)
    ·
      refine ⟨1315364135963539404888553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1753818847951385873184737 1315364135963539404888553)
      ·
        refine ⟨986523101972654553666415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1315364135963539404888553 986523101972654553666415)
        ·
          refine ⟨1479784652958981830499623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 986523101972654553666415 1479784652958981830499623)
          ·
            refine ⟨2219676979438472745749435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1479784652958981830499623 2219676979438472745749435)
            ·
              refine ⟨3329515469157709118624153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2219676979438472745749435 3329515469157709118624153)
              ·
                refine ⟨2497136601868281838968115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3329515469157709118624153 2497136601868281838968115)
                ·
                  refine ⟨3745704902802422758452173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2497136601868281838968115 3745704902802422758452173)
                  ·
                    refine ⟨1404639338550908534419565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3745704902802422758452173 1404639338550908534419565)
                    ·
                      refine ⟨526739751956590700407337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1404639338550908534419565 526739751956590700407337)
                      ·
                        rfl

theorem cell23_1025822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_1025822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025822 prefixEnd_1025822 := by exact prefixLift 1025822
  have htrace : WordTrace (prefixWord ++ tailWord_1025822) baseStart_1025822 baseEnd_1025822 := by
    simpa [prefixWord, tailWord_1025822, baseEnd_1025822] using wordTrace_append hprefix tailTrace_1025822
  have hstable : (prefixWord ++ tailWord_1025822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025822).length < 2 ^ (prefixWord ++ tailWord_1025822).sum := by decide
  have hdescent : baseEnd_1025822 < baseStart_1025822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025828 : List Nat := [2, 3, 1, 3, 2, 1, 1, 1, 3, 4, 2]
def baseStart_1025828 : Nat := 118140960795 + 1025828 * 2 ^ 59
def prefixEnd_1025828 : Nat := 4983230072969 + 3 ^ 40 * 1025828 * 2
def baseEnd_1025828 : Nat := 526742832840517676932309

theorem tailTrace_1025828 : CollatzResearch.WordTrace tailWord_1025828 prefixEnd_1025828 526742832840517676932309 := by
  unfold tailWord_1025828
  simp only [CollatzResearch.WordTrace]
  refine ⟨18707510463803914159663069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24943347285071885546217425 18707510463803914159663069)
  ·
    refine ⟨7015316423926467809873651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18707510463803914159663069 7015316423926467809873651)
    ·
      refine ⟨10522974635889701714810477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7015316423926467809873651 10522974635889701714810477)
      ·
        refine ⟨3946115488458638143053929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10522974635889701714810477 3946115488458638143053929)
        ·
          refine ⟨2959586616343978607290447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3946115488458638143053929 2959586616343978607290447)
          ·
            refine ⟨4439379924515967910935671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2959586616343978607290447 4439379924515967910935671)
            ·
              refine ⟨6659069886773951866403507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4439379924515967910935671 6659069886773951866403507)
              ·
                refine ⟨9988604830160927799605261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6659069886773951866403507 9988604830160927799605261)
                ·
                  refine ⟨3745726811310347924851973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9988604830160927799605261 3745726811310347924851973)
                  ·
                    refine ⟨702323777120690235909745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3745726811310347924851973 702323777120690235909745)
                    ·
                      refine ⟨526742832840517676932309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 702323777120690235909745 526742832840517676932309)
                      ·
                        rfl

theorem cell23_1025828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_1025828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025828 prefixEnd_1025828 := by exact prefixLift 1025828
  have htrace : WordTrace (prefixWord ++ tailWord_1025828) baseStart_1025828 baseEnd_1025828 := by
    simpa [prefixWord, tailWord_1025828, baseEnd_1025828] using wordTrace_append hprefix tailTrace_1025828
  have hstable : (prefixWord ++ tailWord_1025828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025828).length < 2 ^ (prefixWord ++ tailWord_1025828).sum := by decide
  have hdescent : baseEnd_1025828 < baseStart_1025828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025832 : List Nat := [2, 1, 5, 1, 1, 3, 3, 1, 1, 3, 2]
def baseStart_1025832 : Nat := 118140960795 + 1025832 * 2 ^ 59
def prefixEnd_1025832 : Nat := 4983230072969 + 3 ^ 40 * 1025832 * 2
def baseEnd_1025832 : Nat := 526744886763135661282291

theorem tailTrace_1025832 : CollatzResearch.WordTrace tailWord_1025832 prefixEnd_1025832 526744886763135661282291 := by
  unfold tailWord_1025832
  simp only [CollatzResearch.WordTrace]
  refine ⟨18707583409796668501235875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24943444546395558001647833 18707583409796668501235875)
  ·
    refine ⟨28061375114695002751853813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18707583409796668501235875 28061375114695002751853813)
    ·
      refine ⟨2630753917002656507986295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28061375114695002751853813 2630753917002656507986295)
      ·
        refine ⟨3946130875503984761979443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2630753917002656507986295 3946130875503984761979443)
        ·
          refine ⟨5919196313255977142969165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3946130875503984761979443 5919196313255977142969165)
          ·
            refine ⟨2219698617470991428613437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5919196313255977142969165 2219698617470991428613437)
            ·
              refine ⟨832386981551621785730039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2219698617470991428613437 832386981551621785730039)
              ·
                refine ⟨1248580472327432678595059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 832386981551621785730039 1248580472327432678595059)
                ·
                  refine ⟨1872870708491149017892589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1248580472327432678595059 1872870708491149017892589)
                  ·
                    refine ⟨702326515684180881709721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1872870708491149017892589 702326515684180881709721)
                    ·
                      refine ⟨526744886763135661282291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 702326515684180881709721 526744886763135661282291)
                      ·
                        rfl

theorem cell23_1025832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_1025832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025832 prefixEnd_1025832 := by exact prefixLift 1025832
  have htrace : WordTrace (prefixWord ++ tailWord_1025832) baseStart_1025832 baseEnd_1025832 := by
    simpa [prefixWord, tailWord_1025832, baseEnd_1025832] using wordTrace_append hprefix tailTrace_1025832
  have hstable : (prefixWord ++ tailWord_1025832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025832).length < 2 ^ (prefixWord ++ tailWord_1025832).sum := by decide
  have hdescent : baseEnd_1025832 < baseStart_1025832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025861 : List Nat := [1, 3, 1, 1, 1, 2, 5, 1, 2, 3, 3]
def baseStart_1025861 : Nat := 118140960795 + 1025861 * 2 ^ 59
def prefixEnd_1025861 : Nat := 4983230072969 + 3 ^ 40 * 1025861 * 2
def baseEnd_1025861 : Nat := 526759777702116047819657

theorem tailTrace_1025861 : CollatzResearch.WordTrace tailWord_1025861 prefixEnd_1025861 526759777702116047819657 := by
  unfold tailWord_1025861
  simp only [CollatzResearch.WordTrace]
  refine ⟨37416224536488274955277437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24944149690992183303518291 37416224536488274955277437)
  ·
    refine ⟨14031084201183103108229039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37416224536488274955277437 14031084201183103108229039)
    ·
      refine ⟨21046626301774654662343559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14031084201183103108229039 21046626301774654662343559)
      ·
        refine ⟨31569939452661981993515339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21046626301774654662343559 31569939452661981993515339)
        ·
          refine ⟨47354909178992972990273009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31569939452661981993515339 47354909178992972990273009)
          ·
            refine ⟨35516181884244729742704757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47354909178992972990273009 35516181884244729742704757)
            ·
              refine ⟨3329642051647943413378571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35516181884244729742704757 3329642051647943413378571)
              ·
                refine ⟨4994463077471915120067857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3329642051647943413378571 4994463077471915120067857)
                ·
                  refine ⟨3745847308103936340050893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4994463077471915120067857 3745847308103936340050893)
                  ·
                    refine ⟨1404692740538976127519085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3745847308103936340050893 1404692740538976127519085)
                    ·
                      refine ⟨526759777702116047819657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1404692740538976127519085 526759777702116047819657)
                      ·
                        rfl

theorem cell23_1025861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 3, 3].length) (baseStart_1025861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025861 prefixEnd_1025861 := by exact prefixLift 1025861
  have htrace : WordTrace (prefixWord ++ tailWord_1025861) baseStart_1025861 baseEnd_1025861 := by
    simpa [prefixWord, tailWord_1025861, baseEnd_1025861] using wordTrace_append hprefix tailTrace_1025861
  have hstable : (prefixWord ++ tailWord_1025861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025861).length < 2 ^ (prefixWord ++ tailWord_1025861).sum := by decide
  have hdescent : baseEnd_1025861 < baseStart_1025861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025862 : List Nat := [6, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2]
def baseStart_1025862 : Nat := 118140960795 + 1025862 * 2 ^ 59
def prefixEnd_1025862 : Nat := 4983230072969 + 3 ^ 40 * 1025862 * 2
def baseEnd_1025862 : Nat := 526760291182770543907153

theorem tailTrace_1025862 : CollatzResearch.WordTrace tailWord_1025862 prefixEnd_1025862 526760291182770543907153 := by
  unfold tailWord_1025862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1169258156546395378939495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24944174006323101417375893 1169258156546395378939495)
  ·
    refine ⟨1753887234819593068409243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1169258156546395378939495 1753887234819593068409243)
    ·
      refine ⟨2630830852229389602613865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1753887234819593068409243 2630830852229389602613865)
      ·
        refine ⟨1973123139172042201960399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2630830852229389602613865 1973123139172042201960399)
        ·
          refine ⟨2959684708758063302940599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1973123139172042201960399 2959684708758063302940599)
          ·
            refine ⟨4439527063137094954410899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2959684708758063302940599 4439527063137094954410899)
            ·
              refine ⟨6659290594705642431616349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4439527063137094954410899 6659290594705642431616349)
              ·
                refine ⟨2497233973014615911856131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6659290594705642431616349 2497233973014615911856131)
                ·
                  refine ⟨3745850959521923867784197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2497233973014615911856131 3745850959521923867784197)
                  ·
                    refine ⟨702347054910360725209537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3745850959521923867784197 702347054910360725209537)
                    ·
                      refine ⟨526760291182770543907153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 702347054910360725209537 526760291182770543907153)
                      ·
                        rfl

theorem cell23_1025862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_1025862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025862 prefixEnd_1025862 := by exact prefixLift 1025862
  have htrace : WordTrace (prefixWord ++ tailWord_1025862) baseStart_1025862 baseEnd_1025862 := by
    simpa [prefixWord, tailWord_1025862, baseEnd_1025862] using wordTrace_append hprefix tailTrace_1025862
  have hstable : (prefixWord ++ tailWord_1025862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025862).length < 2 ^ (prefixWord ++ tailWord_1025862).sum := by decide
  have hdescent : baseEnd_1025862 < baseStart_1025862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025945 : List Nat := [1, 2, 1, 2, 1, 3, 5, 3, 1, 4]
def baseStart_1025945 : Nat := 118140960795 + 1025945 * 2 ^ 59
def prefixEnd_1025945 : Nat := 4983230072969 + 3 ^ 40 * 1025945 * 2
def baseEnd_1025945 : Nat := 175600970025697906389757

theorem tailTrace_1025945 : CollatzResearch.WordTrace tailWord_1025945 prefixEnd_1025945 175600970025697906389757 := by
  unfold tailWord_1025945
  simp only [CollatzResearch.WordTrace]
  refine ⟨37419288268183957301335289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24946192178789304867556859 37419288268183957301335289)
  ·
    refine ⟨28064466201137967976001467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37419288268183957301335289 28064466201137967976001467)
    ·
      refine ⟨42096699301706951964002201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28064466201137967976001467 42096699301706951964002201)
      ·
        refine ⟨31572524476280213973001651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42096699301706951964002201 31572524476280213973001651)
        ·
          refine ⟨47358786714420320959502477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31572524476280213973001651 47358786714420320959502477)
          ·
            refine ⟨17759545017907620359813429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47358786714420320959502477 17759545017907620359813429)
            ·
              refine ⟨1664957345428839408732509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17759545017907620359813429 1664957345428839408732509)
              ·
                refine ⟨624359004535814778274691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1664957345428839408732509 624359004535814778274691)
                ·
                  refine ⟨936538506803722167412037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 624359004535814778274691 936538506803722167412037)
                  ·
                    refine ⟨175600970025697906389757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 936538506803722167412037 175600970025697906389757)
                    ·
                      rfl

theorem cell23_1025945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 3, 1, 4].length) (baseStart_1025945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025945 prefixEnd_1025945 := by exact prefixLift 1025945
  have htrace : WordTrace (prefixWord ++ tailWord_1025945) baseStart_1025945 baseEnd_1025945 := by
    simpa [prefixWord, tailWord_1025945, baseEnd_1025945] using wordTrace_append hprefix tailTrace_1025945
  have hstable : (prefixWord ++ tailWord_1025945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025945).length < 2 ^ (prefixWord ++ tailWord_1025945).sum := by decide
  have hdescent : baseEnd_1025945 < baseStart_1025945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025971 : List Nat := [1, 1, 1, 2, 3, 1, 4, 2, 3, 5]
def baseStart_1025971 : Nat := 118140960795 + 1025971 * 2 ^ 59
def prefixEnd_1025971 : Nat := 4983230072969 + 3 ^ 40 * 1025971 * 2
def baseEnd_1025971 : Nat := 175605420191370205814717

theorem tailTrace_1025971 : CollatzResearch.WordTrace tailWord_1025971 prefixEnd_1025971 175605420191370205814717 := by
  unfold tailWord_1025971
  simp only [CollatzResearch.WordTrace]
  refine ⟨37420236566089763741781767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24946824377393175827854511 37420236566089763741781767)
  ·
    refine ⟨56130354849134645612672651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37420236566089763741781767 56130354849134645612672651)
    ·
      refine ⟨84195532273701968419008977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56130354849134645612672651 84195532273701968419008977)
      ·
        refine ⟨63146649205276476314256733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84195532273701968419008977 63146649205276476314256733)
        ·
          refine ⟨23679993451978678617846275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63146649205276476314256733 23679993451978678617846275)
          ·
            refine ⟨35519990177968017926769413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23679993451978678617846275 35519990177968017926769413)
            ·
              refine ⟨6659998158369003361269265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35519990177968017926769413 6659998158369003361269265)
              ·
                refine ⟨4994998618776752520951949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6659998158369003361269265 4994998618776752520951949)
                ·
                  refine ⟨1873124482041282195356981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4994998618776752520951949 1873124482041282195356981)
                  ·
                    refine ⟨175605420191370205814717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1873124482041282195356981 175605420191370205814717)
                    ·
                      rfl

theorem cell23_1025971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 5].length) (baseStart_1025971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025971 prefixEnd_1025971 := by exact prefixLift 1025971
  have htrace : WordTrace (prefixWord ++ tailWord_1025971) baseStart_1025971 baseEnd_1025971 := by
    simpa [prefixWord, tailWord_1025971, baseEnd_1025971] using wordTrace_append hprefix tailTrace_1025971
  have hstable : (prefixWord ++ tailWord_1025971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025971).length < 2 ^ (prefixWord ++ tailWord_1025971).sum := by decide
  have hdescent : baseEnd_1025971 < baseStart_1025971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025978 : List Nat := [3, 1, 1, 1, 2, 1, 2, 4, 1, 5, 2]
def baseStart_1025978 : Nat := 118140960795 + 1025978 * 2 ^ 59
def prefixEnd_1025978 : Nat := 4983230072969 + 3 ^ 40 * 1025978 * 2
def baseEnd_1025978 : Nat := 526819854938692090056619

theorem tailTrace_1025978 : CollatzResearch.WordTrace tailWord_1025978 prefixEnd_1025978 526819854938692090056619 := by
  unfold tailWord_1025978
  simp only [CollatzResearch.WordTrace]
  refine ⟨9355122969266100984321647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24946994584709602624857725 9355122969266100984321647)
  ·
    refine ⟨14032684453899151476482471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9355122969266100984321647 14032684453899151476482471)
    ·
      refine ⟨21049026680848727214723707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14032684453899151476482471 21049026680848727214723707)
      ·
        refine ⟨31573540021273090822085561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21049026680848727214723707 31573540021273090822085561)
        ·
          refine ⟨23680155015954818116564171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31573540021273090822085561 23680155015954818116564171)
          ·
            refine ⟨35520232523932227174846257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23680155015954818116564171 35520232523932227174846257)
            ·
              refine ⟨26640174392949170381134693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35520232523932227174846257 26640174392949170381134693)
              ·
                refine ⟨4995032698677969446462755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26640174392949170381134693 4995032698677969446462755)
                ·
                  refine ⟨7492549048016954169694133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4995032698677969446462755 7492549048016954169694133)
                  ·
                    refine ⟨702426473251589453408825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7492549048016954169694133 702426473251589453408825)
                    ·
                      refine ⟨526819854938692090056619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 702426473251589453408825 526819854938692090056619)
                      ·
                        rfl

theorem cell23_1025978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 1, 5, 2].length) (baseStart_1025978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025978 prefixEnd_1025978 := by exact prefixLift 1025978
  have htrace : WordTrace (prefixWord ++ tailWord_1025978) baseStart_1025978 baseEnd_1025978 := by
    simpa [prefixWord, tailWord_1025978, baseEnd_1025978] using wordTrace_append hprefix tailTrace_1025978
  have hstable : (prefixWord ++ tailWord_1025978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025978).length < 2 ^ (prefixWord ++ tailWord_1025978).sum := by decide
  have hdescent : baseEnd_1025978 < baseStart_1025978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025995 : List Nat := [1, 1, 1, 1, 3, 4, 4, 1, 2, 3, 2]
def baseStart_1025995 : Nat := 118140960795 + 1025995 * 2 ^ 59
def prefixEnd_1025995 : Nat := 4983230072969 + 3 ^ 40 * 1025995 * 2
def baseEnd_1025995 : Nat := 526828584109818523544041

theorem tailTrace_1025995 : CollatzResearch.WordTrace tailWord_1025995 prefixEnd_1025995 526828584109818523544041 := by
  unfold tailWord_1025995
  simp only [CollatzResearch.WordTrace]
  refine ⟨37421111918002815840655439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24947407945335210560436959 37421111918002815840655439)
  ·
    refine ⟨56131667877004223760983159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37421111918002815840655439 56131667877004223760983159)
    ·
      refine ⟨84197501815506335641474739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56131667877004223760983159 84197501815506335641474739)
      ·
        refine ⟨126296252723259503462212109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84197501815506335641474739 126296252723259503462212109)
        ·
          refine ⟨47361094771222313798329541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126296252723259503462212109 47361094771222313798329541)
          ·
            refine ⟨8880205269604183837186789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47361094771222313798329541 8880205269604183837186789)
            ·
              refine ⟨1665038488050784469472523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8880205269604183837186789 1665038488050784469472523)
              ·
                refine ⟨2497557732076176704208785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1665038488050784469472523 2497557732076176704208785)
                ·
                  refine ⟨1873168299057132528156589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2497557732076176704208785 1873168299057132528156589)
                  ·
                    refine ⟨702438112146424698058721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1873168299057132528156589 702438112146424698058721)
                    ·
                      refine ⟨526828584109818523544041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 702438112146424698058721 526828584109818523544041)
                      ·
                        rfl

theorem cell23_1025995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 3, 2].length) (baseStart_1025995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1025995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1025995 prefixEnd_1025995 := by exact prefixLift 1025995
  have htrace : WordTrace (prefixWord ++ tailWord_1025995) baseStart_1025995 baseEnd_1025995 := by
    simpa [prefixWord, tailWord_1025995, baseEnd_1025995] using wordTrace_append hprefix tailTrace_1025995
  have hstable : (prefixWord ++ tailWord_1025995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025995).length < 2 ^ (prefixWord ++ tailWord_1025995).sum := by decide
  have hdescent : baseEnd_1025995 < baseStart_1025995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026019 : List Nat := [1, 1, 1, 6, 1, 2, 4, 2, 1, 1, 3]
def baseStart_1026019 : Nat := 118140960795 + 1026019 * 2 ^ 59
def prefixEnd_1026019 : Nat := 4983230072969 + 3 ^ 40 * 1026019 * 2
def baseEnd_1026019 : Nat := 526840907645526429643931

theorem tailTrace_1026019 : CollatzResearch.WordTrace tailWord_1026019 prefixEnd_1026019 526840907645526429643931 := by
  unfold tailWord_1026019
  simp only [CollatzResearch.WordTrace]
  refine ⟨37421987269915867939529111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24947991513277245293019407 37421987269915867939529111)
  ·
    refine ⟨56132980904873801909293667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37421987269915867939529111 56132980904873801909293667)
    ·
      refine ⟨84199471357310702863940501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56132980904873801909293667 84199471357310702863940501)
      ·
        refine ⟨3946850219873939196747211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 84199471357310702863940501 3946850219873939196747211)
        ·
          refine ⟨5920275329810908795120817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3946850219873939196747211 5920275329810908795120817)
          ·
            refine ⟨4440206497358181596340613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5920275329810908795120817 4440206497358181596340613)
            ·
              refine ⟨832538718254659049313865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4440206497358181596340613 832538718254659049313865)
              ·
                refine ⟨624404038690994286985399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 832538718254659049313865 624404038690994286985399)
                ·
                  refine ⟨936606058036491430478099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 624404038690994286985399 936606058036491430478099)
                  ·
                    refine ⟨1404909087054737145717149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 936606058036491430478099 1404909087054737145717149)
                    ·
                      refine ⟨526840907645526429643931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1404909087054737145717149 526840907645526429643931)
                      ·
                        rfl

theorem cell23_1026019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_1026019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026019 prefixEnd_1026019 := by exact prefixLift 1026019
  have htrace : WordTrace (prefixWord ++ tailWord_1026019) baseStart_1026019 baseEnd_1026019 := by
    simpa [prefixWord, tailWord_1026019, baseEnd_1026019] using wordTrace_append hprefix tailTrace_1026019
  have hstable : (prefixWord ++ tailWord_1026019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026019).length < 2 ^ (prefixWord ++ tailWord_1026019).sum := by decide
  have hdescent : baseEnd_1026019 < baseStart_1026019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026059 : List Nat := [1, 1, 1, 1, 6, 1, 4, 3, 1, 2, 2]
def baseStart_1026059 : Nat := 118140960795 + 1026059 * 2 ^ 59
def prefixEnd_1026059 : Nat := 4983230072969 + 3 ^ 40 * 1026059 * 2
def baseEnd_1026059 : Nat := 526861446871706273143747

theorem tailTrace_1026059 : CollatzResearch.WordTrace tailWord_1026059 prefixEnd_1026059 526861446871706273143747 := by
  unfold tailWord_1026059
  simp only [CollatzResearch.WordTrace]
  refine ⟨37423446189770954770985231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24948964126513969847323487 37423446189770954770985231)
  ·
    refine ⟨56135169284656432156477847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37423446189770954770985231 56135169284656432156477847)
    ·
      refine ⟨84202753926984648234716771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56135169284656432156477847 84202753926984648234716771)
      ·
        refine ⟨126304130890476972352075157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84202753926984648234716771 126304130890476972352075157)
        ·
          refine ⟨5920506135491108079003523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 126304130890476972352075157 5920506135491108079003523)
          ·
            refine ⟨8880759203236662118505285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5920506135491108079003523 8880759203236662118505285)
            ·
              refine ⟨1665142350606874147219741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8880759203236662118505285 1665142350606874147219741)
              ·
                refine ⟨624428381477577805207403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1665142350606874147219741 624428381477577805207403)
                ·
                  refine ⟨936642572216366707811105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 624428381477577805207403 936642572216366707811105)
                  ·
                    refine ⟨702481929162275030858329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 936642572216366707811105 702481929162275030858329)
                    ·
                      refine ⟨526861446871706273143747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 702481929162275030858329 526861446871706273143747)
                      ·
                        rfl

theorem cell23_1026059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 3, 1, 2, 2].length) (baseStart_1026059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026059 prefixEnd_1026059 := by exact prefixLift 1026059
  have htrace : WordTrace (prefixWord ++ tailWord_1026059) baseStart_1026059 baseEnd_1026059 := by
    simpa [prefixWord, tailWord_1026059, baseEnd_1026059] using wordTrace_append hprefix tailTrace_1026059
  have hstable : (prefixWord ++ tailWord_1026059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026059).length < 2 ^ (prefixWord ++ tailWord_1026059).sum := by decide
  have hdescent : baseEnd_1026059 < baseStart_1026059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026069 : List Nat := [1, 3, 2, 1, 6, 1, 1, 2, 2, 4]
def baseStart_1026069 : Nat := 118140960795 + 1026069 * 2 ^ 59
def prefixEnd_1026069 : Nat := 4983230072969 + 3 ^ 40 * 1026069 * 2
def baseEnd_1026069 : Nat := 175622193892750411339567

theorem tailTrace_1026069 : CollatzResearch.WordTrace tailWord_1026069 prefixEnd_1026069 175622193892750411339567 := by
  unfold tailWord_1026069
  simp only [CollatzResearch.WordTrace]
  refine ⟨37423810919734726478849261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24949207279823150985899507 37423810919734726478849261)
  ·
    refine ⟨14033929094900522429568473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37423810919734726478849261 14033929094900522429568473)
    ·
      refine ⟨10525446821175391822176355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14033929094900522429568473 10525446821175391822176355)
      ·
        refine ⟨15788170231763087733264533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10525446821175391822176355 15788170231763087733264533)
        ·
          refine ⟨740070479613894737496775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15788170231763087733264533 740070479613894737496775)
          ·
            refine ⟨1110105719420842106245163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740070479613894737496775 1110105719420842106245163)
            ·
              refine ⟨1665158579131263159367745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1110105719420842106245163 1665158579131263159367745)
              ·
                refine ⟨1248868934348447369525809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1665158579131263159367745 1248868934348447369525809)
                ·
                  refine ⟨936651700761335527144357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1248868934348447369525809 936651700761335527144357)
                  ·
                    refine ⟨175622193892750411339567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 936651700761335527144357 175622193892750411339567)
                    ·
                      rfl

theorem cell23_1026069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 2, 4].length) (baseStart_1026069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026069 prefixEnd_1026069 := by exact prefixLift 1026069
  have htrace : WordTrace (prefixWord ++ tailWord_1026069) baseStart_1026069 baseEnd_1026069 := by
    simpa [prefixWord, tailWord_1026069, baseEnd_1026069] using wordTrace_append hprefix tailTrace_1026069
  have hstable : (prefixWord ++ tailWord_1026069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026069).length < 2 ^ (prefixWord ++ tailWord_1026069).sum := by decide
  have hdescent : baseEnd_1026069 < baseStart_1026069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026075 : List Nat := [1, 1, 1, 1, 1, 1, 3, 8, 2, 1, 3]
def baseStart_1026075 : Nat := 118140960795 + 1026075 * 2 ^ 59
def prefixEnd_1026075 : Nat := 4983230072969 + 3 ^ 40 * 1026075 * 2
def baseEnd_1026075 : Nat := 526869662562178210543673

theorem tailTrace_1026075 : CollatzResearch.WordTrace tailWord_1026075 prefixEnd_1026075 526869662562178210543673 := by
  unfold tailWord_1026075
  simp only [CollatzResearch.WordTrace]
  refine ⟨37424029757712989503567679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24949353171808659669045119 37424029757712989503567679)
  ·
    refine ⟨56136044636569484255351519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37424029757712989503567679 56136044636569484255351519)
    ·
      refine ⟨84204066954854226383027279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56136044636569484255351519 84204066954854226383027279)
      ·
        refine ⟨126306100432281339574540919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84204066954854226383027279 126306100432281339574540919)
        ·
          refine ⟨189459150648422009361811379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126306100432281339574540919 189459150648422009361811379)
          ·
            refine ⟨284188725972633014042717069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189459150648422009361811379 284188725972633014042717069)
            ·
              refine ⟨106570772239737380266018901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 284188725972633014042717069 106570772239737380266018901)
              ·
                refine ⟨1248876237184422424992409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 106570772239737380266018901 1248876237184422424992409)
                ·
                  refine ⟨936657177888316818744307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1248876237184422424992409 936657177888316818744307)
                  ·
                    refine ⟨1404985766832475228116461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 936657177888316818744307 1404985766832475228116461)
                    ·
                      refine ⟨526869662562178210543673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1404985766832475228116461 526869662562178210543673)
                      ·
                        rfl

theorem cell23_1026075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 2, 1, 3].length) (baseStart_1026075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026075 prefixEnd_1026075 := by exact prefixLift 1026075
  have htrace : WordTrace (prefixWord ++ tailWord_1026075) baseStart_1026075 baseEnd_1026075 := by
    simpa [prefixWord, tailWord_1026075, baseEnd_1026075] using wordTrace_append hprefix tailTrace_1026075
  have hstable : (prefixWord ++ tailWord_1026075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026075).length < 2 ^ (prefixWord ++ tailWord_1026075).sum := by decide
  have hdescent : baseEnd_1026075 < baseStart_1026075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026091 : List Nat := [1, 1, 1, 1, 2, 1, 4, 3, 1, 8]
def baseStart_1026091 : Nat := 118140960795 + 1026091 * 2 ^ 59
def prefixEnd_1026091 : Nat := 4983230072969 + 3 ^ 40 * 1026091 * 2
def baseEnd_1026091 : Nat := 175625959417550049314533

theorem tailTrace_1026091 : CollatzResearch.WordTrace tailWord_1026091 prefixEnd_1026091 175625959417550049314533 := by
  unfold tailWord_1026091
  simp only [CollatzResearch.WordTrace]
  refine ⟨37424613325655024236150127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24949742217103349490766751 37424613325655024236150127)
  ·
    refine ⟨56136919988482536354225191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37424613325655024236150127 56136919988482536354225191)
    ·
      refine ⟨84205379982723804531337787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56136919988482536354225191 84205379982723804531337787)
      ·
        refine ⟨126308069974085706797006681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84205379982723804531337787 126308069974085706797006681)
        ·
          refine ⟨94731052480564280097755011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126308069974085706797006681 94731052480564280097755011)
          ·
            refine ⟨142096578720846420146632517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94731052480564280097755011 142096578720846420146632517)
            ·
              refine ⟨26643108510158703777493597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142096578720846420146632517 26643108510158703777493597)
              ·
                refine ⟨9991165691309513916560099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26643108510158703777493597 9991165691309513916560099)
                ·
                  refine ⟨14986748536964270874840149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9991165691309513916560099 14986748536964270874840149)
                  ·
                    refine ⟨175625959417550049314533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14986748536964270874840149 175625959417550049314533)
                    ·
                      rfl

theorem cell23_1026091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 8].length) (baseStart_1026091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026091 prefixEnd_1026091 := by exact prefixLift 1026091
  have htrace : WordTrace (prefixWord ++ tailWord_1026091) baseStart_1026091 baseEnd_1026091 := by
    simpa [prefixWord, tailWord_1026091, baseEnd_1026091] using wordTrace_append hprefix tailTrace_1026091
  have hstable : (prefixWord ++ tailWord_1026091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026091).length < 2 ^ (prefixWord ++ tailWord_1026091).sum := by decide
  have hdescent : baseEnd_1026091 < baseStart_1026091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026110 : List Nat := [4, 2, 1, 3, 3, 1, 1, 3, 1, 2, 2]
def baseStart_1026110 : Nat := 118140960795 + 1026110 * 2 ^ 59
def prefixEnd_1026110 : Nat := 4983230072969 + 3 ^ 40 * 1026110 * 2
def baseEnd_1026110 : Nat := 526887634385085573606013

theorem tailTrace_1026110 : CollatzResearch.WordTrace tailWord_1026110 prefixEnd_1026110 526887634385085573606013 := by
  unfold tailWord_1026110
  simp only [CollatzResearch.WordTrace]
  refine ⟨4678163289073273810136473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24950204208390793654061189 4678163289073273810136473)
  ·
    refine ⟨3508622466804955357602355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4678163289073273810136473 3508622466804955357602355)
    ·
      refine ⟨5262933700207433036403533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3508622466804955357602355 5262933700207433036403533)
      ·
        refine ⟨1973600137577787388651325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5262933700207433036403533 1973600137577787388651325)
        ·
          refine ⟨740100051591670270744247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1973600137577787388651325 740100051591670270744247)
          ·
            refine ⟨1110150077387505406116371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740100051591670270744247 1110150077387505406116371)
            ·
              refine ⟨1665225116081258109174557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1110150077387505406116371 1665225116081258109174557)
              ·
                refine ⟨624459418530471790940459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1665225116081258109174557 624459418530471790940459)
                ·
                  refine ⟨936689127795707686410689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 624459418530471790940459 936689127795707686410689)
                  ·
                    refine ⟨702516845846780764808017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 936689127795707686410689 702516845846780764808017)
                    ·
                      refine ⟨526887634385085573606013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 702516845846780764808017 526887634385085573606013)
                      ·
                        rfl

theorem cell23_1026110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_1026110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026110 prefixEnd_1026110 := by exact prefixLift 1026110
  have htrace : WordTrace (prefixWord ++ tailWord_1026110) baseStart_1026110 baseEnd_1026110 := by
    simpa [prefixWord, tailWord_1026110, baseEnd_1026110] using wordTrace_append hprefix tailTrace_1026110
  have hstable : (prefixWord ++ tailWord_1026110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026110).length < 2 ^ (prefixWord ++ tailWord_1026110).sum := by decide
  have hdescent : baseEnd_1026110 < baseStart_1026110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026149 : List Nat := [1, 3, 1, 3, 2, 3, 1, 3, 2, 2, 2]
def baseStart_1026149 : Nat := 118140960795 + 1026149 * 2 ^ 59
def prefixEnd_1026149 : Nat := 4983230072969 + 3 ^ 40 * 1026149 * 2
def baseEnd_1026149 : Nat := 526907660130610921018333

theorem tailTrace_1026149 : CollatzResearch.WordTrace tailWord_1026149 prefixEnd_1026149 526907660130610921018333 := by
  unfold tailWord_1026149
  simp only [CollatzResearch.WordTrace]
  refine ⟨37426728759444900141761501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24951152506296600094507667 37426728759444900141761501)
  ·
    refine ⟨14035023284791837553160563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37426728759444900141761501 14035023284791837553160563)
    ·
      refine ⟨21052534927187756329740845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14035023284791837553160563 21052534927187756329740845)
      ·
        refine ⟨7894700597695408623652817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21052534927187756329740845 7894700597695408623652817)
        ·
          refine ⟨5921025448271556467739613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7894700597695408623652817 5921025448271556467739613)
          ·
            refine ⟨2220384543101833675402355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5921025448271556467739613 2220384543101833675402355)
            ·
              refine ⟨3330576814652750513103533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2220384543101833675402355 3330576814652750513103533)
              ·
                refine ⟨1248966305494781442413825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3330576814652750513103533 1248966305494781442413825)
                ·
                  refine ⟨936724729121086081810369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1248966305494781442413825 936724729121086081810369)
                  ·
                    refine ⟨702543546840814561357777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 936724729121086081810369 702543546840814561357777)
                    ·
                      refine ⟨526907660130610921018333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 702543546840814561357777 526907660130610921018333)
                      ·
                        rfl

theorem cell23_1026149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_1026149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026149 prefixEnd_1026149 := by exact prefixLift 1026149
  have htrace : WordTrace (prefixWord ++ tailWord_1026149) baseStart_1026149 baseEnd_1026149 := by
    simpa [prefixWord, tailWord_1026149, baseEnd_1026149] using wordTrace_append hprefix tailTrace_1026149
  have hstable : (prefixWord ++ tailWord_1026149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026149).length < 2 ^ (prefixWord ++ tailWord_1026149).sum := by decide
  have hdescent : baseEnd_1026149 < baseStart_1026149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026188 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 5, 3, 4]
def baseStart_1026188 : Nat := 118140960795 + 1026188 * 2 ^ 59
def prefixEnd_1026188 : Nat := 4983230072969 + 3 ^ 40 * 1026188 * 2
def baseEnd_1026188 : Nat := 526927685876136268430653

theorem tailTrace_1026188 : CollatzResearch.WordTrace tailWord_1026188 prefixEnd_1026188 526927685876136268430653 := by
  unfold tailWord_1026188
  simp only [CollatzResearch.WordTrace]
  refine ⟨18714075603151804901215609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24952100804202406534954145 18714075603151804901215609)
  ·
    refine ⟨14035556702363853675911707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18714075603151804901215609 14035556702363853675911707)
    ·
      refine ⟨21053335053545780513867561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14035556702363853675911707 21053335053545780513867561)
      ·
        refine ⟨15790001290159335385400671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21053335053545780513867561 15790001290159335385400671)
        ·
          refine ⟨23685001935239003078101007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15790001290159335385400671 23685001935239003078101007)
          ·
            refine ⟨35527502902858504617151511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23685001935239003078101007 35527502902858504617151511)
            ·
              refine ⟨53291254354287756925727267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35527502902858504617151511 53291254354287756925727267)
              ·
                refine ⟨79936881531431635388590901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53291254354287756925727267 79936881531431635388590901)
                ·
                  refine ⟨7494082643571715817680397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79936881531431635388590901 7494082643571715817680397)
                  ·
                    refine ⟨2810280991339393431630149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7494082643571715817680397 2810280991339393431630149)
                    ·
                      refine ⟨526927685876136268430653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2810280991339393431630149 526927685876136268430653)
                      ·
                        rfl

theorem cell23_1026188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_1026188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026188 prefixEnd_1026188 := by exact prefixLift 1026188
  have htrace : WordTrace (prefixWord ++ tailWord_1026188) baseStart_1026188 baseEnd_1026188 := by
    simpa [prefixWord, tailWord_1026188, baseEnd_1026188] using wordTrace_append hprefix tailTrace_1026188
  have hstable : (prefixWord ++ tailWord_1026188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026188).length < 2 ^ (prefixWord ++ tailWord_1026188).sum := by decide
  have hdescent : baseEnd_1026188 < baseStart_1026188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026245 : List Nat := [1, 3, 1, 1, 1, 1, 7, 2, 6]
def baseStart_1026245 : Nat := 118140960795 + 1026245 * 2 ^ 59
def prefixEnd_1026245 : Nat := 4983230072969 + 3 ^ 40 * 1026245 * 2
def baseEnd_1026245 : Nat := 58550772697049171713099

theorem tailTrace_1026245 : CollatzResearch.WordTrace tailWord_1026245 prefixEnd_1026245 58550772697049171713099 := by
  unfold tailWord_1026245
  simp only [CollatzResearch.WordTrace]
  refine ⟨37430230167097108537256189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24953486778064739024837459 37430230167097108537256189)
  ·
    refine ⟨14036336312661415701471071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37430230167097108537256189 14036336312661415701471071)
    ·
      refine ⟨21054504468992123552206607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14036336312661415701471071 21054504468992123552206607)
      ·
        refine ⟨31581756703488185328309911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21054504468992123552206607 31581756703488185328309911)
        ·
          refine ⟨47372635055232277992464867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31581756703488185328309911 47372635055232277992464867)
          ·
            refine ⟨71058952582848416988697301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47372635055232277992464867 71058952582848416988697301)
            ·
              refine ⟨1665444201160509773172593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 71058952582848416988697301 1665444201160509773172593)
              ·
                refine ⟨1249083150870382329879445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1665444201160509773172593 1249083150870382329879445)
                ·
                  refine ⟨58550772697049171713099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1249083150870382329879445 58550772697049171713099)
                  ·
                    rfl

theorem cell23_1026245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 6].length) (baseStart_1026245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026245 prefixEnd_1026245 := by exact prefixLift 1026245
  have htrace : WordTrace (prefixWord ++ tailWord_1026245) baseStart_1026245 baseEnd_1026245 := by
    simpa [prefixWord, tailWord_1026245, baseEnd_1026245] using wordTrace_append hprefix tailTrace_1026245
  have hstable : (prefixWord ++ tailWord_1026245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026245).length < 2 ^ (prefixWord ++ tailWord_1026245).sum := by decide
  have hdescent : baseEnd_1026245 < baseStart_1026245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026272 : List Nat := [2, 1, 1, 3, 1, 3, 1, 4, 3, 1, 3]
def baseStart_1026272 : Nat := 118140960795 + 1026272 * 2 ^ 59
def prefixEnd_1026272 : Nat := 4983230072969 + 3 ^ 40 * 1026272 * 2
def baseEnd_1026272 : Nat := 526970818251113939780267

theorem tailTrace_1026272 : CollatzResearch.WordTrace tailWord_1026272 prefixEnd_1026272 526970818251113939780267 := by
  unfold tailWord_1026272
  simp only [CollatzResearch.WordTrace]
  refine ⟨18715607468999646074244535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24954143291999528098992713 18715607468999646074244535)
  ·
    refine ⟨28073411203499469111366803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18715607468999646074244535 28073411203499469111366803)
    ·
      refine ⟨42110116805249203667050205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28073411203499469111366803 42110116805249203667050205)
      ·
        refine ⟨15791293801968451375143827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42110116805249203667050205 15791293801968451375143827)
        ·
          refine ⟨23686940702952677062715741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15791293801968451375143827 23686940702952677062715741)
          ·
            refine ⟨8882602763607253898518403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23686940702952677062715741 8882602763607253898518403)
            ·
              refine ⟨13323904145410880847777605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8882602763607253898518403 13323904145410880847777605)
              ·
                refine ⟨2498232027264540158958301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13323904145410880847777605 2498232027264540158958301)
                ·
                  refine ⟨936837010224202559609363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2498232027264540158958301 936837010224202559609363)
                  ·
                    refine ⟨1405255515336303839414045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 936837010224202559609363 1405255515336303839414045)
                    ·
                      refine ⟨526970818251113939780267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1405255515336303839414045 526970818251113939780267)
                      ·
                        rfl

theorem cell23_1026272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 3, 1, 3].length) (baseStart_1026272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026272 prefixEnd_1026272 := by exact prefixLift 1026272
  have htrace : WordTrace (prefixWord ++ tailWord_1026272) baseStart_1026272 baseEnd_1026272 := by
    simpa [prefixWord, tailWord_1026272, baseEnd_1026272] using wordTrace_append hprefix tailTrace_1026272
  have hstable : (prefixWord ++ tailWord_1026272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026272).length < 2 ^ (prefixWord ++ tailWord_1026272).sum := by decide
  have hdescent : baseEnd_1026272 < baseStart_1026272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026282 : List Nat := [3, 1, 3, 1, 1, 2, 1, 3, 1, 5, 2]
def baseStart_1026282 : Nat := 118140960795 + 1026282 * 2 ^ 59
def prefixEnd_1026282 : Nat := 4983230072969 + 3 ^ 40 * 1026282 * 2
def baseEnd_1026282 : Nat := 526975953057658900655221

theorem tailTrace_1026282 : CollatzResearch.WordTrace tailWord_1026282 prefixEnd_1026282 526975953057658900655221 := by
  unfold tailWord_1026282
  simp only [CollatzResearch.WordTrace]
  refine ⟨9357894916990765964088275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24954386445308709237568733 9357894916990765964088275)
  ·
    refine ⟨14036842375486148946132413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9357894916990765964088275 14036842375486148946132413)
    ·
      refine ⟨5263815890807305854799655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14036842375486148946132413 5263815890807305854799655)
      ·
        refine ⟨7895723836210958782199483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5263815890807305854799655 7895723836210958782199483)
        ·
          refine ⟨11843585754316438173299225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7895723836210958782199483 11843585754316438173299225)
          ·
            refine ⟨8882689315737328629974419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11843585754316438173299225 8882689315737328629974419)
            ·
              refine ⟨13324033973605992944961629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8882689315737328629974419 13324033973605992944961629)
              ·
                refine ⟨4996512740102247354360611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13324033973605992944961629 4996512740102247354360611)
                ·
                  refine ⟨7494769110153371031540917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4996512740102247354360611 7494769110153371031540917)
                  ·
                    refine ⟨702634604076878534206961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7494769110153371031540917 702634604076878534206961)
                    ·
                      refine ⟨526975953057658900655221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 702634604076878534206961 526975953057658900655221)
                      ·
                        rfl

theorem cell23_1026282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_1026282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026282 prefixEnd_1026282 := by exact prefixLift 1026282
  have htrace : WordTrace (prefixWord ++ tailWord_1026282) baseStart_1026282 baseEnd_1026282 := by
    simpa [prefixWord, tailWord_1026282, baseEnd_1026282] using wordTrace_append hprefix tailTrace_1026282
  have hstable : (prefixWord ++ tailWord_1026282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026282).length < 2 ^ (prefixWord ++ tailWord_1026282).sum := by decide
  have hdescent : baseEnd_1026282 < baseStart_1026282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026306 : List Nat := [3, 4, 1, 1, 2, 1, 3, 1, 3, 1, 3]
def baseStart_1026306 : Nat := 118140960795 + 1026306 * 2 ^ 59
def prefixEnd_1026306 : Nat := 4983230072969 + 3 ^ 40 * 1026306 * 2
def baseEnd_1026306 : Nat := 526988276593366806755111

theorem tailTrace_1026306 : CollatzResearch.WordTrace tailWord_1026306 prefixEnd_1026306 526988276593366806755111 := by
  unfold tailWord_1026306
  simp only [CollatzResearch.WordTrace]
  refine ⟨9358113754969028988806693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24954970013250743970151181 9358113754969028988806693)
  ·
    refine ⟨1754646329056692935401255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9358113754969028988806693 1754646329056692935401255)
    ·
      refine ⟨2631969493585039403101883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1754646329056692935401255 2631969493585039403101883)
      ·
        refine ⟨3947954240377559104652825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2631969493585039403101883 3947954240377559104652825)
        ·
          refine ⟨2960965680283169328489619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3947954240377559104652825 2960965680283169328489619)
          ·
            refine ⟨4441448520424753992734429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2960965680283169328489619 4441448520424753992734429)
            ·
              refine ⟨1665543195159282747275411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4441448520424753992734429 1665543195159282747275411)
              ·
                refine ⟨2498314792738924120913117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1665543195159282747275411 2498314792738924120913117)
                ·
                  refine ⟨936868047277096545342419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2498314792738924120913117 936868047277096545342419)
                  ·
                    refine ⟨1405302070915644818013629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 936868047277096545342419 1405302070915644818013629)
                    ·
                      refine ⟨526988276593366806755111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1405302070915644818013629 526988276593366806755111)
                      ·
                        rfl

theorem cell23_1026306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_1026306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026306 prefixEnd_1026306 := by exact prefixLift 1026306
  have htrace : WordTrace (prefixWord ++ tailWord_1026306) baseStart_1026306 baseEnd_1026306 := by
    simpa [prefixWord, tailWord_1026306, baseEnd_1026306] using wordTrace_append hprefix tailTrace_1026306
  have hstable : (prefixWord ++ tailWord_1026306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026306).length < 2 ^ (prefixWord ++ tailWord_1026306).sum := by decide
  have hdescent : baseEnd_1026306 < baseStart_1026306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026315 : List Nat := [1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 5]
def baseStart_1026315 : Nat := 118140960795 + 1026315 * 2 ^ 59
def prefixEnd_1026315 : Nat := 4983230072969 + 3 ^ 40 * 1026315 * 2
def baseEnd_1026315 : Nat := 526992897919257271542569

theorem tailTrace_1026315 : CollatzResearch.WordTrace tailWord_1026315 prefixEnd_1026315 526992897919257271542569 := by
  unfold tailWord_1026315
  simp only [CollatzResearch.WordTrace]
  refine ⟨37432783276843510492304399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24955188851229006994869599 37432783276843510492304399)
  ·
    refine ⟨56149174915265265738456599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37432783276843510492304399 56149174915265265738456599)
    ·
      refine ⟨84223762372897898607684899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56149174915265265738456599 84223762372897898607684899)
      ·
        refine ⟨126335643559346847911527349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84223762372897898607684899 126335643559346847911527349)
        ·
          refine ⟨11843966583688766991705689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126335643559346847911527349 11843966583688766991705689)
          ·
            refine ⟨8882974937766575243779267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11843966583688766991705689 8882974937766575243779267)
            ·
              refine ⟨13324462406649862865668901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8882974937766575243779267 13324462406649862865668901)
              ·
                refine ⟨2498336701246849287312919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13324462406649862865668901 2498336701246849287312919)
                ·
                  refine ⟨3747505051870273930969379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2498336701246849287312919 3747505051870273930969379)
                  ·
                    refine ⟨5621257577805410896454069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3747505051870273930969379 5621257577805410896454069)
                    ·
                      refine ⟨526992897919257271542569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5621257577805410896454069 526992897919257271542569)
                      ·
                        rfl

theorem cell23_1026315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 5].length) (baseStart_1026315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026315 prefixEnd_1026315 := by exact prefixLift 1026315
  have htrace : WordTrace (prefixWord ++ tailWord_1026315) baseStart_1026315 baseEnd_1026315 := by
    simpa [prefixWord, tailWord_1026315, baseEnd_1026315] using wordTrace_append hprefix tailTrace_1026315
  have hstable : (prefixWord ++ tailWord_1026315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026315).length < 2 ^ (prefixWord ++ tailWord_1026315).sum := by decide
  have hdescent : baseEnd_1026315 < baseStart_1026315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026325 : List Nat := [1, 3, 2, 1, 2, 1, 4, 1, 1, 1, 6]
def baseStart_1026325 : Nat := 118140960795 + 1026325 * 2 ^ 59
def prefixEnd_1026325 : Nat := 4983230072969 + 3 ^ 40 * 1026325 * 2
def baseEnd_1026325 : Nat := 526998032725802232417523

theorem tailTrace_1026325 : CollatzResearch.WordTrace tailWord_1026325 prefixEnd_1026325 526998032725802232417523 := by
  unfold tailWord_1026325
  simp only [CollatzResearch.WordTrace]
  refine ⟨37433148006807282200168429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24955432004538188133445619 37433148006807282200168429)
  ·
    refine ⟨14037430502552730825063161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37433148006807282200168429 14037430502552730825063161)
    ·
      refine ⟨10528072876914548118797371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14037430502552730825063161 10528072876914548118797371)
      ·
        refine ⟨15792109315371822178196057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10528072876914548118797371 15792109315371822178196057)
        ·
          refine ⟨11844081986528866633647043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15792109315371822178196057 11844081986528866633647043)
          ·
            refine ⟨17766122979793299950470565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11844081986528866633647043 17766122979793299950470565)
            ·
              refine ⟨3331148058711243740713231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17766122979793299950470565 3331148058711243740713231)
              ·
                refine ⟨4996722088066865611069847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3331148058711243740713231 4996722088066865611069847)
                ·
                  refine ⟨7495083132100298416604771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4996722088066865611069847 7495083132100298416604771)
                  ·
                    refine ⟨11242624698150447624907157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7495083132100298416604771 11242624698150447624907157)
                    ·
                      refine ⟨526998032725802232417523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11242624698150447624907157 526998032725802232417523)
                      ·
                        rfl

theorem cell23_1026325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_1026325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026325 prefixEnd_1026325 := by exact prefixLift 1026325
  have htrace : WordTrace (prefixWord ++ tailWord_1026325) baseStart_1026325 baseEnd_1026325 := by
    simpa [prefixWord, tailWord_1026325, baseEnd_1026325] using wordTrace_append hprefix tailTrace_1026325
  have hstable : (prefixWord ++ tailWord_1026325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026325).length < 2 ^ (prefixWord ++ tailWord_1026325).sum := by decide
  have hdescent : baseEnd_1026325 < baseStart_1026325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026335 : List Nat := [1, 1, 2, 4, 3, 1, 2, 9]
def baseStart_1026335 : Nat := 118140960795 + 1026335 * 2 ^ 59
def prefixEnd_1026335 : Nat := 4983230072969 + 3 ^ 40 * 1026335 * 2
def baseEnd_1026335 : Nat := 19518635834531377529351

theorem tailTrace_1026335 : CollatzResearch.WordTrace tailWord_1026335 prefixEnd_1026335 19518635834531377529351 := by
  unfold tailWord_1026335
  simp only [CollatzResearch.WordTrace]
  refine ⟨37433512736771053908032459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24955675157847369272021639 37433512736771053908032459)
  ·
    refine ⟨56150269105156580862048689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37433512736771053908032459 56150269105156580862048689)
    ·
      refine ⟨42112701828867435646536517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56150269105156580862048689 42112701828867435646536517)
      ·
        refine ⟨7896131592912644183725597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42112701828867435646536517 7896131592912644183725597)
        ·
          refine ⟨2961049347342241568897099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7896131592912644183725597 2961049347342241568897099)
          ·
            refine ⟨4441574021013362353345649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2961049347342241568897099 4441574021013362353345649)
            ·
              refine ⟨3331180515760021765009237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4441574021013362353345649 3331180515760021765009237)
              ·
                refine ⟨19518635834531377529351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3331180515760021765009237 19518635834531377529351)
                ·
                  rfl

theorem cell23_1026335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 9].length) (baseStart_1026335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026335 prefixEnd_1026335 := by exact prefixLift 1026335
  have htrace : WordTrace (prefixWord ++ tailWord_1026335) baseStart_1026335 baseEnd_1026335 := by
    simpa [prefixWord, tailWord_1026335, baseEnd_1026335] using wordTrace_append hprefix tailTrace_1026335
  have hstable : (prefixWord ++ tailWord_1026335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026335).length < 2 ^ (prefixWord ++ tailWord_1026335).sum := by decide
  have hdescent : baseEnd_1026335 < baseStart_1026335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026356 : List Nat := [2, 5, 1, 1, 1, 3, 2, 2, 2, 4]
def baseStart_1026356 : Nat := 118140960795 + 1026356 * 2 ^ 59
def prefixEnd_1026356 : Nat := 4983230072969 + 3 ^ 40 * 1026356 * 2
def baseEnd_1026356 : Nat := 175671316875363870376627

theorem tailTrace_1026356 : CollatzResearch.WordTrace tailWord_1026356 prefixEnd_1026356 175671316875363870376627 := by
  unfold tailWord_1026356
  simp only [CollatzResearch.WordTrace]
  refine ⟨18717139334847487247273461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24956185779796649663031281 18717139334847487247273461)
  ·
    refine ⟨1754731812641951929431887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18717139334847487247273461 1754731812641951929431887)
    ·
      refine ⟨2632097718962927894147831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1754731812641951929431887 2632097718962927894147831)
      ·
        refine ⟨3948146578444391841221747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2632097718962927894147831 3948146578444391841221747)
        ·
          refine ⟨5922219867666587761832621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3948146578444391841221747 5922219867666587761832621)
          ·
            refine ⟨2220832450374970410687233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5922219867666587761832621 2220832450374970410687233)
            ·
              refine ⟨1665624337781227808015425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2220832450374970410687233 1665624337781227808015425)
              ·
                refine ⟨1249218253335920856011569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1665624337781227808015425 1249218253335920856011569)
                ·
                  refine ⟨936913690001940642008677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1249218253335920856011569 936913690001940642008677)
                  ·
                    refine ⟨175671316875363870376627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 936913690001940642008677 175671316875363870376627)
                    ·
                      rfl

theorem cell23_1026356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_1026356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026356 prefixEnd_1026356 := by exact prefixLift 1026356
  have htrace : WordTrace (prefixWord ++ tailWord_1026356) baseStart_1026356 baseEnd_1026356 := by
    simpa [prefixWord, tailWord_1026356, baseEnd_1026356] using wordTrace_append hprefix tailTrace_1026356
  have hstable : (prefixWord ++ tailWord_1026356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026356).length < 2 ^ (prefixWord ++ tailWord_1026356).sum := by decide
  have hdescent : baseEnd_1026356 < baseStart_1026356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026369 : List Nat := [1, 2, 5, 2, 2, 2, 1, 8]
def baseStart_1026369 : Nat := 118140960795 + 1026369 * 2 ^ 59
def prefixEnd_1026369 : Nat := 4983230072969 + 3 ^ 40 * 1026369 * 2
def baseEnd_1026369 : Nat := 19519282439800002232123

theorem tailTrace_1026369 : CollatzResearch.WordTrace tailWord_1026369 prefixEnd_1026369 19519282439800002232123 := by
  unfold tailWord_1026369
  simp only [CollatzResearch.WordTrace]
  refine ⟨37434752818647877714770161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24956501879098585143180107 37434752818647877714770161)
  ·
    refine ⟨28076064613985908286077621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37434752818647877714770161 28076064613985908286077621)
    ·
      refine ⟨2632131057561178901819777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28076064613985908286077621 2632131057561178901819777)
      ·
        refine ⟨1974098293170884176364833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2632131057561178901819777 1974098293170884176364833)
        ·
          refine ⟨1480573719878163132273625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1974098293170884176364833 1480573719878163132273625)
          ·
            refine ⟨1110430289908622349205219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1480573719878163132273625 1110430289908622349205219)
            ·
              refine ⟨1665645434862933523807829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1110430289908622349205219 1665645434862933523807829)
              ·
                refine ⟨19519282439800002232123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1665645434862933523807829 19519282439800002232123)
                ·
                  rfl

theorem cell23_1026369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 8].length) (baseStart_1026369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026369 prefixEnd_1026369 := by exact prefixLift 1026369
  have htrace : WordTrace (prefixWord ++ tailWord_1026369) baseStart_1026369 baseEnd_1026369 := by
    simpa [prefixWord, tailWord_1026369, baseEnd_1026369] using wordTrace_append hprefix tailTrace_1026369
  have hstable : (prefixWord ++ tailWord_1026369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026369).length < 2 ^ (prefixWord ++ tailWord_1026369).sum := by decide
  have hdescent : baseEnd_1026369 < baseStart_1026369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026419 : List Nat := [1, 1, 1, 2, 2, 1, 2, 5, 4, 2, 2]
def baseStart_1026419 : Nat := 118140960795 + 1026419 * 2 ^ 59
def prefixEnd_1026419 : Nat := 4983230072969 + 3 ^ 40 * 1026419 * 2
def baseEnd_1026419 : Nat := 527046299907324864642091

theorem tailTrace_1026419 : CollatzResearch.WordTrace tailWord_1026419 prefixEnd_1026419 527046299907324864642091 := by
  unfold tailWord_1026419
  simp only [CollatzResearch.WordTrace]
  refine ⟨37436576468466736254090311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24957717645644490836060207 37436576468466736254090311)
  ·
    refine ⟨56154864702700104381135467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37436576468466736254090311 56154864702700104381135467)
    ·
      refine ⟨84232297054050156571703201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56154864702700104381135467 84232297054050156571703201)
      ·
        refine ⟨63174222790537617428777401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84232297054050156571703201 63174222790537617428777401)
        ·
          refine ⟨47380667092903213071583051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63174222790537617428777401 47380667092903213071583051)
          ·
            refine ⟨71071000639354819607374577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47380667092903213071583051 71071000639354819607374577)
            ·
              refine ⟨53303250479516114705530933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71071000639354819607374577 53303250479516114705530933)
              ·
                refine ⟨4997179732454635753643525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53303250479516114705530933 4997179732454635753643525)
                ·
                  refine ⟨936971199835244203808161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4997179732454635753643525 936971199835244203808161)
                  ·
                    refine ⟨702728399876433152856121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 936971199835244203808161 702728399876433152856121)
                    ·
                      refine ⟨527046299907324864642091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 702728399876433152856121 527046299907324864642091)
                      ·
                        rfl

theorem cell23_1026419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 4, 2, 2].length) (baseStart_1026419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026419 prefixEnd_1026419 := by exact prefixLift 1026419
  have htrace : WordTrace (prefixWord ++ tailWord_1026419) baseStart_1026419 baseEnd_1026419 := by
    simpa [prefixWord, tailWord_1026419, baseEnd_1026419] using wordTrace_append hprefix tailTrace_1026419
  have hstable : (prefixWord ++ tailWord_1026419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026419).length < 2 ^ (prefixWord ++ tailWord_1026419).sum := by decide
  have hdescent : baseEnd_1026419 < baseStart_1026419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026482 : List Nat := [3, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5]
def baseStart_1026482 : Nat := 118140960795 + 1026482 * 2 ^ 59
def prefixEnd_1026482 : Nat := 4983230072969 + 3 ^ 40 * 1026482 * 2
def baseEnd_1026482 : Nat := 527078649188558118154301

theorem tailTrace_1026482 : CollatzResearch.WordTrace tailWord_1026482 prefixEnd_1026482 527078649188558118154301 := by
  unfold tailWord_1026482
  simp only [CollatzResearch.WordTrace]
  refine ⟨9359718566809624503408425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24959249511492332009089133 9359718566809624503408425)
  ·
    refine ⟨7019788925107218377556319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9359718566809624503408425 7019788925107218377556319)
    ·
      refine ⟨10529683387660827566334479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7019788925107218377556319 10529683387660827566334479)
      ·
        refine ⟨15794525081491241349501719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10529683387660827566334479 15794525081491241349501719)
        ·
          refine ⟨23691787622236862024252579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15794525081491241349501719 23691787622236862024252579)
          ·
            refine ⟨35537681433355293036378869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23691787622236862024252579 35537681433355293036378869)
            ·
              refine ⟨3331657634377058722160519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35537681433355293036378869 3331657634377058722160519)
              ·
                refine ⟨4997486451565588083240779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3331657634377058722160519 4997486451565588083240779)
                ·
                  refine ⟨7496229677348382124861169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4997486451565588083240779 7496229677348382124861169)
                  ·
                    refine ⟨5622172258011286593645877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7496229677348382124861169 5622172258011286593645877)
                    ·
                      refine ⟨527078649188558118154301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5622172258011286593645877 527078649188558118154301)
                      ·
                        rfl

theorem cell23_1026482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_1026482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026482 prefixEnd_1026482 := by exact prefixLift 1026482
  have htrace : WordTrace (prefixWord ++ tailWord_1026482) baseStart_1026482 baseEnd_1026482 := by
    simpa [prefixWord, tailWord_1026482, baseEnd_1026482] using wordTrace_append hprefix tailTrace_1026482
  have hstable : (prefixWord ++ tailWord_1026482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026482).length < 2 ^ (prefixWord ++ tailWord_1026482).sum := by decide
  have hdescent : baseEnd_1026482 < baseStart_1026482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026522 : List Nat := [3, 1, 1, 2, 3, 1, 2, 1, 2, 1, 6]
def baseStart_1026522 : Nat := 118140960795 + 1026522 * 2 ^ 59
def prefixEnd_1026522 : Nat := 4983230072969 + 3 ^ 40 * 1026522 * 2
def baseEnd_1026522 : Nat := 527099188414737961654117

theorem tailTrace_1026522 : CollatzResearch.WordTrace tailWord_1026522 prefixEnd_1026522 527099188414737961654117 := by
  unfold tailWord_1026522
  simp only [CollatzResearch.WordTrace]
  refine ⟨9360083296773396211272455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24960222124729056563393213 9360083296773396211272455)
  ·
    refine ⟨14040124945160094316908683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9360083296773396211272455 14040124945160094316908683)
    ·
      refine ⟨21060187417740141475363025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14040124945160094316908683 21060187417740141475363025)
      ·
        refine ⟨15795140563305106106522269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21060187417740141475363025 15795140563305106106522269)
        ·
          refine ⟨5923177711239414789945851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15795140563305106106522269 5923177711239414789945851)
          ·
            refine ⟨8884766566859122184918777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5923177711239414789945851 8884766566859122184918777)
            ·
              refine ⟨6663574925144341638689083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8884766566859122184918777 6663574925144341638689083)
              ·
                refine ⟨9995362387716512458033625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6663574925144341638689083 9995362387716512458033625)
                ·
                  refine ⟨7496521790787384343525219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9995362387716512458033625 7496521790787384343525219)
                  ·
                    refine ⟨11244782686181076515287829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7496521790787384343525219 11244782686181076515287829)
                    ·
                      refine ⟨527099188414737961654117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11244782686181076515287829 527099188414737961654117)
                      ·
                        rfl

theorem cell23_1026522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_1026522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026522 prefixEnd_1026522 := by exact prefixLift 1026522
  have htrace : WordTrace (prefixWord ++ tailWord_1026522) baseStart_1026522 baseEnd_1026522 := by
    simpa [prefixWord, tailWord_1026522, baseEnd_1026522] using wordTrace_append hprefix tailTrace_1026522
  have hstable : (prefixWord ++ tailWord_1026522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026522).length < 2 ^ (prefixWord ++ tailWord_1026522).sum := by decide
  have hdescent : baseEnd_1026522 < baseStart_1026522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026529 : List Nat := [1, 2, 3, 1, 2, 2, 1, 4, 2, 2, 3]
def baseStart_1026529 : Nat := 118140960795 + 1026529 * 2 ^ 59
def prefixEnd_1026529 : Nat := 4983230072969 + 3 ^ 40 * 1026529 * 2
def baseEnd_1026529 : Nat := 527102782779319434266585

theorem tailTrace_1026529 : CollatzResearch.WordTrace tailWord_1026529 prefixEnd_1026529 527102782779319434266585 := by
  unfold tailWord_1026529
  simp only [CollatzResearch.WordTrace]
  refine ⟨37440588498068225040594641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24960392332045483360396427 37440588498068225040594641)
  ·
    refine ⟨28080441373551168780445981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37440588498068225040594641 28080441373551168780445981)
    ·
      refine ⟨10530165515081688292667243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28080441373551168780445981 10530165515081688292667243)
      ·
        refine ⟨15795248272622532439000865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10530165515081688292667243 15795248272622532439000865)
        ·
          refine ⟨11846436204466899329250649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15795248272622532439000865 11846436204466899329250649)
          ·
            refine ⟨8884827153350174496937987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11846436204466899329250649 8884827153350174496937987)
            ·
              refine ⟨13327240730025261745406981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8884827153350174496937987 13327240730025261745406981)
              ·
                refine ⟨2498857636879736577263809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13327240730025261745406981 2498857636879736577263809)
                ·
                  refine ⟨1874143227659802432947857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2498857636879736577263809 1874143227659802432947857)
                  ·
                    refine ⟨1405607420744851824710893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1874143227659802432947857 1405607420744851824710893)
                    ·
                      refine ⟨527102782779319434266585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1405607420744851824710893 527102782779319434266585)
                      ·
                        rfl

theorem cell23_1026529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 2, 3].length) (baseStart_1026529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026529 prefixEnd_1026529 := by exact prefixLift 1026529
  have htrace : WordTrace (prefixWord ++ tailWord_1026529) baseStart_1026529 baseEnd_1026529 := by
    simpa [prefixWord, tailWord_1026529, baseEnd_1026529] using wordTrace_append hprefix tailTrace_1026529
  have hstable : (prefixWord ++ tailWord_1026529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026529).length < 2 ^ (prefixWord ++ tailWord_1026529).sum := by decide
  have hdescent : baseEnd_1026529 < baseStart_1026529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026579 : List Nat := [1, 1, 1, 2, 1, 5, 3, 3, 1, 5]
def baseStart_1026579 : Nat := 118140960795 + 1026579 * 2 ^ 59
def prefixEnd_1026579 : Nat := 4983230072969 + 3 ^ 40 * 1026579 * 2
def baseEnd_1026579 : Nat := 175709485604014746213785

theorem tailTrace_1026579 : CollatzResearch.WordTrace tailWord_1026579 prefixEnd_1026579 175709485604014746213785 := by
  unfold tailWord_1026579
  simp only [CollatzResearch.WordTrace]
  refine ⟨37442412147887083579914791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24961608098591389053276527 37442412147887083579914791)
  ·
    refine ⟨56163618221830625369872187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37442412147887083579914791 56163618221830625369872187)
    ·
      refine ⟨84245427332745938054808281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56163618221830625369872187 84245427332745938054808281)
      ·
        refine ⟨63184070499559453541106211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84245427332745938054808281 63184070499559453541106211)
        ·
          refine ⟨94776105749339180311659317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63184070499559453541106211 94776105749339180311659317)
          ·
            refine ⟨8885259914000548154218061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94776105749339180311659317 8885259914000548154218061)
            ·
              refine ⟨3331972467750205557831773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8885259914000548154218061 3331972467750205557831773)
              ·
                refine ⟨1249489675406327084186915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3331972467750205557831773 1249489675406327084186915)
                ·
                  refine ⟨1874234513109490626280373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1249489675406327084186915 1874234513109490626280373)
                  ·
                    refine ⟨175709485604014746213785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1874234513109490626280373 175709485604014746213785)
                    ·
                      rfl

theorem cell23_1026579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 5].length) (baseStart_1026579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026579 prefixEnd_1026579 := by exact prefixLift 1026579
  have htrace : WordTrace (prefixWord ++ tailWord_1026579) baseStart_1026579 baseEnd_1026579 := by
    simpa [prefixWord, tailWord_1026579, baseEnd_1026579] using wordTrace_append hprefix tailTrace_1026579
  have hstable : (prefixWord ++ tailWord_1026579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026579).length < 2 ^ (prefixWord ++ tailWord_1026579).sum := by decide
  have hdescent : baseEnd_1026579 < baseStart_1026579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026583 : List Nat := [1, 1, 3, 6, 1, 2, 1, 2, 6]
def baseStart_1026583 : Nat := 118140960795 + 1026583 * 2 ^ 59
def prefixEnd_1026583 : Nat := 4983230072969 + 3 ^ 40 * 1026583 * 2
def baseEnd_1026583 : Nat := 58570056748295802554593

theorem tailTrace_1026583 : CollatzResearch.WordTrace tailWord_1026583 prefixEnd_1026583 58570056748295802554593 := by
  unfold tailWord_1026583
  simp only [CollatzResearch.WordTrace]
  refine ⟨37442558039872592263060403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24961705359915061508706935 37442558039872592263060403)
  ·
    refine ⟨56163837059808888394590605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37442558039872592263060403 56163837059808888394590605)
    ·
      refine ⟨21061438897428333147971477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56163837059808888394590605 21061438897428333147971477)
      ·
        refine ⟨987254948316953116311163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 21061438897428333147971477 987254948316953116311163)
        ·
          refine ⟨1480882422475429674466745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 987254948316953116311163 1480882422475429674466745)
          ·
            refine ⟨1110661816856572255850059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1480882422475429674466745 1110661816856572255850059)
            ·
              refine ⟨1665992725284858383775089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1110661816856572255850059 1665992725284858383775089)
              ·
                refine ⟨1249494543963643787831317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1665992725284858383775089 1249494543963643787831317)
                ·
                  refine ⟨58570056748295802554593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1249494543963643787831317 58570056748295802554593)
                  ·
                    rfl

theorem cell23_1026583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 6].length) (baseStart_1026583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026583 prefixEnd_1026583 := by exact prefixLift 1026583
  have htrace : WordTrace (prefixWord ++ tailWord_1026583) baseStart_1026583 baseEnd_1026583 := by
    simpa [prefixWord, tailWord_1026583, baseEnd_1026583] using wordTrace_append hprefix tailTrace_1026583
  have hstable : (prefixWord ++ tailWord_1026583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026583).length < 2 ^ (prefixWord ++ tailWord_1026583).sum := by decide
  have hdescent : baseEnd_1026583 < baseStart_1026583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026586 : List Nat := [3, 1, 1, 3, 1, 1, 2, 4, 2, 3, 2]
def baseStart_1026586 : Nat := 118140960795 + 1026586 * 2 ^ 59
def prefixEnd_1026586 : Nat := 4983230072969 + 3 ^ 40 * 1026586 * 2
def baseEnd_1026586 : Nat := 527132051176625711253823

theorem tailTrace_1026586 : CollatzResearch.WordTrace tailWord_1026586 prefixEnd_1026586 527132051176625711253823 := by
  unfold tailWord_1026586
  simp only [CollatzResearch.WordTrace]
  refine ⟨9360666864715430943854903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24961778305907815850279741 9360666864715430943854903)
  ·
    refine ⟨14041000297073146415782355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9360666864715430943854903 14041000297073146415782355)
    ·
      refine ⟨21061500445609719623673533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14041000297073146415782355 21061500445609719623673533)
      ·
        refine ⟨7898062667103644858877575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21061500445609719623673533 7898062667103644858877575)
        ·
          refine ⟨11847094000655467288316363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7898062667103644858877575 11847094000655467288316363)
          ·
            refine ⟨17770641000983200932474545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11847094000655467288316363 17770641000983200932474545)
            ·
              refine ⟨13327980750737400699355909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17770641000983200932474545 13327980750737400699355909)
              ·
                refine ⟨2498996390763262631129233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13327980750737400699355909 2498996390763262631129233)
                ·
                  refine ⟨1874247293072446973346925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2498996390763262631129233 1874247293072446973346925)
                  ·
                    refine ⟨702842734902167615005097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1874247293072446973346925 702842734902167615005097)
                    ·
                      refine ⟨527132051176625711253823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 702842734902167615005097 527132051176625711253823)
                      ·
                        rfl

theorem cell23_1026586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_1026586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026586 prefixEnd_1026586 := by exact prefixLift 1026586
  have htrace : WordTrace (prefixWord ++ tailWord_1026586) baseStart_1026586 baseEnd_1026586 := by
    simpa [prefixWord, tailWord_1026586, baseEnd_1026586] using wordTrace_append hprefix tailTrace_1026586
  have hstable : (prefixWord ++ tailWord_1026586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026586).length < 2 ^ (prefixWord ++ tailWord_1026586).sum := by decide
  have hdescent : baseEnd_1026586 < baseStart_1026586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026593 : List Nat := [1, 2, 3, 2, 2, 1, 1, 6, 1, 1, 3]
def baseStart_1026593 : Nat := 118140960795 + 1026593 * 2 ^ 59
def prefixEnd_1026593 : Nat := 4983230072969 + 3 ^ 40 * 1026593 * 2
def baseEnd_1026593 : Nat := 527135645541207183866291

theorem tailTrace_1026593 : CollatzResearch.WordTrace tailWord_1026593 prefixEnd_1026593 527135645541207183866291 := by
  unfold tailWord_1026593
  simp only [CollatzResearch.WordTrace]
  refine ⟨37442922769836363970924433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24961948513224242647282955 37442922769836363970924433)
  ·
    refine ⟨28082192077377272978193325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37442922769836363970924433 28082192077377272978193325)
    ·
      refine ⟨10530822029016477366822497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28082192077377272978193325 10530822029016477366822497)
      ·
        refine ⟨7898116521762358025116873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10530822029016477366822497 7898116521762358025116873)
        ·
          refine ⟨5923587391321768518837655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7898116521762358025116873 5923587391321768518837655)
          ·
            refine ⟨8885381086982652778256483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5923587391321768518837655 8885381086982652778256483)
            ·
              refine ⟨13328071630473979167384725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8885381086982652778256483 13328071630473979167384725)
              ·
                refine ⟨624753357678467773471159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13328071630473979167384725 624753357678467773471159)
                ·
                  refine ⟨937130036517701660206739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 624753357678467773471159 937130036517701660206739)
                  ·
                    refine ⟨1405695054776552490310109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 937130036517701660206739 1405695054776552490310109)
                    ·
                      refine ⟨527135645541207183866291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1405695054776552490310109 527135645541207183866291)
                      ·
                        rfl

theorem cell23_1026593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 6, 1, 1, 3].length) (baseStart_1026593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026593 prefixEnd_1026593 := by exact prefixLift 1026593
  have htrace : WordTrace (prefixWord ++ tailWord_1026593) baseStart_1026593 baseEnd_1026593 := by
    simpa [prefixWord, tailWord_1026593, baseEnd_1026593] using wordTrace_append hprefix tailTrace_1026593
  have hstable : (prefixWord ++ tailWord_1026593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026593).length < 2 ^ (prefixWord ++ tailWord_1026593).sum := by decide
  have hdescent : baseEnd_1026593 < baseStart_1026593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026609 : List Nat := [1, 2, 2, 3, 1, 1, 5, 1, 1, 6]
def baseStart_1026609 : Nat := 118140960795 + 1026609 * 2 ^ 59
def prefixEnd_1026609 : Nat := 4983230072969 + 3 ^ 40 * 1026609 * 2
def baseEnd_1026609 : Nat := 175714620410559707088739

theorem tailTrace_1026609 : CollatzResearch.WordTrace tailWord_1026609 prefixEnd_1026609 175714620410559707088739 := by
  unfold tailWord_1026609
  simp only [CollatzResearch.WordTrace]
  refine ⟨37443506337778398703506881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24962337558518932469004587 37443506337778398703506881)
  ·
    refine ⟨28082629753333799027630161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37443506337778398703506881 28082629753333799027630161)
    ·
      refine ⟨21061972315000349270722621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28082629753333799027630161 21061972315000349270722621)
      ·
        refine ⟨7898239618125130976520983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21061972315000349270722621 7898239618125130976520983)
        ·
          refine ⟨11847359427187696464781475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7898239618125130976520983 11847359427187696464781475)
          ·
            refine ⟨17771039140781544697172213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11847359427187696464781475 17771039140781544697172213)
            ·
              refine ⟨1666034919448269815359895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17771039140781544697172213 1666034919448269815359895)
              ·
                refine ⟨2499052379172404723039843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1666034919448269815359895 2499052379172404723039843)
                ·
                  refine ⟨3748578568758607084559765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2499052379172404723039843 3748578568758607084559765)
                  ·
                    refine ⟨175714620410559707088739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3748578568758607084559765 175714620410559707088739)
                    ·
                      rfl

theorem cell23_1026609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 6].length) (baseStart_1026609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026609 prefixEnd_1026609 := by exact prefixLift 1026609
  have htrace : WordTrace (prefixWord ++ tailWord_1026609) baseStart_1026609 baseEnd_1026609 := by
    simpa [prefixWord, tailWord_1026609, baseEnd_1026609] using wordTrace_append hprefix tailTrace_1026609
  have hstable : (prefixWord ++ tailWord_1026609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026609).length < 2 ^ (prefixWord ++ tailWord_1026609).sum := by decide
  have hdescent : baseEnd_1026609 < baseStart_1026609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026616 : List Nat := [2, 1, 2, 1, 4, 1, 4, 2, 1, 1, 4]
def baseStart_1026616 : Nat := 118140960795 + 1026616 * 2 ^ 59
def prefixEnd_1026616 : Nat := 4983230072969 + 3 ^ 40 * 1026616 * 2
def baseEnd_1026616 : Nat := 527147455596260593878685

theorem tailTrace_1026616 : CollatzResearch.WordTrace tailWord_1026616 prefixEnd_1026616 527147455596260593878685 := by
  unfold tailWord_1026616
  simp only [CollatzResearch.WordTrace]
  refine ⟨18721880824376519449505851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24962507765835359266007801 18721880824376519449505851)
  ·
    refine ⟨28082821236564779174258777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18721880824376519449505851 28082821236564779174258777)
    ·
      refine ⟨21062115927423584380694083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28082821236564779174258777 21062115927423584380694083)
      ·
        refine ⟨31593173891135376571041125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21062115927423584380694083 31593173891135376571041125)
        ·
          refine ⟨5923720104587883107070211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31593173891135376571041125 5923720104587883107070211)
          ·
            refine ⟨8885580156881824660605317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5923720104587883107070211 8885580156881824660605317)
            ·
              refine ⟨1666046279415342123863497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8885580156881824660605317 1666046279415342123863497)
              ·
                refine ⟨1249534709561506592897623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1666046279415342123863497 1249534709561506592897623)
                ·
                  refine ⟨1874302064342259889346435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1249534709561506592897623 1874302064342259889346435)
                  ·
                    refine ⟨2811453096513389834019653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1874302064342259889346435 2811453096513389834019653)
                    ·
                      refine ⟨527147455596260593878685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2811453096513389834019653 527147455596260593878685)
                      ·
                        rfl

theorem cell23_1026616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 1, 1, 4].length) (baseStart_1026616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026616 prefixEnd_1026616 := by exact prefixLift 1026616
  have htrace : WordTrace (prefixWord ++ tailWord_1026616) baseStart_1026616 baseEnd_1026616 := by
    simpa [prefixWord, tailWord_1026616, baseEnd_1026616] using wordTrace_append hprefix tailTrace_1026616
  have hstable : (prefixWord ++ tailWord_1026616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026616).length < 2 ^ (prefixWord ++ tailWord_1026616).sum := by decide
  have hdescent : baseEnd_1026616 < baseStart_1026616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026636 : List Nat := [2, 2, 1, 3, 1, 2, 1, 5, 1, 2, 3]
def baseStart_1026636 : Nat := 118140960795 + 1026636 * 2 ^ 59
def prefixEnd_1026636 : Nat := 4983230072969 + 3 ^ 40 * 1026636 * 2
def baseEnd_1026636 : Nat := 527157725209350515628593

theorem tailTrace_1026636 : CollatzResearch.WordTrace tailWord_1026636 prefixEnd_1026636 527157725209350515628593 := by
  unfold tailWord_1026636
  simp only [CollatzResearch.WordTrace]
  refine ⟨18722245554340291157369881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24962994072453721543159841 18722245554340291157369881)
  ·
    refine ⟨14041684165755218368027411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18722245554340291157369881 14041684165755218368027411)
    ·
      refine ⟨21062526248632827552041117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14041684165755218368027411 21062526248632827552041117)
      ·
        refine ⟨7898447343237310332015419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21062526248632827552041117 7898447343237310332015419)
        ·
          refine ⟨11847671014855965498023129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7898447343237310332015419 11847671014855965498023129)
          ·
            refine ⟨8885753261141974123517347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11847671014855965498023129 8885753261141974123517347)
            ·
              refine ⟨13328629891712961185276021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8885753261141974123517347 13328629891712961185276021)
              ·
                refine ⟨1249559052348090111119627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13328629891712961185276021 1249559052348090111119627)
                ·
                  refine ⟨1874338578522135166679441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1249559052348090111119627 1874338578522135166679441)
                  ·
                    refine ⟨1405753933891601375009581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1874338578522135166679441 1405753933891601375009581)
                    ·
                      refine ⟨527157725209350515628593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1405753933891601375009581 527157725209350515628593)
                      ·
                        rfl

theorem cell23_1026636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_1026636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026636 prefixEnd_1026636 := by exact prefixLift 1026636
  have htrace : WordTrace (prefixWord ++ tailWord_1026636) baseStart_1026636 baseEnd_1026636 := by
    simpa [prefixWord, tailWord_1026636, baseEnd_1026636] using wordTrace_append hprefix tailTrace_1026636
  have hstable : (prefixWord ++ tailWord_1026636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026636).length < 2 ^ (prefixWord ++ tailWord_1026636).sum := by decide
  have hdescent : baseEnd_1026636 < baseStart_1026636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026666 : List Nat := [3, 1, 3, 2, 1, 1, 2, 3, 1, 3, 3]
def baseStart_1026666 : Nat := 118140960795 + 1026666 * 2 ^ 59
def prefixEnd_1026666 : Nat := 4983230072969 + 3 ^ 40 * 1026666 * 2
def baseEnd_1026666 : Nat := 527173129628985398253455

theorem tailTrace_1026666 : CollatzResearch.WordTrace tailWord_1026666 prefixEnd_1026666 527173129628985398253455 := by
  unfold tailWord_1026666
  simp only [CollatzResearch.WordTrace]
  refine ⟨9361396324642974359582963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24963723532381264958887901 9361396324642974359582963)
  ·
    refine ⟨14042094486964461539374445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9361396324642974359582963 14042094486964461539374445)
    ·
      refine ⟨5265785432611673077265417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14042094486964461539374445 5265785432611673077265417)
      ·
        refine ⟨3949339074458754807949063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5265785432611673077265417 3949339074458754807949063)
        ·
          refine ⟨5924008611688132211923595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3949339074458754807949063 5924008611688132211923595)
          ·
            refine ⟨8886012917532198317885393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5924008611688132211923595 8886012917532198317885393)
            ·
              refine ⟨6664509688149148738414045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8886012917532198317885393 6664509688149148738414045)
              ·
                refine ⟨2499191133055930776905267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6664509688149148738414045 2499191133055930776905267)
                ·
                  refine ⟨3748786699583896165357901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2499191133055930776905267 3748786699583896165357901)
                  ·
                    refine ⟨1405795012343961062009213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3748786699583896165357901 1405795012343961062009213)
                    ·
                      refine ⟨527173129628985398253455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1405795012343961062009213 527173129628985398253455)
                      ·
                        rfl

theorem cell23_1026666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_1026666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026666 prefixEnd_1026666 := by exact prefixLift 1026666
  have htrace : WordTrace (prefixWord ++ tailWord_1026666) baseStart_1026666 baseEnd_1026666 := by
    simpa [prefixWord, tailWord_1026666, baseEnd_1026666] using wordTrace_append hprefix tailTrace_1026666
  have hstable : (prefixWord ++ tailWord_1026666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026666).length < 2 ^ (prefixWord ++ tailWord_1026666).sum := by decide
  have hdescent : baseEnd_1026666 < baseStart_1026666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026670 : List Nat := [4, 1, 2, 2, 2, 3, 1, 2, 1, 2, 3]
def baseStart_1026670 : Nat := 118140960795 + 1026670 * 2 ^ 59
def prefixEnd_1026670 : Nat := 4983230072969 + 3 ^ 40 * 1026670 * 2
def baseEnd_1026670 : Nat := 527175183551603382603437

theorem tailTrace_1026670 : CollatzResearch.WordTrace tailWord_1026670 prefixEnd_1026670 527175183551603382603437 := by
  unfold tailWord_1026670
  simp only [CollatzResearch.WordTrace]
  refine ⟨4680716398819675765184683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24963820793704937414318309 4680716398819675765184683)
  ·
    refine ⟨7021074598229513647777025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4680716398819675765184683 7021074598229513647777025)
    ·
      refine ⟨5265805948672135235832769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7021074598229513647777025 5265805948672135235832769)
      ·
        refine ⟨3949354461504101426874577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5265805948672135235832769 3949354461504101426874577)
        ·
          refine ⟨2962015846128076070155933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3949354461504101426874577 2962015846128076070155933)
          ·
            refine ⟨1110755942298028526308475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2962015846128076070155933 1110755942298028526308475)
            ·
              refine ⟨1666133913447042789462713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1110755942298028526308475 1666133913447042789462713)
              ·
                refine ⟨1249600435085282092097035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1666133913447042789462713 1249600435085282092097035)
                ·
                  refine ⟨1874400652627923138145553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1249600435085282092097035 1874400652627923138145553)
                  ·
                    refine ⟨1405800489470942353609165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1874400652627923138145553 1405800489470942353609165)
                    ·
                      refine ⟨527175183551603382603437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1405800489470942353609165 527175183551603382603437)
                      ·
                        rfl

theorem cell23_1026670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_1026670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026670 prefixEnd_1026670 := by exact prefixLift 1026670
  have htrace : WordTrace (prefixWord ++ tailWord_1026670) baseStart_1026670 baseEnd_1026670 := by
    simpa [prefixWord, tailWord_1026670, baseEnd_1026670] using wordTrace_append hprefix tailTrace_1026670
  have hstable : (prefixWord ++ tailWord_1026670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026670).length < 2 ^ (prefixWord ++ tailWord_1026670).sum := by decide
  have hdescent : baseEnd_1026670 < baseStart_1026670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026690 : List Nat := [3, 4, 3, 1, 2, 10]
def baseStart_1026690 : Nat := 118140960795 + 1026690 * 2 ^ 59
def prefixEnd_1026690 : Nat := 4983230072969 + 3 ^ 40 * 1026690 * 2
def baseEnd_1026690 : Nat := 2169487461583100017915

theorem tailTrace_1026690 : CollatzResearch.WordTrace tailWord_1026690 prefixEnd_1026690 2169487461583100017915 := by
  unfold tailWord_1026690
  simp only [CollatzResearch.WordTrace]
  refine ⟨9361615162621237384301381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24964307100323299691470349 9361615162621237384301381)
  ·
    refine ⟨1755302842991482009556509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9361615162621237384301381 1755302842991482009556509)
    ·
      refine ⟨658238566121805753583691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1755302842991482009556509 658238566121805753583691)
      ·
        refine ⟨987357849182708630375537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 658238566121805753583691 987357849182708630375537)
        ·
          refine ⟨740518386887031472781653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 987357849182708630375537 740518386887031472781653)
          ·
            refine ⟨2169487461583100017915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 740518386887031472781653 2169487461583100017915)
            ·
              rfl

theorem cell23_1026690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 10].length) (baseStart_1026690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026690 prefixEnd_1026690 := by exact prefixLift 1026690
  have htrace : WordTrace (prefixWord ++ tailWord_1026690) baseStart_1026690 baseEnd_1026690 := by
    simpa [prefixWord, tailWord_1026690, baseEnd_1026690] using wordTrace_append hprefix tailTrace_1026690
  have hstable : (prefixWord ++ tailWord_1026690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026690).length < 2 ^ (prefixWord ++ tailWord_1026690).sum := by decide
  have hdescent : baseEnd_1026690 < baseStart_1026690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026706 : List Nat := [3, 2, 3, 1, 2, 1, 1, 1, 2, 3, 4]
def baseStart_1026706 : Nat := 118140960795 + 1026706 * 2 ^ 59
def prefixEnd_1026706 : Nat := 4983230072969 + 3 ^ 40 * 1026706 * 2
def baseEnd_1026706 : Nat := 527193668855165241753271

theorem tailTrace_1026706 : CollatzResearch.WordTrace tailWord_1026706 prefixEnd_1026706 527193668855165241753271 := by
  unfold tailWord_1026706
  simp only [CollatzResearch.WordTrace]
  refine ⟨9361761054606746067446993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24964696145617989513191981 9361761054606746067446993)
  ·
    refine ⟨7021320790955059550585245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9361761054606746067446993 7021320790955059550585245)
    ·
      refine ⟨2632995296608147331469467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7021320790955059550585245 2632995296608147331469467)
      ·
        refine ⟨3949492944912220997204201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2632995296608147331469467 3949492944912220997204201)
        ·
          refine ⟨2962119708684165747903151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3949492944912220997204201 2962119708684165747903151)
          ·
            refine ⟨4443179563026248621854727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2962119708684165747903151 4443179563026248621854727)
            ·
              refine ⟨6664769344539372932782091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4443179563026248621854727 6664769344539372932782091)
              ·
                refine ⟨9997154016809059399173137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6664769344539372932782091 9997154016809059399173137)
                ·
                  refine ⟨7497865512606794549379853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9997154016809059399173137 7497865512606794549379853)
                  ·
                    refine ⟨2811699567227547956017445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7497865512606794549379853 2811699567227547956017445)
                    ·
                      refine ⟨527193668855165241753271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2811699567227547956017445 527193668855165241753271)
                      ·
                        rfl

theorem cell23_1026706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_1026706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026706 prefixEnd_1026706 := by exact prefixLift 1026706
  have htrace : WordTrace (prefixWord ++ tailWord_1026706) baseStart_1026706 baseEnd_1026706 := by
    simpa [prefixWord, tailWord_1026706, baseEnd_1026706] using wordTrace_append hprefix tailTrace_1026706
  have hstable : (prefixWord ++ tailWord_1026706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026706).length < 2 ^ (prefixWord ++ tailWord_1026706).sum := by decide
  have hdescent : baseEnd_1026706 < baseStart_1026706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026716 : List Nat := [2, 2, 3, 2, 2, 2, 1, 1, 2, 6]
def baseStart_1026716 : Nat := 118140960795 + 1026716 * 2 ^ 59
def prefixEnd_1026716 : Nat := 4983230072969 + 3 ^ 40 * 1026716 * 2
def baseEnd_1026716 : Nat := 175732934553903400876075

theorem tailTrace_1026716 : CollatzResearch.WordTrace tailWord_1026716 prefixEnd_1026716 175732934553903400876075 := by
  unfold tailWord_1026716
  simp only [CollatzResearch.WordTrace]
  refine ⟨18723704474195377988826001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24964939298927170651768001 18723704474195377988826001)
  ·
    refine ⟨14042778355646533491619501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18723704474195377988826001 14042778355646533491619501)
    ·
      refine ⟨5266041883367450059357313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14042778355646533491619501 5266041883367450059357313)
      ·
        refine ⟨3949531412525587544517985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5266041883367450059357313 3949531412525587544517985)
        ·
          refine ⟨2962148559394190658388489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3949531412525587544517985 2962148559394190658388489)
          ·
            refine ⟨2221611419545642993791367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2962148559394190658388489 2221611419545642993791367)
            ·
              refine ⟨3332417129318464490687051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2221611419545642993791367 3332417129318464490687051)
              ·
                refine ⟨4998625693977696736030577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3332417129318464490687051 4998625693977696736030577)
                ·
                  refine ⟨3748969270483272552022933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4998625693977696736030577 3748969270483272552022933)
                  ·
                    refine ⟨175732934553903400876075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3748969270483272552022933 175732934553903400876075)
                    ·
                      rfl

theorem cell23_1026716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_1026716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026716 prefixEnd_1026716 := by exact prefixLift 1026716
  have htrace : WordTrace (prefixWord ++ tailWord_1026716) baseStart_1026716 baseEnd_1026716 := by
    simpa [prefixWord, tailWord_1026716, baseEnd_1026716] using wordTrace_append hprefix tailTrace_1026716
  have hstable : (prefixWord ++ tailWord_1026716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026716).length < 2 ^ (prefixWord ++ tailWord_1026716).sum := by decide
  have hdescent : baseEnd_1026716 < baseStart_1026716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026769 : List Nat := [1, 2, 2, 1, 2, 3, 2, 1, 1, 1, 7]
def baseStart_1026769 : Nat := 118140960795 + 1026769 * 2 ^ 59
def prefixEnd_1026769 : Nat := 4983230072969 + 3 ^ 40 * 1026769 * 2
def baseEnd_1026769 : Nat := 527226018136398495265481

theorem tailTrace_1026769 : CollatzResearch.WordTrace tailWord_1026769 prefixEnd_1026769 527226018136398495265481 := by
  unfold tailWord_1026769
  simp only [CollatzResearch.WordTrace]
  refine ⟨37449342017198746029331361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24966228011465830686220907 37449342017198746029331361)
  ·
    refine ⟨28087006512899059521998521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37449342017198746029331361 28087006512899059521998521)
    ·
      refine ⟨21065254884674294641498891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28087006512899059521998521 21065254884674294641498891)
      ·
        refine ⟨31597882327011441962248337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21065254884674294641498891 31597882327011441962248337)
        ·
          refine ⟨23698411745258581471686253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31597882327011441962248337 23698411745258581471686253)
          ·
            refine ⟨8886904404471968051882345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23698411745258581471686253 8886904404471968051882345)
            ·
              refine ⟨6665178303353976038911759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8886904404471968051882345 6665178303353976038911759)
              ·
                refine ⟨9997767455030964058367639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6665178303353976038911759 9997767455030964058367639)
                ·
                  refine ⟨14996651182546446087551459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9997767455030964058367639 14996651182546446087551459)
                  ·
                    refine ⟨22494976773819669131327189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14996651182546446087551459 22494976773819669131327189)
                    ·
                      refine ⟨527226018136398495265481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 22494976773819669131327189 527226018136398495265481)
                      ·
                        rfl

theorem cell23_1026769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_1026769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026769 prefixEnd_1026769 := by exact prefixLift 1026769
  have htrace : WordTrace (prefixWord ++ tailWord_1026769) baseStart_1026769 baseEnd_1026769 := by
    simpa [prefixWord, tailWord_1026769, baseEnd_1026769] using wordTrace_append hprefix tailTrace_1026769
  have hstable : (prefixWord ++ tailWord_1026769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026769).length < 2 ^ (prefixWord ++ tailWord_1026769).sum := by decide
  have hdescent : baseEnd_1026769 < baseStart_1026769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026796 : List Nat := [2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 4]
def baseStart_1026796 : Nat := 118140960795 + 1026796 * 2 ^ 59
def prefixEnd_1026796 : Nat := 4983230072969 + 3 ^ 40 * 1026796 * 2
def baseEnd_1026796 : Nat := 527239882114069889627857

theorem tailTrace_1026796 : CollatzResearch.WordTrace tailWord_1026796 prefixEnd_1026796 527239882114069889627857 := by
  unfold tailWord_1026796
  simp only [CollatzResearch.WordTrace]
  refine ⟨18725163394050464820282121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24966884525400619760376161 18725163394050464820282121)
  ·
    refine ⟨14043872545537848615211591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18725163394050464820282121 14043872545537848615211591)
    ·
      refine ⟨21065808818306772922817387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14043872545537848615211591 21065808818306772922817387)
      ·
        refine ⟨31598713227460159384226081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21065808818306772922817387 31598713227460159384226081)
        ·
          refine ⟨23699034920595119538169561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31598713227460159384226081 23699034920595119538169561)
          ·
            refine ⟨17774276190446339653627171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23699034920595119538169561 17774276190446339653627171)
            ·
              refine ⟨26661414285669509480440757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17774276190446339653627171 26661414285669509480440757)
              ·
                refine ⟨2499507589281516513791321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26661414285669509480440757 2499507589281516513791321)
                ·
                  refine ⟨1874630691961137385343491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2499507589281516513791321 1874630691961137385343491)
                  ·
                    refine ⟨2811946037941706078015237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1874630691961137385343491 2811946037941706078015237)
                    ·
                      refine ⟨527239882114069889627857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2811946037941706078015237 527239882114069889627857)
                      ·
                        rfl

theorem cell23_1026796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 4].length) (baseStart_1026796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026796 prefixEnd_1026796 := by exact prefixLift 1026796
  have htrace : WordTrace (prefixWord ++ tailWord_1026796) baseStart_1026796 baseEnd_1026796 := by
    simpa [prefixWord, tailWord_1026796, baseEnd_1026796] using wordTrace_append hprefix tailTrace_1026796
  have hstable : (prefixWord ++ tailWord_1026796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026796).length < 2 ^ (prefixWord ++ tailWord_1026796).sum := by decide
  have hdescent : baseEnd_1026796 < baseStart_1026796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026809 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 1, 3, 6]
def baseStart_1026809 : Nat := 118140960795 + 1026809 * 2 ^ 59
def prefixEnd_1026809 : Nat := 4983230072969 + 3 ^ 40 * 1026809 * 2
def baseEnd_1026809 : Nat := 527246557362578338765297

theorem tailTrace_1026809 : CollatzResearch.WordTrace tailWord_1026809 prefixEnd_1026809 527246557362578338765297 := by
  unfold tailWord_1026809
  simp only [CollatzResearch.WordTrace]
  refine ⟨37450800937053832860787481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24967200624702555240524987 37450800937053832860787481)
  ·
    refine ⟨28088100702790374645590611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37450800937053832860787481 28088100702790374645590611)
    ·
      refine ⟨42132151054185561968385917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28088100702790374645590611 42132151054185561968385917)
      ·
        refine ⟨15799556645319585738144719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42132151054185561968385917 15799556645319585738144719)
        ·
          refine ⟨23699334967979378607217079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15799556645319585738144719 23699334967979378607217079)
          ·
            refine ⟨35549002451969067910825619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23699334967979378607217079 35549002451969067910825619)
            ·
              refine ⟨53323503677953601866238429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35549002451969067910825619 53323503677953601866238429)
              ·
                refine ⟨19996313879232600699839411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53323503677953601866238429 19996313879232600699839411)
                ·
                  refine ⟨29994470818848901049759117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19996313879232600699839411 29994470818848901049759117)
                  ·
                    refine ⟨11247926557068337893659669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29994470818848901049759117 11247926557068337893659669)
                    ·
                      refine ⟨527246557362578338765297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11247926557068337893659669 527246557362578338765297)
                      ·
                        rfl

theorem cell23_1026809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_1026809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026809 prefixEnd_1026809 := by exact prefixLift 1026809
  have htrace : WordTrace (prefixWord ++ tailWord_1026809) baseStart_1026809 baseEnd_1026809 := by
    simpa [prefixWord, tailWord_1026809, baseEnd_1026809] using wordTrace_append hprefix tailTrace_1026809
  have hstable : (prefixWord ++ tailWord_1026809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026809).length < 2 ^ (prefixWord ++ tailWord_1026809).sum := by decide
  have hdescent : baseEnd_1026809 < baseStart_1026809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026850 : List Nat := [3, 3, 1, 1, 2, 3, 2, 1, 2, 2, 3]
def baseStart_1026850 : Nat := 118140960795 + 1026850 * 2 ^ 59
def prefixEnd_1026850 : Nat := 4983230072969 + 3 ^ 40 * 1026850 * 2
def baseEnd_1026850 : Nat := 527267610069412678352609

theorem tailTrace_1026850 : CollatzResearch.WordTrace tailWord_1026850 prefixEnd_1026850 527267610069412678352609 := by
  unfold tailWord_1026850
  simp only [CollatzResearch.WordTrace]
  refine ⟨9363074082476324215757501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24968197553270197908686669 9363074082476324215757501)
  ·
    refine ⟨3511152780928621580909063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9363074082476324215757501 3511152780928621580909063)
    ·
      refine ⟨5266729171392932371363595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3511152780928621580909063 5266729171392932371363595)
      ·
        refine ⟨7900093757089398557045393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5266729171392932371363595 7900093757089398557045393)
        ·
          refine ⟨5925070317817048917784045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7900093757089398557045393 5925070317817048917784045)
          ·
            refine ⟨2221901369181393344169017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5925070317817048917784045 2221901369181393344169017)
            ·
              refine ⟨1666426026886045008126763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2221901369181393344169017 1666426026886045008126763)
              ·
                refine ⟨2499639040329067512190145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1666426026886045008126763 2499639040329067512190145)
                ·
                  refine ⟨1874729280246800634142609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2499639040329067512190145 1874729280246800634142609)
                  ·
                    refine ⟨1406046960185100475606957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1874729280246800634142609 1406046960185100475606957)
                    ·
                      refine ⟨527267610069412678352609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1406046960185100475606957 527267610069412678352609)
                      ·
                        rfl

theorem cell23_1026850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_1026850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026850 prefixEnd_1026850 := by exact prefixLift 1026850
  have htrace : WordTrace (prefixWord ++ tailWord_1026850) baseStart_1026850 baseEnd_1026850 := by
    simpa [prefixWord, tailWord_1026850, baseEnd_1026850] using wordTrace_append hprefix tailTrace_1026850
  have hstable : (prefixWord ++ tailWord_1026850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026850).length < 2 ^ (prefixWord ++ tailWord_1026850).sum := by decide
  have hdescent : baseEnd_1026850 < baseStart_1026850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026874 : List Nat := [3, 1, 1, 1, 6, 2, 2, 2, 1, 4]
def baseStart_1026874 : Nat := 118140960795 + 1026874 * 2 ^ 59
def prefixEnd_1026874 : Nat := 4983230072969 + 3 ^ 40 * 1026874 * 2
def baseEnd_1026874 : Nat := 175759977868373528150833

theorem tailTrace_1026874 : CollatzResearch.WordTrace tailWord_1026874 prefixEnd_1026874 175759977868373528150833 := by
  unfold tailWord_1026874
  simp only [CollatzResearch.WordTrace]
  refine ⟨9363292920454587240475919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24968781121212232641269117 9363292920454587240475919)
  ·
    refine ⟨14044939380681880860713879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9363292920454587240475919 14044939380681880860713879)
    ·
      refine ⟨21067409071022821291070819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14044939380681880860713879 21067409071022821291070819)
      ·
        refine ⟨31601113606534231936606229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21067409071022821291070819 31601113606534231936606229)
        ·
          refine ⟨1481302200306292122028417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31601113606534231936606229 1481302200306292122028417)
          ·
            refine ⟨1110976650229719091521313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1481302200306292122028417 1110976650229719091521313)
            ·
              refine ⟨833232487672289318640985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1110976650229719091521313 833232487672289318640985)
              ·
                refine ⟨624924365754216988980739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 833232487672289318640985 624924365754216988980739)
                ·
                  refine ⟨937386548631325483471109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 624924365754216988980739 937386548631325483471109)
                  ·
                    refine ⟨175759977868373528150833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 937386548631325483471109 175759977868373528150833)
                    ·
                      rfl

theorem cell23_1026874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 2, 1, 4].length) (baseStart_1026874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026874 prefixEnd_1026874 := by exact prefixLift 1026874
  have htrace : WordTrace (prefixWord ++ tailWord_1026874) baseStart_1026874 baseEnd_1026874 := by
    simpa [prefixWord, tailWord_1026874, baseEnd_1026874] using wordTrace_append hprefix tailTrace_1026874
  have hstable : (prefixWord ++ tailWord_1026874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026874).length < 2 ^ (prefixWord ++ tailWord_1026874).sum := by decide
  have hdescent : baseEnd_1026874 < baseStart_1026874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026896 : List Nat := [2, 1, 1, 1, 1, 4, 3, 3, 1, 6]
def baseStart_1026896 : Nat := 118140960795 + 1026896 * 2 ^ 59
def prefixEnd_1026896 : Nat := 4983230072969 + 3 ^ 40 * 1026896 * 2
def baseEnd_1026896 : Nat := 175763743393173166125799

theorem tailTrace_1026896 : CollatzResearch.WordTrace tailWord_1026896 prefixEnd_1026896 175763743393173166125799 := by
  unfold tailWord_1026896
  simp only [CollatzResearch.WordTrace]
  refine ⟨18726987043869323359602271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24969316058492431146136361 18726987043869323359602271)
  ·
    refine ⟨28090480565803985039403407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18726987043869323359602271 28090480565803985039403407)
    ·
      refine ⟨42135720848705977559105111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28090480565803985039403407 42135720848705977559105111)
      ·
        refine ⟨63203581273058966338657667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42135720848705977559105111 63203581273058966338657667)
        ·
          refine ⟨94805371909588449507986501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63203581273058966338657667 94805371909588449507986501)
          ·
            refine ⟨17776007233047834282747469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94805371909588449507986501 17776007233047834282747469)
            ·
              refine ⟨6666002712392937856030301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17776007233047834282747469 6666002712392937856030301)
              ·
                refine ⟨2499751017147351696011363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6666002712392937856030301 2499751017147351696011363)
                ·
                  refine ⟨3749626525721027544017045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2499751017147351696011363 3749626525721027544017045)
                  ·
                    refine ⟨175763743393173166125799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3749626525721027544017045 175763743393173166125799)
                    ·
                      rfl

theorem cell23_1026896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 1, 6].length) (baseStart_1026896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026896 prefixEnd_1026896 := by exact prefixLift 1026896
  have htrace : WordTrace (prefixWord ++ tailWord_1026896) baseStart_1026896 baseEnd_1026896 := by
    simpa [prefixWord, tailWord_1026896, baseEnd_1026896] using wordTrace_append hprefix tailTrace_1026896
  have hstable : (prefixWord ++ tailWord_1026896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026896).length < 2 ^ (prefixWord ++ tailWord_1026896).sum := by decide
  have hdescent : baseEnd_1026896 < baseStart_1026896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026903 : List Nat := [1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 4]
def baseStart_1026903 : Nat := 118140960795 + 1026903 * 2 ^ 59
def prefixEnd_1026903 : Nat := 4983230072969 + 3 ^ 40 * 1026903 * 2
def baseEnd_1026903 : Nat := 527294824544100970989865

theorem tailTrace_1026903 : CollatzResearch.WordTrace tailWord_1026903 prefixEnd_1026903 527294824544100970989865 := by
  unfold tailWord_1026903
  simp only [CollatzResearch.WordTrace]
  refine ⟨37454229398713286914709363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24969486265808857943139575 37454229398713286914709363)
  ·
    refine ⟨56181344098069930372064045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37454229398713286914709363 56181344098069930372064045)
    ·
      refine ⟨21068004036776223889524017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56181344098069930372064045 21068004036776223889524017)
      ·
        refine ⟨15801003027582167917143013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21068004036776223889524017 15801003027582167917143013)
        ·
          refine ⟨2962688067671656484464315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15801003027582167917143013 2962688067671656484464315)
          ·
            refine ⟨4444032101507484726696473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2962688067671656484464315 4444032101507484726696473)
            ·
              refine ⟨3333024076130613545022355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4444032101507484726696473 3333024076130613545022355)
              ·
                refine ⟨4999536114195920317533533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3333024076130613545022355 4999536114195920317533533)
                ·
                  refine ⟨1874826042823470119075075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4999536114195920317533533 1874826042823470119075075)
                  ·
                    refine ⟨2812239064235205178612613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1874826042823470119075075 2812239064235205178612613)
                    ·
                      refine ⟨527294824544100970989865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2812239064235205178612613 527294824544100970989865)
                      ·
                        rfl

theorem cell23_1026903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_1026903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026903 prefixEnd_1026903 := by exact prefixLift 1026903
  have htrace : WordTrace (prefixWord ++ tailWord_1026903) baseStart_1026903 baseEnd_1026903 := by
    simpa [prefixWord, tailWord_1026903, baseEnd_1026903] using wordTrace_append hprefix tailTrace_1026903
  have hstable : (prefixWord ++ tailWord_1026903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026903).length < 2 ^ (prefixWord ++ tailWord_1026903).sum := by decide
  have hdescent : baseEnd_1026903 < baseStart_1026903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026920 : List Nat := [2, 1, 4, 2, 1, 3, 1, 3, 1, 1, 4]
def baseStart_1026920 : Nat := 118140960795 + 1026920 * 2 ^ 59
def prefixEnd_1026920 : Nat := 4983230072969 + 3 ^ 40 * 1026920 * 2
def baseEnd_1026920 : Nat := 527303553715227404477287

theorem tailTrace_1026920 : CollatzResearch.WordTrace tailWord_1026920 prefixEnd_1026920 527303553715227404477287 := by
  unfold tailWord_1026920
  simp only [CollatzResearch.WordTrace]
  refine ⟨18727424719825849409039107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24969899626434465878718809 18727424719825849409039107)
  ·
    refine ⟨28091137079738774113558661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18727424719825849409039107 28091137079738774113558661)
    ·
      refine ⟨5267088202451020146292249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28091137079738774113558661 5267088202451020146292249)
      ·
        refine ⟨3950316151838265109719187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5267088202451020146292249 3950316151838265109719187)
        ·
          refine ⟨5925474227757397664578781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3950316151838265109719187 5925474227757397664578781)
          ·
            refine ⟨2222052835409024124217043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5925474227757397664578781 2222052835409024124217043)
            ·
              refine ⟨3333079253113536186325565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2222052835409024124217043 3333079253113536186325565)
              ·
                refine ⟨1249904719917576069872087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3333079253113536186325565 1249904719917576069872087)
                ·
                  refine ⟨1874857079876364104808131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1249904719917576069872087 1874857079876364104808131)
                  ·
                    refine ⟨2812285619814546157212197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1874857079876364104808131 2812285619814546157212197)
                    ·
                      refine ⟨527303553715227404477287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2812285619814546157212197 527303553715227404477287)
                      ·
                        rfl

theorem cell23_1026920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_1026920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026920 prefixEnd_1026920 := by exact prefixLift 1026920
  have htrace : WordTrace (prefixWord ++ tailWord_1026920) baseStart_1026920 baseEnd_1026920 := by
    simpa [prefixWord, tailWord_1026920, baseEnd_1026920] using wordTrace_append hprefix tailTrace_1026920
  have hstable : (prefixWord ++ tailWord_1026920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026920).length < 2 ^ (prefixWord ++ tailWord_1026920).sum := by decide
  have hdescent : baseEnd_1026920 < baseStart_1026920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026930 : List Nat := [3, 2, 1, 2, 1, 1, 5, 2, 2, 4]
def baseStart_1026930 : Nat := 118140960795 + 1026930 * 2 ^ 59
def prefixEnd_1026930 : Nat := 4983230072969 + 3 ^ 40 * 1026930 * 2
def baseEnd_1026930 : Nat := 175769562840590788450747

theorem tailTrace_1026930 : CollatzResearch.WordTrace tailWord_1026930 prefixEnd_1026930 175769562840590788450747 := by
  unfold tailWord_1026930
  simp only [CollatzResearch.WordTrace]
  refine ⟨9363803542403867631485561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24970142779743647017294829 9363803542403867631485561)
  ·
    refine ⟨7022852656802900723614171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9363803542403867631485561 7022852656802900723614171)
    ·
      refine ⟨10534278985204351085421257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7022852656802900723614171 10534278985204351085421257)
      ·
        refine ⟨7900709238903263314065943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10534278985204351085421257 7900709238903263314065943)
        ·
          refine ⟨11851063858354894971098915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7900709238903263314065943 11851063858354894971098915)
          ·
            refine ⟨17776595787532342456648373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11851063858354894971098915 17776595787532342456648373)
            ·
              refine ⟨1666555855081157105310785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17776595787532342456648373 1666555855081157105310785)
              ·
                refine ⟨1249916891310867828983089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1666555855081157105310785 1249916891310867828983089)
                ·
                  refine ⟨937437668483150871737317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1249916891310867828983089 937437668483150871737317)
                  ·
                    refine ⟨175769562840590788450747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 937437668483150871737317 175769562840590788450747)
                    ·
                      rfl

theorem cell23_1026930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 2, 4].length) (baseStart_1026930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026930 prefixEnd_1026930 := by exact prefixLift 1026930
  have htrace : WordTrace (prefixWord ++ tailWord_1026930) baseStart_1026930 baseEnd_1026930 := by
    simpa [prefixWord, tailWord_1026930, baseEnd_1026930] using wordTrace_append hprefix tailTrace_1026930
  have hstable : (prefixWord ++ tailWord_1026930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026930).length < 2 ^ (prefixWord ++ tailWord_1026930).sum := by decide
  have hdescent : baseEnd_1026930 < baseStart_1026930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026937 : List Nat := [1, 2, 1, 3, 2, 4, 2, 1, 3, 2, 2]
def baseStart_1026937 : Nat := 118140960795 + 1026937 * 2 ^ 59
def prefixEnd_1026937 : Nat := 4983230072969 + 3 ^ 40 * 1026937 * 2
def baseEnd_1026937 : Nat := 527312282886353837964709

theorem tailTrace_1026937 : CollatzResearch.WordTrace tailWord_1026937 prefixEnd_1026937 527312282886353837964709 := by
  unfold tailWord_1026937
  simp only [CollatzResearch.WordTrace]
  refine ⟨37455469480590110721447065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24970312987060073814298043 37455469480590110721447065)
  ·
    refine ⟨28091602110442583041085299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37455469480590110721447065 28091602110442583041085299)
    ·
      refine ⟨42137403165663874561627949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28091602110442583041085299 42137403165663874561627949)
      ·
        refine ⟨15801526187123952960610481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42137403165663874561627949 15801526187123952960610481)
        ·
          refine ⟨11851144640342964720457861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15801526187123952960610481 11851144640342964720457861)
          ·
            refine ⟨2222089620064305885085849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11851144640342964720457861 2222089620064305885085849)
            ·
              refine ⟨1666567215048229413814387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2222089620064305885085849 1666567215048229413814387)
              ·
                refine ⟨2499850822572344120721581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1666567215048229413814387 2499850822572344120721581)
                ·
                  refine ⟨937444058464629045270593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2499850822572344120721581 937444058464629045270593)
                  ·
                    refine ⟨703083043848471783952945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 937444058464629045270593 703083043848471783952945)
                    ·
                      refine ⟨527312282886353837964709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 703083043848471783952945 527312282886353837964709)
                      ·
                        rfl

theorem cell23_1026937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 3, 2, 2].length) (baseStart_1026937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026937 prefixEnd_1026937 := by exact prefixLift 1026937
  have htrace : WordTrace (prefixWord ++ tailWord_1026937) baseStart_1026937 baseEnd_1026937 := by
    simpa [prefixWord, tailWord_1026937, baseEnd_1026937] using wordTrace_append hprefix tailTrace_1026937
  have hstable : (prefixWord ++ tailWord_1026937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026937).length < 2 ^ (prefixWord ++ tailWord_1026937).sum := by decide
  have hdescent : baseEnd_1026937 < baseStart_1026937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026956 : List Nat := [2, 2, 1, 2, 1, 2, 2, 2, 2, 7]
def baseStart_1026956 : Nat := 118140960795 + 1026956 * 2 ^ 59
def prefixEnd_1026956 : Nat := 4983230072969 + 3 ^ 40 * 1026956 * 2
def baseEnd_1026956 : Nat := 175774013006263087875707

theorem tailTrace_1026956 : CollatzResearch.WordTrace tailWord_1026956 prefixEnd_1026956 175774013006263087875707 := by
  unfold tailWord_1026956
  simp only [CollatzResearch.WordTrace]
  refine ⟨18728081233760638483194361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24970774978347517977592481 18728081233760638483194361)
  ·
    refine ⟨14046060925320478862395771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18728081233760638483194361 14046060925320478862395771)
    ·
      refine ⟨21069091387980718293593657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14046060925320478862395771 21069091387980718293593657)
      ·
        refine ⟨15801818540985538720195243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21069091387980718293593657 15801818540985538720195243)
        ·
          refine ⟨23702727811478308080292865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15801818540985538720195243 23702727811478308080292865)
          ·
            refine ⟨17777045858608731060219649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23702727811478308080292865 17777045858608731060219649)
            ·
              refine ⟨13332784393956548295164737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17777045858608731060219649 13332784393956548295164737)
              ·
                refine ⟨9999588295467411221373553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13332784393956548295164737 9999588295467411221373553)
                ·
                  refine ⟨7499691221600558416030165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9999588295467411221373553 7499691221600558416030165)
                  ·
                    refine ⟨175774013006263087875707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7499691221600558416030165 175774013006263087875707)
                    ·
                      rfl

theorem cell23_1026956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 2, 7].length) (baseStart_1026956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1026956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1026956 prefixEnd_1026956 := by exact prefixLift 1026956
  have htrace : WordTrace (prefixWord ++ tailWord_1026956) baseStart_1026956 baseEnd_1026956 := by
    simpa [prefixWord, tailWord_1026956, baseEnd_1026956] using wordTrace_append hprefix tailTrace_1026956
  have hstable : (prefixWord ++ tailWord_1026956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026956).length < 2 ^ (prefixWord ++ tailWord_1026956).sum := by decide
  have hdescent : baseEnd_1026956 < baseStart_1026956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027021 : List Nat := [1, 6, 3, 1, 1, 1, 1, 2, 1, 3, 3]
def baseStart_1027021 : Nat := 118140960795 + 1027021 * 2 ^ 59
def prefixEnd_1027021 : Nat := 4983230072969 + 3 ^ 40 * 1027021 * 2
def baseEnd_1027021 : Nat := 527355415261331509314323

theorem tailTrace_1027021 : CollatzResearch.WordTrace tailWord_1027021 prefixEnd_1027021 527355415261331509314323 := by
  unfold tailWord_1027021
  simp only [CollatzResearch.WordTrace]
  refine ⟨37458533212285793067504917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24972355474857195378336611 37458533212285793067504917)
  ·
    refine ⟨1755868744325896550039293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37458533212285793067504917 1755868744325896550039293)
    ·
      refine ⟨658450779122211206264735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1755868744325896550039293 658450779122211206264735)
      ·
        refine ⟨987676168683316809397103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 658450779122211206264735 987676168683316809397103)
        ·
          refine ⟨1481514253024975214095655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 987676168683316809397103 1481514253024975214095655)
          ·
            refine ⟨2222271379537462821143483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1481514253024975214095655 2222271379537462821143483)
            ·
              refine ⟨3333407069306194231715225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2222271379537462821143483 3333407069306194231715225)
              ·
                refine ⟨2500055301979645673786419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3333407069306194231715225 2500055301979645673786419)
                ·
                  refine ⟨3750082952969468510679629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2500055301979645673786419 3750082952969468510679629)
                  ·
                    refine ⟨1406281107363550691504861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3750082952969468510679629 1406281107363550691504861)
                    ·
                      refine ⟨527355415261331509314323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1406281107363550691504861 527355415261331509314323)
                      ·
                        rfl

theorem cell23_1027021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_1027021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1027021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1027021 prefixEnd_1027021 := by exact prefixLift 1027021
  have htrace : WordTrace (prefixWord ++ tailWord_1027021) baseStart_1027021 baseEnd_1027021 := by
    simpa [prefixWord, tailWord_1027021, baseEnd_1027021] using wordTrace_append hprefix tailTrace_1027021
  have hstable : (prefixWord ++ tailWord_1027021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027021).length < 2 ^ (prefixWord ++ tailWord_1027021).sum := by decide
  have hdescent : baseEnd_1027021 < baseStart_1027021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027061 : List Nat := [1, 3, 5, 2, 1, 1, 2, 1, 1, 4, 2]
def baseStart_1027061 : Nat := 118140960795 + 1027061 * 2 ^ 59
def prefixEnd_1027061 : Nat := 4983230072969 + 3 ^ 40 * 1027061 * 2
def baseEnd_1027061 : Nat := 527375954487511352814139

theorem tailTrace_1027061 : CollatzResearch.WordTrace tailWord_1027061 prefixEnd_1027061 527375954487511352814139 := by
  unfold tailWord_1027061
  simp only [CollatzResearch.WordTrace]
  refine ⟨37459992132140879898961037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24973328088093919932640691 37459992132140879898961037)
  ·
    refine ⟨14047497049552829962110389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37459992132140879898961037 14047497049552829962110389)
    ·
      refine ⟨1316952848395577808947849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14047497049552829962110389 1316952848395577808947849)
      ·
        refine ⟨987714636296683356710887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1316952848395577808947849 987714636296683356710887)
        ·
          refine ⟨1481571954445025035066331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 987714636296683356710887 1481571954445025035066331)
          ·
            refine ⟨2222357931667537552599497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1481571954445025035066331 2222357931667537552599497)
            ·
              refine ⟨1666768448750653164449623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2222357931667537552599497 1666768448750653164449623)
              ·
                refine ⟨2500152673125979746674435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1666768448750653164449623 2500152673125979746674435)
                ·
                  refine ⟨3750229009688969620011653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2500152673125979746674435 3750229009688969620011653)
                  ·
                    refine ⟨703167939316681803752185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3750229009688969620011653 703167939316681803752185)
                    ·
                      refine ⟨527375954487511352814139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 703167939316681803752185 527375954487511352814139)
                      ·
                        rfl

theorem cell23_1027061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_1027061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1027061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1027061 prefixEnd_1027061 := by exact prefixLift 1027061
  have htrace : WordTrace (prefixWord ++ tailWord_1027061) baseStart_1027061 baseEnd_1027061 := by
    simpa [prefixWord, tailWord_1027061, baseEnd_1027061] using wordTrace_append hprefix tailTrace_1027061
  have hstable : (prefixWord ++ tailWord_1027061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027061).length < 2 ^ (prefixWord ++ tailWord_1027061).sum := by decide
  have hdescent : baseEnd_1027061 < baseStart_1027061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027080 : List Nat := [2, 1, 3, 2, 1, 3, 3, 1, 2, 5]
def baseStart_1027080 : Nat := 118140960795 + 1027080 * 2 ^ 59
def prefixEnd_1027080 : Nat := 4983230072969 + 3 ^ 40 * 1027080 * 2
def baseEnd_1027080 : Nat := 175795236873315592825517

theorem tailTrace_1027080 : CollatzResearch.WordTrace tailWord_1027080 prefixEnd_1027080 175795236873315592825517 := by
  unfold tailWord_1027080
  simp only [CollatzResearch.WordTrace]
  refine ⟨18730342559536023071951347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24973790079381364095935129 18730342559536023071951347)
  ·
    refine ⟨28095513839304034607927021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18730342559536023071951347 28095513839304034607927021)
    ·
      refine ⟨10535817689739012977972633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28095513839304034607927021 10535817689739012977972633)
      ·
        refine ⟨7901863267304259733479475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10535817689739012977972633 7901863267304259733479475)
        ·
          refine ⟨11852794900956389600219213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7901863267304259733479475 11852794900956389600219213)
          ·
            refine ⟨4444798087858646100082205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11852794900956389600219213 4444798087858646100082205)
            ·
              refine ⟨1666799282946992287530827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4444798087858646100082205 1666799282946992287530827)
              ·
                refine ⟨2500198924420488431296241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1666799282946992287530827 2500198924420488431296241)
                ·
                  refine ⟨1875149193315366323472181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2500198924420488431296241 1875149193315366323472181)
                  ·
                    refine ⟨175795236873315592825517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1875149193315366323472181 175795236873315592825517)
                    ·
                      rfl

theorem cell23_1027080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 2, 5].length) (baseStart_1027080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1027080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1027080 prefixEnd_1027080 := by exact prefixLift 1027080
  have htrace : WordTrace (prefixWord ++ tailWord_1027080) baseStart_1027080 baseEnd_1027080 := by
    simpa [prefixWord, tailWord_1027080, baseEnd_1027080] using wordTrace_append hprefix tailTrace_1027080
  have hstable : (prefixWord ++ tailWord_1027080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027080).length < 2 ^ (prefixWord ++ tailWord_1027080).sum := by decide
  have hdescent : baseEnd_1027080 < baseStart_1027080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027200 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 6, 4]
def baseStart_1027200 : Nat := 118140960795 + 1027200 * 2 ^ 59
def prefixEnd_1027200 : Nat := 4983230072969 + 3 ^ 40 * 1027200 * 2
def baseEnd_1027200 : Nat := 175815776099495436325333

theorem tailTrace_1027200 : CollatzResearch.WordTrace tailWord_1027200 prefixEnd_1027200 175815776099495436325333 := by
  unfold tailWord_1027200
  simp only [CollatzResearch.WordTrace]
  refine ⟨18732530939318653319135527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24976707919091537758847369 18732530939318653319135527)
  ·
    refine ⟨28098796408977979978703291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18732530939318653319135527 28098796408977979978703291)
    ·
      refine ⟨42148194613466969968054937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28098796408977979978703291 42148194613466969968054937)
      ·
        refine ⟨31611145960100227476041203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42148194613466969968054937 31611145960100227476041203)
        ·
          refine ⟨47416718940150341214061805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31611145960100227476041203 47416718940150341214061805)
          ·
            refine ⟨17781269602556377955273177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47416718940150341214061805 17781269602556377955273177)
            ·
              refine ⟨13335952201917283466454883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17781269602556377955273177 13335952201917283466454883)
              ·
                refine ⟨20003928302875925199682325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13335952201917283466454883 20003928302875925199682325)
                ·
                  refine ⟨937684139197308993735109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 20003928302875925199682325 937684139197308993735109)
                  ·
                    refine ⟨175815776099495436325333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 937684139197308993735109 175815776099495436325333)
                    ·
                      rfl

theorem cell23_1027200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 6, 4].length) (baseStart_1027200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1027200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1027200 prefixEnd_1027200 := by exact prefixLift 1027200
  have htrace : WordTrace (prefixWord ++ tailWord_1027200) baseStart_1027200 baseEnd_1027200 := by
    simpa [prefixWord, tailWord_1027200, baseEnd_1027200] using wordTrace_append hprefix tailTrace_1027200
  have hstable : (prefixWord ++ tailWord_1027200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027200).length < 2 ^ (prefixWord ++ tailWord_1027200).sum := by decide
  have hdescent : baseEnd_1027200 < baseStart_1027200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027204 : List Nat := [2, 3, 2, 1, 2, 3, 3, 1, 1, 5]
def baseStart_1027204 : Nat := 118140960795 + 1027204 * 2 ^ 59
def prefixEnd_1027204 : Nat := 4983230072969 + 3 ^ 40 * 1027204 * 2
def baseEnd_1027204 : Nat := 175816460740368097775327

theorem tailTrace_1027204 : CollatzResearch.WordTrace tailWord_1027204 prefixEnd_1027204 175816460740368097775327 := by
  unfold tailWord_1027204
  simp only [CollatzResearch.WordTrace]
  refine ⟨18732603885311407660708333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24976805180415210214277777 18732603885311407660708333)
  ·
    refine ⟨7024726456991777872765625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18732603885311407660708333 7024726456991777872765625)
    ·
      refine ⟨5268544842743833404574219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7024726456991777872765625 5268544842743833404574219)
      ·
        refine ⟨7902817264115750106861329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5268544842743833404574219 7902817264115750106861329)
        ·
          refine ⟨5927112948086812580145997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7902817264115750106861329 5927112948086812580145997)
          ·
            refine ⟨2222667355532554717554749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5927112948086812580145997 2222667355532554717554749)
            ·
              refine ⟨833500258324708019083031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2222667355532554717554749 833500258324708019083031)
              ·
                refine ⟨1250250387487062028624547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 833500258324708019083031 1250250387487062028624547)
                ·
                  refine ⟨1875375581230593042936821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1250250387487062028624547 1875375581230593042936821)
                  ·
                    refine ⟨175816460740368097775327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1875375581230593042936821 175816460740368097775327)
                    ·
                      rfl

theorem cell23_1027204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_1027204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1027204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1027204 prefixEnd_1027204 := by exact prefixLift 1027204
  have htrace : WordTrace (prefixWord ++ tailWord_1027204) baseStart_1027204 baseEnd_1027204 := by
    simpa [prefixWord, tailWord_1027204, baseEnd_1027204] using wordTrace_append hprefix tailTrace_1027204
  have hstable : (prefixWord ++ tailWord_1027204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027204).length < 2 ^ (prefixWord ++ tailWord_1027204).sum := by decide
  have hdescent : baseEnd_1027204 < baseStart_1027204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027218 : List Nat := [3, 2, 3, 1, 1, 2, 4, 2, 1, 1, 3]
def baseStart_1027218 : Nat := 118140960795 + 1027218 * 2 ^ 59
def prefixEnd_1027218 : Nat := 4983230072969 + 3 ^ 40 * 1027218 * 2
def baseEnd_1027218 : Nat := 527456570950267238550917

theorem tailTrace_1027218 : CollatzResearch.WordTrace tailWord_1027218 prefixEnd_1027218 527456570950267238550917 := by
  unfold tailWord_1027218
  simp only [CollatzResearch.WordTrace]
  refine ⟨9366429598143023928106577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24977145595048063808284205 9366429598143023928106577)
  ·
    refine ⟨7024822198607267946079933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9366429598143023928106577 7024822198607267946079933)
    ·
      refine ⟨2634308324477725479779975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7024822198607267946079933 2634308324477725479779975)
      ·
        refine ⟨3951462486716588219669963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2634308324477725479779975 3951462486716588219669963)
        ·
          refine ⟨5927193730074882329504945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3951462486716588219669963 5927193730074882329504945)
          ·
            refine ⟨4445395297556161747128709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5927193730074882329504945 4445395297556161747128709)
            ·
              refine ⟨833511618291780327586633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4445395297556161747128709 833511618291780327586633)
              ·
                refine ⟨625133713718835245689975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 833511618291780327586633 625133713718835245689975)
                ·
                  refine ⟨937700570578252868534963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 625133713718835245689975 937700570578252868534963)
                  ·
                    refine ⟨1406550855867379302802445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 937700570578252868534963 1406550855867379302802445)
                    ·
                      refine ⟨527456570950267238550917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1406550855867379302802445 527456570950267238550917)
                      ·
                        rfl

theorem cell23_1027218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_1027218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1027218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1027218 prefixEnd_1027218 := by exact prefixLift 1027218
  have htrace : WordTrace (prefixWord ++ tailWord_1027218) baseStart_1027218 baseEnd_1027218 := by
    simpa [prefixWord, tailWord_1027218, baseEnd_1027218] using wordTrace_append hprefix tailTrace_1027218
  have hstable : (prefixWord ++ tailWord_1027218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027218).length < 2 ^ (prefixWord ++ tailWord_1027218).sum := by decide
  have hdescent : baseEnd_1027218 < baseStart_1027218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027234 : List Nat := [3, 3, 1, 3, 2, 1, 2, 1, 1, 6]
def baseStart_1027234 : Nat := 118140960795 + 1027234 * 2 ^ 59
def prefixEnd_1027234 : Nat := 4983230072969 + 3 ^ 40 * 1027234 * 2
def baseEnd_1027234 : Nat := 175821595546913058650281

theorem tailTrace_1027234 : CollatzResearch.WordTrace tailWord_1027234 prefixEnd_1027234 175821595546913058650281 := by
  unfold tailWord_1027234
  simp only [CollatzResearch.WordTrace]
  refine ⟨9366575490128532611252189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24977534640342753630005837 9366575490128532611252189)
  ·
    refine ⟨3512465808798199729219571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9366575490128532611252189 3512465808798199729219571)
    ·
      refine ⟨5268698713197299593829357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3512465808798199729219571 5268698713197299593829357)
      ·
        refine ⟨1975762017448987347686009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5268698713197299593829357 1975762017448987347686009)
        ·
          refine ⟨1481821513086740510764507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1975762017448987347686009 1481821513086740510764507)
          ·
            refine ⟨2222732269630110766146761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1481821513086740510764507 2222732269630110766146761)
            ·
              refine ⟨1667049202222583074610071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2222732269630110766146761 1667049202222583074610071)
              ·
                refine ⟨2500573803333874611915107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1667049202222583074610071 2500573803333874611915107)
                ·
                  refine ⟨3750860705000811917872661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2500573803333874611915107 3750860705000811917872661)
                  ·
                    refine ⟨175821595546913058650281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3750860705000811917872661 175821595546913058650281)
                    ·
                      rfl

theorem cell23_1027234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_1027234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1027234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1027234 prefixEnd_1027234 := by exact prefixLift 1027234
  have htrace : WordTrace (prefixWord ++ tailWord_1027234) baseStart_1027234 baseEnd_1027234 := by
    simpa [prefixWord, tailWord_1027234, baseEnd_1027234] using wordTrace_append hprefix tailTrace_1027234
  have hstable : (prefixWord ++ tailWord_1027234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027234).length < 2 ^ (prefixWord ++ tailWord_1027234).sum := by decide
  have hdescent : baseEnd_1027234 < baseStart_1027234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027237 : List Nat := [1, 3, 1, 2, 1, 5, 2, 1, 1, 2, 4]
def baseStart_1027237 : Nat := 118140960795 + 1027237 * 2 ^ 59
def prefixEnd_1027237 : Nat := 4983230072969 + 3 ^ 40 * 1027237 * 2
def baseEnd_1027237 : Nat := 527466327082702664213329

theorem tailTrace_1027237 : CollatzResearch.WordTrace tailWord_1027237 prefixEnd_1027237 527466327082702664213329 := by
  unfold tailWord_1027237
  simp only [CollatzResearch.WordTrace]
  refine ⟨37466411379503261957367965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24977607586335507971578643 37466411379503261957367965)
  ·
    refine ⟨14049904267313723234012987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37466411379503261957367965 14049904267313723234012987)
    ·
      refine ⟨21074856400970584851019481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14049904267313723234012987 21074856400970584851019481)
      ·
        refine ⟨15806142300727938638264611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21074856400970584851019481 15806142300727938638264611)
        ·
          refine ⟨23709213451091907957396917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15806142300727938638264611 23709213451091907957396917)
          ·
            refine ⟨2222738761039866371005961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23709213451091907957396917 2222738761039866371005961)
            ·
              refine ⟨1667054070779899778254471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2222738761039866371005961 1667054070779899778254471)
              ·
                refine ⟨2500581106169849667381707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1667054070779899778254471 2500581106169849667381707)
                ·
                  refine ⟨3750871659254774501072561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2500581106169849667381707 3750871659254774501072561)
                  ·
                    refine ⟨2813153744441080875804421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3750871659254774501072561 2813153744441080875804421)
                    ·
                      refine ⟨527466327082702664213329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2813153744441080875804421 527466327082702664213329)
                      ·
                        rfl

theorem cell23_1027237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 2, 4].length) (baseStart_1027237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1027237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1027237 prefixEnd_1027237 := by exact prefixLift 1027237
  have htrace : WordTrace (prefixWord ++ tailWord_1027237) baseStart_1027237 baseEnd_1027237 := by
    simpa [prefixWord, tailWord_1027237, baseEnd_1027237] using wordTrace_append hprefix tailTrace_1027237
  have hstable : (prefixWord ++ tailWord_1027237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027237).length < 2 ^ (prefixWord ++ tailWord_1027237).sum := by decide
  have hdescent : baseEnd_1027237 < baseStart_1027237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027257 : List Nat := [1, 2, 1, 4, 1, 3, 2, 2, 1, 3, 3]
def baseStart_1027257 : Nat := 118140960795 + 1027257 * 2 ^ 59
def prefixEnd_1027257 : Nat := 4983230072969 + 3 ^ 40 * 1027257 * 2
def baseEnd_1027257 : Nat := 527476596695792585963237

theorem tailTrace_1027257 : CollatzResearch.WordTrace tailWord_1027257 prefixEnd_1027257 527476596695792585963237 := by
  unfold tailWord_1027257
  simp only [CollatzResearch.WordTrace]
  refine ⟨37467140839430805373096025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24978093892953870248730683 37467140839430805373096025)
  ·
    refine ⟨28100355629573104029822019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37467140839430805373096025 28100355629573104029822019)
    ·
      refine ⟨42150533444359656044733029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28100355629573104029822019 42150533444359656044733029)
      ·
        refine ⟨7903225020817435508387443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42150533444359656044733029 7903225020817435508387443)
        ·
          refine ⟨11854837531226153262581165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7903225020817435508387443 11854837531226153262581165)
          ·
            refine ⟨4445564074209807473467937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11854837531226153262581165 4445564074209807473467937)
            ·
              refine ⟨3334173055657355605100953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4445564074209807473467937 3334173055657355605100953)
              ·
                refine ⟨2500629791743016703825715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3334173055657355605100953 2500629791743016703825715)
                ·
                  refine ⟨3750944687614525055738573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2500629791743016703825715 3750944687614525055738573)
                  ·
                    refine ⟨1406604257855446895901965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3750944687614525055738573 1406604257855446895901965)
                    ·
                      refine ⟨527476596695792585963237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1406604257855446895901965 527476596695792585963237)
                      ·
                        rfl

theorem cell23_1027257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_1027257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1027257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1027257 prefixEnd_1027257 := by exact prefixLift 1027257
  have htrace : WordTrace (prefixWord ++ tailWord_1027257) baseStart_1027257 baseEnd_1027257 := by
    simpa [prefixWord, tailWord_1027257, baseEnd_1027257] using wordTrace_append hprefix tailTrace_1027257
  have hstable : (prefixWord ++ tailWord_1027257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027257).length < 2 ^ (prefixWord ++ tailWord_1027257).sum := by decide
  have hdescent : baseEnd_1027257 < baseStart_1027257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027267 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 5, 3, 2]
def baseStart_1027267 : Nat := 118140960795 + 1027267 * 2 ^ 59
def prefixEnd_1027267 : Nat := 4983230072969 + 3 ^ 40 * 1027267 * 2
def baseEnd_1027267 : Nat := 527481731502337546838191

theorem tailTrace_1027267 : CollatzResearch.WordTrace tailWord_1027267 prefixEnd_1027267 527481731502337546838191 := by
  unfold tailWord_1027267
  simp only [CollatzResearch.WordTrace]
  refine ⟨37467505569394577080960055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24978337046263051387306703 37467505569394577080960055)
  ·
    refine ⟨56201258354091865621440083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37467505569394577080960055 56201258354091865621440083)
    ·
      refine ⟨84301887531137798432160125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56201258354091865621440083 84301887531137798432160125)
      ·
        refine ⟨31613207824176674412060047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84301887531137798432160125 31613207824176674412060047)
        ·
          refine ⟨47419811736265011618090071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31613207824176674412060047 47419811736265011618090071)
          ·
            refine ⟨71129717604397517427135107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47419811736265011618090071 71129717604397517427135107)
            ·
              refine ⟨106694576406596276140702661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71129717604397517427135107 106694576406596276140702661)
              ·
                refine ⟨20005233076236801776381749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106694576406596276140702661 20005233076236801776381749)
                ·
                  refine ⟨1875490600897200166535789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20005233076236801776381749 1875490600897200166535789)
                  ·
                    refine ⟨703308975336450062450921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1875490600897200166535789 703308975336450062450921)
                    ·
                      refine ⟨527481731502337546838191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 703308975336450062450921 527481731502337546838191)
                      ·
                        rfl

theorem cell23_1027267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 3, 2].length) (baseStart_1027267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1027267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1027267 prefixEnd_1027267 := by exact prefixLift 1027267
  have htrace : WordTrace (prefixWord ++ tailWord_1027267) baseStart_1027267 baseEnd_1027267 := by
    simpa [prefixWord, tailWord_1027267, baseEnd_1027267] using wordTrace_append hprefix tailTrace_1027267
  have hstable : (prefixWord ++ tailWord_1027267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027267).length < 2 ^ (prefixWord ++ tailWord_1027267).sum := by decide
  have hdescent : baseEnd_1027267 < baseStart_1027267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027268 : List Nat := [2, 3, 3, 1, 4, 1, 1, 2, 2, 4]
def baseStart_1027268 : Nat := 118140960795 + 1027268 * 2 ^ 59
def prefixEnd_1027268 : Nat := 4983230072969 + 3 ^ 40 * 1027268 * 2
def baseEnd_1027268 : Nat := 175827414994330680975229

theorem tailTrace_1027268 : CollatzResearch.WordTrace tailWord_1027268 prefixEnd_1027268 175827414994330680975229 := by
  unfold tailWord_1027268
  simp only [CollatzResearch.WordTrace]
  refine ⟨18733771021195477125873229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24978361361593969501164305 18733771021195477125873229)
  ·
    refine ⟨7025164132948303922202461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18733771021195477125873229 7025164132948303922202461)
    ·
      refine ⟨2634436549855613970825923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7025164132948303922202461 2634436549855613970825923)
      ·
        refine ⟨3951654824783420956238885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2634436549855613970825923 3951654824783420956238885)
        ·
          refine ⟨740935279646891429294791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3951654824783420956238885 740935279646891429294791)
          ·
            refine ⟨1111402919470337143942187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740935279646891429294791 1111402919470337143942187)
            ·
              refine ⟨1667104379205505715913281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1111402919470337143942187 1667104379205505715913281)
              ·
                refine ⟨1250328284404129286934961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1667104379205505715913281 1250328284404129286934961)
                ·
                  refine ⟨937746213303096965201221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1250328284404129286934961 937746213303096965201221)
                  ·
                    refine ⟨175827414994330680975229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 937746213303096965201221 175827414994330680975229)
                    ·
                      rfl

theorem cell23_1027268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_1027268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1027268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1027268 prefixEnd_1027268 := by exact prefixLift 1027268
  have htrace : WordTrace (prefixWord ++ tailWord_1027268) baseStart_1027268 baseEnd_1027268 := by
    simpa [prefixWord, tailWord_1027268, baseEnd_1027268] using wordTrace_append hprefix tailTrace_1027268
  have hstable : (prefixWord ++ tailWord_1027268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027268).length < 2 ^ (prefixWord ++ tailWord_1027268).sum := by decide
  have hdescent : baseEnd_1027268 < baseStart_1027268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027274 : List Nat := [3, 1, 2, 1, 3, 3, 1, 1, 4, 1, 3]
def baseStart_1027274 : Nat := 118140960795 + 1027274 * 2 ^ 59
def prefixEnd_1027274 : Nat := 4983230072969 + 3 ^ 40 * 1027274 * 2
def baseEnd_1027274 : Nat := 527485325866919019450659

theorem tailTrace_1027274 : CollatzResearch.WordTrace tailWord_1027274 prefixEnd_1027274 527485325866919019450659 := by
  unfold tailWord_1027274
  simp only [CollatzResearch.WordTrace]
  refine ⟨9366940220092304319116219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24978507253579478184309917 9366940220092304319116219)
  ·
    refine ⟨14050410330138456478674329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9366940220092304319116219 14050410330138456478674329)
    ·
      refine ⟨10537807747603842359005747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14050410330138456478674329 10537807747603842359005747)
      ·
        refine ⟨15806711621405763538508621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10537807747603842359005747 15806711621405763538508621)
        ·
          refine ⟨5927516858027161326940733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15806711621405763538508621 5927516858027161326940733)
          ·
            refine ⟨2222818821760185497602775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5927516858027161326940733 2222818821760185497602775)
            ·
              refine ⟨3334228232640278246404163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2222818821760185497602775 3334228232640278246404163)
              ·
                refine ⟨5001342348960417369606245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3334228232640278246404163 5001342348960417369606245)
                ·
                  refine ⟨937751690430078256801171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5001342348960417369606245 937751690430078256801171)
                  ·
                    refine ⟨1406627535645117385201757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 937751690430078256801171 1406627535645117385201757)
                    ·
                      refine ⟨527485325866919019450659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1406627535645117385201757 527485325866919019450659)
                      ·
                        rfl

theorem cell23_1027274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 4, 1, 3].length) (baseStart_1027274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1027274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1027274 prefixEnd_1027274 := by exact prefixLift 1027274
  have htrace : WordTrace (prefixWord ++ tailWord_1027274) baseStart_1027274 baseEnd_1027274 := by
    simpa [prefixWord, tailWord_1027274, baseEnd_1027274] using wordTrace_append hprefix tailTrace_1027274
  have hstable : (prefixWord ++ tailWord_1027274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027274).length < 2 ^ (prefixWord ++ tailWord_1027274).sum := by decide
  have hdescent : baseEnd_1027274 < baseStart_1027274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027377 : List Nat := [1, 2, 2, 3, 3, 1, 1, 2, 1, 2, 5]
def baseStart_1027377 : Nat := 118140960795 + 1027377 * 2 ^ 59
def prefixEnd_1027377 : Nat := 4983230072969 + 3 ^ 40 * 1027377 * 2
def baseEnd_1027377 : Nat := 527538214374332116462685

theorem tailTrace_1027377 : CollatzResearch.WordTrace tailWord_1027377 prefixEnd_1027377 527538214374332116462685 := by
  unfold tailWord_1027377
  simp only [CollatzResearch.WordTrace]
  refine ⟨37471517598996065867464385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24981011732664043911642923 37471517598996065867464385)
  ·
    refine ⟨28103638199247049400598289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37471517598996065867464385 28103638199247049400598289)
    ·
      refine ⟨21077728649435287050448717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28103638199247049400598289 21077728649435287050448717)
      ·
        refine ⟨7904148243538232643918269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21077728649435287050448717 7904148243538232643918269)
        ·
          refine ⟨2964055591326837241469351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7904148243538232643918269 2964055591326837241469351)
          ·
            refine ⟨4446083386990255862204027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2964055591326837241469351 4446083386990255862204027)
            ·
              refine ⟨6669125080485383793306041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4446083386990255862204027 6669125080485383793306041)
              ·
                refine ⟨5001843810364037844979531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6669125080485383793306041 5001843810364037844979531)
                ·
                  refine ⟨7502765715546056767469297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5001843810364037844979531 7502765715546056767469297)
                  ·
                    refine ⟨5627074286659542575601973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7502765715546056767469297 5627074286659542575601973)
                    ·
                      refine ⟨527538214374332116462685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5627074286659542575601973 527538214374332116462685)
                      ·
                        rfl

theorem cell23_1027377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_1027377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1027377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1027377 prefixEnd_1027377 := by exact prefixLift 1027377
  have htrace : WordTrace (prefixWord ++ tailWord_1027377) baseStart_1027377 baseEnd_1027377 := by
    simpa [prefixWord, tailWord_1027377, baseEnd_1027377] using wordTrace_append hprefix tailTrace_1027377
  have hstable : (prefixWord ++ tailWord_1027377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027377).length < 2 ^ (prefixWord ++ tailWord_1027377).sum := by decide
  have hdescent : baseEnd_1027377 < baseStart_1027377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027382 : List Nat := [5, 1, 2, 3, 1, 1, 2, 2, 2, 2, 2]
def baseStart_1027382 : Nat := 118140960795 + 1027382 * 2 ^ 59
def prefixEnd_1027382 : Nat := 4983230072969 + 3 ^ 40 * 1027382 * 2
def baseEnd_1027382 : Nat := 527540781777604596900163

theorem tailTrace_1027382 : CollatzResearch.WordTrace tailWord_1027382 prefixEnd_1027382 527540781777604596900163 := by
  unfold tailWord_1027382
  simp only [CollatzResearch.WordTrace]
  refine ⟨2341981247748621982587275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24981133309318634480930933 2341981247748621982587275)
  ·
    refine ⟨3512971871622932973880913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2341981247748621982587275 3512971871622932973880913)
    ·
      refine ⟨2634728903717199730410685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3512971871622932973880913 2634728903717199730410685)
      ·
        refine ⟨988023338893949898904007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2634728903717199730410685 988023338893949898904007)
        ·
          refine ⟨1482035008340924848356011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 988023338893949898904007 1482035008340924848356011)
          ·
            refine ⟨2223052512511387272534017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1482035008340924848356011 2223052512511387272534017)
            ·
              refine ⟨1667289384383540454400513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2223052512511387272534017 1667289384383540454400513)
              ·
                refine ⟨1250467038287655340800385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1667289384383540454400513 1250467038287655340800385)
                ·
                  refine ⟨937850278715741505600289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1250467038287655340800385 937850278715741505600289)
                  ·
                    refine ⟨703387709036806129200217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 937850278715741505600289 703387709036806129200217)
                    ·
                      refine ⟨527540781777604596900163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 703387709036806129200217 527540781777604596900163)
                      ·
                        rfl

theorem cell23_1027382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_1027382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1027382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1027382 prefixEnd_1027382 := by exact prefixLift 1027382
  have htrace : WordTrace (prefixWord ++ tailWord_1027382) baseStart_1027382 baseEnd_1027382 := by
    simpa [prefixWord, tailWord_1027382, baseEnd_1027382] using wordTrace_append hprefix tailTrace_1027382
  have hstable : (prefixWord ++ tailWord_1027382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027382).length < 2 ^ (prefixWord ++ tailWord_1027382).sum := by decide
  have hdescent : baseEnd_1027382 < baseStart_1027382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027397 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 7, 4]
def baseStart_1027397 : Nat := 118140960795 + 1027397 * 2 ^ 59
def prefixEnd_1027397 : Nat := 4983230072969 + 3 ^ 40 * 1027397 * 2
def baseEnd_1027397 : Nat := 175849494662474012737531

theorem tailTrace_1027397 : CollatzResearch.WordTrace tailWord_1027397 prefixEnd_1027397 175849494662474012737531 := by
  unfold tailWord_1027397
  simp only [CollatzResearch.WordTrace]
  refine ⟨37472247058923609283192445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24981498039282406188794963 37472247058923609283192445)
  ·
    refine ⟨14052092647096353481197167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37472247058923609283192445 14052092647096353481197167)
    ·
      refine ⟨21078138970644530221795751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14052092647096353481197167 21078138970644530221795751)
      ·
        refine ⟨31617208455966795332693627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21078138970644530221795751 31617208455966795332693627)
        ·
          refine ⟨47425812683950192999040441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31617208455966795332693627 47425812683950192999040441)
          ·
            refine ⟨35569359512962644749280331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47425812683950192999040441 35569359512962644749280331)
            ·
              refine ⟨53354039269443967123920497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35569359512962644749280331 53354039269443967123920497)
              ·
                refine ⟨40015529452082975342940373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53354039269443967123920497 40015529452082975342940373)
                ·
                  refine ⟨937863971533194734600165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 40015529452082975342940373 937863971533194734600165)
                  ·
                    refine ⟨175849494662474012737531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 937863971533194734600165 175849494662474012737531)
                    ·
                      rfl

theorem cell23_1027397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 7, 4].length) (baseStart_1027397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1027397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1027397 prefixEnd_1027397 := by exact prefixLift 1027397
  have htrace : WordTrace (prefixWord ++ tailWord_1027397) baseStart_1027397 baseEnd_1027397 := by
    simpa [prefixWord, tailWord_1027397, baseEnd_1027397] using wordTrace_append hprefix tailTrace_1027397
  have hstable : (prefixWord ++ tailWord_1027397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027397).length < 2 ^ (prefixWord ++ tailWord_1027397).sum := by decide
  have hdescent : baseEnd_1027397 < baseStart_1027397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027404 : List Nat := [2, 2, 1, 3, 2, 2, 1, 1, 1, 6, 2]
def baseStart_1027404 : Nat := 118140960795 + 1027404 * 2 ^ 59
def prefixEnd_1027404 : Nat := 4983230072969 + 3 ^ 40 * 1027404 * 2
def baseEnd_1027404 : Nat := 527552078352003510825061

theorem tailTrace_1027404 : CollatzResearch.WordTrace tailWord_1027404 prefixEnd_1027404 527552078352003510825061 := by
  unfold tailWord_1027404
  simp only [CollatzResearch.WordTrace]
  refine ⟨18736251184949124739348633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24981668246598832985798177 18736251184949124739348633)
  ·
    refine ⟨14052188388711843554511475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18736251184949124739348633 14052188388711843554511475)
    ·
      refine ⟨21078282583067765331767213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14052188388711843554511475 21078282583067765331767213)
      ·
        refine ⟨7904355968650411999412705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21078282583067765331767213 7904355968650411999412705)
        ·
          refine ⟨5928266976487808999559529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7904355968650411999412705 5928266976487808999559529)
          ·
            refine ⟨4446200232365856749669647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5928266976487808999559529 4446200232365856749669647)
            ·
              refine ⟨6669300348548785124504471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4446200232365856749669647 6669300348548785124504471)
              ·
                refine ⟨10003950522823177686756707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6669300348548785124504471 10003950522823177686756707)
                ·
                  refine ⟨15005925784234766530135061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10003950522823177686756707 15005925784234766530135061)
                  ·
                    refine ⟨703402771136004681100081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15005925784234766530135061 703402771136004681100081)
                    ·
                      refine ⟨527552078352003510825061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 703402771136004681100081 527552078352003510825061)
                      ·
                        rfl

theorem cell23_1027404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_1027404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1027404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1027404 prefixEnd_1027404 := by exact prefixLift 1027404
  have htrace : WordTrace (prefixWord ++ tailWord_1027404) baseStart_1027404 baseEnd_1027404 := by
    simpa [prefixWord, tailWord_1027404, baseEnd_1027404] using wordTrace_append hprefix tailTrace_1027404
  have hstable : (prefixWord ++ tailWord_1027404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027404).length < 2 ^ (prefixWord ++ tailWord_1027404).sum := by decide
  have hdescent : baseEnd_1027404 < baseStart_1027404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027424 : List Nat := [2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 3]
def baseStart_1027424 : Nat := 118140960795 + 1027424 * 2 ^ 59
def prefixEnd_1027424 : Nat := 4983230072969 + 3 ^ 40 * 1027424 * 2
def baseEnd_1027424 : Nat := 527562347965093432574969

theorem tailTrace_1027424 : CollatzResearch.WordTrace tailWord_1027424 prefixEnd_1027424 527562347965093432574969 := by
  unfold tailWord_1027424
  simp only [CollatzResearch.WordTrace]
  refine ⟨18736615914912896447212663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24982154553217195262950217 18736615914912896447212663)
  ·
    refine ⟨28104923872369344670818995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18736615914912896447212663 28104923872369344670818995)
    ·
      refine ⟨42157385808554017006228493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28104923872369344670818995 42157385808554017006228493)
      ·
        refine ⟨15809019678207756377335685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42157385808554017006228493 15809019678207756377335685)
        ·
          refine ⟨2964191189663954320750441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15809019678207756377335685 2964191189663954320750441)
          ·
            refine ⟨2223143392247965740562831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2964191189663954320750441 2223143392247965740562831)
            ·
              refine ⟨3334715088371948610844247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2223143392247965740562831 3334715088371948610844247)
              ·
                refine ⟨5002072632557922916266371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3334715088371948610844247 5002072632557922916266371)
                ·
                  refine ⟨7503108948836884374399557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5002072632557922916266371 7503108948836884374399557)
                  ·
                    refine ⟨1406832927906915820199917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7503108948836884374399557 1406832927906915820199917)
                    ·
                      refine ⟨527562347965093432574969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1406832927906915820199917 527562347965093432574969)
                      ·
                        rfl

theorem cell23_1027424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 3].length) (baseStart_1027424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1027424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1027424 prefixEnd_1027424 := by exact prefixLift 1027424
  have htrace : WordTrace (prefixWord ++ tailWord_1027424) baseStart_1027424 baseEnd_1027424 := by
    simpa [prefixWord, tailWord_1027424, baseEnd_1027424] using wordTrace_append hprefix tailTrace_1027424
  have hstable : (prefixWord ++ tailWord_1027424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027424).length < 2 ^ (prefixWord ++ tailWord_1027424).sum := by decide
  have hdescent : baseEnd_1027424 < baseStart_1027424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027505 : List Nat := [1, 2, 2, 4, 1, 1, 5, 2, 1, 1, 3]
def baseStart_1027505 : Nat := 118140960795 + 1027505 * 2 ^ 59
def prefixEnd_1027505 : Nat := 4983230072969 + 3 ^ 40 * 1027505 * 2
def baseEnd_1027505 : Nat := 527603939898107615662097

theorem tailTrace_1027505 : CollatzResearch.WordTrace tailWord_1027505 prefixEnd_1027505 527603939898107615662097 := by
  unfold tailWord_1027505
  simp only [CollatzResearch.WordTrace]
  refine ⟨37476186142532343728123969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24984124095021562485415979 37476186142532343728123969)
  ·
    refine ⟨28107139606899257796092977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37476186142532343728123969 28107139606899257796092977)
    ·
      refine ⟨21080354705174443347069733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28107139606899257796092977 21080354705174443347069733)
      ·
        refine ⟨3952566507220208127575575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21080354705174443347069733 3952566507220208127575575)
        ·
          refine ⟨5928849760830312191363363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3952566507220208127575575 5928849760830312191363363)
          ·
            refine ⟨8893274641245468287045045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5928849760830312191363363 8893274641245468287045045)
            ·
              refine ⟨833744497616762651910473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8893274641245468287045045 833744497616762651910473)
              ·
                refine ⟨625308373212571988932855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 833744497616762651910473 625308373212571988932855)
                ·
                  refine ⟨937962559818857983399283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 625308373212571988932855 937962559818857983399283)
                  ·
                    refine ⟨1406943839728286975098925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 937962559818857983399283 1406943839728286975098925)
                    ·
                      refine ⟨527603939898107615662097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1406943839728286975098925 527603939898107615662097)
                      ·
                        rfl

theorem cell23_1027505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_1027505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1027505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1027505 prefixEnd_1027505 := by exact prefixLift 1027505
  have htrace : WordTrace (prefixWord ++ tailWord_1027505) baseStart_1027505 baseEnd_1027505 := by
    simpa [prefixWord, tailWord_1027505, baseEnd_1027505] using wordTrace_append hprefix tailTrace_1027505
  have hstable : (prefixWord ++ tailWord_1027505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027505).length < 2 ^ (prefixWord ++ tailWord_1027505).sum := by decide
  have hdescent : baseEnd_1027505 < baseStart_1027505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027531 : List Nat := [1, 1, 1, 1, 3, 3, 5, 2, 1, 2, 3]
def baseStart_1027531 : Nat := 118140960795 + 1027531 * 2 ^ 59
def prefixEnd_1027531 : Nat := 4983230072969 + 3 ^ 40 * 1027531 * 2
def baseEnd_1027531 : Nat := 527617290395124513936977

theorem tailTrace_1027531 : CollatzResearch.WordTrace tailWord_1027531 prefixEnd_1027531 527617290395124513936977 := by
  unfold tailWord_1027531
  simp only [CollatzResearch.WordTrace]
  refine ⟨37477134440438150168570447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24984756293625433445713631 37477134440438150168570447)
  ·
    refine ⟨56215701660657225252855671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37477134440438150168570447 56215701660657225252855671)
    ·
      refine ⟨84323552490985837879283507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56215701660657225252855671 84323552490985837879283507)
      ·
        refine ⟨126485328736478756818925261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84323552490985837879283507 126485328736478756818925261)
        ·
          refine ⟨47431998276179533807096973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126485328736478756818925261 47431998276179533807096973)
          ·
            refine ⟨17786999353567325177661365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47431998276179533807096973 17786999353567325177661365)
            ·
              refine ⟨1667531189396936735405753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17786999353567325177661365 1667531189396936735405753)
              ·
                refine ⟨1250648392047702551554315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1667531189396936735405753 1250648392047702551554315)
                ·
                  refine ⟨1875972588071553827331473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1250648392047702551554315 1875972588071553827331473)
                  ·
                    refine ⟨1406979441053665370498605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1875972588071553827331473 1406979441053665370498605)
                    ·
                      refine ⟨527617290395124513936977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1406979441053665370498605 527617290395124513936977)
                      ·
                        rfl

theorem cell23_1027531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 2, 3].length) (baseStart_1027531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1027531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1027531 prefixEnd_1027531 := by exact prefixLift 1027531
  have htrace : WordTrace (prefixWord ++ tailWord_1027531) baseStart_1027531 baseEnd_1027531 := by
    simpa [prefixWord, tailWord_1027531, baseEnd_1027531] using wordTrace_append hprefix tailTrace_1027531
  have hstable : (prefixWord ++ tailWord_1027531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027531).length < 2 ^ (prefixWord ++ tailWord_1027531).sum := by decide
  have hdescent : baseEnd_1027531 < baseStart_1027531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027544 : List Nat := [2, 1, 2, 2, 2, 1, 3, 1, 3, 3, 3]
def baseStart_1027544 : Nat := 118140960795 + 1027544 * 2 ^ 59
def prefixEnd_1027544 : Nat := 4983230072969 + 3 ^ 40 * 1027544 * 2
def baseEnd_1027544 : Nat := 527623965643632963074417

theorem tailTrace_1027544 : CollatzResearch.WordTrace tailWord_1027544 prefixEnd_1027544 527623965643632963074417 := by
  unfold tailWord_1027544
  simp only [CollatzResearch.WordTrace]
  refine ⟨18738804294695526694396843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24985072392927368925862457 18738804294695526694396843)
  ·
    refine ⟨28108206442043290041595265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18738804294695526694396843 28108206442043290041595265)
    ·
      refine ⟨21081154831532467531196449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28108206442043290041595265 21081154831532467531196449)
      ·
        refine ⟨15810866123649350648397337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21081154831532467531196449 15810866123649350648397337)
        ·
          refine ⟨11858149592737012986298003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15810866123649350648397337 11858149592737012986298003)
          ·
            refine ⟨17787224389105519479447005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11858149592737012986298003 17787224389105519479447005)
            ·
              refine ⟨6670209145914569804792627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17787224389105519479447005 6670209145914569804792627)
              ·
                refine ⟨10005313718871854707188941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6670209145914569804792627 10005313718871854707188941)
                ·
                  refine ⟨3751992644576945515195853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10005313718871854707188941 3751992644576945515195853)
                  ·
                    refine ⟨1406997241716354568198445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3751992644576945515195853 1406997241716354568198445)
                    ·
                      refine ⟨527623965643632963074417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1406997241716354568198445 527623965643632963074417)
                      ·
                        rfl

theorem cell23_1027544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 3, 3, 3].length) (baseStart_1027544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1027544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1027544 prefixEnd_1027544 := by exact prefixLift 1027544
  have htrace : WordTrace (prefixWord ++ tailWord_1027544) baseStart_1027544 baseEnd_1027544 := by
    simpa [prefixWord, tailWord_1027544, baseEnd_1027544] using wordTrace_append hprefix tailTrace_1027544
  have hstable : (prefixWord ++ tailWord_1027544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027544).length < 2 ^ (prefixWord ++ tailWord_1027544).sum := by decide
  have hdescent : baseEnd_1027544 < baseStart_1027544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027562 : List Nat := [3, 1, 3, 1, 4, 1, 1, 4, 1, 2, 2]
def baseStart_1027562 : Nat := 118140960795 + 1027562 * 2 ^ 59
def prefixEnd_1027562 : Nat := 4983230072969 + 3 ^ 40 * 1027562 * 2
def baseEnd_1027562 : Nat := 527633208295413892649335

theorem tailTrace_1027562 : CollatzResearch.WordTrace tailWord_1027562 prefixEnd_1027562 527633208295413892649335 := by
  unfold tailWord_1027562
  simp only [CollatzResearch.WordTrace]
  refine ⟨9369566275831460615737235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24985510068883894975299293 9369566275831460615737235)
  ·
    refine ⟨14054349413747190923605853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9369566275831460615737235 14054349413747190923605853)
    ·
      refine ⟨5270381030155196596352195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14054349413747190923605853 5270381030155196596352195)
      ·
        refine ⟨7905571545232794894528293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5270381030155196596352195 7905571545232794894528293)
        ·
          refine ⟨1482294664731149042724055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7905571545232794894528293 1482294664731149042724055)
          ·
            refine ⟨2223441997096723564086083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1482294664731149042724055 2223441997096723564086083)
            ·
              refine ⟨3335162995645085346129125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2223441997096723564086083 3335162995645085346129125)
              ·
                refine ⟨625343061683453502399211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3335162995645085346129125 625343061683453502399211)
                ·
                  refine ⟨938014592525180253598817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 625343061683453502399211 938014592525180253598817)
                  ·
                    refine ⟨703510944393885190199113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 938014592525180253598817 703510944393885190199113)
                    ·
                      refine ⟨527633208295413892649335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 703510944393885190199113 527633208295413892649335)
                      ·
                        rfl

theorem cell23_1027562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 4, 1, 2, 2].length) (baseStart_1027562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1027562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1027562 prefixEnd_1027562 := by exact prefixLift 1027562
  have htrace : WordTrace (prefixWord ++ tailWord_1027562) baseStart_1027562 baseEnd_1027562 := by
    simpa [prefixWord, tailWord_1027562, baseEnd_1027562] using wordTrace_append hprefix tailTrace_1027562
  have hstable : (prefixWord ++ tailWord_1027562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027562).length < 2 ^ (prefixWord ++ tailWord_1027562).sum := by decide
  have hdescent : baseEnd_1027562 < baseStart_1027562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027601 : List Nat := [1, 2, 2, 1, 1, 2, 3, 4, 1, 4, 2]
def baseStart_1027601 : Nat := 118140960795 + 1027601 * 2 ^ 59
def prefixEnd_1027601 : Nat := 4983230072969 + 3 ^ 40 * 1027601 * 2
def baseEnd_1027601 : Nat := 527653234040939240061655

theorem tailTrace_1027601 : CollatzResearch.WordTrace tailWord_1027601 prefixEnd_1027601 527653234040939240061655 := by
  unfold tailWord_1027601
  simp only [CollatzResearch.WordTrace]
  refine ⟨37479687550184552123618657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24986458366789701415745771 37479687550184552123618657)
  ·
    refine ⟨28109765662638414092713993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37479687550184552123618657 28109765662638414092713993)
    ·
      refine ⟨21082324246978810569535495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28109765662638414092713993 21082324246978810569535495)
      ·
        refine ⟨31623486370468215854303243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21082324246978810569535495 31623486370468215854303243)
        ·
          refine ⟨47435229555702323781454865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31623486370468215854303243 47435229555702323781454865)
          ·
            refine ⟨35576422166776742836091149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47435229555702323781454865 35576422166776742836091149)
            ·
              refine ⟨13341158312541278563534181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35576422166776742836091149 13341158312541278563534181)
              ·
                refine ⟨2501467183601489730662659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13341158312541278563534181 2501467183601489730662659)
                ·
                  refine ⟨3752200775402234595993989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2501467183601489730662659 3752200775402234595993989)
                  ·
                    refine ⟨703537645387918986748873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3752200775402234595993989 703537645387918986748873)
                    ·
                      refine ⟨527653234040939240061655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 703537645387918986748873 527653234040939240061655)
                      ·
                        rfl

theorem cell23_1027601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 4, 2].length) (baseStart_1027601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1027601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1027601 prefixEnd_1027601 := by exact prefixLift 1027601
  have htrace : WordTrace (prefixWord ++ tailWord_1027601) baseStart_1027601 baseEnd_1027601 := by
    simpa [prefixWord, tailWord_1027601, baseEnd_1027601] using wordTrace_append hprefix tailTrace_1027601
  have hstable : (prefixWord ++ tailWord_1027601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027601).length < 2 ^ (prefixWord ++ tailWord_1027601).sum := by decide
  have hdescent : baseEnd_1027601 < baseStart_1027601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027605 : List Nat := [1, 3, 2, 1, 3, 2, 4, 1, 1, 3, 2]
def baseStart_1027605 : Nat := 118140960795 + 1027605 * 2 ^ 59
def prefixEnd_1027605 : Nat := 4983230072969 + 3 ^ 40 * 1027605 * 2
def baseEnd_1027605 : Nat := 527655287963557224411637

theorem tailTrace_1027605 : CollatzResearch.WordTrace tailWord_1027605 prefixEnd_1027605 527655287963557224411637 := by
  unfold tailWord_1027605
  simp only [CollatzResearch.WordTrace]
  refine ⟨37479833442170060806764269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24986555628113373871176179 37479833442170060806764269)
  ·
    refine ⟨14054937540813772802536601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37479833442170060806764269 14054937540813772802536601)
    ·
      refine ⟨10541203155610329601902451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14054937540813772802536601 10541203155610329601902451)
      ·
        refine ⟨15811804733415494402853677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10541203155610329601902451 15811804733415494402853677)
        ·
          refine ⟨5929426775030810401070129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15811804733415494402853677 5929426775030810401070129)
          ·
            refine ⟨4447070081273107800802597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5929426775030810401070129 4447070081273107800802597)
            ·
              refine ⟨833825640238707712650487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4447070081273107800802597 833825640238707712650487)
              ·
                refine ⟨1250738460358061568975731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 833825640238707712650487 1250738460358061568975731)
                ·
                  refine ⟨1876107690537092353463597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1250738460358061568975731 1876107690537092353463597)
                  ·
                    refine ⟨703540383951409632548849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1876107690537092353463597 703540383951409632548849)
                    ·
                      refine ⟨527655287963557224411637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 703540383951409632548849 527655287963557224411637)
                      ·
                        rfl

theorem cell23_1027605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 1, 3, 2].length) (baseStart_1027605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1027605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1027605 prefixEnd_1027605 := by exact prefixLift 1027605
  have htrace : WordTrace (prefixWord ++ tailWord_1027605) baseStart_1027605 baseEnd_1027605 := by
    simpa [prefixWord, tailWord_1027605, baseEnd_1027605] using wordTrace_append hprefix tailTrace_1027605
  have hstable : (prefixWord ++ tailWord_1027605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027605).length < 2 ^ (prefixWord ++ tailWord_1027605).sum := by decide
  have hdescent : baseEnd_1027605 < baseStart_1027605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027664 : List Nat := [2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 5]
def baseStart_1027664 : Nat := 118140960795 + 1027664 * 2 ^ 59
def prefixEnd_1027664 : Nat := 4983230072969 + 3 ^ 40 * 1027664 * 2
def baseEnd_1027664 : Nat := 527685583322172493573865

theorem tailTrace_1027664 : CollatzResearch.WordTrace tailWord_1027664 prefixEnd_1027664 527685583322172493573865 := by
  unfold tailWord_1027664
  simp only [CollatzResearch.WordTrace]
  refine ⟨18740992674478156941581023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24987990232637542588774697 18740992674478156941581023)
  ·
    refine ⟨28111489011717235412371535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18740992674478156941581023 28111489011717235412371535)
    ·
      refine ⟨42167233517575853118557303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28111489011717235412371535 42167233517575853118557303)
      ·
        refine ⟨63250850276363779677835955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42167233517575853118557303 63250850276363779677835955)
        ·
          refine ⟨94876275414545669516753933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63250850276363779677835955 94876275414545669516753933)
          ·
            refine ⟨35578603280454626068782725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94876275414545669516753933 35578603280454626068782725)
            ·
              refine ⟨6670988115085242387896761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35578603280454626068782725 6670988115085242387896761)
              ·
                refine ⟨5003241086313931790922571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6670988115085242387896761 5003241086313931790922571)
                ·
                  refine ⟨7504861629470897686383857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5003241086313931790922571 7504861629470897686383857)
                  ·
                    refine ⟨5628646222103173264787893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7504861629470897686383857 5628646222103173264787893)
                    ·
                      refine ⟨527685583322172493573865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5628646222103173264787893 527685583322172493573865)
                      ·
                        rfl

theorem cell23_1027664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 5].length) (baseStart_1027664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1027664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1027664 prefixEnd_1027664 := by exact prefixLift 1027664
  have htrace : WordTrace (prefixWord ++ tailWord_1027664) baseStart_1027664 baseEnd_1027664 := by
    simpa [prefixWord, tailWord_1027664, baseEnd_1027664] using wordTrace_append hprefix tailTrace_1027664
  have hstable : (prefixWord ++ tailWord_1027664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027664).length < 2 ^ (prefixWord ++ tailWord_1027664).sum := by decide
  have hdescent : baseEnd_1027664 < baseStart_1027664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027671 : List Nat := [1, 1, 3, 2, 2, 4, 1, 2, 2, 5]
def baseStart_1027671 : Nat := 118140960795 + 1027671 * 2 ^ 59
def prefixEnd_1027671 : Nat := 4983230072969 + 3 ^ 40 * 1027671 * 2
def baseEnd_1027671 : Nat := 175896392562251322062111

theorem tailTrace_1027671 : CollatzResearch.WordTrace tailWord_1027671 prefixEnd_1027671 175896392562251322062111 := by
  unfold tailWord_1027671
  simp only [CollatzResearch.WordTrace]
  refine ⟨37482240659930954078666867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24988160439953969385777911 37482240659930954078666867)
  ·
    refine ⟨56223360989896431118000301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37482240659930954078666867 56223360989896431118000301)
    ·
      refine ⟨21083760371211161669250113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56223360989896431118000301 21083760371211161669250113)
      ·
        refine ⟨15812820278408371251937585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21083760371211161669250113 15812820278408371251937585)
        ·
          refine ⟨11859615208806278438953189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15812820278408371251937585 11859615208806278438953189)
          ·
            refine ⟨2223677851651177207303723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11859615208806278438953189 2223677851651177207303723)
            ·
              refine ⟨3335516777476765810955585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2223677851651177207303723 3335516777476765810955585)
              ·
                refine ⟨2501637583107574358216689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3335516777476765810955585 2501637583107574358216689)
                ·
                  refine ⟨1876228187330680768662517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2501637583107574358216689 1876228187330680768662517)
                  ·
                    refine ⟨175896392562251322062111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1876228187330680768662517 175896392562251322062111)
                    ·
                      rfl

theorem cell23_1027671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 5].length) (baseStart_1027671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1027671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1027671 prefixEnd_1027671 := by exact prefixLift 1027671
  have htrace : WordTrace (prefixWord ++ tailWord_1027671) baseStart_1027671 baseEnd_1027671 := by
    simpa [prefixWord, tailWord_1027671, baseEnd_1027671] using wordTrace_append hprefix tailTrace_1027671
  have hstable : (prefixWord ++ tailWord_1027671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027671).length < 2 ^ (prefixWord ++ tailWord_1027671).sum := by decide
  have hdescent : baseEnd_1027671 < baseStart_1027671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027691 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 6, 4, 2]
def baseStart_1027691 : Nat := 118140960795 + 1027691 * 2 ^ 59
def prefixEnd_1027691 : Nat := 4983230072969 + 3 ^ 40 * 1027691 * 2
def baseEnd_1027691 : Nat := 527699447299843887936241

theorem tailTrace_1027691 : CollatzResearch.WordTrace tailWord_1027691 prefixEnd_1027691 527699447299843887936241 := by
  unfold tailWord_1027691
  simp only [CollatzResearch.WordTrace]
  refine ⟨37482970119858497494394927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24988646746572331662929951 37482970119858497494394927)
  ·
    refine ⟨56224455179787746241592391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37482970119858497494394927 56224455179787746241592391)
    ·
      refine ⟨84336682769681619362388587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56224455179787746241592391 84336682769681619362388587)
      ·
        refine ⟨126505024154522429043582881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84336682769681619362388587 126505024154522429043582881)
        ·
          refine ⟨94878768115891821782687161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126505024154522429043582881 94878768115891821782687161)
          ·
            refine ⟨71159076086918866337015371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94878768115891821782687161 71159076086918866337015371)
            ·
              refine ⟨106738614130378299505523057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71159076086918866337015371 106738614130378299505523057)
              ·
                refine ⟨80053960597783724629142293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106738614130378299505523057 80053960597783724629142293)
                ·
                  refine ⟨3752529403021112091991045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 80053960597783724629142293 3752529403021112091991045)
                  ·
                    refine ⟨703599263066458517248321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3752529403021112091991045 703599263066458517248321)
                    ·
                      refine ⟨527699447299843887936241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 703599263066458517248321 527699447299843887936241)
                      ·
                        rfl

theorem cell23_1027691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 4, 2].length) (baseStart_1027691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1027691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1027691 prefixEnd_1027691 := by exact prefixLift 1027691
  have htrace : WordTrace (prefixWord ++ tailWord_1027691) baseStart_1027691 baseEnd_1027691 := by
    simpa [prefixWord, tailWord_1027691, baseEnd_1027691] using wordTrace_append hprefix tailTrace_1027691
  have hstable : (prefixWord ++ tailWord_1027691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027691).length < 2 ^ (prefixWord ++ tailWord_1027691).sum := by decide
  have hdescent : baseEnd_1027691 < baseStart_1027691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027735 : List Nat := [1, 1, 3, 3, 2, 3, 1, 4, 1, 4]
def baseStart_1027735 : Nat := 118140960795 + 1027735 * 2 ^ 59
def prefixEnd_1027735 : Nat := 4983230072969 + 3 ^ 40 * 1027735 * 2
def baseEnd_1027735 : Nat := 175907346816213905262013

theorem tailTrace_1027735 : CollatzResearch.WordTrace tailWord_1027735 prefixEnd_1027735 175907346816213905262013 := by
  unfold tailWord_1027735
  simp only [CollatzResearch.WordTrace]
  refine ⟨37484574931699093008996659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24989716621132728672664439 37484574931699093008996659)
  ·
    refine ⟨56226862397548639513494989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37484574931699093008996659 56226862397548639513494989)
    ·
      refine ⟨21085073399080739817560621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56226862397548639513494989 21085073399080739817560621)
      ·
        refine ⟨7906902524655277431585233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21085073399080739817560621 7906902524655277431585233)
        ·
          refine ⟨5930176893491458073688925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7906902524655277431585233 5930176893491458073688925)
          ·
            refine ⟨2223816335059296777633347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5930176893491458073688925 2223816335059296777633347)
            ·
              refine ⟨3335724502588945166450021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2223816335059296777633347 3335724502588945166450021)
              ·
                refine ⟨625448344235427218709379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3335724502588945166450021 625448344235427218709379)
                ·
                  refine ⟨938172516353140828064069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 625448344235427218709379 938172516353140828064069)
                  ·
                    refine ⟨175907346816213905262013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 938172516353140828064069 175907346816213905262013)
                    ·
                      rfl

theorem cell23_1027735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 4, 1, 4].length) (baseStart_1027735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1027735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1027735 prefixEnd_1027735 := by exact prefixLift 1027735
  have htrace : WordTrace (prefixWord ++ tailWord_1027735) baseStart_1027735 baseEnd_1027735 := by
    simpa [prefixWord, tailWord_1027735, baseEnd_1027735] using wordTrace_append hprefix tailTrace_1027735
  have hstable : (prefixWord ++ tailWord_1027735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027735).length < 2 ^ (prefixWord ++ tailWord_1027735).sum := by decide
  have hdescent : baseEnd_1027735 < baseStart_1027735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027741 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 2, 5, 3]
def baseStart_1027741 : Nat := 118140960795 + 1027741 * 2 ^ 59
def prefixEnd_1027741 : Nat := 4983230072969 + 3 ^ 40 * 1027741 * 2
def baseEnd_1027741 : Nat := 527725121332568692311011

theorem tailTrace_1027741 : CollatzResearch.WordTrace tailWord_1027741 prefixEnd_1027741 527725121332568692311011 := by
  unfold tailWord_1027741
  simp only [CollatzResearch.WordTrace]
  refine ⟨37484793769677356033715077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24989862513118237355810051 37484793769677356033715077)
  ·
    refine ⟨7028398831814504256321577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37484793769677356033715077 7028398831814504256321577)
    ·
      refine ⟨5271299123860878192241183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7028398831814504256321577 5271299123860878192241183)
      ·
        refine ⟨7906948685791317288361775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5271299123860878192241183 7906948685791317288361775)
        ·
          refine ⟨11860423028686975932542663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7906948685791317288361775 11860423028686975932542663)
          ·
            refine ⟨17790634543030463898813995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11860423028686975932542663 17790634543030463898813995)
            ·
              refine ⟨26685951814545695848220993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17790634543030463898813995 26685951814545695848220993)
              ·
                refine ⟨20014463860909271886165745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26685951814545695848220993 20014463860909271886165745)
                ·
                  refine ⟨15010847895681953914624309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20014463860909271886165745 15010847895681953914624309)
                  ·
                    refine ⟨1407266990220183179496029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15010847895681953914624309 1407266990220183179496029)
                    ·
                      refine ⟨527725121332568692311011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1407266990220183179496029 527725121332568692311011)
                      ·
                        rfl

theorem cell23_1027741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_1027741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1027741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1027741 prefixEnd_1027741 := by exact prefixLift 1027741
  have htrace : WordTrace (prefixWord ++ tailWord_1027741) baseStart_1027741 baseEnd_1027741 := by
    simpa [prefixWord, tailWord_1027741, baseEnd_1027741] using wordTrace_append hprefix tailTrace_1027741
  have hstable : (prefixWord ++ tailWord_1027741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027741).length < 2 ^ (prefixWord ++ tailWord_1027741).sum := by decide
  have hdescent : baseEnd_1027741 < baseStart_1027741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027782 : List Nat := [6, 1, 2, 1, 1, 1, 3, 2, 6]
def baseStart_1027782 : Nat := 118140960795 + 1027782 * 2 ^ 59
def prefixEnd_1027782 : Nat := 4983230072969 + 3 ^ 40 * 1027782 * 2
def baseEnd_1027782 : Nat := 58638463782155892433147

theorem tailTrace_1027782 : CollatzResearch.WordTrace tailWord_1027782 prefixEnd_1027782 58638463782155892433147 := by
  unfold tailWord_1027782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1171446536329025626123675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24990859441685880023971733 1171446536329025626123675)
  ·
    refine ⟨1757169804493538439185513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1171446536329025626123675 1757169804493538439185513)
    ·
      refine ⟨1317877353370153829389135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1757169804493538439185513 1317877353370153829389135)
      ·
        refine ⟨1976816030055230744083703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1317877353370153829389135 1976816030055230744083703)
        ·
          refine ⟨2965224045082846116125555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1976816030055230744083703 2965224045082846116125555)
          ·
            refine ⟨4447836067624269174188333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2965224045082846116125555 4447836067624269174188333)
            ·
              refine ⟨1667938525359100940320625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4447836067624269174188333 1667938525359100940320625)
              ·
                refine ⟨1250953894019325705240469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1667938525359100940320625 1250953894019325705240469)
                ·
                  refine ⟨58638463782155892433147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1250953894019325705240469 58638463782155892433147)
                  ·
                    rfl

theorem cell23_1027782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_1027782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1027782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1027782 prefixEnd_1027782 := by exact prefixLift 1027782
  have htrace : WordTrace (prefixWord ++ tailWord_1027782) baseStart_1027782 baseEnd_1027782 := by
    simpa [prefixWord, tailWord_1027782, baseEnd_1027782] using wordTrace_append hprefix tailTrace_1027782
  have hstable : (prefixWord ++ tailWord_1027782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027782).length < 2 ^ (prefixWord ++ tailWord_1027782).sum := by decide
  have hdescent : baseEnd_1027782 < baseStart_1027782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027801 : List Nat := [1, 2, 1, 2, 3, 3, 1, 1, 3, 1, 5]
def baseStart_1027801 : Nat := 118140960795 + 1027801 * 2 ^ 59
def prefixEnd_1027801 : Nat := 4983230072969 + 3 ^ 40 * 1027801 * 2
def baseEnd_1027801 : Nat := 527755930171838457560735

theorem tailTrace_1027801 : CollatzResearch.WordTrace tailWord_1027801 prefixEnd_1027801 527755930171838457560735 := by
  unfold tailWord_1027801
  simp only [CollatzResearch.WordTrace]
  refine ⟨37486982149459986280899257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24991321432973324187266171 37486982149459986280899257)
  ·
    refine ⟨28115236612094989710674443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37486982149459986280899257 28115236612094989710674443)
    ·
      refine ⟨42172854918142484566011665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28115236612094989710674443 42172854918142484566011665)
      ·
        refine ⟨31629641188606863424508749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42172854918142484566011665 31629641188606863424508749)
        ·
          refine ⟨11861115445727573784190781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31629641188606863424508749 11861115445727573784190781)
          ·
            refine ⟨4447918292147840169071543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11861115445727573784190781 4447918292147840169071543)
            ·
              refine ⟨6671877438221760253607315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4447918292147840169071543 6671877438221760253607315)
              ·
                refine ⟨10007816157332640380410973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6671877438221760253607315 10007816157332640380410973)
                ·
                  refine ⟨3752931058999740142654115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10007816157332640380410973 3752931058999740142654115)
                  ·
                    refine ⟨5629396588499610213981173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3752931058999740142654115 5629396588499610213981173)
                    ·
                      refine ⟨527755930171838457560735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5629396588499610213981173 527755930171838457560735)
                      ·
                        rfl

theorem cell23_1027801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 1, 5].length) (baseStart_1027801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1027801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1027801 prefixEnd_1027801 := by exact prefixLift 1027801
  have htrace : WordTrace (prefixWord ++ tailWord_1027801) baseStart_1027801 baseEnd_1027801 := by
    simpa [prefixWord, tailWord_1027801, baseEnd_1027801] using wordTrace_append hprefix tailTrace_1027801
  have hstable : (prefixWord ++ tailWord_1027801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027801).length < 2 ^ (prefixWord ++ tailWord_1027801).sum := by decide
  have hdescent : baseEnd_1027801 < baseStart_1027801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027808 : List Nat := [2, 1, 1, 3, 1, 2, 2, 5, 2, 4]
def baseStart_1027808 : Nat := 118140960795 + 1027808 * 2 ^ 59
def prefixEnd_1027808 : Nat := 4983230072969 + 3 ^ 40 * 1027808 * 2
def baseEnd_1027808 : Nat := 175919841512139976724401

theorem tailTrace_1027808 : CollatzResearch.WordTrace tailWord_1027808 prefixEnd_1027808 175919841512139976724401 := by
  unfold tailWord_1027808
  simp only [CollatzResearch.WordTrace]
  refine ⟨18743618730217313238202039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24991491640289750984269385 18743618730217313238202039)
  ·
    refine ⟨28115428095325969857303059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18743618730217313238202039 28115428095325969857303059)
    ·
      refine ⟨42173142142988954785954589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28115428095325969857303059 42173142142988954785954589)
      ·
        refine ⟨15814928303620858044732971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42173142142988954785954589 15814928303620858044732971)
        ·
          refine ⟨23722392455431287067099457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15814928303620858044732971 23722392455431287067099457)
          ·
            refine ⟨17791794341573465300324593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23722392455431287067099457 17791794341573465300324593)
            ·
              refine ⟨13343845756180098975243445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17791794341573465300324593 13343845756180098975243445)
              ·
                refine ⟨1250985539641884278929073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13343845756180098975243445 1250985539641884278929073)
                ·
                  refine ⟨938239154731413209196805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1250985539641884278929073 938239154731413209196805)
                  ·
                    refine ⟨175919841512139976724401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 938239154731413209196805 175919841512139976724401)
                    ·
                      rfl

theorem cell23_1027808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 2, 4].length) (baseStart_1027808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1027808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1027808 prefixEnd_1027808 := by exact prefixLift 1027808
  have htrace : WordTrace (prefixWord ++ tailWord_1027808) baseStart_1027808 baseEnd_1027808 := by
    simpa [prefixWord, tailWord_1027808, baseEnd_1027808] using wordTrace_append hprefix tailTrace_1027808
  have hstable : (prefixWord ++ tailWord_1027808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027808).length < 2 ^ (prefixWord ++ tailWord_1027808).sum := by decide
  have hdescent : baseEnd_1027808 < baseStart_1027808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027818 : List Nat := [3, 1, 3, 1, 1, 1, 2, 3, 3, 2, 3]
def baseStart_1027818 : Nat := 118140960795 + 1027818 * 2 ^ 59
def prefixEnd_1027818 : Nat := 4983230072969 + 3 ^ 40 * 1027818 * 2
def baseEnd_1027818 : Nat := 527764659342964891048157

theorem tailTrace_1027818 : CollatzResearch.WordTrace tailWord_1027818 prefixEnd_1027818 527764659342964891048157 := by
  unfold tailWord_1027818
  simp only [CollatzResearch.WordTrace]
  refine ⟨9371900547599599546067027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24991734793598932122845405 9371900547599599546067027)
  ·
    refine ⟨14057850821399399319100541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9371900547599599546067027 14057850821399399319100541)
    ·
      refine ⟨5271694058024774744662703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14057850821399399319100541 5271694058024774744662703)
      ·
        refine ⟨7907541087037162116994055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5271694058024774744662703 7907541087037162116994055)
        ·
          refine ⟨11861311630555743175491083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7907541087037162116994055 11861311630555743175491083)
          ·
            refine ⟨17791967445833614763236625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11861311630555743175491083 17791967445833614763236625)
            ·
              refine ⟨13343975584375211072427469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17791967445833614763236625 13343975584375211072427469)
              ·
                refine ⟨5003990844140704152160301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13343975584375211072427469 5003990844140704152160301)
                ·
                  refine ⟨1876496566552764057060113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5003990844140704152160301 1876496566552764057060113)
                  ·
                    refine ⟨1407372424914573042795085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1876496566552764057060113 1407372424914573042795085)
                    ·
                      refine ⟨527764659342964891048157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1407372424914573042795085 527764659342964891048157)
                      ·
                        rfl

theorem cell23_1027818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_1027818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1027818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1027818 prefixEnd_1027818 := by exact prefixLift 1027818
  have htrace : WordTrace (prefixWord ++ tailWord_1027818) baseStart_1027818 baseEnd_1027818 := by
    simpa [prefixWord, tailWord_1027818, baseEnd_1027818] using wordTrace_append hprefix tailTrace_1027818
  have hstable : (prefixWord ++ tailWord_1027818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027818).length < 2 ^ (prefixWord ++ tailWord_1027818).sum := by decide
  have hdescent : baseEnd_1027818 < baseStart_1027818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027832 : List Nat := [2, 1, 2, 1, 1, 2, 2, 7, 1, 2, 2]
def baseStart_1027832 : Nat := 118140960795 + 1027832 * 2 ^ 59
def prefixEnd_1027832 : Nat := 4983230072969 + 3 ^ 40 * 1027832 * 2
def baseEnd_1027832 : Nat := 527771848072127836273093

theorem tailTrace_1027832 : CollatzResearch.WordTrace tailWord_1027832 prefixEnd_1027832 527771848072127836273093 := by
  unfold tailWord_1027832
  simp only [CollatzResearch.WordTrace]
  refine ⟨18744056406173839287638875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24992075208231785716851833 18744056406173839287638875)
  ·
    refine ⟨28116084609260758931458313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18744056406173839287638875 28116084609260758931458313)
    ·
      refine ⟨21087063456945569198593735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28116084609260758931458313 21087063456945569198593735)
      ·
        refine ⟨31630595185418353797890603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21087063456945569198593735 31630595185418353797890603)
        ·
          refine ⟨47445892778127530696835905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31630595185418353797890603 47445892778127530696835905)
          ·
            refine ⟨35584419583595648022626929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47445892778127530696835905 35584419583595648022626929)
            ·
              refine ⟨26688314687696736016970197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35584419583595648022626929 26688314687696736016970197)
              ·
                refine ⟨625507375492892250397739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 26688314687696736016970197 625507375492892250397739)
                ·
                  refine ⟨938261063239338375596609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 625507375492892250397739 938261063239338375596609)
                  ·
                    refine ⟨703695797429503781697457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 938261063239338375596609 703695797429503781697457)
                    ·
                      refine ⟨527771848072127836273093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 703695797429503781697457 527771848072127836273093)
                      ·
                        rfl

theorem cell23_1027832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 7, 1, 2, 2].length) (baseStart_1027832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1027832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1027832 prefixEnd_1027832 := by exact prefixLift 1027832
  have htrace : WordTrace (prefixWord ++ tailWord_1027832) baseStart_1027832 baseEnd_1027832 := by
    simpa [prefixWord, tailWord_1027832, baseEnd_1027832] using wordTrace_append hprefix tailTrace_1027832
  have hstable : (prefixWord ++ tailWord_1027832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027832).length < 2 ^ (prefixWord ++ tailWord_1027832).sum := by decide
  have hdescent : baseEnd_1027832 < baseStart_1027832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027922 : List Nat := [3, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2]
def baseStart_1027922 : Nat := 118140960795 + 1027922 * 2 ^ 59
def prefixEnd_1027922 : Nat := 4983230072969 + 3 ^ 40 * 1027922 * 2
def baseEnd_1027922 : Nat := 527818061331032484147679

theorem tailTrace_1027922 : CollatzResearch.WordTrace tailWord_1027922 prefixEnd_1027922 527818061331032484147679 := by
  unfold tailWord_1027922
  simp only [CollatzResearch.WordTrace]
  refine ⟨9372848845505405986513505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24994263588014415964036013 9372848845505405986513505)
  ·
    refine ⟨7029636634129054489885129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9372848845505405986513505 7029636634129054489885129)
    ·
      refine ⟨5272227475596790867413847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7029636634129054489885129 5272227475596790867413847)
      ·
        refine ⟨7908341213395186301120771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5272227475596790867413847 7908341213395186301120771)
        ·
          refine ⟨11862511820092779451681157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7908341213395186301120771 11862511820092779451681157)
          ·
            refine ⟨2224220966267396147190217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11862511820092779451681157 2224220966267396147190217)
            ·
              refine ⟨1668165724700547110392663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2224220966267396147190217 1668165724700547110392663)
              ·
                refine ⟨2502248587050820665588995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1668165724700547110392663 2502248587050820665588995)
                ·
                  refine ⟨3753372880576230998383493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2502248587050820665588995 3753372880576230998383493)
                  ·
                    refine ⟨703757415108043312196905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3753372880576230998383493 703757415108043312196905)
                    ·
                      refine ⟨527818061331032484147679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 703757415108043312196905 527818061331032484147679)
                      ·
                        rfl

theorem cell23_1027922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_1027922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1027922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1027922 prefixEnd_1027922 := by exact prefixLift 1027922
  have htrace : WordTrace (prefixWord ++ tailWord_1027922) baseStart_1027922 baseEnd_1027922 := by
    simpa [prefixWord, tailWord_1027922, baseEnd_1027922] using wordTrace_append hprefix tailTrace_1027922
  have hstable : (prefixWord ++ tailWord_1027922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027922).length < 2 ^ (prefixWord ++ tailWord_1027922).sum := by decide
  have hdescent : baseEnd_1027922 < baseStart_1027922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028015 : List Nat := [1, 1, 2, 1, 2, 2, 5, 2, 2, 2, 3]
def baseStart_1028015 : Nat := 118140960795 + 1028015 * 2 ^ 59
def prefixEnd_1028015 : Nat := 4983230072969 + 3 ^ 40 * 1028015 * 2
def baseEnd_1028015 : Nat := 527865815031900620284751

theorem tailTrace_1028015 : CollatzResearch.WordTrace tailWord_1028015 prefixEnd_1028015 527865815031900620284751 := by
  unfold tailWord_1028015
  simp only [CollatzResearch.WordTrace]
  refine ⟨37494787370684700829189499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24996524913789800552792999 37494787370684700829189499)
  ·
    refine ⟨56242181056027051243784249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37494787370684700829189499 56242181056027051243784249)
    ·
      refine ⟨42181635792020288432838187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56242181056027051243784249 42181635792020288432838187)
      ·
        refine ⟨63272453688030432649257281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42181635792020288432838187 63272453688030432649257281)
        ·
          refine ⟨47454340266022824486942961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63272453688030432649257281 47454340266022824486942961)
          ·
            refine ⟨35590755199517118365207221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47454340266022824486942961 35590755199517118365207221)
            ·
              refine ⟨3336633299954729846738177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35590755199517118365207221 3336633299954729846738177)
              ·
                refine ⟨2502474974966047385053633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3336633299954729846738177 2502474974966047385053633)
                ·
                  refine ⟨1876856231224535538790225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2502474974966047385053633 1876856231224535538790225)
                  ·
                    refine ⟨1407642173418401654092669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1876856231224535538790225 1407642173418401654092669)
                    ·
                      refine ⟨527865815031900620284751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1407642173418401654092669 527865815031900620284751)
                      ·
                        rfl

theorem cell23_1028015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 2, 3].length) (baseStart_1028015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1028015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1028015 prefixEnd_1028015 := by exact prefixLift 1028015
  have htrace : WordTrace (prefixWord ++ tailWord_1028015) baseStart_1028015 baseEnd_1028015 := by
    simpa [prefixWord, tailWord_1028015, baseEnd_1028015] using wordTrace_append hprefix tailTrace_1028015
  have hstable : (prefixWord ++ tailWord_1028015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028015).length < 2 ^ (prefixWord ++ tailWord_1028015).sum := by decide
  have hdescent : baseEnd_1028015 < baseStart_1028015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028065 : List Nat := [1, 2, 3, 1, 2, 1, 2, 5, 1, 5]
def baseStart_1028065 : Nat := 118140960795 + 1028065 * 2 ^ 59
def prefixEnd_1028065 : Nat := 4983230072969 + 3 ^ 40 * 1028065 * 2
def baseEnd_1028065 : Nat := 175963829688208474886507

theorem tailTrace_1028065 : CollatzResearch.WordTrace tailWord_1028065 prefixEnd_1028065 175963829688208474886507 := by
  unfold tailWord_1028065
  simp only [CollatzResearch.WordTrace]
  refine ⟨37496611020503559368509649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24997740680335706245673099 37496611020503559368509649)
  ·
    refine ⟨28122458265377669526382237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37496611020503559368509649 28122458265377669526382237)
    ·
      refine ⟨10545921849516626072393339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28122458265377669526382237 10545921849516626072393339)
      ·
        refine ⟨15818882774274939108590009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10545921849516626072393339 15818882774274939108590009)
        ·
          refine ⟨11864162080706204331442507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15818882774274939108590009 11864162080706204331442507)
          ·
            refine ⟨17796243121059306497163761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11864162080706204331442507 17796243121059306497163761)
            ·
              refine ⟨13347182340794479872872821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17796243121059306497163761 13347182340794479872872821)
              ·
                refine ⟨1251298344449482488081827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13347182340794479872872821 1251298344449482488081827)
                ·
                  refine ⟨1876947516674223732122741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1251298344449482488081827 1876947516674223732122741)
                  ·
                    refine ⟨175963829688208474886507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1876947516674223732122741 175963829688208474886507)
                    ·
                      rfl

theorem cell23_1028065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 5].length) (baseStart_1028065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1028065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1028065 prefixEnd_1028065 := by exact prefixLift 1028065
  have htrace : WordTrace (prefixWord ++ tailWord_1028065) baseStart_1028065 baseEnd_1028065 := by
    simpa [prefixWord, tailWord_1028065, baseEnd_1028065] using wordTrace_append hprefix tailTrace_1028065
  have hstable : (prefixWord ++ tailWord_1028065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028065).length < 2 ^ (prefixWord ++ tailWord_1028065).sum := by decide
  have hdescent : baseEnd_1028065 < baseStart_1028065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028079 : List Nat := [1, 1, 2, 1, 4, 2, 3, 4, 1, 1, 3]
def baseStart_1028079 : Nat := 118140960795 + 1028079 * 2 ^ 59
def prefixEnd_1028079 : Nat := 4983230072969 + 3 ^ 40 * 1028079 * 2
def baseEnd_1028079 : Nat := 527898677793788369884457

theorem tailTrace_1028079 : CollatzResearch.WordTrace tailWord_1028079 prefixEnd_1028079 527898677793788369884457 := by
  unfold tailWord_1028079
  simp only [CollatzResearch.WordTrace]
  refine ⟨37497121642452839759519291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24998081094968559839679527 37497121642452839759519291)
  ·
    refine ⟨56245682463679259639278937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37497121642452839759519291 56245682463679259639278937)
    ·
      refine ⟨42184261847759444729459203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56245682463679259639278937 42184261847759444729459203)
      ·
        refine ⟨63276392771639167094188805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42184261847759444729459203 63276392771639167094188805)
        ·
          refine ⟨11864323644682343830160401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63276392771639167094188805 11864323644682343830160401)
          ·
            refine ⟨8898242733511757872620301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11864323644682343830160401 8898242733511757872620301)
            ·
              refine ⟨3336841025066909202232613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8898242733511757872620301 3336841025066909202232613)
              ·
                refine ⟨625657692200045475418615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3336841025066909202232613 625657692200045475418615)
                ·
                  refine ⟨938486538300068213127923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 625657692200045475418615 938486538300068213127923)
                  ·
                    refine ⟨1407729807450102319691885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 938486538300068213127923 1407729807450102319691885)
                    ·
                      refine ⟨527898677793788369884457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1407729807450102319691885 527898677793788369884457)
                      ·
                        rfl

theorem cell23_1028079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 4, 1, 1, 3].length) (baseStart_1028079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1028079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1028079 prefixEnd_1028079 := by exact prefixLift 1028079
  have htrace : WordTrace (prefixWord ++ tailWord_1028079) baseStart_1028079 baseEnd_1028079 := by
    simpa [prefixWord, tailWord_1028079, baseEnd_1028079] using wordTrace_append hprefix tailTrace_1028079
  have hstable : (prefixWord ++ tailWord_1028079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028079).length < 2 ^ (prefixWord ++ tailWord_1028079).sum := by decide
  have hdescent : baseEnd_1028079 < baseStart_1028079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028106 : List Nat := [3, 1, 2, 2, 4, 2, 1, 1, 2, 3, 2]
def baseStart_1028106 : Nat := 118140960795 + 1028106 * 2 ^ 59
def prefixEnd_1028106 : Nat := 4983230072969 + 3 ^ 40 * 1028106 * 2
def baseEnd_1028106 : Nat := 527912541771459764246833

theorem tailTrace_1028106 : CollatzResearch.WordTrace tailWord_1028106 prefixEnd_1028106 527912541771459764246833 := by
  unfold tailWord_1028106
  simp only [CollatzResearch.WordTrace]
  refine ⟨9374526603338755842688043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24998737608903348913834781 9374526603338755842688043)
  ·
    refine ⟨14061789905008133764032065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9374526603338755842688043 14061789905008133764032065)
    ·
      refine ⟨10546342428756100323024049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14061789905008133764032065 10546342428756100323024049)
      ·
        refine ⟨7909756821567075242268037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10546342428756100323024049 7909756821567075242268037)
        ·
          refine ⟨1483079404043826607925257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7909756821567075242268037 1483079404043826607925257)
          ·
            refine ⟨1112309553032869955943943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1483079404043826607925257 1112309553032869955943943)
            ·
              refine ⟨1668464329549304933915915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1112309553032869955943943 1668464329549304933915915)
              ·
                refine ⟨2502696494323957400873873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1668464329549304933915915 2502696494323957400873873)
                ·
                  refine ⟨1877022370742968050655405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2502696494323957400873873 1877022370742968050655405)
                  ·
                    refine ⟨703883389028613018995777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1877022370742968050655405 703883389028613018995777)
                    ·
                      refine ⟨527912541771459764246833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 703883389028613018995777 527912541771459764246833)
                      ·
                        rfl

theorem cell23_1028106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_1028106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1028106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1028106 prefixEnd_1028106 := by exact prefixLift 1028106
  have htrace : WordTrace (prefixWord ++ tailWord_1028106) baseStart_1028106 baseEnd_1028106 := by
    simpa [prefixWord, tailWord_1028106, baseEnd_1028106] using wordTrace_append hprefix tailTrace_1028106
  have hstable : (prefixWord ++ tailWord_1028106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028106).length < 2 ^ (prefixWord ++ tailWord_1028106).sum := by decide
  have hdescent : baseEnd_1028106 < baseStart_1028106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028115 : List Nat := [1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 4]
def baseStart_1028115 : Nat := 118140960795 + 1028115 * 2 ^ 59
def prefixEnd_1028115 : Nat := 4983230072969 + 3 ^ 40 * 1028115 * 2
def baseEnd_1028115 : Nat := 527917163097350229034291

theorem tailTrace_1028115 : CollatzResearch.WordTrace tailWord_1028115 prefixEnd_1028115 527917163097350229034291 := by
  unfold tailWord_1028115
  simp only [CollatzResearch.WordTrace]
  refine ⟨37498434670322417907829799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24998956446881611938553199 37498434670322417907829799)
  ·
    refine ⟨56247652005483626861744699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37498434670322417907829799 56247652005483626861744699)
    ·
      refine ⟨84371478008225440292617049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56247652005483626861744699 84371478008225440292617049)
      ·
        refine ⟨63278608506169080219462787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84371478008225440292617049 63278608506169080219462787)
        ·
          refine ⟨94917912759253620329194181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63278608506169080219462787 94917912759253620329194181)
          ·
            refine ⟨17797108642360053811723909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94917912759253620329194181 17797108642360053811723909)
            ·
              refine ⟨3336957870442510089698233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17797108642360053811723909 3336957870442510089698233)
              ·
                refine ⟨2502718402831882567273675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3336957870442510089698233 2502718402831882567273675)
                ·
                  refine ⟨3754077604247823850910513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2502718402831882567273675 3754077604247823850910513)
                  ·
                    refine ⟨2815558203185867888182885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3754077604247823850910513 2815558203185867888182885)
                    ·
                      refine ⟨527917163097350229034291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2815558203185867888182885 527917163097350229034291)
                      ·
                        rfl

theorem cell23_1028115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 4].length) (baseStart_1028115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1028115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1028115 prefixEnd_1028115 := by exact prefixLift 1028115
  have htrace : WordTrace (prefixWord ++ tailWord_1028115) baseStart_1028115 baseEnd_1028115 := by
    simpa [prefixWord, tailWord_1028115, baseEnd_1028115] using wordTrace_append hprefix tailTrace_1028115
  have hstable : (prefixWord ++ tailWord_1028115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028115).length < 2 ^ (prefixWord ++ tailWord_1028115).sum := by decide
  have hdescent : baseEnd_1028115 < baseStart_1028115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028116 : List Nat := [2, 4, 3, 2, 1, 1, 1, 3, 1, 5]
def baseStart_1028116 : Nat := 118140960795 + 1028116 * 2 ^ 59
def prefixEnd_1028116 : Nat := 4983230072969 + 3 ^ 40 * 1028116 * 2
def baseEnd_1028116 : Nat := 175972558859334908373929

theorem tailTrace_1028116 : CollatzResearch.WordTrace tailWord_1028116 prefixEnd_1028116 175972558859334908373929 := by
  unfold tailWord_1028116
  simp only [CollatzResearch.WordTrace]
  refine ⟨18749235571659397539308101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24998980762212530052410801 18749235571659397539308101)
  ·
    refine ⟨3515481669686137038620269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18749235571659397539308101 3515481669686137038620269)
    ·
      refine ⟨1318305626132301389482601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3515481669686137038620269 1318305626132301389482601)
      ·
        refine ⟨988729219599226042111951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1318305626132301389482601 988729219599226042111951)
        ·
          refine ⟨1483093829398839063167927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 988729219599226042111951 1483093829398839063167927)
          ·
            refine ⟨2224640744098258594751891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1483093829398839063167927 2224640744098258594751891)
            ·
              refine ⟨3336961116147387892127837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2224640744098258594751891 3336961116147387892127837)
              ·
                refine ⟨1251360418555270459547939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3336961116147387892127837 1251360418555270459547939)
                ·
                  refine ⟨1877040627832905689321909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1251360418555270459547939 1877040627832905689321909)
                  ·
                    refine ⟨175972558859334908373929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1877040627832905689321909 175972558859334908373929)
                    ·
                      rfl

theorem cell23_1028116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_1028116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1028116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1028116 prefixEnd_1028116 := by exact prefixLift 1028116
  have htrace : WordTrace (prefixWord ++ tailWord_1028116) baseStart_1028116 baseEnd_1028116 := by
    simpa [prefixWord, tailWord_1028116, baseEnd_1028116] using wordTrace_append hprefix tailTrace_1028116
  have hstable : (prefixWord ++ tailWord_1028116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028116).length < 2 ^ (prefixWord ++ tailWord_1028116).sum := by decide
  have hdescent : baseEnd_1028116 < baseStart_1028116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028119 : List Nat := [1, 1, 3, 5, 2, 1, 1, 3, 1, 1, 4]
def baseStart_1028119 : Nat := 118140960795 + 1028119 * 2 ^ 59
def prefixEnd_1028119 : Nat := 4983230072969 + 3 ^ 40 * 1028119 * 2
def baseEnd_1028119 : Nat := 527919217019968213384273

theorem tailTrace_1028119 : CollatzResearch.WordTrace tailWord_1028119 prefixEnd_1028119 527919217019968213384273 := by
  unfold tailWord_1028119
  simp only [CollatzResearch.WordTrace]
  refine ⟨37498580562307926590975411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24999053708205284393983607 37498580562307926590975411)
  ·
    refine ⟨56247870843461889886463117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37498580562307926590975411 56247870843461889886463117)
    ·
      refine ⟨21092951566298208707423669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56247870843461889886463117 21092951566298208707423669)
      ·
        refine ⟨1977464209340457066320969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21092951566298208707423669 1977464209340457066320969)
        ·
          refine ⟨1483098157005342799740727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1977464209340457066320969 1483098157005342799740727)
          ·
            refine ⟨2224647235508014199611091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1483098157005342799740727 2224647235508014199611091)
            ·
              refine ⟨3336970853262021299416637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2224647235508014199611091 3336970853262021299416637)
              ·
                refine ⟨1251364069973257987281239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3336970853262021299416637 1251364069973257987281239)
                ·
                  refine ⟨1877046104959886980921859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1251364069973257987281239 1877046104959886980921859)
                  ·
                    refine ⟨2815569157439830471382789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1877046104959886980921859 2815569157439830471382789)
                    ·
                      refine ⟨527919217019968213384273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2815569157439830471382789 527919217019968213384273)
                      ·
                        rfl

theorem cell23_1028119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_1028119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1028119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1028119 prefixEnd_1028119 := by exact prefixLift 1028119
  have htrace : WordTrace (prefixWord ++ tailWord_1028119) baseStart_1028119 baseEnd_1028119 := by
    simpa [prefixWord, tailWord_1028119, baseEnd_1028119] using wordTrace_append hprefix tailTrace_1028119
  have hstable : (prefixWord ++ tailWord_1028119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028119).length < 2 ^ (prefixWord ++ tailWord_1028119).sum := by decide
  have hdescent : baseEnd_1028119 < baseStart_1028119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028125 : List Nat := [1, 4, 2, 2, 2, 2, 10]
def baseStart_1028125 : Nat := 118140960795 + 1028125 * 2 ^ 59
def prefixEnd_1028125 : Nat := 4983230072969 + 3 ^ 40 * 1028125 * 2
def baseEnd_1028125 : Nat := 6517559233381422097645

theorem tailTrace_1028125 : CollatzResearch.WordTrace tailWord_1028125 prefixEnd_1028125 6517559233381422097645 := by
  unfold tailWord_1028125
  simp only [CollatzResearch.WordTrace]
  refine ⟨37498799400286189615693829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24999199600190793077129219 37498799400286189615693829)
  ·
    refine ⟨7031024887553660552942593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37498799400286189615693829 7031024887553660552942593)
    ·
      refine ⟨5273268665665245414706945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7031024887553660552942593 5273268665665245414706945)
      ·
        refine ⟨3954951499248934061030209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5273268665665245414706945 3954951499248934061030209)
        ·
          refine ⟨2966213624436700545772657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3954951499248934061030209 2966213624436700545772657)
          ·
            refine ⟨2224660218327525409329493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2966213624436700545772657 2224660218327525409329493)
            ·
              refine ⟨6517559233381422097645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2224660218327525409329493 6517559233381422097645)
              ·
                rfl

theorem cell23_1028125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 10].length) (baseStart_1028125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1028125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1028125 prefixEnd_1028125 := by exact prefixLift 1028125
  have htrace : WordTrace (prefixWord ++ tailWord_1028125) baseStart_1028125 baseEnd_1028125 := by
    simpa [prefixWord, tailWord_1028125, baseEnd_1028125] using wordTrace_append hprefix tailTrace_1028125
  have hstable : (prefixWord ++ tailWord_1028125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028125).length < 2 ^ (prefixWord ++ tailWord_1028125).sum := by decide
  have hdescent : baseEnd_1028125 < baseStart_1028125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028279 : List Nat := [1, 1, 3, 1, 4, 4, 1, 1, 2, 5]
def baseStart_1028279 : Nat := 118140960795 + 1028279 * 2 ^ 59
def prefixEnd_1028279 : Nat := 4983230072969 + 3 ^ 40 * 1028279 * 2
def baseEnd_1028279 : Nat := 176000457974895862461179

theorem tailTrace_1028279 : CollatzResearch.WordTrace tailWord_1028279 prefixEnd_1028279 176000457974895862461179 := by
  unfold tailWord_1028279
  simp only [CollatzResearch.WordTrace]
  refine ⟨37504416241728273916799891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25002944161152182611199927 37504416241728273916799891)
  ·
    refine ⟨56256624362592410875199837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37504416241728273916799891 56256624362592410875199837)
    ·
      refine ⟨21096234135972154078199939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56256624362592410875199837 21096234135972154078199939)
      ·
        refine ⟨31644351203958231117299909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21096234135972154078199939 31644351203958231117299909)
        ·
          refine ⟨5933315850742168334493733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31644351203958231117299909 5933315850742168334493733)
          ·
            refine ⟨1112496722014156562717575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5933315850742168334493733 1112496722014156562717575)
            ·
              refine ⟨1668745083021234844076363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1112496722014156562717575 1668745083021234844076363)
              ·
                refine ⟨2503117624531852266114545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1668745083021234844076363 2503117624531852266114545)
                ·
                  refine ⟨1877338218398889199585909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2503117624531852266114545 1877338218398889199585909)
                  ·
                    refine ⟨176000457974895862461179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1877338218398889199585909 176000457974895862461179)
                    ·
                      rfl

theorem cell23_1028279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 5].length) (baseStart_1028279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1028279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1028279 prefixEnd_1028279 := by exact prefixLift 1028279
  have htrace : WordTrace (prefixWord ++ tailWord_1028279) baseStart_1028279 baseEnd_1028279 := by
    simpa [prefixWord, tailWord_1028279, baseEnd_1028279] using wordTrace_append hprefix tailTrace_1028279
  have hstable : (prefixWord ++ tailWord_1028279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028279).length < 2 ^ (prefixWord ++ tailWord_1028279).sum := by decide
  have hdescent : baseEnd_1028279 < baseStart_1028279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028332 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 3]
def baseStart_1028332 : Nat := 118140960795 + 1028332 * 2 ^ 59
def prefixEnd_1028332 : Nat := 4983230072969 + 3 ^ 40 * 1028332 * 2
def baseEnd_1028332 : Nat := 528028588399375880020793

theorem tailTrace_1028332 : CollatzResearch.WordTrace tailWord_1028332 prefixEnd_1028332 528028588399375880020793 := by
  unfold tailWord_1028332
  simp only [CollatzResearch.WordTrace]
  refine ⟨18753174655268131984239625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25004232873690842645652833 18753174655268131984239625)
  ·
    refine ⟨14064880991451098988179719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18753174655268131984239625 14064880991451098988179719)
    ·
      refine ⟨21097321487176648482269579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14064880991451098988179719 21097321487176648482269579)
      ·
        refine ⟨31645982230764972723404369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21097321487176648482269579 31645982230764972723404369)
        ·
          refine ⟨23734486673073729542553277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31645982230764972723404369 23734486673073729542553277)
          ·
            refine ⟨8900432502402648578457479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23734486673073729542553277 8900432502402648578457479)
            ·
              refine ⟨13350648753603972867686219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8900432502402648578457479 13350648753603972867686219)
              ·
                refine ⟨20025973130405959301529329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13350648753603972867686219 20025973130405959301529329)
                ·
                  refine ⟨15019479847804469476146997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20025973130405959301529329 15019479847804469476146997)
                  ·
                    refine ⟨1408076235731669013388781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15019479847804469476146997 1408076235731669013388781)
                    ·
                      refine ⟨528028588399375880020793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1408076235731669013388781 528028588399375880020793)
                      ·
                        rfl

theorem cell23_1028332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 3].length) (baseStart_1028332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1028332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1028332 prefixEnd_1028332 := by exact prefixLift 1028332
  have htrace : WordTrace (prefixWord ++ tailWord_1028332) baseStart_1028332 baseEnd_1028332 := by
    simpa [prefixWord, tailWord_1028332, baseEnd_1028332] using wordTrace_append hprefix tailTrace_1028332
  have hstable : (prefixWord ++ tailWord_1028332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028332).length < 2 ^ (prefixWord ++ tailWord_1028332).sum := by decide
  have hdescent : baseEnd_1028332 < baseStart_1028332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028349 : List Nat := [1, 4, 1, 1, 1, 1, 1, 4, 5, 1, 3]
def baseStart_1028349 : Nat := 118140960795 + 1028349 * 2 ^ 59
def prefixEnd_1028349 : Nat := 4983230072969 + 3 ^ 40 * 1028349 * 2
def baseEnd_1028349 : Nat := 528037317570502313508215

theorem tailTrace_1028349 : CollatzResearch.WordTrace tailWord_1028349 prefixEnd_1028349 528037317570502313508215 := by
  unfold tailWord_1028349
  simp only [CollatzResearch.WordTrace]
  refine ⟨37506969351474675871848101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25004646234316450581232067 37506969351474675871848101)
  ·
    refine ⟨7032556753401501725971519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37506969351474675871848101 7032556753401501725971519)
    ·
      refine ⟨10548835130102252588957279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7032556753401501725971519 10548835130102252588957279)
      ·
        refine ⟨15823252695153378883435919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10548835130102252588957279 15823252695153378883435919)
        ·
          refine ⟨23734879042730068325153879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15823252695153378883435919 23734879042730068325153879)
          ·
            refine ⟨35602318564095102487730819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23734879042730068325153879 35602318564095102487730819)
            ·
              refine ⟨53403477846142653731596229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35602318564095102487730819 53403477846142653731596229)
              ·
                refine ⟨10013152096151747574674293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53403477846142653731596229 10013152096151747574674293)
                ·
                  refine ⟨938733009014226335125715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10013152096151747574674293 938733009014226335125715)
                  ·
                    refine ⟨1408099513521339502688573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 938733009014226335125715 1408099513521339502688573)
                    ·
                      refine ⟨528037317570502313508215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1408099513521339502688573 528037317570502313508215)
                      ·
                        rfl

theorem cell23_1028349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 5, 1, 3].length) (baseStart_1028349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1028349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1028349 prefixEnd_1028349 := by exact prefixLift 1028349
  have htrace : WordTrace (prefixWord ++ tailWord_1028349) baseStart_1028349 baseEnd_1028349 := by
    simpa [prefixWord, tailWord_1028349, baseEnd_1028349] using wordTrace_append hprefix tailTrace_1028349
  have hstable : (prefixWord ++ tailWord_1028349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028349).length < 2 ^ (prefixWord ++ tailWord_1028349).sum := by decide
  have hdescent : baseEnd_1028349 < baseStart_1028349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028386 : List Nat := [3, 3, 1, 1, 3, 1, 3, 2, 1, 5]
def baseStart_1028386 : Nat := 118140960795 + 1028386 * 2 ^ 59
def prefixEnd_1028386 : Nat := 4983230072969 + 3 ^ 40 * 1028386 * 2
def baseEnd_1028386 : Nat := 176018772118239556248515

theorem tailTrace_1028386 : CollatzResearch.WordTrace tailWord_1028386 prefixEnd_1028386 176018772118239556248515 := by
  unfold tailWord_1028386
  simp only [CollatzResearch.WordTrace]
  refine ⟨9377079713085157797736253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25005545901560420793963341 9377079713085157797736253)
  ·
    refine ⟨3516404892406934174151095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9377079713085157797736253 3516404892406934174151095)
    ·
      refine ⟨5274607338610401261226643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3516404892406934174151095 5274607338610401261226643)
      ·
        refine ⟨7911911007915601891839965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5274607338610401261226643 7911911007915601891839965)
        ·
          refine ⟨2966966627968350709439987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7911911007915601891839965 2966966627968350709439987)
          ·
            refine ⟨4450449941952526064159981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2966966627968350709439987 4450449941952526064159981)
            ·
              refine ⟨1668918728232197274059993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4450449941952526064159981 1668918728232197274059993)
              ·
                refine ⟨1251689046174147955544995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1668918728232197274059993 1251689046174147955544995)
                ·
                  refine ⟨1877533569261221933317493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1251689046174147955544995 1877533569261221933317493)
                  ·
                    refine ⟨176018772118239556248515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1877533569261221933317493 176018772118239556248515)
                    ·
                      rfl

theorem cell23_1028386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_1028386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1028386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1028386 prefixEnd_1028386 := by exact prefixLift 1028386
  have htrace : WordTrace (prefixWord ++ tailWord_1028386) baseStart_1028386 baseEnd_1028386 := by
    simpa [prefixWord, tailWord_1028386, baseEnd_1028386] using wordTrace_append hprefix tailTrace_1028386
  have hstable : (prefixWord ++ tailWord_1028386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028386).length < 2 ^ (prefixWord ++ tailWord_1028386).sum := by decide
  have hdescent : baseEnd_1028386 < baseStart_1028386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028436 : List Nat := [2, 4, 1, 1, 2, 3, 2, 1, 1, 2, 4]
def baseStart_1028436 : Nat := 118140960795 + 1028436 * 2 ^ 59
def prefixEnd_1028436 : Nat := 4983230072969 + 3 ^ 40 * 1028436 * 2
def baseEnd_1028436 : Nat := 528081990387443473120315

theorem tailTrace_1028436 : CollatzResearch.WordTrace tailWord_1028436 prefixEnd_1028436 528081990387443473120315 := by
  unfold tailWord_1028436
  simp only [CollatzResearch.WordTrace]
  refine ⟨18755071251079744865132581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25006761668106326486843441 18755071251079744865132581)
  ·
    refine ⟨3516575859577452162212359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18755071251079744865132581 3516575859577452162212359)
    ·
      refine ⟨5274863789366178243318539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3516575859577452162212359 5274863789366178243318539)
      ·
        refine ⟨7912295684049267364977809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5274863789366178243318539 7912295684049267364977809)
        ·
          refine ⟨5934221763036950523733357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7912295684049267364977809 5934221763036950523733357)
          ·
            refine ⟨2225333161138856446400009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5934221763036950523733357 2225333161138856446400009)
            ·
              refine ⟨1668999870854142334800007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2225333161138856446400009 1668999870854142334800007)
              ·
                refine ⟨2503499806281213502200011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1668999870854142334800007 2503499806281213502200011)
                ·
                  refine ⟨3755249709421820253300017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2503499806281213502200011 3755249709421820253300017)
                  ·
                    refine ⟨2816437282066365189975013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3755249709421820253300017 2816437282066365189975013)
                    ·
                      refine ⟨528081990387443473120315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2816437282066365189975013 528081990387443473120315)
                      ·
                        rfl

theorem cell23_1028436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_1028436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1028436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1028436 prefixEnd_1028436 := by exact prefixLift 1028436
  have htrace : WordTrace (prefixWord ++ tailWord_1028436) baseStart_1028436 baseEnd_1028436 := by
    simpa [prefixWord, tailWord_1028436, baseEnd_1028436] using wordTrace_append hprefix tailTrace_1028436
  have hstable : (prefixWord ++ tailWord_1028436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028436).length < 2 ^ (prefixWord ++ tailWord_1028436).sum := by decide
  have hdescent : baseEnd_1028436 < baseStart_1028436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028442 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 4, 7]
def baseStart_1028442 : Nat := 118140960795 + 1028442 * 2 ^ 59
def prefixEnd_1028442 : Nat := 4983230072969 + 3 ^ 40 * 1028442 * 2
def baseEnd_1028442 : Nat := 176028357090456816548429

theorem tailTrace_1028442 : CollatzResearch.WordTrace tailWord_1028442 prefixEnd_1028442 176028357090456816548429 := by
  unfold tailWord_1028442
  simp only [CollatzResearch.WordTrace]
  refine ⟨9377590335034438188745895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25006907560091835169989053 9377590335034438188745895)
  ·
    refine ⟨14066385502551657283118843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9377590335034438188745895 14066385502551657283118843)
    ·
      refine ⟨21099578253827485924678265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14066385502551657283118843 21099578253827485924678265)
      ·
        refine ⟨15824683690370614443508699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21099578253827485924678265 15824683690370614443508699)
        ·
          refine ⟨23737025535555921665263049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15824683690370614443508699 23737025535555921665263049)
          ·
            refine ⟨17802769151666941248947287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23737025535555921665263049 17802769151666941248947287)
            ·
              refine ⟨26704153727500411873420931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17802769151666941248947287 26704153727500411873420931)
              ·
                refine ⟨40056230591250617810131397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26704153727500411873420931 40056230591250617810131397)
                ·
                  refine ⟨7510543235859490839399637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40056230591250617810131397 7510543235859490839399637)
                  ·
                    refine ⟨176028357090456816548429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7510543235859490839399637 176028357090456816548429)
                    ·
                      rfl

theorem cell23_1028442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 4, 7].length) (baseStart_1028442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1028442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1028442 prefixEnd_1028442 := by exact prefixLift 1028442
  have htrace : WordTrace (prefixWord ++ tailWord_1028442) baseStart_1028442 baseEnd_1028442 := by
    simpa [prefixWord, tailWord_1028442, baseEnd_1028442] using wordTrace_append hprefix tailTrace_1028442
  have hstable : (prefixWord ++ tailWord_1028442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028442).length < 2 ^ (prefixWord ++ tailWord_1028442).sum := by decide
  have hdescent : baseEnd_1028442 < baseStart_1028442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028456 : List Nat := [2, 1, 4, 2, 2, 1, 2, 2, 1, 3, 3]
def baseStart_1028456 : Nat := 118140960795 + 1028456 * 2 ^ 59
def prefixEnd_1028456 : Nat := 4983230072969 + 3 ^ 40 * 1028456 * 2
def baseEnd_1028456 : Nat := 528092260000533394870223

theorem tailTrace_1028456 : CollatzResearch.WordTrace tailWord_1028456 prefixEnd_1028456 528092260000533394870223 := by
  unfold tailWord_1028456
  simp only [CollatzResearch.WordTrace]
  refine ⟨18755435981043516572996611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25007247974724688763995481 18755435981043516572996611)
  ·
    refine ⟨28133153971565274859494917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18755435981043516572996611 28133153971565274859494917)
    ·
      refine ⟨5274966369668489036155297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28133153971565274859494917 5274966369668489036155297)
      ·
        refine ⟨3956224777251366777116473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5274966369668489036155297 3956224777251366777116473)
        ·
          refine ⟨2967168582938525082837355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3956224777251366777116473 2967168582938525082837355)
          ·
            refine ⟨4450752874407787624256033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2967168582938525082837355 4450752874407787624256033)
            ·
              refine ⟨3338064655805840718192025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4450752874407787624256033 3338064655805840718192025)
              ·
                refine ⟨2503548491854380538644019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3338064655805840718192025 2503548491854380538644019)
                ·
                  refine ⟨3755322737781570807966029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2503548491854380538644019 3755322737781570807966029)
                  ·
                    refine ⟨1408246026668089052987261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3755322737781570807966029 1408246026668089052987261)
                    ·
                      refine ⟨528092260000533394870223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1408246026668089052987261 528092260000533394870223)
                      ·
                        rfl

theorem cell23_1028456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_1028456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1028456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1028456 prefixEnd_1028456 := by exact prefixLift 1028456
  have htrace : WordTrace (prefixWord ++ tailWord_1028456) baseStart_1028456 baseEnd_1028456 := by
    simpa [prefixWord, tailWord_1028456, baseEnd_1028456] using wordTrace_append hprefix tailTrace_1028456
  have hstable : (prefixWord ++ tailWord_1028456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028456).length < 2 ^ (prefixWord ++ tailWord_1028456).sum := by decide
  have hdescent : baseEnd_1028456 < baseStart_1028456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028460 : List Nat := [2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 3]
def baseStart_1028460 : Nat := 118140960795 + 1028460 * 2 ^ 59
def prefixEnd_1028460 : Nat := 4983230072969 + 3 ^ 40 * 1028460 * 2
def baseEnd_1028460 : Nat := 528094313923151379220205

theorem tailTrace_1028460 : CollatzResearch.WordTrace tailWord_1028460 prefixEnd_1028460 528094313923151379220205 := by
  unfold tailWord_1028460
  simp only [CollatzResearch.WordTrace]
  refine ⟨18755508927036270914569417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25007345236048361219425889 18755508927036270914569417)
  ·
    refine ⟨14066631695277203185927063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18755508927036270914569417 14066631695277203185927063)
    ·
      refine ⟨21099947542915804778890595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14066631695277203185927063 21099947542915804778890595)
      ·
        refine ⟨31649921314373707168335893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21099947542915804778890595 31649921314373707168335893)
        ·
          refine ⟨1483590061611267523515745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31649921314373707168335893 1483590061611267523515745)
          ·
            refine ⟨1112692546208450642636809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1483590061611267523515745 1112692546208450642636809)
            ·
              refine ⟨834519409656337981977607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1112692546208450642636809 834519409656337981977607)
              ·
                refine ⟨1251779114484506972966411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 834519409656337981977607 1251779114484506972966411)
                ·
                  refine ⟨1877668671726760459449617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1251779114484506972966411 1877668671726760459449617)
                  ·
                    refine ⟨1408251503795070344587213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1877668671726760459449617 1408251503795070344587213)
                    ·
                      refine ⟨528094313923151379220205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1408251503795070344587213 528094313923151379220205)
                      ·
                        rfl

theorem cell23_1028460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 3].length) (baseStart_1028460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1028460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1028460 prefixEnd_1028460 := by exact prefixLift 1028460
  have htrace : WordTrace (prefixWord ++ tailWord_1028460) baseStart_1028460 baseEnd_1028460 := by
    simpa [prefixWord, tailWord_1028460, baseEnd_1028460] using wordTrace_append hprefix tailTrace_1028460
  have hstable : (prefixWord ++ tailWord_1028460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028460).length < 2 ^ (prefixWord ++ tailWord_1028460).sum := by decide
  have hdescent : baseEnd_1028460 < baseStart_1028460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028489 : List Nat := [1, 2, 1, 1, 6, 1, 2, 1, 2, 6]
def baseStart_1028489 : Nat := 118140960795 + 1028489 * 2 ^ 59
def prefixEnd_1028489 : Nat := 4983230072969 + 3 ^ 40 * 1028489 * 2
def baseEnd_1028489 : Nat := 176036401620710588585857

theorem tailTrace_1028489 : CollatzResearch.WordTrace tailWord_1028489 prefixEnd_1028489 176036401620710588585857 := by
  unfold tailWord_1028489
  simp only [CollatzResearch.WordTrace]
  refine ⟨37512075570967479781944521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25008050380644986521296347 37512075570967479781944521)
  ·
    refine ⟨28134056678225609836458391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37512075570967479781944521 28134056678225609836458391)
    ·
      refine ⟨42201085017338414754687587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28134056678225609836458391 42201085017338414754687587)
      ·
        refine ⟨63301627526007622132031381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42201085017338414754687587 63301627526007622132031381)
        ·
          refine ⟨2967263790281607287438971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 63301627526007622132031381 2967263790281607287438971)
          ·
            refine ⟨4450895685422410931158457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2967263790281607287438971 4450895685422410931158457)
            ·
              refine ⟨3338171764066808198368843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4450895685422410931158457 3338171764066808198368843)
              ·
                refine ⟨5007257646100212297553265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3338171764066808198368843 5007257646100212297553265)
                ·
                  refine ⟨3755443234575159223164949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5007257646100212297553265 3755443234575159223164949)
                  ·
                    refine ⟨176036401620710588585857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3755443234575159223164949 176036401620710588585857)
                    ·
                      rfl

theorem cell23_1028489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 6].length) (baseStart_1028489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1028489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1028489 prefixEnd_1028489 := by exact prefixLift 1028489
  have htrace : WordTrace (prefixWord ++ tailWord_1028489) baseStart_1028489 baseEnd_1028489 := by
    simpa [prefixWord, tailWord_1028489, baseEnd_1028489] using wordTrace_append hprefix tailTrace_1028489
  have hstable : (prefixWord ++ tailWord_1028489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028489).length < 2 ^ (prefixWord ++ tailWord_1028489).sum := by decide
  have hdescent : baseEnd_1028489 < baseStart_1028489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028490 : List Nat := [3, 1, 2, 5, 1, 2, 1, 1, 1, 3, 3]
def baseStart_1028490 : Nat := 118140960795 + 1028490 * 2 ^ 59
def prefixEnd_1028490 : Nat := 4983230072969 + 3 ^ 40 * 1028490 * 2
def baseEnd_1028490 : Nat := 528109718342786261845067

theorem tailTrace_1028490 : CollatzResearch.WordTrace tailWord_1028490 prefixEnd_1028490 528109718342786261845067 := by
  unfold tailWord_1028490
  simp only [CollatzResearch.WordTrace]
  refine ⟨9378028010990964238182731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25008074695975904635153949 9378028010990964238182731)
  ·
    refine ⟨14067042016486446357274097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9378028010990964238182731 14067042016486446357274097)
    ·
      refine ⟨10550281512364834767955573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14067042016486446357274097 10550281512364834767955573)
      ·
        refine ⟨989088891784203259495835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10550281512364834767955573 989088891784203259495835)
        ·
          refine ⟨1483633337676304889243753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 989088891784203259495835 1483633337676304889243753)
          ·
            refine ⟨1112725003257228666932815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1483633337676304889243753 1112725003257228666932815)
            ·
              refine ⟨1669087504885843000399223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1112725003257228666932815 1669087504885843000399223)
              ·
                refine ⟨2503631257328764500598835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1669087504885843000399223 2503631257328764500598835)
                ·
                  refine ⟨3755446885993146750898253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2503631257328764500598835 3755446885993146750898253)
                  ·
                    refine ⟨1408292582247430031586845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3755446885993146750898253 1408292582247430031586845)
                    ·
                      refine ⟨528109718342786261845067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1408292582247430031586845 528109718342786261845067)
                      ·
                        rfl

theorem cell23_1028490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_1028490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1028490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1028490 prefixEnd_1028490 := by exact prefixLift 1028490
  have htrace : WordTrace (prefixWord ++ tailWord_1028490) baseStart_1028490 baseEnd_1028490 := by
    simpa [prefixWord, tailWord_1028490, baseEnd_1028490] using wordTrace_append hprefix tailTrace_1028490
  have hstable : (prefixWord ++ tailWord_1028490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028490).length < 2 ^ (prefixWord ++ tailWord_1028490).sum := by decide
  have hdescent : baseEnd_1028490 < baseStart_1028490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028643 : List Nat := [1, 1, 1, 4, 4, 3, 1, 2, 6]
def baseStart_1028643 : Nat := 118140960795 + 1028643 * 2 ^ 59
def prefixEnd_1028643 : Nat := 4983230072969 + 3 ^ 40 * 1028643 * 2
def baseEnd_1028643 : Nat := 58687586764769351470207

theorem tailTrace_1028643 : CollatzResearch.WordTrace tailWord_1028643 prefixEnd_1028643 58687586764769351470207 := by
  unfold tailWord_1028643
  simp only [CollatzResearch.WordTrace]
  refine ⟨37517692412409564083050583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25011794941606376055367055 37517692412409564083050583)
  ·
    refine ⟨56276538618614346124575875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37517692412409564083050583 56276538618614346124575875)
    ·
      refine ⟨84414807927921519186863813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56276538618614346124575875 84414807927921519186863813)
      ·
        refine ⟨15827776486485284847536965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84414807927921519186863813 15827776486485284847536965)
        ·
          refine ⟨2967708091215990908913181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15827776486485284847536965 2967708091215990908913181)
          ·
            refine ⟨1112890534205996590842443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2967708091215990908913181 1112890534205996590842443)
            ·
              refine ⟨1669335801308994886263665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1112890534205996590842443 1669335801308994886263665)
              ·
                refine ⟨1252001850981746164697749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1669335801308994886263665 1252001850981746164697749)
                ·
                  refine ⟨58687586764769351470207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1252001850981746164697749 58687586764769351470207)
                  ·
                    rfl

theorem cell23_1028643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 6].length) (baseStart_1028643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1028643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1028643 prefixEnd_1028643 := by exact prefixLift 1028643
  have htrace : WordTrace (prefixWord ++ tailWord_1028643) baseStart_1028643 baseEnd_1028643 := by
    simpa [prefixWord, tailWord_1028643, baseEnd_1028643] using wordTrace_append hprefix tailTrace_1028643
  have hstable : (prefixWord ++ tailWord_1028643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028643).length < 2 ^ (prefixWord ++ tailWord_1028643).sum := by decide
  have hdescent : baseEnd_1028643 < baseStart_1028643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028647 : List Nat := [1, 1, 7, 2, 1, 1, 2, 1, 3, 4]
def baseStart_1028647 : Nat := 118140960795 + 1028647 * 2 ^ 59
def prefixEnd_1028647 : Nat := 4983230072969 + 3 ^ 40 * 1028647 * 2
def baseEnd_1028647 : Nat := 176063444935180715860615

theorem tailTrace_1028647 : CollatzResearch.WordTrace tailWord_1028647 prefixEnd_1028647 176063444935180715860615 := by
  unfold tailWord_1028647
  simp only [CollatzResearch.WordTrace]
  refine ⟨37517838304395072766196195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25011892202930048510797463 37517838304395072766196195)
  ·
    refine ⟨56276757456592609149294293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37517838304395072766196195 56276757456592609149294293)
    ·
      refine ⟨1318986502888889276936585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 56276757456592609149294293 1318986502888889276936585)
      ·
        refine ⟨989239877166666957702439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1318986502888889276936585 989239877166666957702439)
        ·
          refine ⟨1483859815750000436553659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 989239877166666957702439 1483859815750000436553659)
          ·
            refine ⟨2225789723625000654830489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1483859815750000436553659 2225789723625000654830489)
            ·
              refine ⟨1669342292718750491122867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2225789723625000654830489 1669342292718750491122867)
              ·
                refine ⟨2504013439078125736684301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1669342292718750491122867 2504013439078125736684301)
                ·
                  refine ⟨939005039654297151256613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2504013439078125736684301 939005039654297151256613)
                  ·
                    refine ⟨176063444935180715860615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 939005039654297151256613 176063444935180715860615)
                    ·
                      rfl

theorem cell23_1028647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_1028647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1028647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1028647 prefixEnd_1028647 := by exact prefixLift 1028647
  have htrace : WordTrace (prefixWord ++ tailWord_1028647) baseStart_1028647 baseEnd_1028647 := by
    simpa [prefixWord, tailWord_1028647, baseEnd_1028647] using wordTrace_append hprefix tailTrace_1028647
  have hstable : (prefixWord ++ tailWord_1028647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028647).length < 2 ^ (prefixWord ++ tailWord_1028647).sum := by decide
  have hdescent : baseEnd_1028647 < baseStart_1028647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028673 : List Nat := [1, 2, 5, 1, 1, 2, 1, 4, 1, 5]
def baseStart_1028673 : Nat := 118140960795 + 1028673 * 2 ^ 59
def prefixEnd_1028673 : Nat := 4983230072969 + 3 ^ 40 * 1028673 * 2
def baseEnd_1028673 : Nat := 176067895100853015285575

theorem tailTrace_1028673 : CollatzResearch.WordTrace tailWord_1028673 prefixEnd_1028673 176067895100853015285575 := by
  unfold tailWord_1028673
  simp only [CollatzResearch.WordTrace]
  refine ⟨37518786602300879206642673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25012524401533919471095115 37518786602300879206642673)
  ·
    refine ⟨28139089951725659404982005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37518786602300879206642673 28139089951725659404982005)
    ·
      refine ⟨2638039682974280569217063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28139089951725659404982005 2638039682974280569217063)
      ·
        refine ⟨3957059524461420853825595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2638039682974280569217063 3957059524461420853825595)
        ·
          refine ⟨5935589286692131280738393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3957059524461420853825595 5935589286692131280738393)
          ·
            refine ⟨4451691965019098460553795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5935589286692131280738393 4451691965019098460553795)
            ·
              refine ⟨6677537947528647690830693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4451691965019098460553795 6677537947528647690830693)
              ·
                refine ⟨1252038365161621442030755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6677537947528647690830693 1252038365161621442030755)
                ·
                  refine ⟨1878057547742432163046133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1252038365161621442030755 1878057547742432163046133)
                  ·
                    refine ⟨176067895100853015285575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1878057547742432163046133 176067895100853015285575)
                    ·
                      rfl

theorem cell23_1028673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_1028673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1028673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1028673 prefixEnd_1028673 := by exact prefixLift 1028673
  have htrace : WordTrace (prefixWord ++ tailWord_1028673) baseStart_1028673 baseEnd_1028673 := by
    simpa [prefixWord, tailWord_1028673, baseEnd_1028673] using wordTrace_append hprefix tailTrace_1028673
  have hstable : (prefixWord ++ tailWord_1028673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028673).length < 2 ^ (prefixWord ++ tailWord_1028673).sum := by decide
  have hdescent : baseEnd_1028673 < baseStart_1028673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028686 : List Nat := [4, 1, 1, 1, 1, 2, 2, 4, 1, 6]
def baseStart_1028686 : Nat := 118140960795 + 1028686 * 2 ^ 59
def prefixEnd_1028686 : Nat := 4983230072969 + 3 ^ 40 * 1028686 * 2
def baseEnd_1028686 : Nat := 176070120183689164998055

theorem tailTrace_1028686 : CollatzResearch.WordTrace tailWord_1028686 prefixEnd_1028686 176070120183689164998055 := by
  unfold tailWord_1028686
  simp only [CollatzResearch.WordTrace]
  refine ⟨4689907593906722803358239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25012840500835854951243941 4689907593906722803358239)
  ·
    refine ⟨7034861390860084205037359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4689907593906722803358239 7034861390860084205037359)
    ·
      refine ⟨10552292086290126307556039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7034861390860084205037359 10552292086290126307556039)
      ·
        refine ⟨15828438129435189461334059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10552292086290126307556039 15828438129435189461334059)
        ·
          refine ⟨23742657194152784192001089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15828438129435189461334059 23742657194152784192001089)
          ·
            refine ⟨17806992895614588144000817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23742657194152784192001089 17806992895614588144000817)
            ·
              refine ⟨13355244671710941108000613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17806992895614588144000817 13355244671710941108000613)
              ·
                refine ⟨2504108375945801457750115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13355244671710941108000613 2504108375945801457750115)
                ·
                  refine ⟨3756162563918702186625173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2504108375945801457750115 3756162563918702186625173)
                  ·
                    refine ⟨176070120183689164998055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3756162563918702186625173 176070120183689164998055)
                    ·
                      rfl

theorem cell23_1028686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_1028686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1028686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1028686 prefixEnd_1028686 := by exact prefixLift 1028686
  have htrace : WordTrace (prefixWord ++ tailWord_1028686) baseStart_1028686 baseEnd_1028686 := by
    simpa [prefixWord, tailWord_1028686, baseEnd_1028686] using wordTrace_append hprefix tailTrace_1028686
  have hstable : (prefixWord ++ tailWord_1028686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028686).length < 2 ^ (prefixWord ++ tailWord_1028686).sum := by decide
  have hdescent : baseEnd_1028686 < baseStart_1028686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028693 : List Nat := [1, 3, 2, 2, 1, 1, 4, 3, 1, 1, 4]
def baseStart_1028693 : Nat := 118140960795 + 1028693 * 2 ^ 59
def prefixEnd_1028693 : Nat := 4983230072969 + 3 ^ 40 * 1028693 * 2
def baseEnd_1028693 : Nat := 528213954915648967606633

theorem tailTrace_1028693 : CollatzResearch.WordTrace tailWord_1028693 prefixEnd_1028693 528213954915648967606633 := by
  unfold tailWord_1028693
  simp only [CollatzResearch.WordTrace]
  refine ⟨37519516062228422622370733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25013010708152281748247155 37519516062228422622370733)
  ·
    refine ⟨14069818523335658483389025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37519516062228422622370733 14069818523335658483389025)
    ·
      refine ⟨10552363892501743862541769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14069818523335658483389025 10552363892501743862541769)
      ·
        refine ⟨7914272919376307896906327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10552363892501743862541769 7914272919376307896906327)
        ·
          refine ⟨11871409379064461845359491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7914272919376307896906327 11871409379064461845359491)
          ·
            refine ⟨17807114068596692768039237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11871409379064461845359491 17807114068596692768039237)
            ·
              refine ⟨3338833887861879894007357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17807114068596692768039237 3338833887861879894007357)
              ·
                refine ⟨1252062707948204960252759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3338833887861879894007357 1252062707948204960252759)
                ·
                  refine ⟨1878094061922307440379139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1252062707948204960252759 1878094061922307440379139)
                  ·
                    refine ⟨2817141092883461160568709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1878094061922307440379139 2817141092883461160568709)
                    ·
                      refine ⟨528213954915648967606633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2817141092883461160568709 528213954915648967606633)
                      ·
                        rfl

theorem cell23_1028693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_1028693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1028693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1028693 prefixEnd_1028693 := by exact prefixLift 1028693
  have htrace : WordTrace (prefixWord ++ tailWord_1028693) baseStart_1028693 baseEnd_1028693 := by
    simpa [prefixWord, tailWord_1028693, baseEnd_1028693] using wordTrace_append hprefix tailTrace_1028693
  have hstable : (prefixWord ++ tailWord_1028693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028693).length < 2 ^ (prefixWord ++ tailWord_1028693).sum := by decide
  have hdescent : baseEnd_1028693 < baseStart_1028693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028696 : List Nat := [2, 1, 2, 2, 1, 2, 3, 3, 1, 1, 5]
def baseStart_1028696 : Nat := 118140960795 + 1028696 * 2 ^ 59
def prefixEnd_1028696 : Nat := 4983230072969 + 3 ^ 40 * 1028696 * 2
def baseEnd_1028696 : Nat := 528215495357612455869119

theorem tailTrace_1028696 : CollatzResearch.WordTrace tailWord_1028696 prefixEnd_1028696 528215495357612455869119 := by
  unfold tailWord_1028696
  simp only [CollatzResearch.WordTrace]
  refine ⟨18759812740608777067364971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25013083654145036089819961 18759812740608777067364971)
  ·
    refine ⟨28139719110913165601047457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18759812740608777067364971 28139719110913165601047457)
    ·
      refine ⟨21104789333184874200785593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28139719110913165601047457 21104789333184874200785593)
      ·
        refine ⟨15828591999888655650589195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21104789333184874200785593 15828591999888655650589195)
        ·
          refine ⟨23742887999832983475883793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15828591999888655650589195 23742887999832983475883793)
          ·
            refine ⟨17807165999874737606912845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23742887999832983475883793 17807165999874737606912845)
            ·
              refine ⟨6677687249953026602592317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17807165999874737606912845 6677687249953026602592317)
              ·
                refine ⟨2504132718732384975972119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6677687249953026602592317 2504132718732384975972119)
                ·
                  refine ⟨3756199078098577463958179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2504132718732384975972119 3756199078098577463958179)
                  ·
                    refine ⟨5634298617147866195937269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3756199078098577463958179 5634298617147866195937269)
                    ·
                      refine ⟨528215495357612455869119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5634298617147866195937269 528215495357612455869119)
                      ·
                        rfl

theorem cell23_1028696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_1028696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1028696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1028696 prefixEnd_1028696 := by exact prefixLift 1028696
  have htrace : WordTrace (prefixWord ++ tailWord_1028696) baseStart_1028696 baseEnd_1028696 := by
    simpa [prefixWord, tailWord_1028696, baseEnd_1028696] using wordTrace_append hprefix tailTrace_1028696
  have hstable : (prefixWord ++ tailWord_1028696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028696).length < 2 ^ (prefixWord ++ tailWord_1028696).sum := by decide
  have hdescent : baseEnd_1028696 < baseStart_1028696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028720 : List Nat := [2, 1, 1, 1, 7, 1, 1, 3, 2, 4]
def baseStart_1028720 : Nat := 118140960795 + 1028720 * 2 ^ 59
def prefixEnd_1028720 : Nat := 4983230072969 + 3 ^ 40 * 1028720 * 2
def baseEnd_1028720 : Nat := 176075939631106787323003

theorem tailTrace_1028720 : CollatzResearch.WordTrace tailWord_1028720 prefixEnd_1028720 176075939631106787323003 := by
  unfold tailWord_1028720
  simp only [CollatzResearch.WordTrace]
  refine ⟨18760250416565303116801807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25013667222087070822402409 18760250416565303116801807)
  ·
    refine ⟨28140375624847954675202711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18760250416565303116801807 28140375624847954675202711)
    ·
      refine ⟨42210563437271932012804067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28140375624847954675202711 42210563437271932012804067)
      ·
        refine ⟨63315845155907898019206101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42210563437271932012804067 63315845155907898019206101)
        ·
          refine ⟨1483965120841591359825143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 63315845155907898019206101 1483965120841591359825143)
          ·
            refine ⟨2225947681262387039737715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1483965120841591359825143 2225947681262387039737715)
            ·
              refine ⟨3338921521893580559606573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2225947681262387039737715 3338921521893580559606573)
              ·
                refine ⟨1252095570710092709852465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3338921521893580559606573 1252095570710092709852465)
                ·
                  refine ⟨939071678032569532389349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1252095570710092709852465 939071678032569532389349)
                  ·
                    refine ⟨176075939631106787323003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 939071678032569532389349 176075939631106787323003)
                    ·
                      rfl

theorem cell23_1028720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 2, 4].length) (baseStart_1028720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1028720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1028720 prefixEnd_1028720 := by exact prefixLift 1028720
  have htrace : WordTrace (prefixWord ++ tailWord_1028720) baseStart_1028720 baseEnd_1028720 := by
    simpa [prefixWord, tailWord_1028720, baseEnd_1028720] using wordTrace_append hprefix tailTrace_1028720
  have hstable : (prefixWord ++ tailWord_1028720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028720).length < 2 ^ (prefixWord ++ tailWord_1028720).sum := by decide
  have hdescent : baseEnd_1028720 < baseStart_1028720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028743 : List Nat := [1, 1, 4, 2, 1, 2, 3, 2, 1, 3, 3]
def baseStart_1028743 : Nat := 118140960795 + 1028743 * 2 ^ 59
def prefixEnd_1028743 : Nat := 4983230072969 + 3 ^ 40 * 1028743 * 2
def baseEnd_1028743 : Nat := 528239628948373771981403

theorem tailTrace_1028743 : CollatzResearch.WordTrace tailWord_1028743 prefixEnd_1028743 528239628948373771981403 := by
  unfold tailWord_1028743
  simp only [CollatzResearch.WordTrace]
  refine ⟨37521339712047281161690883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25014226474698187441127255 37521339712047281161690883)
  ·
    refine ⟨56282009568070921742536325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37521339712047281161690883 56282009568070921742536325)
    ·
      refine ⟨10552876794013297826725561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56282009568070921742536325 10552876794013297826725561)
      ·
        refine ⟨7914657595509973370044171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10552876794013297826725561 7914657595509973370044171)
        ·
          refine ⟨11871986393264960055066257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7914657595509973370044171 11871986393264960055066257)
          ·
            refine ⟨8903989794948720041299693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11871986393264960055066257 8903989794948720041299693)
            ·
              refine ⟨3338996173105770015487385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8903989794948720041299693 3338996173105770015487385)
              ·
                refine ⟨2504247129829327511615539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3338996173105770015487385 2504247129829327511615539)
                ·
                  refine ⟨3756370694743991267423309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2504247129829327511615539 3756370694743991267423309)
                  ·
                    refine ⟨1408639010528996725283741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3756370694743991267423309 1408639010528996725283741)
                    ·
                      refine ⟨528239628948373771981403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1408639010528996725283741 528239628948373771981403)
                      ·
                        rfl

theorem cell23_1028743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_1028743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1028743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1028743 prefixEnd_1028743 := by exact prefixLift 1028743
  have htrace : WordTrace (prefixWord ++ tailWord_1028743) baseStart_1028743 baseEnd_1028743 := by
    simpa [prefixWord, tailWord_1028743, baseEnd_1028743] using wordTrace_append hprefix tailTrace_1028743
  have hstable : (prefixWord ++ tailWord_1028743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028743).length < 2 ^ (prefixWord ++ tailWord_1028743).sum := by decide
  have hdescent : baseEnd_1028743 < baseStart_1028743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028800 : List Nat := [2, 1, 1, 2, 4, 2, 2, 2, 1, 4, 2]
def baseStart_1028800 : Nat := 118140960795 + 1028800 * 2 ^ 59
def prefixEnd_1028800 : Nat := 4983230072969 + 3 ^ 40 * 1028800 * 2
def baseEnd_1028800 : Nat := 528268897345680048968641

theorem tailTrace_1028800 : CollatzResearch.WordTrace tailWord_1028800 prefixEnd_1028800 528268897345680048968641 := by
  unfold tailWord_1028800
  simp only [CollatzResearch.WordTrace]
  refine ⟨18761709336420389948257927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25015612448560519931010569 18761709336420389948257927)
  ·
    refine ⟨28142564004630584922386891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18761709336420389948257927 28142564004630584922386891)
    ·
      refine ⟨42213846006945877383580337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28142564004630584922386891 42213846006945877383580337)
      ·
        refine ⟨31660384505209408037685253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42213846006945877383580337 31660384505209408037685253)
        ·
          refine ⟨5936322094726764007065985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31660384505209408037685253 5936322094726764007065985)
          ·
            refine ⟨4452241571045073005299489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5936322094726764007065985 4452241571045073005299489)
            ·
              refine ⟨3339181178283804753974617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4452241571045073005299489 3339181178283804753974617)
              ·
                refine ⟨2504385883712853565480963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3339181178283804753974617 2504385883712853565480963)
                ·
                  refine ⟨3756578825569280348221445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2504385883712853565480963 3756578825569280348221445)
                  ·
                    refine ⟨704358529794240065291521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3756578825569280348221445 704358529794240065291521)
                    ·
                      refine ⟨528268897345680048968641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 704358529794240065291521 528268897345680048968641)
                      ·
                        rfl

theorem cell23_1028800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 1, 4, 2].length) (baseStart_1028800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1028800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1028800 prefixEnd_1028800 := by exact prefixLift 1028800
  have htrace : WordTrace (prefixWord ++ tailWord_1028800) baseStart_1028800 baseEnd_1028800 := by
    simpa [prefixWord, tailWord_1028800, baseEnd_1028800] using wordTrace_append hprefix tailTrace_1028800
  have hstable : (prefixWord ++ tailWord_1028800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028800).length < 2 ^ (prefixWord ++ tailWord_1028800).sum := by decide
  have hdescent : baseEnd_1028800 < baseStart_1028800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028804 : List Nat := [2, 3, 3, 1, 1, 2, 4, 1, 1, 3, 2]
def baseStart_1028804 : Nat := 118140960795 + 1028804 * 2 ^ 59
def prefixEnd_1028804 : Nat := 4983230072969 + 3 ^ 40 * 1028804 * 2
def baseEnd_1028804 : Nat := 528270951268298033318623

theorem tailTrace_1028804 : CollatzResearch.WordTrace tailWord_1028804 prefixEnd_1028804 528270951268298033318623 := by
  unfold tailWord_1028804
  simp only [CollatzResearch.WordTrace]
  refine ⟨18761782282413144289830733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25015709709884192386440977 18761782282413144289830733)
  ·
    refine ⟨7035668355904929108686525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18761782282413144289830733 7035668355904929108686525)
    ·
      refine ⟨2638375633464348415757447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7035668355904929108686525 2638375633464348415757447)
      ·
        refine ⟨3957563450196522623636171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2638375633464348415757447 3957563450196522623636171)
        ·
          refine ⟨5936345175294783935454257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3957563450196522623636171 5936345175294783935454257)
          ·
            refine ⟨4452258881471087951590693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5936345175294783935454257 4452258881471087951590693)
            ·
              refine ⟨834798540275828990923255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4452258881471087951590693 834798540275828990923255)
              ·
                refine ⟨1252197810413743486384883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 834798540275828990923255 1252197810413743486384883)
                ·
                  refine ⟨1878296715620615229577325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1252197810413743486384883 1878296715620615229577325)
                  ·
                    refine ⟨704361268357730711091497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1878296715620615229577325 704361268357730711091497)
                    ·
                      refine ⟨528270951268298033318623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 704361268357730711091497 528270951268298033318623)
                      ·
                        rfl

theorem cell23_1028804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_1028804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1028804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1028804 prefixEnd_1028804 := by exact prefixLift 1028804
  have htrace : WordTrace (prefixWord ++ tailWord_1028804) baseStart_1028804 baseEnd_1028804 := by
    simpa [prefixWord, tailWord_1028804, baseEnd_1028804] using wordTrace_append hprefix tailTrace_1028804
  have hstable : (prefixWord ++ tailWord_1028804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028804).length < 2 ^ (prefixWord ++ tailWord_1028804).sum := by decide
  have hdescent : baseEnd_1028804 < baseStart_1028804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028823 : List Nat := [1, 1, 3, 2, 1, 5, 2, 1, 7]
def baseStart_1028823 : Nat := 118140960795 + 1028823 * 2 ^ 59
def prefixEnd_1028823 : Nat := 4983230072969 + 3 ^ 40 * 1028823 * 2
def baseEnd_1028823 : Nat := 58697856377859273220115

theorem tailTrace_1028823 : CollatzResearch.WordTrace tailWord_1028823 prefixEnd_1028823 58697856377859273220115 := by
  unfold tailWord_1028823
  simp only [CollatzResearch.WordTrace]
  refine ⟨37524257551757454824603123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25016171701171636549735415 37524257551757454824603123)
  ·
    refine ⟨56286386327636182236904685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37524257551757454824603123 56286386327636182236904685)
    ·
      refine ⟨21107394872863568338839257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56286386327636182236904685 21107394872863568338839257)
      ·
        refine ⟨15830546154647676254129443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21107394872863568338839257 15830546154647676254129443)
        ·
          refine ⟨23745819231971514381194165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15830546154647676254129443 23745819231971514381194165)
          ·
            refine ⟨2226170552997329473236953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23745819231971514381194165 2226170552997329473236953)
            ·
              refine ⟨1669627914747997104927715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2226170552997329473236953 1669627914747997104927715)
              ·
                refine ⟨2504441872121995657391573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1669627914747997104927715 2504441872121995657391573)
                ·
                  refine ⟨58697856377859273220115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2504441872121995657391573 58697856377859273220115)
                  ·
                    rfl

theorem cell23_1028823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 7].length) (baseStart_1028823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1028823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1028823 prefixEnd_1028823 := by exact prefixLift 1028823
  have htrace : WordTrace (prefixWord ++ tailWord_1028823) baseStart_1028823 baseEnd_1028823 := by
    simpa [prefixWord, tailWord_1028823, baseEnd_1028823] using wordTrace_append hprefix tailTrace_1028823
  have hstable : (prefixWord ++ tailWord_1028823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028823).length < 2 ^ (prefixWord ++ tailWord_1028823).sum := by decide
  have hdescent : baseEnd_1028823 < baseStart_1028823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028873 : List Nat := [1, 2, 1, 1, 3, 2, 3, 1, 4, 1, 4]
def baseStart_1028873 : Nat := 118140960795 + 1028873 * 2 ^ 59
def prefixEnd_1028873 : Nat := 4983230072969 + 3 ^ 40 * 1028873 * 2
def baseEnd_1028873 : Nat := 528306381433458263355805

theorem tailTrace_1028873 : CollatzResearch.WordTrace tailWord_1028873 prefixEnd_1028873 528306381433458263355805 := by
  unfold tailWord_1028873
  simp only [CollatzResearch.WordTrace]
  refine ⟨37526081201576313363923273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25017387467717542242615515 37526081201576313363923273)
  ·
    refine ⟨28144560901182235022942455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37526081201576313363923273 28144560901182235022942455)
    ·
      refine ⟨42216841351773352534413683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28144560901182235022942455 42216841351773352534413683)
      ·
        refine ⟨63325262027660028801620525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42216841351773352534413683 63325262027660028801620525)
        ·
          refine ⟨23746973260372510800607697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63325262027660028801620525 23746973260372510800607697)
          ·
            refine ⟨17810229945279383100455773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23746973260372510800607697 17810229945279383100455773)
            ·
              refine ⟨6678836229479768662670915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17810229945279383100455773 6678836229479768662670915)
              ·
                refine ⟨10018254344219652994006373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6678836229479768662670915 10018254344219652994006373)
                ·
                  refine ⟨1878422689541184936376195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10018254344219652994006373 1878422689541184936376195)
                  ·
                    refine ⟨2817634034311777404564293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1878422689541184936376195 2817634034311777404564293)
                    ·
                      refine ⟨528306381433458263355805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2817634034311777404564293 528306381433458263355805)
                      ·
                        rfl

theorem cell23_1028873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 1, 4].length) (baseStart_1028873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1028873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1028873 prefixEnd_1028873 := by exact prefixLift 1028873
  have htrace : WordTrace (prefixWord ++ tailWord_1028873) baseStart_1028873 baseEnd_1028873 := by
    simpa [prefixWord, tailWord_1028873, baseEnd_1028873] using wordTrace_append hprefix tailTrace_1028873
  have hstable : (prefixWord ++ tailWord_1028873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028873).length < 2 ^ (prefixWord ++ tailWord_1028873).sum := by decide
  have hdescent : baseEnd_1028873 < baseStart_1028873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028890 : List Nat := [3, 1, 1, 3, 2, 1, 2, 1, 1, 6, 2]
def baseStart_1028890 : Nat := 118140960795 + 1028890 * 2 ^ 59
def prefixEnd_1028890 : Nat := 4983230072969 + 3 ^ 40 * 1028890 * 2
def baseEnd_1028890 : Nat := 528315110604584696843227

theorem tailTrace_1028890 : CollatzResearch.WordTrace tailWord_1028890 prefixEnd_1028890 528315110604584696843227 := by
  unfold tailWord_1028890
  simp only [CollatzResearch.WordTrace]
  refine ⟨9381675310628681316823031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25017800828343150178194749 9381675310628681316823031)
  ·
    refine ⟨14072512965943021975234547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9381675310628681316823031 14072512965943021975234547)
    ·
      refine ⟨21108769448914532962851821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14072512965943021975234547 21108769448914532962851821)
      ·
        refine ⟨7915788543342949861069433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21108769448914532962851821 7915788543342949861069433)
        ·
          refine ⟨5936841407507212395802075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7915788543342949861069433 5936841407507212395802075)
          ·
            refine ⟨8905262111260818593703113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5936841407507212395802075 8905262111260818593703113)
            ·
              refine ⟨6678946583445613945277335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8905262111260818593703113 6678946583445613945277335)
              ·
                refine ⟨10018419875168420917916003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6678946583445613945277335 10018419875168420917916003)
                ·
                  refine ⟨15027629812752631376874005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10018419875168420917916003 15027629812752631376874005)
                  ·
                    refine ⟨704420147472779595790969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15027629812752631376874005 704420147472779595790969)
                    ·
                      refine ⟨528315110604584696843227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 704420147472779595790969 528315110604584696843227)
                      ·
                        rfl

theorem cell23_1028890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_1028890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1028890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1028890 prefixEnd_1028890 := by exact prefixLift 1028890
  have htrace : WordTrace (prefixWord ++ tailWord_1028890) baseStart_1028890 baseEnd_1028890 := by
    simpa [prefixWord, tailWord_1028890, baseEnd_1028890] using wordTrace_append hprefix tailTrace_1028890
  have hstable : (prefixWord ++ tailWord_1028890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028890).length < 2 ^ (prefixWord ++ tailWord_1028890).sum := by decide
  have hdescent : baseEnd_1028890 < baseStart_1028890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028960 : List Nat := [2, 1, 1, 3, 3, 1, 2, 4, 1, 5]
def baseStart_1028960 : Nat := 118140960795 + 1028960 * 2 ^ 59
def prefixEnd_1028960 : Nat := 4983230072969 + 3 ^ 40 * 1028960 * 2
def baseEnd_1028960 : Nat := 176117018083466474322635

theorem tailTrace_1028960 : CollatzResearch.WordTrace tailWord_1028960 prefixEnd_1028960 176117018083466474322635 := by
  unfold tailWord_1028960
  simp only [CollatzResearch.WordTrace]
  refine ⟨18764627176130563611170167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25019502901507418148226889 18764627176130563611170167)
  ·
    refine ⟨28146940764195845416755251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18764627176130563611170167 28146940764195845416755251)
    ·
      refine ⟨42220411146293768125132877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28146940764195845416755251 42220411146293768125132877)
      ·
        refine ⟨15832654179860163046924829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42220411146293768125132877 15832654179860163046924829)
        ·
          refine ⟨5937245317447561142596811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15832654179860163046924829 5937245317447561142596811)
          ·
            refine ⟨8905867976171341713895217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5937245317447561142596811 8905867976171341713895217)
            ·
              refine ⟨6679400982128506285421413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8905867976171341713895217 6679400982128506285421413)
              ·
                refine ⟨1252387684149094928516515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6679400982128506285421413 1252387684149094928516515)
                ·
                  refine ⟨1878581526223642392774773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1252387684149094928516515 1878581526223642392774773)
                  ·
                    refine ⟨176117018083466474322635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1878581526223642392774773 176117018083466474322635)
                    ·
                      rfl

theorem cell23_1028960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 1, 5].length) (baseStart_1028960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1028960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1028960 prefixEnd_1028960 := by exact prefixLift 1028960
  have htrace : WordTrace (prefixWord ++ tailWord_1028960) baseStart_1028960 baseEnd_1028960 := by
    simpa [prefixWord, tailWord_1028960, baseEnd_1028960] using wordTrace_append hprefix tailTrace_1028960
  have hstable : (prefixWord ++ tailWord_1028960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028960).length < 2 ^ (prefixWord ++ tailWord_1028960).sum := by decide
  have hdescent : baseEnd_1028960 < baseStart_1028960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028967 : List Nat := [1, 1, 5, 1, 2, 3, 1, 1, 1, 5, 2]
def baseStart_1028967 : Nat := 118140960795 + 1028967 * 2 ^ 59
def prefixEnd_1028967 : Nat := 4983230072969 + 3 ^ 40 * 1028967 * 2
def baseEnd_1028967 : Nat := 528354648614980895580373

theorem tailTrace_1028967 : CollatzResearch.WordTrace tailWord_1028967 prefixEnd_1028967 528354648614980895580373 := by
  unfold tailWord_1028967
  simp only [CollatzResearch.WordTrace]
  refine ⟨37529509663235767417845155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25019673108823844945230103 37529509663235767417845155)
  ·
    refine ⟨56294264494853651126767733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37529509663235767417845155 56294264494853651126767733)
    ·
      refine ⟨5277587296392529793134475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56294264494853651126767733 5277587296392529793134475)
      ·
        refine ⟨7916380944588794689701713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5277587296392529793134475 7916380944588794689701713)
        ·
          refine ⟨5937285708441596017276285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7916380944588794689701713 5937285708441596017276285)
          ·
            refine ⟨2226482140665598506478607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5937285708441596017276285 2226482140665598506478607)
            ·
              refine ⟨3339723210998397759717911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2226482140665598506478607 3339723210998397759717911)
              ·
                refine ⟨5009584816497596639576867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3339723210998397759717911 5009584816497596639576867)
                ·
                  refine ⟨7514377224746394959365301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5009584816497596639576867 7514377224746394959365301)
                  ·
                    refine ⟨704472864819974527440497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7514377224746394959365301 704472864819974527440497)
                    ·
                      refine ⟨528354648614980895580373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 704472864819974527440497 528354648614980895580373)
                      ·
                        rfl

theorem cell23_1028967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_1028967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1028967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1028967 prefixEnd_1028967 := by exact prefixLift 1028967
  have htrace : WordTrace (prefixWord ++ tailWord_1028967) baseStart_1028967 baseEnd_1028967 := by
    simpa [prefixWord, tailWord_1028967, baseEnd_1028967] using wordTrace_append hprefix tailTrace_1028967
  have hstable : (prefixWord ++ tailWord_1028967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028967).length < 2 ^ (prefixWord ++ tailWord_1028967).sum := by decide
  have hdescent : baseEnd_1028967 < baseStart_1028967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028977 : List Nat := [1, 2, 2, 2, 1, 4, 4, 1, 1, 5]
def baseStart_1028977 : Nat := 118140960795 + 1028977 * 2 ^ 59
def prefixEnd_1028977 : Nat := 4983230072969 + 3 ^ 40 * 1028977 * 2
def baseEnd_1028977 : Nat := 176119927807175285485109

theorem tailTrace_1028977 : CollatzResearch.WordTrace tailWord_1028977 prefixEnd_1028977 176119927807175285485109 := by
  unfold tailWord_1028977
  simp only [CollatzResearch.WordTrace]
  refine ⟨37529874393199539125709185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25019916262133026083806123 37529874393199539125709185)
  ·
    refine ⟨28147405794899654344281889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37529874393199539125709185 28147405794899654344281889)
    ·
      refine ⟨21110554346174740758211417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28147405794899654344281889 21110554346174740758211417)
      ·
        refine ⟨15832915759631055568658563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21110554346174740758211417 15832915759631055568658563)
        ·
          refine ⟨23749373639446583352987845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15832915759631055568658563 23749373639446583352987845)
          ·
            refine ⟨4453007557396234378685221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23749373639446583352987845 4453007557396234378685221)
            ·
              refine ⟨834938917011793946003479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4453007557396234378685221 834938917011793946003479)
              ·
                refine ⟨1252408375517690919005219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 834938917011793946003479 1252408375517690919005219)
                ·
                  refine ⟨1878612563276536378507829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1252408375517690919005219 1878612563276536378507829)
                  ·
                    refine ⟨176119927807175285485109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1878612563276536378507829 176119927807175285485109)
                    ·
                      rfl

theorem cell23_1028977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 1, 5].length) (baseStart_1028977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1028977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1028977 prefixEnd_1028977 := by exact prefixLift 1028977
  have htrace : WordTrace (prefixWord ++ tailWord_1028977) baseStart_1028977 baseEnd_1028977 := by
    simpa [prefixWord, tailWord_1028977, baseEnd_1028977] using wordTrace_append hprefix tailTrace_1028977
  have hstable : (prefixWord ++ tailWord_1028977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028977).length < 2 ^ (prefixWord ++ tailWord_1028977).sum := by decide
  have hdescent : baseEnd_1028977 < baseStart_1028977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028983 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 5]
def baseStart_1028983 : Nat := 118140960795 + 1028983 * 2 ^ 59
def prefixEnd_1028983 : Nat := 4983230072969 + 3 ^ 40 * 1028983 * 2
def baseEnd_1028983 : Nat := 528362864305452832980299

theorem tailTrace_1028983 : CollatzResearch.WordTrace tailWord_1028983 prefixEnd_1028983 528362864305452832980299 := by
  unfold tailWord_1028983
  simp only [CollatzResearch.WordTrace]
  refine ⟨37530093231177802150427603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25020062154118534766951735 37530093231177802150427603)
  ·
    refine ⟨56295139846766703225641405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37530093231177802150427603 56295139846766703225641405)
    ·
      refine ⟨21110677442537513709615527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56295139846766703225641405 21110677442537513709615527)
      ·
        refine ⟨31666016163806270564423291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21110677442537513709615527 31666016163806270564423291)
        ·
          refine ⟨47499024245709405846634937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31666016163806270564423291 47499024245709405846634937)
          ·
            refine ⟨35624268184282054384976203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47499024245709405846634937 35624268184282054384976203)
            ·
              refine ⟨53436402276423081577464305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35624268184282054384976203 53436402276423081577464305)
              ·
                refine ⟨40077301707317311183098229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53436402276423081577464305 40077301707317311183098229)
                ·
                  refine ⟨3757247035060997923415459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40077301707317311183098229 3757247035060997923415459)
                  ·
                    refine ⟨5635870552591496885123189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3757247035060997923415459 5635870552591496885123189)
                    ·
                      refine ⟨528362864305452832980299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5635870552591496885123189 528362864305452832980299)
                      ·
                        rfl

theorem cell23_1028983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 5].length) (baseStart_1028983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1028983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1028983 prefixEnd_1028983 := by exact prefixLift 1028983
  have htrace : WordTrace (prefixWord ++ tailWord_1028983) baseStart_1028983 baseEnd_1028983 := by
    simpa [prefixWord, tailWord_1028983, baseEnd_1028983] using wordTrace_append hprefix tailTrace_1028983
  have hstable : (prefixWord ++ tailWord_1028983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028983).length < 2 ^ (prefixWord ++ tailWord_1028983).sum := by decide
  have hdescent : baseEnd_1028983 < baseStart_1028983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029000 : List Nat := [2, 1, 3, 3, 2, 1, 1, 1, 3, 1, 5]
def baseStart_1029000 : Nat := 118140960795 + 1029000 * 2 ^ 59
def prefixEnd_1029000 : Nat := 4983230072969 + 3 ^ 40 * 1029000 * 2
def baseEnd_1029000 : Nat := 528371593476579266467721

theorem tailTrace_1029000 : CollatzResearch.WordTrace tailWord_1029000 prefixEnd_1029000 528371593476579266467721 := by
  unfold tailWord_1029000
  simp only [CollatzResearch.WordTrace]
  refine ⟨18765356636058107026898227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25020475514744142702530969 18765356636058107026898227)
  ·
    refine ⟨28148034954087160540347341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18765356636058107026898227 28148034954087160540347341)
    ·
      refine ⟨10555513107782685202630253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28148034954087160540347341 10555513107782685202630253)
      ·
        refine ⟨3958317415418506950986345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10555513107782685202630253 3958317415418506950986345)
        ·
          refine ⟨2968738061563880213239759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3958317415418506950986345 2968738061563880213239759)
          ·
            refine ⟨4453107092345820319859639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2968738061563880213239759 4453107092345820319859639)
            ·
              refine ⟨6679660638518730479789459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4453107092345820319859639 6679660638518730479789459)
              ·
                refine ⟨10019490957778095719684189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6679660638518730479789459 10019490957778095719684189)
                ·
                  refine ⟨3757309109166785894881571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10019490957778095719684189 3757309109166785894881571)
                  ·
                    refine ⟨5635963663750178842322357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3757309109166785894881571 5635963663750178842322357)
                    ·
                      refine ⟨528371593476579266467721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5635963663750178842322357 528371593476579266467721)
                      ·
                        rfl

theorem cell23_1029000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_1029000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1029000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1029000 prefixEnd_1029000 := by exact prefixLift 1029000
  have htrace : WordTrace (prefixWord ++ tailWord_1029000) baseStart_1029000 baseEnd_1029000 := by
    simpa [prefixWord, tailWord_1029000, baseEnd_1029000] using wordTrace_append hprefix tailTrace_1029000
  have hstable : (prefixWord ++ tailWord_1029000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029000).length < 2 ^ (prefixWord ++ tailWord_1029000).sum := by decide
  have hdescent : baseEnd_1029000 < baseStart_1029000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029047 : List Nat := [1, 1, 3, 1, 3, 1, 4, 1, 4, 1, 3]
def baseStart_1029047 : Nat := 118140960795 + 1029047 * 2 ^ 59
def prefixEnd_1029047 : Nat := 4983230072969 + 3 ^ 40 * 1029047 * 2
def baseEnd_1029047 : Nat := 528395727067340582580005

theorem tailTrace_1029047 : CollatzResearch.WordTrace tailWord_1029047 prefixEnd_1029047 528395727067340582580005 := by
  unfold tailWord_1029047
  simp only [CollatzResearch.WordTrace]
  refine ⟨37532427502945941080757395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25021618335297294053838263 37532427502945941080757395)
  ·
    refine ⟨56298641254418911621136093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37532427502945941080757395 56298641254418911621136093)
    ·
      refine ⟨21111990470407091857926035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56298641254418911621136093 21111990470407091857926035)
      ·
        refine ⟨31667985705610637786889053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21111990470407091857926035 31667985705610637786889053)
        ·
          refine ⟨11875494639603989170083395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31667985705610637786889053 11875494639603989170083395)
          ·
            refine ⟨17813241959405983755125093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11875494639603989170083395 17813241959405983755125093)
            ·
              refine ⟨3339982867388621954085955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17813241959405983755125093 3339982867388621954085955)
              ·
                refine ⟨5009974301082932931128933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3339982867388621954085955 5009974301082932931128933)
                ·
                  refine ⟨939370181453049924586675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5009974301082932931128933 939370181453049924586675)
                  ·
                    refine ⟨1409055272179574886880013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 939370181453049924586675 1409055272179574886880013)
                    ·
                      refine ⟨528395727067340582580005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1409055272179574886880013 528395727067340582580005)
                      ·
                        rfl

theorem cell23_1029047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 4, 1, 3].length) (baseStart_1029047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1029047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1029047 prefixEnd_1029047 := by exact prefixLift 1029047
  have htrace : WordTrace (prefixWord ++ tailWord_1029047) baseStart_1029047 baseEnd_1029047 := by
    simpa [prefixWord, tailWord_1029047, baseEnd_1029047] using wordTrace_append hprefix tailTrace_1029047
  have hstable : (prefixWord ++ tailWord_1029047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029047).length < 2 ^ (prefixWord ++ tailWord_1029047).sum := by decide
  have hdescent : baseEnd_1029047 < baseStart_1029047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029048 : List Nat := [2, 1, 2, 1, 2, 5, 3, 2, 1, 2, 2]
def baseStart_1029048 : Nat := 118140960795 + 1029048 * 2 ^ 59
def prefixEnd_1029048 : Nat := 4983230072969 + 3 ^ 40 * 1029048 * 2
def baseEnd_1029048 : Nat := 528396240547995078667501

theorem tailTrace_1029048 : CollatzResearch.WordTrace tailWord_1029048 prefixEnd_1029048 528396240547995078667501 := by
  unfold tailWord_1029048
  simp only [CollatzResearch.WordTrace]
  refine ⟨18766231987971159125771899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25021642650628212167695865 18766231987971159125771899)
  ·
    refine ⟨28149347981956738688657849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18766231987971159125771899 28149347981956738688657849)
    ·
      refine ⟨21112010986467554016493387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28149347981956738688657849 21112010986467554016493387)
      ·
        refine ⟨31668016479701331024740081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21112010986467554016493387 31668016479701331024740081)
        ·
          refine ⟨23751012359775998268555061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31668016479701331024740081 23751012359775998268555061)
          ·
            refine ⟨2226657408728999837677037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23751012359775998268555061 2226657408728999837677037)
            ·
              refine ⟨834996528273374939128889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2226657408728999837677037 834996528273374939128889)
              ·
                refine ⟨626247396205031204346667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 834996528273374939128889 626247396205031204346667)
                ·
                  refine ⟨939371094307546806520001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 626247396205031204346667 939371094307546806520001)
                  ·
                    refine ⟨704528320730660104890001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 939371094307546806520001 704528320730660104890001)
                    ·
                      refine ⟨528396240547995078667501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 704528320730660104890001 528396240547995078667501)
                      ·
                        rfl

theorem cell23_1029048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 2, 1, 2, 2].length) (baseStart_1029048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1029048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1029048 prefixEnd_1029048 := by exact prefixLift 1029048
  have htrace : WordTrace (prefixWord ++ tailWord_1029048) baseStart_1029048 baseEnd_1029048 := by
    simpa [prefixWord, tailWord_1029048, baseEnd_1029048] using wordTrace_append hprefix tailTrace_1029048
  have hstable : (prefixWord ++ tailWord_1029048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029048).length < 2 ^ (prefixWord ++ tailWord_1029048).sum := by decide
  have hdescent : baseEnd_1029048 < baseStart_1029048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029062 : List Nat := [6, 1, 3, 1, 2, 1, 1, 2, 1, 5]
def baseStart_1029062 : Nat := 118140960795 + 1029062 * 2 ^ 59
def prefixEnd_1029062 : Nat := 4983230072969 + 3 ^ 40 * 1029062 * 2
def baseEnd_1029062 : Nat := 176134476425719341297479

theorem tailTrace_1029062 : CollatzResearch.WordTrace tailWord_1029062 prefixEnd_1029062 176134476425719341297479 := by
  unfold tailWord_1029062
  simp only [CollatzResearch.WordTrace]
  refine ⟨1172905456184112457579795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25021983065261065761702293 1172905456184112457579795)
  ·
    refine ⟨1759358184276168686369693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1172905456184112457579795 1759358184276168686369693)
    ·
      refine ⟨659759319103563257388635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1759358184276168686369693 659759319103563257388635)
      ·
        refine ⟨989638978655344886082953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659759319103563257388635 989638978655344886082953)
        ·
          refine ⟨742229233991508664562215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 989638978655344886082953 742229233991508664562215)
          ·
            refine ⟨1113343850987262996843323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 742229233991508664562215 1113343850987262996843323)
            ·
              refine ⟨1670015776480894495264985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1113343850987262996843323 1670015776480894495264985)
              ·
                refine ⟨1252511832360670871448739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1670015776480894495264985 1252511832360670871448739)
                ·
                  refine ⟨1878767748541006307173109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1252511832360670871448739 1878767748541006307173109)
                  ·
                    refine ⟨176134476425719341297479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1878767748541006307173109 176134476425719341297479)
                    ·
                      rfl

theorem cell23_1029062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_1029062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1029062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1029062 prefixEnd_1029062 := by exact prefixLift 1029062
  have htrace : WordTrace (prefixWord ++ tailWord_1029062) baseStart_1029062 baseEnd_1029062 := by
    simpa [prefixWord, tailWord_1029062, baseEnd_1029062] using wordTrace_append hprefix tailTrace_1029062
  have hstable : (prefixWord ++ tailWord_1029062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029062).length < 2 ^ (prefixWord ++ tailWord_1029062).sum := by decide
  have hdescent : baseEnd_1029062 < baseStart_1029062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029091 : List Nat := [1, 1, 1, 6, 1, 1, 5, 1, 1, 3, 2]
def baseStart_1029091 : Nat := 118140960795 + 1029091 * 2 ^ 59
def prefixEnd_1029091 : Nat := 4983230072969 + 3 ^ 40 * 1029091 * 2
def baseEnd_1029091 : Nat := 528418320216138410429803

theorem tailTrace_1029091 : CollatzResearch.WordTrace tailWord_1029091 prefixEnd_1029091 528418320216138410429803 := by
  unfold tailWord_1029091
  simp only [CollatzResearch.WordTrace]
  refine ⟨37534032314786536595359127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25022688209857691063572751 37534032314786536595359127)
  ·
    refine ⟨56301048472179804893038691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37534032314786536595359127 56301048472179804893038691)
    ·
      refine ⟨84451572708269707339558037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56301048472179804893038691 84451572708269707339558037)
      ·
        refine ⟨3958667470700142531541783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 84451572708269707339558037 3958667470700142531541783)
        ·
          refine ⟨5938001206050213797312675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3958667470700142531541783 5938001206050213797312675)
          ·
            refine ⟨8907001809075320695969013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5938001206050213797312675 8907001809075320695969013)
            ·
              refine ⟨835031419600811315247095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8907001809075320695969013 835031419600811315247095)
              ·
                refine ⟨1252547129401216972870643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 835031419600811315247095 1252547129401216972870643)
                ·
                  refine ⟨1878820694101825459305965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1252547129401216972870643 1878820694101825459305965)
                  ·
                    refine ⟨704557760288184547239737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1878820694101825459305965 704557760288184547239737)
                    ·
                      refine ⟨528418320216138410429803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 704557760288184547239737 528418320216138410429803)
                      ·
                        rfl

theorem cell23_1029091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_1029091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1029091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1029091 prefixEnd_1029091 := by exact prefixLift 1029091
  have htrace : WordTrace (prefixWord ++ tailWord_1029091) baseStart_1029091 baseEnd_1029091 := by
    simpa [prefixWord, tailWord_1029091, baseEnd_1029091] using wordTrace_append hprefix tailTrace_1029091
  have hstable : (prefixWord ++ tailWord_1029091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029091).length < 2 ^ (prefixWord ++ tailWord_1029091).sum := by decide
  have hdescent : baseEnd_1029091 < baseStart_1029091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029121 : List Nat := [1, 2, 4, 1, 2, 2, 2, 3, 2, 2, 2]
def baseStart_1029121 : Nat := 118140960795 + 1029121 * 2 ^ 59
def prefixEnd_1029121 : Nat := 4983230072969 + 3 ^ 40 * 1029121 * 2
def baseEnd_1029121 : Nat := 528433724635773293054665

theorem tailTrace_1029121 : CollatzResearch.WordTrace tailWord_1029121 prefixEnd_1029121 528433724635773293054665 := by
  unfold tailWord_1029121
  simp only [CollatzResearch.WordTrace]
  refine ⟨37535126504677851718951217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25023417669785234479300811 37535126504677851718951217)
  ·
    refine ⟨28151344878508388789213413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37535126504677851718951217 28151344878508388789213413)
    ·
      refine ⟨5278377164720322897977515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28151344878508388789213413 5278377164720322897977515)
      ·
        refine ⟨7917565747080484346966273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5278377164720322897977515 7917565747080484346966273)
        ·
          refine ⟨5938174310310363260224705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7917565747080484346966273 5938174310310363260224705)
          ·
            refine ⟨4453630732732772445168529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5938174310310363260224705 4453630732732772445168529)
            ·
              refine ⟨3340223049549579333876397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4453630732732772445168529 3340223049549579333876397)
              ·
                refine ⟨1252583643581092250203649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3340223049549579333876397 1252583643581092250203649)
                ·
                  refine ⟨939437732685819187652737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1252583643581092250203649 939437732685819187652737)
                  ·
                    refine ⟨704578299514364390739553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 939437732685819187652737 704578299514364390739553)
                    ·
                      refine ⟨528433724635773293054665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 704578299514364390739553 528433724635773293054665)
                      ·
                        rfl

theorem cell23_1029121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_1029121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1029121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1029121 prefixEnd_1029121 := by exact prefixLift 1029121
  have htrace : WordTrace (prefixWord ++ tailWord_1029121) baseStart_1029121 baseEnd_1029121 := by
    simpa [prefixWord, tailWord_1029121, baseEnd_1029121] using wordTrace_append hprefix tailTrace_1029121
  have hstable : (prefixWord ++ tailWord_1029121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029121).length < 2 ^ (prefixWord ++ tailWord_1029121).sum := by decide
  have hdescent : baseEnd_1029121 < baseStart_1029121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029144 : List Nat := [2, 1, 2, 3, 2, 3, 2, 3, 5]
def baseStart_1029144 : Nat := 118140960795 + 1029144 * 2 ^ 59
def prefixEnd_1029144 : Nat := 4983230072969 + 3 ^ 40 * 1029144 * 2
def baseEnd_1029144 : Nat := 58716170521202967007451

theorem tailTrace_1029144 : CollatzResearch.WordTrace tailWord_1029144 prefixEnd_1029144 58716170521202967007451 := by
  unfold tailWord_1029144
  simp only [CollatzResearch.WordTrace]
  refine ⟨18767982691797263323519243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25023976922396351098025657 18767982691797263323519243)
  ·
    refine ⟨28151974037695894985278865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18767982691797263323519243 28151974037695894985278865)
    ·
      refine ⟨21113980528271921238959149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28151974037695894985278865 21113980528271921238959149)
      ·
        refine ⟨7917742698101970464609681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21113980528271921238959149 7917742698101970464609681)
        ·
          refine ⟨5938307023576477848457261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7917742698101970464609681 5938307023576477848457261)
          ·
            refine ⟨2226865133841179193171473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5938307023576477848457261 2226865133841179193171473)
            ·
              refine ⟨1670148850380884394878605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2226865133841179193171473 1670148850380884394878605)
              ·
                refine ⟨626305818892831648079477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1670148850380884394878605 626305818892831648079477)
                ·
                  refine ⟨58716170521202967007451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 626305818892831648079477 58716170521202967007451)
                  ·
                    rfl

theorem cell23_1029144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 3, 5].length) (baseStart_1029144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1029144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1029144 prefixEnd_1029144 := by exact prefixLift 1029144
  have htrace : WordTrace (prefixWord ++ tailWord_1029144) baseStart_1029144 baseEnd_1029144 := by
    simpa [prefixWord, tailWord_1029144, baseEnd_1029144] using wordTrace_append hprefix tailTrace_1029144
  have hstable : (prefixWord ++ tailWord_1029144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029144).length < 2 ^ (prefixWord ++ tailWord_1029144).sum := by decide
  have hdescent : baseEnd_1029144 < baseStart_1029144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029177 : List Nat := [1, 2, 1, 5, 2, 1, 1, 2, 1, 3, 4]
def baseStart_1029177 : Nat := 118140960795 + 1029177 * 2 ^ 59
def prefixEnd_1029177 : Nat := 4983230072969 + 3 ^ 40 * 1029177 * 2
def baseEnd_1029177 : Nat := 528462479552425073954407

theorem tailTrace_1029177 : CollatzResearch.WordTrace tailWord_1029177 prefixEnd_1029177 528462479552425073954407 := by
  unfold tailWord_1029177
  simp only [CollatzResearch.WordTrace]
  refine ⟨37537168992474973282989785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25024779328316648855326523 37537168992474973282989785)
  ·
    refine ⟨28152876744356229962242339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37537168992474973282989785 28152876744356229962242339)
    ·
      refine ⟨42229315116534344943363509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28152876744356229962242339 42229315116534344943363509)
      ·
        refine ⟨3958998292175094838440329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42229315116534344943363509 3958998292175094838440329)
        ·
          refine ⟨2969248719131321128830247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3958998292175094838440329 2969248719131321128830247)
          ·
            refine ⟨4453873078696981693245371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2969248719131321128830247 4453873078696981693245371)
            ·
              refine ⟨6680809618045472539868057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4453873078696981693245371 6680809618045472539868057)
              ·
                refine ⟨5010607213534104404901043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6680809618045472539868057 5010607213534104404901043)
                ·
                  refine ⟨7515910820301156607351565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5010607213534104404901043 7515910820301156607351565)
                  ·
                    refine ⟨2818466557612933727756837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7515910820301156607351565 2818466557612933727756837)
                    ·
                      refine ⟨528462479552425073954407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2818466557612933727756837 528462479552425073954407)
                      ·
                        rfl

theorem cell23_1029177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_1029177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1029177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1029177 prefixEnd_1029177 := by exact prefixLift 1029177
  have htrace : WordTrace (prefixWord ++ tailWord_1029177) baseStart_1029177 baseEnd_1029177 := by
    simpa [prefixWord, tailWord_1029177, baseEnd_1029177] using wordTrace_append hprefix tailTrace_1029177
  have hstable : (prefixWord ++ tailWord_1029177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029177).length < 2 ^ (prefixWord ++ tailWord_1029177).sum := by decide
  have hdescent : baseEnd_1029177 < baseStart_1029177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029187 : List Nat := [1, 1, 1, 3, 1, 2, 3, 4, 3, 4]
def baseStart_1029187 : Nat := 118140960795 + 1029187 * 2 ^ 59
def prefixEnd_1029187 : Nat := 4983230072969 + 3 ^ 40 * 1029187 * 2
def baseEnd_1029187 : Nat := 176155871452990011609787

theorem tailTrace_1029187 : CollatzResearch.WordTrace tailWord_1029187 prefixEnd_1029187 176155871452990011609787 := by
  unfold tailWord_1029187
  simp only [CollatzResearch.WordTrace]
  refine ⟨37537533722438744990853815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25025022481625829993902543 37537533722438744990853815)
  ·
    refine ⟨56306300583658117486280723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37537533722438744990853815 56306300583658117486280723)
    ·
      refine ⟨84459450875487176229421085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56306300583658117486280723 84459450875487176229421085)
      ·
        refine ⟨31672294078307691086032907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84459450875487176229421085 31672294078307691086032907)
        ·
          refine ⟨47508441117461536629049361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31672294078307691086032907 47508441117461536629049361)
          ·
            refine ⟨35631330838096152471787021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47508441117461536629049361 35631330838096152471787021)
            ·
              refine ⟨13361749064286057176920133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35631330838096152471787021 13361749064286057176920133)
              ·
                refine ⟨2505327949553635720672525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13361749064286057176920133 2505327949553635720672525)
                ·
                  refine ⟨939497981082613395252197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2505327949553635720672525 939497981082613395252197)
                  ·
                    refine ⟨176155871452990011609787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 939497981082613395252197 176155871452990011609787)
                    ·
                      rfl

theorem cell23_1029187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 3, 4].length) (baseStart_1029187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1029187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1029187 prefixEnd_1029187 := by exact prefixLift 1029187
  have htrace : WordTrace (prefixWord ++ tailWord_1029187) baseStart_1029187 baseEnd_1029187 := by
    simpa [prefixWord, tailWord_1029187, baseEnd_1029187] using wordTrace_append hprefix tailTrace_1029187
  have hstable : (prefixWord ++ tailWord_1029187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029187).length < 2 ^ (prefixWord ++ tailWord_1029187).sum := by decide
  have hdescent : baseEnd_1029187 < baseStart_1029187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029244 : List Nat := [2, 2, 2, 1, 1, 3, 2, 1, 5, 1, 3]
def baseStart_1029244 : Nat := 118140960795 + 1029244 * 2 ^ 59
def prefixEnd_1029244 : Nat := 4983230072969 + 3 ^ 40 * 1029244 * 2
def baseEnd_1029244 : Nat := 528496882756276311816599

theorem tailTrace_1029244 : CollatzResearch.WordTrace tailWord_1029244 prefixEnd_1029244 528496882756276311816599 := by
  unfold tailWord_1029244
  simp only [CollatzResearch.WordTrace]
  refine ⟨18769806341616121862839393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25026408455488162483785857 18769806341616121862839393)
  ·
    refine ⟨14077354756212091397129545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18769806341616121862839393 14077354756212091397129545)
    ·
      refine ⟨10558016067159068547847159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14077354756212091397129545 10558016067159068547847159)
      ·
        refine ⟨15837024100738602821770739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10558016067159068547847159 15837024100738602821770739)
        ·
          refine ⟨23755536151107904232656109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15837024100738602821770739 23755536151107904232656109)
          ·
            refine ⟨8908326056665464087246041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23755536151107904232656109 8908326056665464087246041)
            ·
              refine ⟨6681244542499098065434531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8908326056665464087246041 6681244542499098065434531)
              ·
                refine ⟨10021866813748647098151797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6681244542499098065434531 10021866813748647098151797)
                ·
                  refine ⟨939550013788935665451731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10021866813748647098151797 939550013788935665451731)
                  ·
                    refine ⟨1409325020683403498177597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 939550013788935665451731 1409325020683403498177597)
                    ·
                      refine ⟨528496882756276311816599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1409325020683403498177597 528496882756276311816599)
                      ·
                        rfl

theorem cell23_1029244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 5, 1, 3].length) (baseStart_1029244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1029244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1029244 prefixEnd_1029244 := by exact prefixLift 1029244
  have htrace : WordTrace (prefixWord ++ tailWord_1029244) baseStart_1029244 baseEnd_1029244 := by
    simpa [prefixWord, tailWord_1029244, baseEnd_1029244] using wordTrace_append hprefix tailTrace_1029244
  have hstable : (prefixWord ++ tailWord_1029244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029244).length < 2 ^ (prefixWord ++ tailWord_1029244).sum := by decide
  have hdescent : baseEnd_1029244 < baseStart_1029244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029271 : List Nat := [1, 1, 3, 3, 3, 1, 2, 2, 2, 3, 2]
def baseStart_1029271 : Nat := 118140960795 + 1029271 * 2 ^ 59
def prefixEnd_1029271 : Nat := 4983230072969 + 3 ^ 40 * 1029271 * 2
def baseEnd_1029271 : Nat := 528510746733947706178975

theorem tailTrace_1029271 : CollatzResearch.WordTrace tailWord_1029271 prefixEnd_1029271 528510746733947706178975 := by
  unfold tailWord_1029271
  simp only [CollatzResearch.WordTrace]
  refine ⟨37540597454134427336911667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25027064969422951557941111 37540597454134427336911667)
  ·
    refine ⟨56310896181201641005367501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37540597454134427336911667 56310896181201641005367501)
    ·
      refine ⟨21116586067950615377012813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56310896181201641005367501 21116586067950615377012813)
      ·
        refine ⟨7918719775481480766379805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21116586067950615377012813 7918719775481480766379805)
        ·
          refine ⟨2969519915805555287392427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7918719775481480766379805 2969519915805555287392427)
          ·
            refine ⟨4454279873708332931088641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2969519915805555287392427 4454279873708332931088641)
            ·
              refine ⟨3340709905281249698316481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4454279873708332931088641 3340709905281249698316481)
              ·
                refine ⟨2505532428960937273737361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3340709905281249698316481 2505532428960937273737361)
                ·
                  refine ⟨1879149321720702955303021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2505532428960937273737361 1879149321720702955303021)
                  ·
                    refine ⟨704680995645263608238633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1879149321720702955303021 704680995645263608238633)
                    ·
                      refine ⟨528510746733947706178975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 704680995645263608238633 528510746733947706178975)
                      ·
                        rfl

theorem cell23_1029271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_1029271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1029271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1029271 prefixEnd_1029271 := by exact prefixLift 1029271
  have htrace : WordTrace (prefixWord ++ tailWord_1029271) baseStart_1029271 baseEnd_1029271 := by
    simpa [prefixWord, tailWord_1029271, baseEnd_1029271] using wordTrace_append hprefix tailTrace_1029271
  have hstable : (prefixWord ++ tailWord_1029271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029271).length < 2 ^ (prefixWord ++ tailWord_1029271).sum := by decide
  have hdescent : baseEnd_1029271 < baseStart_1029271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029277 : List Nat := [1, 4, 2, 1, 1, 2, 1, 2, 3, 6]
def baseStart_1029277 : Nat := 118140960795 + 1029277 * 2 ^ 59
def prefixEnd_1029277 : Nat := 4983230072969 + 3 ^ 40 * 1029277 * 2
def baseEnd_1029277 : Nat := 176171275872624894234649

theorem tailTrace_1029277 : CollatzResearch.WordTrace tailWord_1029277 prefixEnd_1029277 176171275872624894234649 := by
  unfold tailWord_1029277
  simp only [CollatzResearch.WordTrace]
  refine ⟨37540816292112690361630085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25027210861408460241086723 37540816292112690361630085)
  ·
    refine ⟨7038903054771129442805641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37540816292112690361630085 7038903054771129442805641)
    ·
      refine ⟨5279177291078347082104231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7038903054771129442805641 5279177291078347082104231)
      ·
        refine ⟨7918765936617520623156347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5279177291078347082104231 7918765936617520623156347)
        ·
          refine ⟨11878148904926280934734521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7918765936617520623156347 11878148904926280934734521)
          ·
            refine ⟨8908611678694710701050891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11878148904926280934734521 8908611678694710701050891)
            ·
              refine ⟨13362917518042066051576337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8908611678694710701050891 13362917518042066051576337)
              ·
                refine ⟨10022188138531549538682253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13362917518042066051576337 10022188138531549538682253)
                ·
                  refine ⟨3758320551949331077005845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10022188138531549538682253 3758320551949331077005845)
                  ·
                    refine ⟨176171275872624894234649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3758320551949331077005845 176171275872624894234649)
                    ·
                      rfl

theorem cell23_1029277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_1029277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1029277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1029277 prefixEnd_1029277 := by exact prefixLift 1029277
  have htrace : WordTrace (prefixWord ++ tailWord_1029277) baseStart_1029277 baseEnd_1029277 := by
    simpa [prefixWord, tailWord_1029277, baseEnd_1029277] using wordTrace_append hprefix tailTrace_1029277
  have hstable : (prefixWord ++ tailWord_1029277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029277).length < 2 ^ (prefixWord ++ tailWord_1029277).sum := by decide
  have hdescent : baseEnd_1029277 < baseStart_1029277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029284 : List Nat := [2, 3, 1, 2, 3, 1, 1, 2, 3, 1, 4]
def baseStart_1029284 : Nat := 118140960795 + 1029284 * 2 ^ 59
def prefixEnd_1029284 : Nat := 4983230072969 + 3 ^ 40 * 1029284 * 2
def baseEnd_1029284 : Nat := 528517421982456155316415

theorem tailTrace_1029284 : CollatzResearch.WordTrace tailWord_1029284 prefixEnd_1029284 528517421982456155316415 := by
  unfold tailWord_1029284
  simp only [CollatzResearch.WordTrace]
  refine ⟨18770535801543665278567453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25027381068724887038089937 18770535801543665278567453)
  ·
    refine ⟨7038950925578874479462795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18770535801543665278567453 7038950925578874479462795)
    ·
      refine ⟨10558426388368311719194193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7038950925578874479462795 10558426388368311719194193)
      ·
        refine ⟨7918819791276233789395645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10558426388368311719194193 7918819791276233789395645)
        ·
          refine ⟨2969557421728587671023367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7918819791276233789395645 2969557421728587671023367)
          ·
            refine ⟨4454336132592881506535051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2969557421728587671023367 4454336132592881506535051)
            ·
              refine ⟨6681504198889322259802577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4454336132592881506535051 6681504198889322259802577)
              ·
                refine ⟨5011128149166991694851933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6681504198889322259802577 5011128149166991694851933)
                ·
                  refine ⟨1879173055937621885569475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5011128149166991694851933 1879173055937621885569475)
                  ·
                    refine ⟨2818759583906432828354213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1879173055937621885569475 2818759583906432828354213)
                    ·
                      refine ⟨528517421982456155316415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2818759583906432828354213 528517421982456155316415)
                      ·
                        rfl

theorem cell23_1029284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_1029284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1029284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1029284 prefixEnd_1029284 := by exact prefixLift 1029284
  have htrace : WordTrace (prefixWord ++ tailWord_1029284) baseStart_1029284 baseEnd_1029284 := by
    simpa [prefixWord, tailWord_1029284, baseEnd_1029284] using wordTrace_append hprefix tailTrace_1029284
  have hstable : (prefixWord ++ tailWord_1029284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029284).length < 2 ^ (prefixWord ++ tailWord_1029284).sum := by decide
  have hdescent : baseEnd_1029284 < baseStart_1029284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029404 : List Nat := [2, 2, 3, 1, 1, 1, 2, 3, 2, 2, 4]
def baseStart_1029404 : Nat := 118140960795 + 1029404 * 2 ^ 59
def prefixEnd_1029404 : Nat := 4983230072969 + 3 ^ 40 * 1029404 * 2
def baseEnd_1029404 : Nat := 528579039660995685815863

theorem tailTrace_1029404 : CollatzResearch.WordTrace tailWord_1029404 prefixEnd_1029404 528579039660995685815863 := by
  unfold tailWord_1029404
  simp only [CollatzResearch.WordTrace]
  refine ⟨18772724181326295525751633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25030298908435060701002177 18772724181326295525751633)
  ·
    refine ⟨14079543135994721644313725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18772724181326295525751633 14079543135994721644313725)
    ·
      refine ⟨5279828675998020616617647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14079543135994721644313725 5279828675998020616617647)
      ·
        refine ⟨7919743013997030924926471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5279828675998020616617647 7919743013997030924926471)
        ·
          refine ⟨11879614520995546387389707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7919743013997030924926471 11879614520995546387389707)
          ·
            refine ⟨17819421781493319581084561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11879614520995546387389707 17819421781493319581084561)
            ·
              refine ⟨13364566336119989685813421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17819421781493319581084561 13364566336119989685813421)
              ·
                refine ⟨5011712376044996132180033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13364566336119989685813421 5011712376044996132180033)
                ·
                  refine ⟨3758784282033747099135025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5011712376044996132180033 3758784282033747099135025)
                  ·
                    refine ⟨2819088211525310324351269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3758784282033747099135025 2819088211525310324351269)
                    ·
                      refine ⟨528579039660995685815863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2819088211525310324351269 528579039660995685815863)
                      ·
                        rfl

theorem cell23_1029404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_1029404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1029404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1029404 prefixEnd_1029404 := by exact prefixLift 1029404
  have htrace : WordTrace (prefixWord ++ tailWord_1029404) baseStart_1029404 baseEnd_1029404 := by
    simpa [prefixWord, tailWord_1029404, baseEnd_1029404] using wordTrace_append hprefix tailTrace_1029404
  have hstable : (prefixWord ++ tailWord_1029404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029404).length < 2 ^ (prefixWord ++ tailWord_1029404).sum := by decide
  have hdescent : baseEnd_1029404 < baseStart_1029404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029454 : List Nat := [4, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5]
def baseStart_1029454 : Nat := 118140960795 + 1029454 * 2 ^ 59
def prefixEnd_1029454 : Nat := 4983230072969 + 3 ^ 40 * 1029454 * 2
def baseEnd_1029454 : Nat := 528604713693720490190633

theorem tailTrace_1029454 : CollatzResearch.WordTrace tailWord_1029454 prefixEnd_1029454 528604713693720490190633 := by
  unfold tailWord_1029454
  simp only [CollatzResearch.WordTrace]
  refine ⟨4693409001558931198852927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25031514674980966393882277 4693409001558931198852927)
  ·
    refine ⟨7040113502338396798279391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4693409001558931198852927 7040113502338396798279391)
    ·
      refine ⟨10560170253507595197419087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7040113502338396798279391 10560170253507595197419087)
      ·
        refine ⟨15840255380261392796128631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10560170253507595197419087 15840255380261392796128631)
        ·
          refine ⟨23760383070392089194192947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15840255380261392796128631 23760383070392089194192947)
          ·
            refine ⟨35640574605588133791289421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23760383070392089194192947 35640574605588133791289421)
            ·
              refine ⟨13365215477095550171733533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35640574605588133791289421 13365215477095550171733533)
              ·
                refine ⟨5011955803910831314400075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13365215477095550171733533 5011955803910831314400075)
                ·
                  refine ⟨7517933705866246971600113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5011955803910831314400075 7517933705866246971600113)
                  ·
                    refine ⟨5638450279399685228700085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7517933705866246971600113 5638450279399685228700085)
                    ·
                      refine ⟨528604713693720490190633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5638450279399685228700085 528604713693720490190633)
                      ·
                        rfl

theorem cell23_1029454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_1029454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1029454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1029454 prefixEnd_1029454 := by exact prefixLift 1029454
  have htrace : WordTrace (prefixWord ++ tailWord_1029454) baseStart_1029454 baseEnd_1029454 := by
    simpa [prefixWord, tailWord_1029454, baseEnd_1029454] using wordTrace_append hprefix tailTrace_1029454
  have hstable : (prefixWord ++ tailWord_1029454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029454).length < 2 ^ (prefixWord ++ tailWord_1029454).sum := by decide
  have hdescent : baseEnd_1029454 < baseStart_1029454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029464 : List Nat := [2, 1, 2, 2, 1, 1, 4, 2, 1, 3, 4]
def baseStart_1029464 : Nat := 118140960795 + 1029464 * 2 ^ 59
def prefixEnd_1029464 : Nat := 4983230072969 + 3 ^ 40 * 1029464 * 2
def baseEnd_1029464 : Nat := 528609848500265451065587

theorem tailTrace_1029464 : CollatzResearch.WordTrace tailWord_1029464 prefixEnd_1029464 528609848500265451065587 := by
  unfold tailWord_1029464
  simp only [CollatzResearch.WordTrace]
  refine ⟨18773818371217610649343723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25031757828290147532458297 18773818371217610649343723)
  ·
    refine ⟨28160727556826415974015585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18773818371217610649343723 28160727556826415974015585)
    ·
      refine ⟨21120545667619811980511689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28160727556826415974015585 21120545667619811980511689)
      ·
        refine ⟨15840409250714858985383767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21120545667619811980511689 15840409250714858985383767)
        ·
          refine ⟨23760613876072288478075651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15840409250714858985383767 23760613876072288478075651)
          ·
            refine ⟨35640920814108432717113477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23760613876072288478075651 35640920814108432717113477)
            ·
              refine ⟨6682672652645331134458777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35640920814108432717113477 6682672652645331134458777)
              ·
                refine ⟨5012004489483998350844083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6682672652645331134458777 5012004489483998350844083)
                ·
                  refine ⟨7518006734225997526266125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5012004489483998350844083 7518006734225997526266125)
                  ·
                    refine ⟨2819252525334749072349797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7518006734225997526266125 2819252525334749072349797)
                    ·
                      refine ⟨528609848500265451065587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2819252525334749072349797 528609848500265451065587)
                      ·
                        rfl

theorem cell23_1029464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_1029464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1029464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1029464 prefixEnd_1029464 := by exact prefixLift 1029464
  have htrace : WordTrace (prefixWord ++ tailWord_1029464) baseStart_1029464 baseEnd_1029464 := by
    simpa [prefixWord, tailWord_1029464, baseEnd_1029464] using wordTrace_append hprefix tailTrace_1029464
  have hstable : (prefixWord ++ tailWord_1029464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029464).length < 2 ^ (prefixWord ++ tailWord_1029464).sum := by decide
  have hdescent : baseEnd_1029464 < baseStart_1029464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029501 : List Nat := [1, 4, 1, 1, 2, 2, 2, 1, 4, 2, 3]
def baseStart_1029501 : Nat := 118140960795 + 1029501 * 2 ^ 59
def prefixEnd_1029501 : Nat := 4983230072969 + 3 ^ 40 * 1029501 * 2
def baseEnd_1029501 : Nat := 528628847284481806302917

theorem tailTrace_1029501 : CollatzResearch.WordTrace tailWord_1029501 prefixEnd_1029501 528628847284481806302917 := by
  unfold tailWord_1029501
  simp only [CollatzResearch.WordTrace]
  refine ⟨37548986243301176617784357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25032657495534117745189571 37548986243301176617784357)
  ·
    refine ⟨7040434920618970615834567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37548986243301176617784357 7040434920618970615834567)
    ·
      refine ⟨10560652380928455923751851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7040434920618970615834567 10560652380928455923751851)
      ·
        refine ⟨15840978571392683885627777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10560652380928455923751851 15840978571392683885627777)
        ·
          refine ⟨11880733928544512914220833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15840978571392683885627777 11880733928544512914220833)
          ·
            refine ⟨8910550446408384685665625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11880733928544512914220833 8910550446408384685665625)
            ·
              refine ⟨6682912834806288514249219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8910550446408384685665625 6682912834806288514249219)
              ·
                refine ⟨10024369252209432771373829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6682912834806288514249219 10024369252209432771373829)
                ·
                  refine ⟨1879569234789268644632593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10024369252209432771373829 1879569234789268644632593)
                  ·
                    refine ⟨1409676926091951483474445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1879569234789268644632593 1409676926091951483474445)
                    ·
                      refine ⟨528628847284481806302917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1409676926091951483474445 528628847284481806302917)
                      ·
                        rfl

theorem cell23_1029501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 2, 3].length) (baseStart_1029501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1029501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1029501 prefixEnd_1029501 := by exact prefixLift 1029501
  have htrace : WordTrace (prefixWord ++ tailWord_1029501) baseStart_1029501 baseEnd_1029501 := by
    simpa [prefixWord, tailWord_1029501, baseEnd_1029501] using wordTrace_append hprefix tailTrace_1029501
  have hstable : (prefixWord ++ tailWord_1029501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029501).length < 2 ^ (prefixWord ++ tailWord_1029501).sum := by decide
  have hdescent : baseEnd_1029501 < baseStart_1029501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029508 : List Nat := [2, 3, 2, 1, 1, 4, 2, 1, 3, 4]
def baseStart_1029508 : Nat := 118140960795 + 1029508 * 2 ^ 59
def prefixEnd_1029508 : Nat := 4983230072969 + 3 ^ 40 * 1029508 * 2
def baseEnd_1029508 : Nat := 176210813883021092971795

theorem tailTrace_1029508 : CollatzResearch.WordTrace tailWord_1029508 prefixEnd_1029508 176210813883021092971795 := by
  unfold tailWord_1029508
  simp only [CollatzResearch.WordTrace]
  refine ⟨18774620777137908406644589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25032827702850544542192785 18774620777137908406644589)
  ·
    refine ⟨7040482791426715652491721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18774620777137908406644589 7040482791426715652491721)
    ·
      refine ⟨5280362093570036739368791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7040482791426715652491721 5280362093570036739368791)
      ·
        refine ⟨7920543140355055109053187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5280362093570036739368791 7920543140355055109053187)
        ·
          refine ⟨11880814710532582663579781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7920543140355055109053187 11880814710532582663579781)
          ·
            refine ⟨2227652758224859249421209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11880814710532582663579781 2227652758224859249421209)
            ·
              refine ⟨1670739568668644437065907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2227652758224859249421209 1670739568668644437065907)
              ·
                refine ⟨2506109353002966655598861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1670739568668644437065907 2506109353002966655598861)
                ·
                  refine ⟨939791007376112495849573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2506109353002966655598861 939791007376112495849573)
                  ·
                    refine ⟨176210813883021092971795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 939791007376112495849573 176210813883021092971795)
                    ·
                      rfl

theorem cell23_1029508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_1029508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1029508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1029508 prefixEnd_1029508 := by exact prefixLift 1029508
  have htrace : WordTrace (prefixWord ++ tailWord_1029508) baseStart_1029508 baseEnd_1029508 := by
    simpa [prefixWord, tailWord_1029508, baseEnd_1029508] using wordTrace_append hprefix tailTrace_1029508
  have hstable : (prefixWord ++ tailWord_1029508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029508).length < 2 ^ (prefixWord ++ tailWord_1029508).sum := by decide
  have hdescent : baseEnd_1029508 < baseStart_1029508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
