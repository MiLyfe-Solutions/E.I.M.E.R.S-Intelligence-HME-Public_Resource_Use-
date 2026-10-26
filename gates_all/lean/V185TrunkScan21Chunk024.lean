import V185TrunkScan21Chunk023

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_288889 : List Nat := [1, 2, 1, 3, 4, 1, 3, 3, 3]
def baseStart_288889 : Nat := 118140960795 + 288889 * 2 ^ 59
def prefixEnd_288889 : Nat := 4983230072969 + 3 ^ 40 * 288889 * 2
def baseEnd_288889 : Nat := 65928405687477979626191

theorem tailTrace_288889 : CollatzResearch.WordTrace tailWord_288889 prefixEnd_288889 65928405687477979626191 := by
  unfold tailWord_288889
  simp only [CollatzResearch.WordTrace]
  refine ⟨10536647450411966158285721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7024431633607977438857147 10536647450411966158285721)
  ·
    refine ⟨7902485587808974618714291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10536647450411966158285721 7902485587808974618714291)
    ·
      refine ⟨11853728381713461928071437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7902485587808974618714291 11853728381713461928071437)
      ·
        refine ⟨4445148143142548223026789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11853728381713461928071437 4445148143142548223026789)
        ·
          refine ⟨833465276839227791817523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4445148143142548223026789 833465276839227791817523)
          ·
            refine ⟨1250197915258841687726285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 833465276839227791817523 1250197915258841687726285)
            ·
              refine ⟨468824218222065632897357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1250197915258841687726285 468824218222065632897357)
              ·
                refine ⟨175809081833274612336509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 468824218222065632897357 175809081833274612336509)
                ·
                  refine ⟨65928405687477979626191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 175809081833274612336509 65928405687477979626191)
                  ·
                    rfl

theorem cell21_288889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 3, 3].length) (baseStart_288889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_288889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_288889 prefixEnd_288889 := by exact prefixLift 288889
  have htrace : WordTrace (prefixWord ++ tailWord_288889) baseStart_288889 baseEnd_288889 := by
    simpa [prefixWord, tailWord_288889, baseEnd_288889] using wordTrace_append hprefix tailTrace_288889
  have hstable : (prefixWord ++ tailWord_288889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288889).length < 2 ^ (prefixWord ++ tailWord_288889).sum := by decide
  have hdescent : baseEnd_288889 < baseStart_288889 := by decide
  rcases family_descends (prefixWord ++ tailWord_288889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288906 : List Nat := [3, 1, 2, 3, 1, 3, 3, 2, 3]
def baseStart_288906 : Nat := 118140960795 + 288906 * 2 ^ 59
def prefixEnd_288906 : Nat := 4983230072969 + 3 ^ 40 * 288906 * 2
def baseEnd_288906 : Nat := 65932285319089727842823

theorem tailTrace_288906 : CollatzResearch.WordTrace tailWord_288906 prefixEnd_288906 65932285319089727842823 := by
  unfold tailWord_288906
  simp only [CollatzResearch.WordTrace]
  refine ⟨2634316872837594515413643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7024844994233585374436381 2634316872837594515413643)
  ·
    refine ⟨3951475309256391773120465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2634316872837594515413643 3951475309256391773120465)
    ·
      refine ⟨2963606481942293829840349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3951475309256391773120465 2963606481942293829840349)
      ·
        refine ⟨1111352430728360186190131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2963606481942293829840349 1111352430728360186190131)
        ·
          refine ⟨1667028646092540279285197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1111352430728360186190131 1667028646092540279285197)
          ·
            refine ⟨625135742284702604731949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1667028646092540279285197 625135742284702604731949)
            ·
              refine ⟨234425903356763476774481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 625135742284702604731949 234425903356763476774481)
              ·
                refine ⟨175819427517572607580861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 234425903356763476774481 175819427517572607580861)
                ·
                  refine ⟨65932285319089727842823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 175819427517572607580861 65932285319089727842823)
                  ·
                    rfl

theorem cell21_288906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 2, 3].length) (baseStart_288906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_288906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_288906 prefixEnd_288906 := by exact prefixLift 288906
  have htrace : WordTrace (prefixWord ++ tailWord_288906) baseStart_288906 baseEnd_288906 := by
    simpa [prefixWord, tailWord_288906, baseEnd_288906] using wordTrace_append hprefix tailTrace_288906
  have hstable : (prefixWord ++ tailWord_288906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288906).length < 2 ^ (prefixWord ++ tailWord_288906).sum := by decide
  have hdescent : baseEnd_288906 < baseStart_288906 := by decide
  rcases family_descends (prefixWord ++ tailWord_288906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288965 : List Nat := [1, 3, 1, 1, 1, 1, 8, 2, 3]
def baseStart_288965 : Nat := 118140960795 + 288965 * 2 ^ 59
def prefixEnd_288965 : Nat := 4983230072969 + 3 ^ 40 * 288965 * 2
def baseEnd_288965 : Nat := 65945749922918736359369

theorem tailTrace_288965 : CollatzResearch.WordTrace tailWord_288965 prefixEnd_288965 65945749922918736359369 := by
  unfold tailWord_288965
  simp only [CollatzResearch.WordTrace]
  refine ⟨10539419398136631138052349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7026279598757754092034899 10539419398136631138052349)
  ·
    refine ⟨3952282274301236676769631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10539419398136631138052349 3952282274301236676769631)
    ·
      refine ⟨5928423411451855015154447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3952282274301236676769631 5928423411451855015154447)
      ·
        refine ⟨8892635117177782522731671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5928423411451855015154447 8892635117177782522731671)
        ·
          refine ⟨13338952675766673784097507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8892635117177782522731671 13338952675766673784097507)
          ·
            refine ⟨20008429013650010676146261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13338952675766673784097507 20008429013650010676146261)
            ·
              refine ⟨234473777503711062611089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 20008429013650010676146261 234473777503711062611089)
              ·
                refine ⟨175855333127783296958317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 234473777503711062611089 175855333127783296958317)
                ·
                  refine ⟨65945749922918736359369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 175855333127783296958317 65945749922918736359369)
                  ·
                    rfl

theorem cell21_288965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 2, 3].length) (baseStart_288965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_288965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_288965 prefixEnd_288965 := by exact prefixLift 288965
  have htrace : WordTrace (prefixWord ++ tailWord_288965) baseStart_288965 baseEnd_288965 := by
    simpa [prefixWord, tailWord_288965, baseEnd_288965] using wordTrace_append hprefix tailTrace_288965
  have hstable : (prefixWord ++ tailWord_288965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288965).length < 2 ^ (prefixWord ++ tailWord_288965).sum := by decide
  have hdescent : baseEnd_288965 < baseStart_288965 := by decide
  rcases family_descends (prefixWord ++ tailWord_288965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288993 : List Nat := [1, 2, 3, 1, 3, 1, 5, 5]
def baseStart_288993 : Nat := 118140960795 + 288993 * 2 ^ 59
def prefixEnd_288993 : Nat := 4983230072969 + 3 ^ 40 * 288993 * 2
def baseEnd_288993 : Nat := 21984046634798969964215

theorem tailTrace_288993 : CollatzResearch.WordTrace tailWord_288993 prefixEnd_288993 21984046634798969964215 := by
  unfold tailWord_288993
  simp only [CollatzResearch.WordTrace]
  refine ⟨10540440642035191920071633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7026960428023461280047755 10540440642035191920071633)
  ·
    refine ⟨7905330481526393940053725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10540440642035191920071633 7905330481526393940053725)
    ·
      refine ⟨2964498930572397727520147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7905330481526393940053725 2964498930572397727520147)
      ·
        refine ⟨4446748395858596591280221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2964498930572397727520147 4446748395858596591280221)
        ·
          refine ⟨1667530648446973721730083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4446748395858596591280221 1667530648446973721730083)
          ·
            refine ⟨2501295972670460582595125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1667530648446973721730083 2501295972670460582595125)
            ·
              refine ⟨234496497437855679618293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2501295972670460582595125 234496497437855679618293)
              ·
                refine ⟨21984046634798969964215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 234496497437855679618293 21984046634798969964215)
                ·
                  rfl

theorem cell21_288993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 5].length) (baseStart_288993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_288993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_288993 prefixEnd_288993 := by exact prefixLift 288993
  have htrace : WordTrace (prefixWord ++ tailWord_288993) baseStart_288993 baseEnd_288993 := by
    simpa [prefixWord, tailWord_288993, baseEnd_288993] using wordTrace_append hprefix tailTrace_288993
  have hstable : (prefixWord ++ tailWord_288993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288993).length < 2 ^ (prefixWord ++ tailWord_288993).sum := by decide
  have hdescent : baseEnd_288993 < baseStart_288993 := by decide
  rcases family_descends (prefixWord ++ tailWord_288993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289024 : List Nat := [2, 1, 1, 2, 1, 1, 6, 4, 3]
def baseStart_289024 : Nat := 118140960795 + 289024 * 2 ^ 59
def prefixEnd_289024 : Nat := 4983230072969 + 3 ^ 40 * 289024 * 2
def baseEnd_289024 : Nat := 65959214526747744875915

theorem tailTrace_289024 : CollatzResearch.WordTrace tailWord_289024 prefixEnd_289024 65959214526747744875915 := by
  unfold tailWord_289024
  simp only [CollatzResearch.WordTrace]
  refine ⟨5270785652461442107225063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7027714203281922809633417 5270785652461442107225063)
  ·
    refine ⟨7906178478692163160837595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5270785652461442107225063 7906178478692163160837595)
    ·
      refine ⟨11859267718038244741256393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7906178478692163160837595 11859267718038244741256393)
      ·
        refine ⟨8894450788528683555942295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11859267718038244741256393 8894450788528683555942295)
        ·
          refine ⟨13341676182793025333913443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8894450788528683555942295 13341676182793025333913443)
          ·
            refine ⟨20012514274189538000870165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13341676182793025333913443 20012514274189538000870165)
            ·
              refine ⟨938086606602634593790789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20012514274189538000870165 938086606602634593790789)
              ·
                refine ⟨175891238737993986335773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 938086606602634593790789 175891238737993986335773)
                ·
                  refine ⟨65959214526747744875915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 175891238737993986335773 65959214526747744875915)
                  ·
                    rfl

theorem cell21_289024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 4, 3].length) (baseStart_289024 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_289024 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_289024 prefixEnd_289024 := by exact prefixLift 289024
  have htrace : WordTrace (prefixWord ++ tailWord_289024) baseStart_289024 baseEnd_289024 := by
    simpa [prefixWord, tailWord_289024, baseEnd_289024] using wordTrace_append hprefix tailTrace_289024
  have hstable : (prefixWord ++ tailWord_289024).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289024).length < 2 ^ (prefixWord ++ tailWord_289024).sum := by decide
  have hdescent : baseEnd_289024 < baseStart_289024 := by decide
  rcases family_descends (prefixWord ++ tailWord_289024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289058 : List Nat := [3, 3, 1, 1, 3, 3, 1, 3, 3]
def baseStart_289058 : Nat := 118140960795 + 289058 * 2 ^ 59
def prefixEnd_289058 : Nat := 4983230072969 + 3 ^ 40 * 289058 * 2
def baseEnd_289058 : Nat := 65966973789971241309179

theorem tailTrace_289058 : CollatzResearch.WordTrace tailWord_289058 prefixEnd_289058 65966973789971241309179 := by
  unfold tailWord_289058
  simp only [CollatzResearch.WordTrace]
  refine ⟨2635702846699927005296957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7028540924533138680791885 2635702846699927005296957)
  ·
    refine ⟨988388567512472626986359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2635702846699927005296957 988388567512472626986359)
    ·
      refine ⟨1482582851268708940479539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 988388567512472626986359 1482582851268708940479539)
      ·
        refine ⟨2223874276903063410719309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1482582851268708940479539 2223874276903063410719309)
        ·
          refine ⟨833952853838648779019741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2223874276903063410719309 833952853838648779019741)
          ·
            refine ⟨312732320189493292132403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 833952853838648779019741 312732320189493292132403)
            ·
              refine ⟨469098480284239938198605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 312732320189493292132403 469098480284239938198605)
              ·
                refine ⟨175911930106589976824477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 469098480284239938198605 175911930106589976824477)
                ·
                  refine ⟨65966973789971241309179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 175911930106589976824477 65966973789971241309179)
                  ·
                    rfl

theorem cell21_289058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_289058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_289058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_289058 prefixEnd_289058 := by exact prefixLift 289058
  have htrace : WordTrace (prefixWord ++ tailWord_289058) baseStart_289058 baseEnd_289058 := by
    simpa [prefixWord, tailWord_289058, baseEnd_289058] using wordTrace_append hprefix tailTrace_289058
  have hstable : (prefixWord ++ tailWord_289058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289058).length < 2 ^ (prefixWord ++ tailWord_289058).sum := by decide
  have hdescent : baseEnd_289058 < baseStart_289058 := by decide
  rcases family_descends (prefixWord ++ tailWord_289058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289089 : List Nat := [1, 2, 5, 2, 2, 2, 2, 1, 4]
def baseStart_289089 : Nat := 118140960795 + 289089 * 2 ^ 59
def prefixEnd_289089 : Nat := 4983230072969 + 3 ^ 40 * 289089 * 2
def baseEnd_289089 : Nat := 65974048412322076292449

theorem tailTrace_289089 : CollatzResearch.WordTrace tailWord_289089 prefixEnd_289089 65974048412322076292449 := by
  unfold tailWord_289089
  simp only [CollatzResearch.WordTrace]
  refine ⟨10543942049687400315566321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7029294699791600210377547 10543942049687400315566321)
  ·
    refine ⟨7907956537265550236674741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10543942049687400315566321 7907956537265550236674741)
    ·
      refine ⟨741370925368645334688257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7907956537265550236674741 741370925368645334688257)
      ·
        refine ⟨556028194026484001016193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 741370925368645334688257 556028194026484001016193)
        ·
          refine ⟨417021145519863000762145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 556028194026484001016193 417021145519863000762145)
          ·
            refine ⟨312765859139897250571609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 417021145519863000762145 312765859139897250571609)
            ·
              refine ⟨234574394354922937928707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 312765859139897250571609 234574394354922937928707)
              ·
                refine ⟨351861591532384406893061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 234574394354922937928707 351861591532384406893061)
                ·
                  refine ⟨65974048412322076292449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 351861591532384406893061 65974048412322076292449)
                  ·
                    rfl

theorem cell21_289089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 4].length) (baseStart_289089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_289089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_289089 prefixEnd_289089 := by exact prefixLift 289089
  have htrace : WordTrace (prefixWord ++ tailWord_289089) baseStart_289089 baseEnd_289089 := by
    simpa [prefixWord, tailWord_289089, baseEnd_289089] using wordTrace_append hprefix tailTrace_289089
  have hstable : (prefixWord ++ tailWord_289089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289089).length < 2 ^ (prefixWord ++ tailWord_289089).sum := by decide
  have hdescent : baseEnd_289089 < baseStart_289089 := by decide
  rcases family_descends (prefixWord ++ tailWord_289089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289128 : List Nat := [2, 1, 4, 2, 2, 10]
def baseStart_289128 : Nat := 118140960795 + 289128 * 2 ^ 59
def prefixEnd_289128 : Nat := 4983230072969 + 3 ^ 40 * 289128 * 2
def baseEnd_289128 : Nat := 2443812916432099079347

theorem tailTrace_289128 : CollatzResearch.WordTrace tailWord_289128 prefixEnd_289128 2443812916432099079347 := by
  unfold tailWord_289128
  simp only [CollatzResearch.WordTrace]
  refine ⟨5272682248273054988118019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7030242997697406650824025 5272682248273054988118019)
  ·
    refine ⟨7909023372409582482177029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5272682248273054988118019 7909023372409582482177029)
    ·
      refine ⟨1482941882326796715408193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7909023372409582482177029 1482941882326796715408193)
      ·
        refine ⟨1112206411745097536556145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1482941882326796715408193 1112206411745097536556145)
        ·
          refine ⟨834154808808823152417109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1112206411745097536556145 834154808808823152417109)
          ·
            refine ⟨2443812916432099079347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 834154808808823152417109 2443812916432099079347)
            ·
              rfl

theorem cell21_289128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 10].length) (baseStart_289128 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_289128 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_289128 prefixEnd_289128 := by exact prefixLift 289128
  have htrace : WordTrace (prefixWord ++ tailWord_289128) baseStart_289128 baseEnd_289128 := by
    simpa [prefixWord, tailWord_289128, baseEnd_289128] using wordTrace_append hprefix tailTrace_289128
  have hstable : (prefixWord ++ tailWord_289128).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289128).length < 2 ^ (prefixWord ++ tailWord_289128).sum := by decide
  have hdescent : baseEnd_289128 < baseStart_289128 := by decide
  rcases family_descends (prefixWord ++ tailWord_289128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289159 : List Nat := [1, 1, 4, 2, 2, 1, 3, 2, 5]
def baseStart_289159 : Nat := 118140960795 + 289159 * 2 ^ 59
def prefixEnd_289159 : Nat := 4983230072969 + 3 ^ 40 * 289159 * 2
def baseEnd_289159 : Nat := 65990023366017510125639

theorem tailTrace_289159 : CollatzResearch.WordTrace tailWord_289159 prefixEnd_289159 65990023366017510125639 := by
  unfold tailWord_289159
  simp only [CollatzResearch.WordTrace]
  refine ⟨10546495159433802270614531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7030996772955868180409687 10546495159433802270614531)
  ·
    refine ⟨15819742739150703405921797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10546495159433802270614531 15819742739150703405921797)
    ·
      refine ⟨2966201763590756888610337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15819742739150703405921797 2966201763590756888610337)
      ·
        refine ⟨2224651322693067666457753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2966201763590756888610337 2224651322693067666457753)
        ·
          refine ⟨1668488492019800749843315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2224651322693067666457753 1668488492019800749843315)
          ·
            refine ⟨2502732738029701124764973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1668488492019800749843315 2502732738029701124764973)
            ·
              refine ⟨938524776761137921786865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2502732738029701124764973 938524776761137921786865)
              ·
                refine ⟨703893582570853441340149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 938524776761137921786865 703893582570853441340149)
                ·
                  refine ⟨65990023366017510125639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 703893582570853441340149 65990023366017510125639)
                  ·
                    rfl

theorem cell21_289159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 5].length) (baseStart_289159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_289159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_289159 prefixEnd_289159 := by exact prefixLift 289159
  have htrace : WordTrace (prefixWord ++ tailWord_289159) baseStart_289159 baseEnd_289159 := by
    simpa [prefixWord, tailWord_289159, baseEnd_289159] using wordTrace_append hprefix tailTrace_289159
  have hstable : (prefixWord ++ tailWord_289159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289159).length < 2 ^ (prefixWord ++ tailWord_289159).sum := by decide
  have hdescent : baseEnd_289159 < baseStart_289159 := by decide
  rcases family_descends (prefixWord ++ tailWord_289159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289173 : List Nat := [1, 3, 2, 1, 1, 2, 1, 4, 6]
def baseStart_289173 : Nat := 118140960795 + 289173 * 2 ^ 59
def prefixEnd_289173 : Nat := 4983230072969 + 3 ^ 40 * 289173 * 2
def baseEnd_289173 : Nat := 65993218356756596892277

theorem tailTrace_289173 : CollatzResearch.WordTrace tailWord_289173 prefixEnd_289173 65993218356756596892277 := by
  unfold tailWord_289173
  simp only [CollatzResearch.WordTrace]
  refine ⟨10547005781383082661624173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7031337187588721774416115 10547005781383082661624173)
  ·
    refine ⟨3955127168018655998109065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10547005781383082661624173 3955127168018655998109065)
    ·
      refine ⟨2966345376013991998581799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3955127168018655998109065 2966345376013991998581799)
      ·
        refine ⟨4449518064020987997872699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2966345376013991998581799 4449518064020987997872699)
        ·
          refine ⟨6674277096031481996809049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4449518064020987997872699 6674277096031481996809049)
          ·
            refine ⟨5005707822023611497606787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6674277096031481996809049 5005707822023611497606787)
            ·
              refine ⟨7508561733035417246410181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5005707822023611497606787 7508561733035417246410181)
              ·
                refine ⟨1407855324944140733701909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7508561733035417246410181 1407855324944140733701909)
                ·
                  refine ⟨65993218356756596892277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1407855324944140733701909 65993218356756596892277)
                  ·
                    rfl

theorem cell21_289173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_289173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_289173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_289173 prefixEnd_289173 := by exact prefixLift 289173
  have htrace : WordTrace (prefixWord ++ tailWord_289173) baseStart_289173 baseEnd_289173 := by
    simpa [prefixWord, tailWord_289173, baseEnd_289173] using wordTrace_append hprefix tailTrace_289173
  have hstable : (prefixWord ++ tailWord_289173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289173).length < 2 ^ (prefixWord ++ tailWord_289173).sum := by decide
  have hdescent : baseEnd_289173 < baseStart_289173 := by decide
  rcases family_descends (prefixWord ++ tailWord_289173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289207 : List Nat := [1, 1, 3, 1, 3, 4, 3, 1, 4]
def baseStart_289207 : Nat := 118140960795 + 289207 * 2 ^ 59
def prefixEnd_289207 : Nat := 4983230072969 + 3 ^ 40 * 289207 * 2
def baseEnd_289207 : Nat := 66000977619980093325541

theorem tailTrace_289207 : CollatzResearch.WordTrace tailWord_289207 prefixEnd_289207 66000977619980093325541 := by
  unfold tailWord_289207
  simp only [CollatzResearch.WordTrace]
  refine ⟨10548245863259906468361875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7032163908839937645574583 10548245863259906468361875)
  ·
    refine ⟨15822368794889859702542813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10548245863259906468361875 15822368794889859702542813)
    ·
      refine ⟨5933388298083697388453555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15822368794889859702542813 5933388298083697388453555)
      ·
        refine ⟨8900082447125546082680333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5933388298083697388453555 8900082447125546082680333)
        ·
          refine ⟨3337530917672079781005125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8900082447125546082680333 3337530917672079781005125)
          ·
            refine ⟨625787047063514958938461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3337530917672079781005125 625787047063514958938461)
            ·
              refine ⟨234670142648818109601923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 625787047063514958938461 234670142648818109601923)
              ·
                refine ⟨352005213973227164402885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 234670142648818109601923 352005213973227164402885)
                ·
                  refine ⟨66000977619980093325541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 352005213973227164402885 66000977619980093325541)
                  ·
                    rfl

theorem cell21_289207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 4].length) (baseStart_289207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_289207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_289207 prefixEnd_289207 := by exact prefixLift 289207
  have htrace : WordTrace (prefixWord ++ tailWord_289207) baseStart_289207 baseEnd_289207 := by
    simpa [prefixWord, tailWord_289207, baseEnd_289207] using wordTrace_append hprefix tailTrace_289207
  have hstable : (prefixWord ++ tailWord_289207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289207).length < 2 ^ (prefixWord ++ tailWord_289207).sum := by decide
  have hdescent : baseEnd_289207 < baseStart_289207 := by decide
  rcases family_descends (prefixWord ++ tailWord_289207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289249 : List Nat := [1, 2, 3, 1, 2, 2, 1, 3, 6]
def baseStart_289249 : Nat := 118140960795 + 289249 * 2 ^ 59
def prefixEnd_289249 : Nat := 4983230072969 + 3 ^ 40 * 289249 * 2
def baseEnd_289249 : Nat := 66010562592197353625455

theorem tailTrace_289249 : CollatzResearch.WordTrace tailWord_289249 prefixEnd_289249 66010562592197353625455 := by
  unfold tailWord_289249
  simp only [CollatzResearch.WordTrace]
  refine ⟨10549777729107747641390801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7033185152738498427593867 10549777729107747641390801)
  ·
    refine ⟨7912333296830810731043101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10549777729107747641390801 7912333296830810731043101)
    ·
      refine ⟨2967124986311554024141163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7912333296830810731043101 2967124986311554024141163)
      ·
        refine ⟨4450687479467331036211745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2967124986311554024141163 4450687479467331036211745)
        ·
          refine ⟨3338015609600498277158809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4450687479467331036211745 3338015609600498277158809)
          ·
            refine ⟨2503511707200373707869107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3338015609600498277158809 2503511707200373707869107)
            ·
              refine ⟨3755267560800560561803661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2503511707200373707869107 3755267560800560561803661)
              ·
                refine ⟨1408225335300210210676373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3755267560800560561803661 1408225335300210210676373)
                ·
                  refine ⟨66010562592197353625455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1408225335300210210676373 66010562592197353625455)
                  ·
                    rfl

theorem cell21_289249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 6].length) (baseStart_289249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_289249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_289249 prefixEnd_289249 := by exact prefixLift 289249
  have htrace : WordTrace (prefixWord ++ tailWord_289249) baseStart_289249 baseEnd_289249 := by
    simpa [prefixWord, tailWord_289249, baseEnd_289249] using wordTrace_append hprefix tailTrace_289249
  have hstable : (prefixWord ++ tailWord_289249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289249).length < 2 ^ (prefixWord ++ tailWord_289249).sum := by decide
  have hdescent : baseEnd_289249 < baseStart_289249 := by decide
  rcases family_descends (prefixWord ++ tailWord_289249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289300 : List Nat := [2, 4, 3, 1, 1, 2, 2, 2, 4]
def baseStart_289300 : Nat := 118140960795 + 289300 * 2 ^ 59
def prefixEnd_289300 : Nat := 4983230072969 + 3 ^ 40 * 289300 * 2
def baseEnd_289300 : Nat := 66022201487032598275351

theorem tailTrace_289300 : CollatzResearch.WordTrace tailWord_289300 prefixEnd_289300 66022201487032598275351 := by
  unfold tailWord_289300
  simp only [CollatzResearch.WordTrace]
  refine ⟨5275818925961491675748677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7034425234615322234331569 5275818925961491675748677)
  ·
    refine ⟨989216048617779689202877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5275818925961491675748677 989216048617779689202877)
    ·
      refine ⟨370956018231667383451079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 989216048617779689202877 370956018231667383451079)
      ·
        refine ⟨556434027347501075176619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 370956018231667383451079 556434027347501075176619)
        ·
          refine ⟨834651041021251612764929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 556434027347501075176619 834651041021251612764929)
          ·
            refine ⟨625988280765938709573697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 834651041021251612764929 625988280765938709573697)
            ·
              refine ⟨469491210574454032180273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 625988280765938709573697 469491210574454032180273)
              ·
                refine ⟨352118407930840524135205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 469491210574454032180273 352118407930840524135205)
                ·
                  refine ⟨66022201487032598275351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 352118407930840524135205 66022201487032598275351)
                  ·
                    rfl

theorem cell21_289300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_289300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_289300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_289300 prefixEnd_289300 := by exact prefixLift 289300
  have htrace : WordTrace (prefixWord ++ tailWord_289300) baseStart_289300 baseEnd_289300 := by
    simpa [prefixWord, tailWord_289300, baseEnd_289300] using wordTrace_append hprefix tailTrace_289300
  have hstable : (prefixWord ++ tailWord_289300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289300).length < 2 ^ (prefixWord ++ tailWord_289300).sum := by decide
  have hdescent : baseEnd_289300 < baseStart_289300 := by decide
  rcases family_descends (prefixWord ++ tailWord_289300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289303 : List Nat := [1, 1, 3, 6, 1, 2, 2, 2, 3]
def baseStart_289303 : Nat := 118140960795 + 289303 * 2 ^ 59
def prefixEnd_289303 : Nat := 4983230072969 + 3 ^ 40 * 289303 * 2
def baseEnd_289303 : Nat := 66022886127905259725345

theorem tailTrace_289303 : CollatzResearch.WordTrace tailWord_289303 prefixEnd_289303 66022886127905259725345 := by
  unfold tailWord_289303
  simp only [CollatzResearch.WordTrace]
  refine ⟨10551747270912114863856563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7034498180608076575904375 10551747270912114863856563)
  ·
    refine ⟨15827620906368172295784845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10551747270912114863856563 15827620906368172295784845)
    ·
      refine ⟨5935357839888064610919317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15827620906368172295784845 5935357839888064610919317)
      ·
        refine ⟨278219898744753028636843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5935357839888064610919317 278219898744753028636843)
        ·
          refine ⟨417329848117129542955265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278219898744753028636843 417329848117129542955265)
          ·
            refine ⟨312997386087847157216449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 417329848117129542955265 312997386087847157216449)
            ·
              refine ⟨234748039565885367912337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 312997386087847157216449 234748039565885367912337)
              ·
                refine ⟨176061029674414025934253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 234748039565885367912337 176061029674414025934253)
                ·
                  refine ⟨66022886127905259725345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 176061029674414025934253 66022886127905259725345)
                  ·
                    rfl

theorem cell21_289303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 2, 3].length) (baseStart_289303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_289303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_289303 prefixEnd_289303 := by exact prefixLift 289303
  have htrace : WordTrace (prefixWord ++ tailWord_289303) baseStart_289303 baseEnd_289303 := by
    simpa [prefixWord, tailWord_289303, baseEnd_289303] using wordTrace_append hprefix tailTrace_289303
  have hstable : (prefixWord ++ tailWord_289303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289303).length < 2 ^ (prefixWord ++ tailWord_289303).sum := by decide
  have hdescent : baseEnd_289303 < baseStart_289303 := by decide
  rcases family_descends (prefixWord ++ tailWord_289303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289345 : List Nat := [1, 2, 5, 1, 1, 3, 2, 3, 3]
def baseStart_289345 : Nat := 118140960795 + 289345 * 2 ^ 59
def prefixEnd_289345 : Nat := 4983230072969 + 3 ^ 40 * 289345 * 2
def baseEnd_289345 : Nat := 66032471100122520025259

theorem tailTrace_289345 : CollatzResearch.WordTrace tailWord_289345 prefixEnd_289345 66032471100122520025259 := by
  unfold tailWord_289345
  simp only [CollatzResearch.WordTrace]
  refine ⟨10553279136759956036885489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7035519424506637357923659 10553279136759956036885489)
  ·
    refine ⟨7914959352569967027664117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10553279136759956036885489 7914959352569967027664117)
    ·
      refine ⟨742027439303434408843511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7914959352569967027664117 742027439303434408843511)
      ·
        refine ⟨1113041158955151613265267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 742027439303434408843511 1113041158955151613265267)
        ·
          refine ⟨1669561738432727419897901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1113041158955151613265267 1669561738432727419897901)
          ·
            refine ⟨626085651912272782461713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1669561738432727419897901 626085651912272782461713)
            ·
              refine ⟨469564238934204586846285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 626085651912272782461713 469564238934204586846285)
              ·
                refine ⟨176086589600326720067357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 469564238934204586846285 176086589600326720067357)
                ·
                  refine ⟨66032471100122520025259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 176086589600326720067357 66032471100122520025259)
                  ·
                    rfl

theorem cell21_289345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 3, 3].length) (baseStart_289345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_289345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_289345 prefixEnd_289345 := by exact prefixLift 289345
  have htrace : WordTrace (prefixWord ++ tailWord_289345) baseStart_289345 baseEnd_289345 := by
    simpa [prefixWord, tailWord_289345, baseEnd_289345] using wordTrace_append hprefix tailTrace_289345
  have hstable : (prefixWord ++ tailWord_289345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289345).length < 2 ^ (prefixWord ++ tailWord_289345).sum := by decide
  have hdescent : baseEnd_289345 < baseStart_289345 := by decide
  rcases family_descends (prefixWord ++ tailWord_289345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289390 : List Nat := [4, 1, 2, 2, 2, 3, 2, 5]
def baseStart_289390 : Nat := 118140960795 + 289390 * 2 ^ 59
def prefixEnd_289390 : Nat := 4983230072969 + 3 ^ 40 * 289390 * 2
def baseEnd_289390 : Nat := 22014246904404147258389

theorem tailTrace_289390 : CollatzResearch.WordTrace tailWord_289390 prefixEnd_289390 22014246904404147258389 := by
  unfold tailWord_289390
  simp only [CollatzResearch.WordTrace]
  refine ⟨1319365052699616090284203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7036613614397952481515749 1319365052699616090284203)
  ·
    refine ⟨1979047579049424135426305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1319365052699616090284203 1979047579049424135426305)
    ·
      refine ⟨1484285684287068101569729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1979047579049424135426305 1484285684287068101569729)
      ·
        refine ⟨1113214263215301076177297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1484285684287068101569729 1113214263215301076177297)
        ·
          refine ⟨834910697411475807132973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1113214263215301076177297 834910697411475807132973)
          ·
            refine ⟨313091511529303427674865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 834910697411475807132973 313091511529303427674865)
            ·
              refine ⟨234818633646977570756149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 313091511529303427674865 234818633646977570756149)
              ·
                refine ⟨22014246904404147258389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 234818633646977570756149 22014246904404147258389)
                ·
                  rfl

theorem cell21_289390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_289390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_289390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_289390 prefixEnd_289390 := by exact prefixLift 289390
  have htrace : WordTrace (prefixWord ++ tailWord_289390) baseStart_289390 baseEnd_289390 := by
    simpa [prefixWord, tailWord_289390, baseEnd_289390] using wordTrace_append hprefix tailTrace_289390
  have hstable : (prefixWord ++ tailWord_289390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289390).length < 2 ^ (prefixWord ++ tailWord_289390).sum := by decide
  have hdescent : baseEnd_289390 < baseStart_289390 := by decide
  rcases family_descends (prefixWord ++ tailWord_289390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289401 : List Nat := [1, 2, 1, 3, 3, 2, 1, 2, 6]
def baseStart_289401 : Nat := 118140960795 + 289401 * 2 ^ 59
def prefixEnd_289401 : Nat := 4983230072969 + 3 ^ 40 * 289401 * 2
def baseEnd_289401 : Nat := 66045251063078867091811

theorem tailTrace_289401 : CollatzResearch.WordTrace tailWord_289401 prefixEnd_289401 66045251063078867091811 := by
  unfold tailWord_289401
  simp only [CollatzResearch.WordTrace]
  refine ⟨10555321624557077600924057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7036881083038051733949371 10555321624557077600924057)
  ·
    refine ⟨7916491218417808200693043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10555321624557077600924057 7916491218417808200693043)
    ·
      refine ⟨11874736827626712301039565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7916491218417808200693043 11874736827626712301039565)
      ·
        refine ⟨4453026310360017112889837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11874736827626712301039565 4453026310360017112889837)
        ·
          refine ⟨1669884866385006417333689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4453026310360017112889837 1669884866385006417333689)
          ·
            refine ⟨1252413649788754813000267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1669884866385006417333689 1252413649788754813000267)
            ·
              refine ⟨1878620474683132219500401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1252413649788754813000267 1878620474683132219500401)
              ·
                refine ⟨1408965356012349164625301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1878620474683132219500401 1408965356012349164625301)
                ·
                  refine ⟨66045251063078867091811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1408965356012349164625301 66045251063078867091811)
                  ·
                    rfl

theorem cell21_289401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 6].length) (baseStart_289401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_289401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_289401 prefixEnd_289401 := by exact prefixLift 289401
  have htrace : WordTrace (prefixWord ++ tailWord_289401) baseStart_289401 baseEnd_289401 := by
    simpa [prefixWord, tailWord_289401, baseEnd_289401] using wordTrace_append hprefix tailTrace_289401
  have hstable : (prefixWord ++ tailWord_289401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289401).length < 2 ^ (prefixWord ++ tailWord_289401).sum := by decide
  have hdescent : baseEnd_289401 < baseStart_289401 := by decide
  rcases family_descends (prefixWord ++ tailWord_289401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289404 : List Nat := [2, 2, 2, 1, 1, 2, 5, 3, 3]
def baseStart_289404 : Nat := 118140960795 + 289404 * 2 ^ 59
def prefixEnd_289404 : Nat := 4983230072969 + 3 ^ 40 * 289404 * 2
def baseEnd_289404 : Nat := 66045935703951528541805

theorem tailTrace_289404 : CollatzResearch.WordTrace tailWord_289404 prefixEnd_289404 66045935703951528541805 := by
  unfold tailWord_289404
  simp only [CollatzResearch.WordTrace]
  refine ⟨5277715521773104556641633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7036954029030806075522177 5277715521773104556641633)
  ·
    refine ⟨3958286641329828417481225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5277715521773104556641633 3958286641329828417481225)
    ·
      refine ⟨2968714980997371313110919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3958286641329828417481225 2968714980997371313110919)
      ·
        refine ⟨4453072471496056969666379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2968714980997371313110919 4453072471496056969666379)
        ·
          refine ⟨6679608707244085454499569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4453072471496056969666379 6679608707244085454499569)
          ·
            refine ⟨5009706530433064090874677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6679608707244085454499569 5009706530433064090874677)
            ·
              refine ⟨469659987228099758519501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5009706530433064090874677 469659987228099758519501)
              ·
                refine ⟨176122495210537409444813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 469659987228099758519501 176122495210537409444813)
                ·
                  refine ⟨66045935703951528541805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 176122495210537409444813 66045935703951528541805)
                  ·
                    rfl

theorem cell21_289404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 3, 3].length) (baseStart_289404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_289404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_289404 prefixEnd_289404 := by exact prefixLift 289404
  have htrace : WordTrace (prefixWord ++ tailWord_289404) baseStart_289404 baseEnd_289404 := by
    simpa [prefixWord, tailWord_289404, baseEnd_289404] using wordTrace_append hprefix tailTrace_289404
  have hstable : (prefixWord ++ tailWord_289404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289404).length < 2 ^ (prefixWord ++ tailWord_289404).sum := by decide
  have hdescent : baseEnd_289404 < baseStart_289404 := by decide
  rcases family_descends (prefixWord ++ tailWord_289404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289432 : List Nat := [2, 1, 2, 4, 1, 1, 4, 6]
def baseStart_289432 : Nat := 118140960795 + 289432 * 2 ^ 59
def prefixEnd_289432 : Nat := 4983230072969 + 3 ^ 40 * 289432 * 2
def baseEnd_289432 : Nat := 22017441895143234025027

theorem tailTrace_289432 : CollatzResearch.WordTrace tailWord_289432 prefixEnd_289432 22017441895143234025027 := by
  unfold tailWord_289432
  simp only [CollatzResearch.WordTrace]
  refine ⟨5278226143722384947651275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7037634858296513263535033 5278226143722384947651275)
  ·
    refine ⟨7917339215583577421476913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5278226143722384947651275 7917339215583577421476913)
    ·
      refine ⟨5938004411687683066107685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7917339215583577421476913 5938004411687683066107685)
      ·
        refine ⟨1113375827191440574895191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5938004411687683066107685 1113375827191440574895191)
        ·
          refine ⟨1670063740787160862342787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1113375827191440574895191 1670063740787160862342787)
          ·
            refine ⟨2505095611180741293514181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1670063740787160862342787 2505095611180741293514181)
            ·
              refine ⟨469705427096388992533909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2505095611180741293514181 469705427096388992533909)
              ·
                refine ⟨22017441895143234025027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 469705427096388992533909 22017441895143234025027)
                ·
                  rfl

theorem cell21_289432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 6].length) (baseStart_289432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_289432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_289432 prefixEnd_289432 := by exact prefixLift 289432
  have htrace : WordTrace (prefixWord ++ tailWord_289432) baseStart_289432 baseEnd_289432 := by
    simpa [prefixWord, tailWord_289432, baseEnd_289432] using wordTrace_append hprefix tailTrace_289432
  have hstable : (prefixWord ++ tailWord_289432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289432).length < 2 ^ (prefixWord ++ tailWord_289432).sum := by decide
  have hdescent : baseEnd_289432 < baseStart_289432 := by decide
  rcases family_descends (prefixWord ++ tailWord_289432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289480 : List Nat := [2, 1, 3, 1, 2, 4, 1, 4, 3]
def baseStart_289480 : Nat := 118140960795 + 289480 * 2 ^ 59
def prefixEnd_289480 : Nat := 4983230072969 + 3 ^ 40 * 289480 * 2
def baseEnd_289480 : Nat := 66063279939392285274983

theorem tailTrace_289480 : CollatzResearch.WordTrace tailWord_289480 prefixEnd_289480 66063279939392285274983 := by
  unfold tailWord_289480
  simp only [CollatzResearch.WordTrace]
  refine ⟨5279101495635437046524947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7038801994180582728699929 5279101495635437046524947)
  ·
    refine ⟨7918652243453155569787421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5279101495635437046524947 7918652243453155569787421)
    ·
      refine ⟨2969494591294933338670283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7918652243453155569787421 2969494591294933338670283)
      ·
        refine ⟨4454241886942400008005425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2969494591294933338670283 4454241886942400008005425)
        ·
          refine ⟨3340681415206800006004069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4454241886942400008005425 3340681415206800006004069)
          ·
            refine ⟨626377765351275001125763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3340681415206800006004069 626377765351275001125763)
            ·
              refine ⟨939566648026912501688645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 626377765351275001125763 939566648026912501688645)
              ·
                refine ⟨176168746505046094066621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 939566648026912501688645 176168746505046094066621)
                ·
                  refine ⟨66063279939392285274983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 176168746505046094066621 66063279939392285274983)
                  ·
                    rfl

theorem cell21_289480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 4, 3].length) (baseStart_289480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_289480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_289480 prefixEnd_289480 := by exact prefixLift 289480
  have htrace : WordTrace (prefixWord ++ tailWord_289480) baseStart_289480 baseEnd_289480 := by
    simpa [prefixWord, tailWord_289480, baseEnd_289480] using wordTrace_append hprefix tailTrace_289480
  have hstable : (prefixWord ++ tailWord_289480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289480).length < 2 ^ (prefixWord ++ tailWord_289480).sum := by decide
  have hdescent : baseEnd_289480 < baseStart_289480 := by decide
  rcases family_descends (prefixWord ++ tailWord_289480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289553 : List Nat := [1, 2, 2, 1, 1, 3, 2, 5, 4]
def baseStart_289553 : Nat := 118140960795 + 289553 * 2 ^ 59
def prefixEnd_289553 : Nat := 4983230072969 + 3 ^ 40 * 289553 * 2
def baseEnd_289553 : Nat := 66079939533960380558167

theorem tailTrace_289553 : CollatzResearch.WordTrace tailWord_289553 prefixEnd_289553 66079939533960380558167 := by
  unfold tailWord_289553
  simp only [CollatzResearch.WordTrace]
  refine ⟨10560865520006407560457313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7040577013337605040304875 10560865520006407560457313)
  ·
    refine ⟨7920649140004805670342985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10560865520006407560457313 7920649140004805670342985)
    ·
      refine ⟨5940486855003604252757239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7920649140004805670342985 5940486855003604252757239)
      ·
        refine ⟨8910730282505406379135859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5940486855003604252757239 8910730282505406379135859)
        ·
          refine ⟨13366095423758109568703789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8910730282505406379135859 13366095423758109568703789)
          ·
            refine ⟨5012285783909291088263921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13366095423758109568703789 5012285783909291088263921)
            ·
              refine ⟨3759214337931968316197941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5012285783909291088263921 3759214337931968316197941)
              ·
                refine ⟨352426344181122029643557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3759214337931968316197941 352426344181122029643557)
                ·
                  refine ⟨66079939533960380558167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 352426344181122029643557 66079939533960380558167)
                  ·
                    rfl

theorem cell21_289553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 4].length) (baseStart_289553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_289553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_289553 prefixEnd_289553 := by exact prefixLift 289553
  have htrace : WordTrace (prefixWord ++ tailWord_289553) baseStart_289553 baseEnd_289553 := by
    simpa [prefixWord, tailWord_289553, baseEnd_289553] using wordTrace_append hprefix tailTrace_289553
  have hstable : (prefixWord ++ tailWord_289553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289553).length < 2 ^ (prefixWord ++ tailWord_289553).sum := by decide
  have hdescent : baseEnd_289553 < baseStart_289553 := by decide
  rcases family_descends (prefixWord ++ tailWord_289553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289590 : List Nat := [5, 1, 2, 2, 3, 1, 1, 1, 5]
def baseStart_289590 : Nat := 118140960795 + 289590 * 2 ^ 59
def prefixEnd_289590 : Nat := 4983230072969 + 3 ^ 40 * 289590 * 2
def baseEnd_289590 : Nat := 66088383438056538441425

theorem tailTrace_289590 : CollatzResearch.WordTrace tailWord_289590 prefixEnd_289590 66088383438056538441425 := by
  unfold tailWord_289590
  simp only [CollatzResearch.WordTrace]
  refine ⟨660138438804522679972139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7041476680581575253036149 660138438804522679972139)
  ·
    refine ⟨990207658206784019958209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 660138438804522679972139 990207658206784019958209)
    ·
      refine ⟨742655743655088014968657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 990207658206784019958209 742655743655088014968657)
      ·
        refine ⟨556991807741316011226493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 742655743655088014968657 556991807741316011226493)
        ·
          refine ⟨208871927902993504209935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 556991807741316011226493 208871927902993504209935)
          ·
            refine ⟨313307891854490256314903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208871927902993504209935 313307891854490256314903)
            ·
              refine ⟨469961837781735384472355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 313307891854490256314903 469961837781735384472355)
              ·
                refine ⟨704942756672603076708533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 469961837781735384472355 704942756672603076708533)
                ·
                  refine ⟨66088383438056538441425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 704942756672603076708533 66088383438056538441425)
                  ·
                    rfl

theorem cell21_289590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_289590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_289590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_289590 prefixEnd_289590 := by exact prefixLift 289590
  have htrace : WordTrace (prefixWord ++ tailWord_289590) baseStart_289590 baseEnd_289590 := by
    simpa [prefixWord, tailWord_289590, baseEnd_289590] using wordTrace_append hprefix tailTrace_289590
  have hstable : (prefixWord ++ tailWord_289590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289590).length < 2 ^ (prefixWord ++ tailWord_289590).sum := by decide
  have hdescent : baseEnd_289590 < baseStart_289590 := by decide
  rcases family_descends (prefixWord ++ tailWord_289590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289604 : List Nat := [2, 3, 4, 2, 1, 1, 1, 3, 4]
def baseStart_289604 : Nat := 118140960795 + 289604 * 2 ^ 59
def prefixEnd_289604 : Nat := 4983230072969 + 3 ^ 40 * 289604 * 2
def baseEnd_289604 : Nat := 66091578428795625208063

theorem tailTrace_289604 : CollatzResearch.WordTrace tailWord_289604 prefixEnd_289604 66091578428795625208063 := by
  unfold tailWord_289604
  simp only [CollatzResearch.WordTrace]
  refine ⟨5281362821410821635281933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7041817095214428847042577 5281362821410821635281933)
  ·
    refine ⟨1980511058029058113230725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5281362821410821635281933 1980511058029058113230725)
    ·
      refine ⟨371345823380448396230761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1980511058029058113230725 371345823380448396230761)
      ·
        refine ⟨278509367535336297173071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 371345823380448396230761 278509367535336297173071)
        ·
          refine ⟨417764051303004445759607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278509367535336297173071 417764051303004445759607)
          ·
            refine ⟨626646076954506668639411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 417764051303004445759607 626646076954506668639411)
            ·
              refine ⟨939969115431760002959117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 626646076954506668639411 939969115431760002959117)
              ·
                refine ⟨352488418286910001109669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 939969115431760002959117 352488418286910001109669)
                ·
                  refine ⟨66091578428795625208063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 352488418286910001109669 66091578428795625208063)
                  ·
                    rfl

theorem cell21_289604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_289604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_289604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_289604 prefixEnd_289604 := by exact prefixLift 289604
  have htrace : WordTrace (prefixWord ++ tailWord_289604) baseStart_289604 baseEnd_289604 := by
    simpa [prefixWord, tailWord_289604, baseEnd_289604] using wordTrace_append hprefix tailTrace_289604
  have hstable : (prefixWord ++ tailWord_289604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289604).length < 2 ^ (prefixWord ++ tailWord_289604).sum := by decide
  have hdescent : baseEnd_289604 < baseStart_289604 := by decide
  rcases family_descends (prefixWord ++ tailWord_289604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289649 : List Nat := [1, 2, 2, 2, 1, 6, 2, 2, 3]
def baseStart_289649 : Nat := 118140960795 + 289649 * 2 ^ 59
def prefixEnd_289649 : Nat := 4983230072969 + 3 ^ 40 * 289649 * 2
def baseEnd_289649 : Nat := 66101848041885546957971

theorem tailTrace_289649 : CollatzResearch.WordTrace tailWord_289649 prefixEnd_289649 66101848041885546957971 := by
  unfold tailWord_289649
  simp only [CollatzResearch.WordTrace]
  refine ⟨10564366927658615955952001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7042911285105743970634667 10564366927658615955952001)
  ·
    refine ⟨7923275195743961966964001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10564366927658615955952001 7923275195743961966964001)
    ·
      refine ⟨5942456396807971475223001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7923275195743961966964001 5942456396807971475223001)
      ·
        refine ⟨4456842297605978606417251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5942456396807971475223001 4456842297605978606417251)
        ·
          refine ⟨6685263446408967909625877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4456842297605978606417251 6685263446408967909625877)
          ·
            refine ⟨313371724050420370763713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6685263446408967909625877 313371724050420370763713)
            ·
              refine ⟨235028793037815278072785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 313371724050420370763713 235028793037815278072785)
              ·
                refine ⟨176271594778361458554589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 235028793037815278072785 176271594778361458554589)
                ·
                  refine ⟨66101848041885546957971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 176271594778361458554589 66101848041885546957971)
                  ·
                    rfl

theorem cell21_289649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 2, 3].length) (baseStart_289649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_289649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_289649 prefixEnd_289649 := by exact prefixLift 289649
  have htrace : WordTrace (prefixWord ++ tailWord_289649) baseStart_289649 baseEnd_289649 := by
    simpa [prefixWord, tailWord_289649, baseEnd_289649] using wordTrace_append hprefix tailTrace_289649
  have hstable : (prefixWord ++ tailWord_289649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289649).length < 2 ^ (prefixWord ++ tailWord_289649).sum := by decide
  have hdescent : baseEnd_289649 < baseStart_289649 := by decide
  rcases family_descends (prefixWord ++ tailWord_289649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289722 : List Nat := [3, 1, 1, 1, 2, 1, 7, 1, 4]
def baseStart_289722 : Nat := 118140960795 + 289722 * 2 ^ 59
def prefixEnd_289722 : Nat := 4983230072969 + 3 ^ 40 * 289722 * 2
def baseEnd_289722 : Nat := 66118507636453642241155

theorem tailTrace_289722 : CollatzResearch.WordTrace tailWord_289722 prefixEnd_289722 66118507636453642241155 := by
  unfold tailWord_289722
  simp only [CollatzResearch.WordTrace]
  refine ⟨2641757364098537355839855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7044686304262766282239613 2641757364098537355839855)
  ·
    refine ⟨3962636046147806033759783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2641757364098537355839855 3962636046147806033759783)
    ·
      refine ⟨5943954069221709050639675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3962636046147806033759783 5943954069221709050639675)
      ·
        refine ⟨8915931103832563575959513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5943954069221709050639675 8915931103832563575959513)
        ·
          refine ⟨6686948327874422681969635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8915931103832563575959513 6686948327874422681969635)
          ·
            refine ⟨10030422491811634022954453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6686948327874422681969635 10030422491811634022954453)
            ·
              refine ⟨235088027151835172412995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 10030422491811634022954453 235088027151835172412995)
              ·
                refine ⟨352632040727752758619493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 235088027151835172412995 352632040727752758619493)
                ·
                  refine ⟨66118507636453642241155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 352632040727752758619493 66118507636453642241155)
                  ·
                    rfl

theorem cell21_289722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 4].length) (baseStart_289722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_289722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_289722 prefixEnd_289722 := by exact prefixLift 289722
  have htrace : WordTrace (prefixWord ++ tailWord_289722) baseStart_289722 baseEnd_289722 := by
    simpa [prefixWord, tailWord_289722, baseEnd_289722] using wordTrace_append hprefix tailTrace_289722
  have hstable : (prefixWord ++ tailWord_289722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289722).length < 2 ^ (prefixWord ++ tailWord_289722).sum := by decide
  have hdescent : baseEnd_289722 < baseStart_289722 := by decide
  rcases family_descends (prefixWord ++ tailWord_289722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289736 : List Nat := [2, 1, 3, 1, 5, 1, 1, 7]
def baseStart_289736 : Nat := 118140960795 + 289736 * 2 ^ 59
def prefixEnd_289736 : Nat := 4983230072969 + 3 ^ 40 * 289736 * 2
def baseEnd_289736 : Nat := 22040567542397576335931

theorem tailTrace_289736 : CollatzResearch.WordTrace tailWord_289736 prefixEnd_289736 22040567542397576335931 := by
  unfold tailWord_289736
  simp only [CollatzResearch.WordTrace]
  refine ⟨5283770039171714907184531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7045026718895619876246041 5283770039171714907184531)
  ·
    refine ⟨7925655058757572360776797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5283770039171714907184531 7925655058757572360776797)
    ·
      refine ⟨2972120647034089635291299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7925655058757572360776797 2972120647034089635291299)
      ·
        refine ⟨4458180970551134452936949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2972120647034089635291299 4458180970551134452936949)
        ·
          refine ⟨417954465989168854962839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4458180970551134452936949 417954465989168854962839)
          ·
            refine ⟨626931698983753282444259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 417954465989168854962839 626931698983753282444259)
            ·
              refine ⟨940397548475629923666389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 626931698983753282444259 940397548475629923666389)
              ·
                refine ⟨22040567542397576335931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 940397548475629923666389 22040567542397576335931)
                ·
                  rfl

theorem cell21_289736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 7].length) (baseStart_289736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_289736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_289736 prefixEnd_289736 := by exact prefixLift 289736
  have htrace : WordTrace (prefixWord ++ tailWord_289736) baseStart_289736 baseEnd_289736 := by
    simpa [prefixWord, tailWord_289736, baseEnd_289736] using wordTrace_append hprefix tailTrace_289736
  have hstable : (prefixWord ++ tailWord_289736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289736).length < 2 ^ (prefixWord ++ tailWord_289736).sum := by decide
  have hdescent : baseEnd_289736 < baseStart_289736 := by decide
  rcases family_descends (prefixWord ++ tailWord_289736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289767 : List Nat := [1, 1, 5, 2, 2, 1, 3, 1, 5]
def baseStart_289767 : Nat := 118140960795 + 289767 * 2 ^ 59
def prefixEnd_289767 : Nat := 4983230072969 + 3 ^ 40 * 289767 * 2
def baseEnd_289767 : Nat := 66128777249543563991063

theorem tailTrace_289767 : CollatzResearch.WordTrace tailWord_289767 prefixEnd_289767 66128777249543563991063 := by
  unfold tailWord_289767
  simp only [CollatzResearch.WordTrace]
  refine ⟨10568670741231122108747555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7045780494154081405831703 10568670741231122108747555)
  ·
    refine ⟨15853006111846683163121333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10568670741231122108747555 15853006111846683163121333)
    ·
      refine ⟨1486219322985626546542625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15853006111846683163121333 1486219322985626546542625)
      ·
        refine ⟨1114664492239219909906969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1486219322985626546542625 1114664492239219909906969)
        ·
          refine ⟨835998369179414932430227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1114664492239219909906969 835998369179414932430227)
          ·
            refine ⟨1253997553769122398645341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 835998369179414932430227 1253997553769122398645341)
            ·
              refine ⟨470249082663420899492003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1253997553769122398645341 470249082663420899492003)
              ·
                refine ⟨705373623995131349238005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 470249082663420899492003 705373623995131349238005)
                ·
                  refine ⟨66128777249543563991063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 705373623995131349238005 66128777249543563991063)
                  ·
                    rfl

theorem cell21_289767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 5].length) (baseStart_289767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_289767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_289767 prefixEnd_289767 := by exact prefixLift 289767
  have htrace : WordTrace (prefixWord ++ tailWord_289767) baseStart_289767 baseEnd_289767 := by
    simpa [prefixWord, tailWord_289767, baseEnd_289767] using wordTrace_append hprefix tailTrace_289767
  have hstable : (prefixWord ++ tailWord_289767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289767).length < 2 ^ (prefixWord ++ tailWord_289767).sum := by decide
  have hdescent : baseEnd_289767 < baseStart_289767 := by decide
  rcases family_descends (prefixWord ++ tailWord_289767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289874 : List Nat := [3, 2, 2, 1, 3, 1, 3, 2, 4]
def baseStart_289874 : Nat := 118140960795 + 289874 * 2 ^ 59
def prefixEnd_289874 : Nat := 4983230072969 + 3 ^ 40 * 289874 * 2
def baseEnd_289874 : Nat := 66153196107335155707511

theorem tailTrace_289874 : CollatzResearch.WordTrace tailWord_289874 prefixEnd_289874 66153196107335155707511 := by
  unfold tailWord_289874
  simp only [CollatzResearch.WordTrace]
  refine ⟨2643143337960869845723169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7048382234562319588595117 2643143337960869845723169)
  ·
    refine ⟨1982357503470652384292377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2643143337960869845723169 1982357503470652384292377)
    ·
      refine ⟨1486768127602989288219283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1982357503470652384292377 1486768127602989288219283)
      ·
        refine ⟨2230152191404483932328925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1486768127602989288219283 2230152191404483932328925)
        ·
          refine ⟨836307071776681474623347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2230152191404483932328925 836307071776681474623347)
          ·
            refine ⟨1254460607665022211935021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 836307071776681474623347 1254460607665022211935021)
            ·
              refine ⟨470422727874383329475633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1254460607665022211935021 470422727874383329475633)
              ·
                refine ⟨352817045905787497106725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 470422727874383329475633 352817045905787497106725)
                ·
                  refine ⟨66153196107335155707511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 352817045905787497106725 66153196107335155707511)
                  ·
                    rfl

theorem cell21_289874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_289874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_289874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_289874 prefixEnd_289874 := by exact prefixLift 289874
  have htrace : WordTrace (prefixWord ++ tailWord_289874) baseStart_289874 baseEnd_289874 := by
    simpa [prefixWord, tailWord_289874, baseEnd_289874] using wordTrace_append hprefix tailTrace_289874
  have hstable : (prefixWord ++ tailWord_289874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289874).length < 2 ^ (prefixWord ++ tailWord_289874).sum := by decide
  have hdescent : baseEnd_289874 < baseStart_289874 := by decide
  rcases family_descends (prefixWord ++ tailWord_289874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289916 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 8]
def baseStart_289916 : Nat := 118140960795 + 289916 * 2 ^ 59
def prefixEnd_289916 : Nat := 4983230072969 + 3 ^ 40 * 289916 * 2
def baseEnd_289916 : Nat := 66162781079552416007425

theorem tailTrace_289916 : CollatzResearch.WordTrace tailWord_289916 prefixEnd_289916 66162781079552416007425 := by
  unfold tailWord_289916
  simp only [CollatzResearch.WordTrace]
  refine ⟨5287052608845660277960801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7049403478460880370614401 5287052608845660277960801)
  ·
    refine ⟨3965289456634245208470601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5287052608845660277960801 3965289456634245208470601)
    ·
      refine ⟨2973967092475683906352951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3965289456634245208470601 2973967092475683906352951)
      ·
        refine ⟨4460950638713525859529427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2973967092475683906352951 4460950638713525859529427)
        ·
          refine ⟨6691425958070288789294141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4460950638713525859529427 6691425958070288789294141)
          ·
            refine ⟨2509284734276358295985303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6691425958070288789294141 2509284734276358295985303)
            ·
              refine ⟨3763927101414537443977955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2509284734276358295985303 3763927101414537443977955)
              ·
                refine ⟨5645890652121806165966933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3763927101414537443977955 5645890652121806165966933)
                ·
                  refine ⟨66162781079552416007425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5645890652121806165966933 66162781079552416007425)
                  ·
                    rfl

theorem cell21_289916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_289916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_289916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_289916 prefixEnd_289916 := by exact prefixLift 289916
  have htrace : WordTrace (prefixWord ++ tailWord_289916) baseStart_289916 baseEnd_289916 := by
    simpa [prefixWord, tailWord_289916, baseEnd_289916] using wordTrace_append hprefix tailTrace_289916
  have hstable : (prefixWord ++ tailWord_289916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289916).length < 2 ^ (prefixWord ++ tailWord_289916).sum := by decide
  have hdescent : baseEnd_289916 < baseStart_289916 := by decide
  rcases family_descends (prefixWord ++ tailWord_289916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289992 : List Nat := [2, 1, 3, 1, 2, 1, 2, 3, 6]
def baseStart_289992 : Nat := 118140960795 + 289992 * 2 ^ 59
def prefixEnd_289992 : Nat := 4983230072969 + 3 ^ 40 * 289992 * 2
def baseEnd_289992 : Nat := 66180125314993172740603

theorem tailTrace_289992 : CollatzResearch.WordTrace tailWord_289992 prefixEnd_289992 66180125314993172740603 := by
  unfold tailWord_289992
  simp only [CollatzResearch.WordTrace]
  refine ⟨5288438582707992767844115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7051251443610657023792153 5288438582707992767844115)
  ·
    refine ⟨7932657874061989151766173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5288438582707992767844115 7932657874061989151766173)
    ·
      refine ⟨2974746702773245931912315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7932657874061989151766173 2974746702773245931912315)
      ·
        refine ⟨4462120054159868897868473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2974746702773245931912315 4462120054159868897868473)
        ·
          refine ⟨3346590040619901673401355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4462120054159868897868473 3346590040619901673401355)
          ·
            refine ⟨5019885060929852510102033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3346590040619901673401355 5019885060929852510102033)
            ·
              refine ⟨3764913795697389382576525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5019885060929852510102033 3764913795697389382576525)
              ·
                refine ⟨1411842673386521018466197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3764913795697389382576525 1411842673386521018466197)
                ·
                  refine ⟨66180125314993172740603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1411842673386521018466197 66180125314993172740603)
                  ·
                    rfl

theorem cell21_289992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 6].length) (baseStart_289992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_289992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_289992 prefixEnd_289992 := by exact prefixLift 289992
  have htrace : WordTrace (prefixWord ++ tailWord_289992) baseStart_289992 baseEnd_289992 := by
    simpa [prefixWord, tailWord_289992, baseEnd_289992] using wordTrace_append hprefix tailTrace_289992
  have hstable : (prefixWord ++ tailWord_289992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289992).length < 2 ^ (prefixWord ++ tailWord_289992).sum := by decide
  have hdescent : baseEnd_289992 < baseStart_289992 := by decide
  rcases family_descends (prefixWord ++ tailWord_289992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290088 : List Nat := [2, 1, 5, 1, 2, 1, 3, 3, 3]
def baseStart_290088 : Nat := 118140960795 + 290088 * 2 ^ 59
def prefixEnd_290088 : Nat := 4983230072969 + 3 ^ 40 * 290088 * 2
def baseEnd_290088 : Nat := 66202033822918339140407

theorem tailTrace_290088 : CollatzResearch.WordTrace tailWord_290088 prefixEnd_290088 66202033822918339140407 := by
  unfold tailWord_290088
  simp only [CollatzResearch.WordTrace]
  refine ⟨5290189286534096965591459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7053585715378795954121945 5290189286534096965591459)
  ·
    refine ⟨7935283929801145448387189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5290189286534096965591459 7935283929801145448387189)
    ·
      refine ⟨743932868418857385786299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7935283929801145448387189 743932868418857385786299)
      ·
        refine ⟨1115899302628286078679449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 743932868418857385786299 1115899302628286078679449)
        ·
          refine ⟨836924476971214559009587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1115899302628286078679449 836924476971214559009587)
          ·
            refine ⟨1255386715456821838514381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 836924476971214559009587 1255386715456821838514381)
            ·
              refine ⟨470770018296308189442893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1255386715456821838514381 470770018296308189442893)
              ·
                refine ⟨176538756861115571041085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 470770018296308189442893 176538756861115571041085)
                ·
                  refine ⟨66202033822918339140407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 176538756861115571041085 66202033822918339140407)
                  ·
                    rfl

theorem cell21_290088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 3, 3].length) (baseStart_290088 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_290088 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_290088 prefixEnd_290088 := by exact prefixLift 290088
  have htrace : WordTrace (prefixWord ++ tailWord_290088) baseStart_290088 baseEnd_290088 := by
    simpa [prefixWord, tailWord_290088, baseEnd_290088] using wordTrace_append hprefix tailTrace_290088
  have hstable : (prefixWord ++ tailWord_290088).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290088).length < 2 ^ (prefixWord ++ tailWord_290088).sum := by decide
  have hdescent : baseEnd_290088 < baseStart_290088 := by decide
  rcases family_descends (prefixWord ++ tailWord_290088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290099 : List Nat := [1, 1, 1, 2, 5, 4, 7]
def baseStart_290099 : Nat := 118140960795 + 290099 * 2 ^ 59
def prefixEnd_290099 : Nat := 4983230072969 + 3 ^ 40 * 290099 * 2
def baseEnd_290099 : Nat := 7356060463642751606339

theorem tailTrace_290099 : CollatzResearch.WordTrace tailWord_290099 prefixEnd_290099 7356060463642751606339 := by
  unfold tailWord_290099
  simp only [CollatzResearch.WordTrace]
  refine ⟨10580779776028342809833351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7053853184018895206555567 10580779776028342809833351)
  ·
    refine ⟨15871169664042514214750027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10580779776028342809833351 15871169664042514214750027)
    ·
      refine ⟨23806754496063771322125041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15871169664042514214750027 23806754496063771322125041)
      ·
        refine ⟨17855065872047828491593781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23806754496063771322125041 17855065872047828491593781)
        ·
          refine ⟨1673912425504483921086917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17855065872047828491593781 1673912425504483921086917)
          ·
            refine ⟨313858579782090735203797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1673912425504483921086917 313858579782090735203797)
            ·
              refine ⟨7356060463642751606339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 313858579782090735203797 7356060463642751606339)
              ·
                rfl

theorem cell21_290099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 7].length) (baseStart_290099 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_290099 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_290099 prefixEnd_290099 := by exact prefixLift 290099
  have htrace : WordTrace (prefixWord ++ tailWord_290099) baseStart_290099 baseEnd_290099 := by
    simpa [prefixWord, tailWord_290099, baseEnd_290099] using wordTrace_append hprefix tailTrace_290099
  have hstable : (prefixWord ++ tailWord_290099).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290099).length < 2 ^ (prefixWord ++ tailWord_290099).sum := by decide
  have hdescent : baseEnd_290099 < baseStart_290099 := by decide
  rcases family_descends (prefixWord ++ tailWord_290099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290105 : List Nat := [1, 2, 1, 6, 2, 1, 3, 2, 3]
def baseStart_290105 : Nat := 118140960795 + 290105 * 2 ^ 59
def prefixEnd_290105 : Nat := 4983230072969 + 3 ^ 40 * 290105 * 2
def baseEnd_290105 : Nat := 66205913454530087357039

theorem tailTrace_290105 : CollatzResearch.WordTrace tailWord_290105 prefixEnd_290105 66205913454530087357039 := by
  unfold tailWord_290105
  simp only [CollatzResearch.WordTrace]
  refine ⟨10580998614006605834551769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7053999076004403889701179 10580998614006605834551769)
  ·
    refine ⟨7935748960504954375913827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10580998614006605834551769 7935748960504954375913827)
    ·
      refine ⟨11903623440757431563870741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7935748960504954375913827 11903623440757431563870741)
      ·
        refine ⟨557982348785504604556441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11903623440757431563870741 557982348785504604556441)
        ·
          refine ⟨418486761589128453417331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 557982348785504604556441 418486761589128453417331)
          ·
            refine ⟨627730142383692680125997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 418486761589128453417331 627730142383692680125997)
            ·
              refine ⟨235398803393884755047249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 627730142383692680125997 235398803393884755047249)
              ·
                refine ⟨176549102545413566285437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 235398803393884755047249 176549102545413566285437)
                ·
                  refine ⟨66205913454530087357039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 176549102545413566285437 66205913454530087357039)
                  ·
                    rfl

theorem cell21_290105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 2, 3].length) (baseStart_290105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_290105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_290105 prefixEnd_290105 := by exact prefixLift 290105
  have htrace : WordTrace (prefixWord ++ tailWord_290105) baseStart_290105 baseEnd_290105 := by
    simpa [prefixWord, tailWord_290105, baseEnd_290105] using wordTrace_append hprefix tailTrace_290105
  have hstable : (prefixWord ++ tailWord_290105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290105).length < 2 ^ (prefixWord ++ tailWord_290105).sum := by decide
  have hdescent : baseEnd_290105 < baseStart_290105 := by decide
  rcases family_descends (prefixWord ++ tailWord_290105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290116 : List Nat := [2, 3, 4, 1, 1, 1, 1, 8]
def baseStart_290116 : Nat := 118140960795 + 290116 * 2 ^ 59
def prefixEnd_290116 : Nat := 4983230072969 + 3 ^ 40 * 290116 * 2
def baseEnd_290116 : Nat := 22069474601465504224561

theorem tailTrace_290116 : CollatzResearch.WordTrace tailWord_290116 prefixEnd_290116 22069474601465504224561 := by
  unfold tailWord_290116
  simp only [CollatzResearch.WordTrace]
  refine ⟨5290699908483377356601101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7054266544644503142134801 5290699908483377356601101)
  ·
    refine ⟨1984012465681266508725413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5290699908483377356601101 1984012465681266508725413)
    ·
      refine ⟨372002337315237470386015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1984012465681266508725413 372002337315237470386015)
      ·
        refine ⟨558003505972856205579023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372002337315237470386015 558003505972856205579023)
        ·
          refine ⟨837005258959284308368535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 558003505972856205579023 837005258959284308368535)
          ·
            refine ⟨1255507888438926462552803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 837005258959284308368535 1255507888438926462552803)
            ·
              refine ⟨1883261832658389693829205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1255507888438926462552803 1883261832658389693829205)
              ·
                refine ⟨22069474601465504224561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1883261832658389693829205 22069474601465504224561)
                ·
                  rfl

theorem cell21_290116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 8].length) (baseStart_290116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_290116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_290116 prefixEnd_290116 := by exact prefixLift 290116
  have htrace : WordTrace (prefixWord ++ tailWord_290116) baseStart_290116 baseEnd_290116 := by
    simpa [prefixWord, tailWord_290116, baseEnd_290116] using wordTrace_append hprefix tailTrace_290116
  have hstable : (prefixWord ++ tailWord_290116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290116).length < 2 ^ (prefixWord ++ tailWord_290116).sum := by decide
  have hdescent : baseEnd_290116 < baseStart_290116 := by decide
  rcases family_descends (prefixWord ++ tailWord_290116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290251 : List Nat := [1, 1, 1, 1, 3, 3, 6, 5]
def baseStart_290251 : Nat := 118140960795 + 290251 * 2 ^ 59
def prefixEnd_290251 : Nat := 4983230072969 + 3 ^ 40 * 290251 * 2
def baseEnd_290251 : Nat := 22079744214555425974469

theorem tailTrace_290251 : CollatzResearch.WordTrace tailWord_290251 prefixEnd_290251 22079744214555425974469 := by
  unfold tailWord_290251
  simp only [CollatzResearch.WordTrace]
  refine ⟨10586323671477672769366607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7057549114318448512911071 10586323671477672769366607)
  ·
    refine ⟨15879485507216509154049911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10586323671477672769366607 15879485507216509154049911)
    ·
      refine ⟨23819228260824763731074867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15879485507216509154049911 23819228260824763731074867)
      ·
        refine ⟨35728842391237145596612301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23819228260824763731074867 35728842391237145596612301)
        ·
          refine ⟨13398315896713929598729613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35728842391237145596612301 13398315896713929598729613)
          ·
            refine ⟨5024368461267723599523605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13398315896713929598729613 5024368461267723599523605)
            ·
              refine ⟨235517271621924543727669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5024368461267723599523605 235517271621924543727669)
              ·
                refine ⟨22079744214555425974469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 235517271621924543727669 22079744214555425974469)
                ·
                  rfl

theorem cell21_290251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 5].length) (baseStart_290251 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_290251 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_290251 prefixEnd_290251 := by exact prefixLift 290251
  have htrace : WordTrace (prefixWord ++ tailWord_290251) baseStart_290251 baseEnd_290251 := by
    simpa [prefixWord, tailWord_290251, baseEnd_290251] using wordTrace_append hprefix tailTrace_290251
  have hstable : (prefixWord ++ tailWord_290251).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290251).length < 2 ^ (prefixWord ++ tailWord_290251).sum := by decide
  have hdescent : baseEnd_290251 < baseStart_290251 := by decide
  rcases family_descends (prefixWord ++ tailWord_290251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290341 : List Nat := [1, 3, 1, 2, 2, 1, 1, 5, 5]
def baseStart_290341 : Nat := 118140960795 + 290341 * 2 ^ 59
def prefixEnd_290341 : Nat := 4983230072969 + 3 ^ 40 * 290341 * 2
def baseEnd_290341 : Nat := 66259771869846121423223

theorem tailTrace_290341 : CollatzResearch.WordTrace tailWord_290341 prefixEnd_290341 66259771869846121423223 := by
  unfold tailWord_290341
  simp only [CollatzResearch.WordTrace]
  refine ⟨10589606241151618140142877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7059737494101078760095251 10589606241151618140142877)
  ·
    refine ⟨3971102340431856802553579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10589606241151618140142877 3971102340431856802553579)
    ·
      refine ⟨5956653510647785203830369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3971102340431856802553579 5956653510647785203830369)
      ·
        refine ⟨4467490132985838902872777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5956653510647785203830369 4467490132985838902872777)
        ·
          refine ⟨3350617599739379177154583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4467490132985838902872777 3350617599739379177154583)
          ·
            refine ⟨5025926399609068765731875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3350617599739379177154583 5025926399609068765731875)
            ·
              refine ⟨7538889599413603148597813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5025926399609068765731875 7538889599413603148597813)
              ·
                refine ⟨706770899945025295181045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7538889599413603148597813 706770899945025295181045)
                ·
                  refine ⟨66259771869846121423223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 706770899945025295181045 66259771869846121423223)
                  ·
                    rfl

theorem cell21_290341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_290341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_290341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_290341 prefixEnd_290341 := by exact prefixLift 290341
  have htrace : WordTrace (prefixWord ++ tailWord_290341) baseStart_290341 baseEnd_290341 := by
    simpa [prefixWord, tailWord_290341, baseEnd_290341] using wordTrace_append hprefix tailTrace_290341
  have hstable : (prefixWord ++ tailWord_290341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290341).length < 2 ^ (prefixWord ++ tailWord_290341).sum := by decide
  have hdescent : baseEnd_290341 < baseStart_290341 := by decide
  rcases family_descends (prefixWord ++ tailWord_290341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290465 : List Nat := [1, 2, 3, 3, 2, 2, 1, 3, 4]
def baseStart_290465 : Nat := 118140960795 + 290465 * 2 ^ 59
def prefixEnd_290465 : Nat := 4983230072969 + 3 ^ 40 * 290465 * 2
def baseEnd_290465 : Nat := 66288070359249461356303

theorem tailTrace_290465 : CollatzResearch.WordTrace tailWord_290465 prefixEnd_290465 66288070359249461356303 := by
  unfold tailWord_290465
  simp only [CollatzResearch.WordTrace]
  refine ⟨10594128892702387317656849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7062752595134924878437899 10594128892702387317656849)
  ·
    refine ⟨7945596669526790488242637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10594128892702387317656849 7945596669526790488242637)
    ·
      refine ⟨2979598751072546433090989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7945596669526790488242637 2979598751072546433090989)
      ·
        refine ⟨1117349531652204912409121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2979598751072546433090989 1117349531652204912409121)
        ·
          refine ⟨838012148739153684306841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1117349531652204912409121 838012148739153684306841)
          ·
            refine ⟨628509111554365263230131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 838012148739153684306841 628509111554365263230131)
            ·
              refine ⟨942763667331547894845197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 628509111554365263230131 942763667331547894845197)
              ·
                refine ⟨353536375249330460566949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 942763667331547894845197 353536375249330460566949)
                ·
                  refine ⟨66288070359249461356303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 353536375249330460566949 66288070359249461356303)
                  ·
                    rfl

theorem cell21_290465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 4].length) (baseStart_290465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_290465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_290465 prefixEnd_290465 := by exact prefixLift 290465
  have htrace : WordTrace (prefixWord ++ tailWord_290465) baseStart_290465 baseEnd_290465 := by
    simpa [prefixWord, tailWord_290465, baseEnd_290465] using wordTrace_append hprefix tailTrace_290465
  have hstable : (prefixWord ++ tailWord_290465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290465).length < 2 ^ (prefixWord ++ tailWord_290465).sum := by decide
  have hdescent : baseEnd_290465 < baseStart_290465 := by decide
  rcases family_descends (prefixWord ++ tailWord_290465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290502 : List Nat := [6, 1, 2, 1, 1, 1, 4, 2, 3]
def baseStart_290502 : Nat := 118140960795 + 290502 * 2 ^ 59
def prefixEnd_290502 : Nat := 4983230072969 + 3 ^ 40 * 290502 * 2
def baseEnd_290502 : Nat := 66296514263345619239561

theorem tailTrace_290502 : CollatzResearch.WordTrace tailWord_290502 prefixEnd_290502 66296514263345619239561 := by
  unfold tailWord_290502
  simp only [CollatzResearch.WordTrace]
  refine ⟨331108699799010707398555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7063652262378895091169173 331108699799010707398555)
  ·
    refine ⟨496663049698516061097833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 331108699799010707398555 496663049698516061097833)
    ·
      refine ⟨372497287273887045823375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 496663049698516061097833 372497287273887045823375)
      ·
        refine ⟨558745930910830568735063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372497287273887045823375 558745930910830568735063)
        ·
          refine ⟨838118896366245853102595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 558745930910830568735063 838118896366245853102595)
          ·
            refine ⟨1257178344549368779653893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 838118896366245853102595 1257178344549368779653893)
            ·
              refine ⟨235720939603006646185105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1257178344549368779653893 235720939603006646185105)
              ·
                refine ⟨176790704702254984638829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 235720939603006646185105 176790704702254984638829)
                ·
                  refine ⟨66296514263345619239561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 176790704702254984638829 66296514263345619239561)
                  ·
                    rfl

theorem cell21_290502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_290502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_290502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_290502 prefixEnd_290502 := by exact prefixLift 290502
  have htrace : WordTrace (prefixWord ++ tailWord_290502) baseStart_290502 baseEnd_290502 := by
    simpa [prefixWord, tailWord_290502, baseEnd_290502] using wordTrace_append hprefix tailTrace_290502
  have hstable : (prefixWord ++ tailWord_290502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290502).length < 2 ^ (prefixWord ++ tailWord_290502).sum := by decide
  have hdescent : baseEnd_290502 < baseStart_290502 := by decide
  rcases family_descends (prefixWord ++ tailWord_290502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290507 : List Nat := [1, 1, 1, 1, 3, 2, 1, 5, 6]
def baseStart_290507 : Nat := 118140960795 + 290507 * 2 ^ 59
def prefixEnd_290507 : Nat := 4983230072969 + 3 ^ 40 * 290507 * 2
def baseEnd_290507 : Nat := 66297655331466721656217

theorem tailTrace_290507 : CollatzResearch.WordTrace tailWord_290507 prefixEnd_290507 66297655331466721656217 := by
  unfold tailWord_290507
  simp only [CollatzResearch.WordTrace]
  refine ⟨10595660758550228490685775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7063773839033485660457183 10595660758550228490685775)
  ·
    refine ⟨15893491137825342736028663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10595660758550228490685775 15893491137825342736028663)
    ·
      refine ⟨23840236706738014104042995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15893491137825342736028663 23840236706738014104042995)
      ·
        refine ⟨35760355060107021156064493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23840236706738014104042995 35760355060107021156064493)
        ·
          refine ⟨13410133147540132933524185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35760355060107021156064493 13410133147540132933524185)
          ·
            refine ⟨10057599860655099700143139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13410133147540132933524185 10057599860655099700143139)
            ·
              refine ⟨15086399790982649550214709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10057599860655099700143139 15086399790982649550214709)
              ·
                refine ⟨1414349980404623395332629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15086399790982649550214709 1414349980404623395332629)
                ·
                  refine ⟨66297655331466721656217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1414349980404623395332629 66297655331466721656217)
                  ·
                    rfl

theorem cell21_290507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 6].length) (baseStart_290507 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_290507 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_290507 prefixEnd_290507 := by exact prefixLift 290507
  have htrace : WordTrace (prefixWord ++ tailWord_290507) baseStart_290507 baseEnd_290507 := by
    simpa [prefixWord, tailWord_290507, baseEnd_290507] using wordTrace_append hprefix tailTrace_290507
  have hstable : (prefixWord ++ tailWord_290507).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290507).length < 2 ^ (prefixWord ++ tailWord_290507).sum := by decide
  have hdescent : baseEnd_290507 < baseStart_290507 := by decide
  rcases family_descends (prefixWord ++ tailWord_290507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290538 : List Nat := [3, 1, 3, 1, 1, 1, 2, 9]
def baseStart_290538 : Nat := 118140960795 + 290538 * 2 ^ 59
def prefixEnd_290538 : Nat := 4983230072969 + 3 ^ 40 * 290538 * 2
def baseEnd_290538 : Nat := 22101576651272518879829

theorem tailTrace_290538 : CollatzResearch.WordTrace tailWord_290538 prefixEnd_290538 22101576651272518879829 := by
  unfold tailWord_290538
  simp only [CollatzResearch.WordTrace]
  refine ⟨2649197855359480196266067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7064527614291947190042845 2649197855359480196266067)
  ·
    refine ⟨3973796783039220294399101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2649197855359480196266067 3973796783039220294399101)
    ·
      refine ⟨1490173793639707610399663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3973796783039220294399101 1490173793639707610399663)
      ·
        refine ⟨2235260690459561415599495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1490173793639707610399663 2235260690459561415599495)
        ·
          refine ⟨3352891035689342123399243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2235260690459561415599495 3352891035689342123399243)
          ·
            refine ⟨5029336553534013185098865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3352891035689342123399243 5029336553534013185098865)
            ·
              refine ⟨3772002415150509888824149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5029336553534013185098865 3772002415150509888824149)
              ·
                refine ⟨22101576651272518879829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3772002415150509888824149 22101576651272518879829)
                ·
                  rfl

theorem cell21_290538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 9].length) (baseStart_290538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_290538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_290538 prefixEnd_290538 := by exact prefixLift 290538
  have htrace : WordTrace (prefixWord ++ tailWord_290538) baseStart_290538 baseEnd_290538 := by
    simpa [prefixWord, tailWord_290538, baseEnd_290538] using wordTrace_append hprefix tailTrace_290538
  have hstable : (prefixWord ++ tailWord_290538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290538).length < 2 ^ (prefixWord ++ tailWord_290538).sum := by decide
  have hdescent : baseEnd_290538 < baseStart_290538 := by decide
  rcases family_descends (prefixWord ++ tailWord_290538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290600 : List Nat := [2, 1, 5, 1, 1, 2, 1, 2, 6]
def baseStart_290600 : Nat := 118140960795 + 290600 * 2 ^ 59
def prefixEnd_290600 : Nat := 4983230072969 + 3 ^ 40 * 290600 * 2
def baseEnd_290600 : Nat := 66318879198519226606027

theorem tailTrace_290600 : CollatzResearch.WordTrace tailWord_290600 prefixEnd_290600 66318879198519226606027 := by
  unfold tailWord_290600
  simp only [CollatzResearch.WordTrace]
  refine ⟨5299526373606652686910627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7066035164808870249214169 5299526373606652686910627)
  ·
    refine ⟨7949289560409979030365941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5299526373606652686910627 7949289560409979030365941)
    ·
      refine ⟨745245896288435534096807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7949289560409979030365941 745245896288435534096807)
      ·
        refine ⟨1117868844432653301145211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 745245896288435534096807 1117868844432653301145211)
        ·
          refine ⟨1676803266648979951717817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1117868844432653301145211 1676803266648979951717817)
          ·
            refine ⟨1257602449986734963788363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1676803266648979951717817 1257602449986734963788363)
            ·
              refine ⟨1886403674980102445682545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1257602449986734963788363 1886403674980102445682545)
              ·
                refine ⟨1414802756235076834261909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1886403674980102445682545 1414802756235076834261909)
                ·
                  refine ⟨66318879198519226606027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1414802756235076834261909 66318879198519226606027)
                  ·
                    rfl

theorem cell21_290600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 6].length) (baseStart_290600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_290600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_290600 prefixEnd_290600 := by exact prefixLift 290600
  have htrace : WordTrace (prefixWord ++ tailWord_290600) baseStart_290600 baseEnd_290600 := by
    simpa [prefixWord, tailWord_290600, baseEnd_290600] using wordTrace_append hprefix tailTrace_290600
  have hstable : (prefixWord ++ tailWord_290600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290600).length < 2 ^ (prefixWord ++ tailWord_290600).sum := by decide
  have hdescent : baseEnd_290600 < baseStart_290600 := by decide
  rcases family_descends (prefixWord ++ tailWord_290600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290704 : List Nat := [2, 1, 1, 1, 1, 1, 2, 5, 7]
def baseStart_290704 : Nat := 118140960795 + 290704 * 2 ^ 59
def prefixEnd_290704 : Nat := 4983230072969 + 3 ^ 40 * 290704 * 2
def baseEnd_290704 : Nat := 66342613415438156872481

theorem tailTrace_290704 : CollatzResearch.WordTrace tailWord_290704 prefixEnd_290704 66342613415438156872481 := by
  unfold tailWord_290704
  simp only [CollatzResearch.WordTrace]
  refine ⟨5301422969418265567803583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7068563959224354090404777 5301422969418265567803583)
  ·
    refine ⟨7952134454127398351705375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5301422969418265567803583 7952134454127398351705375)
    ·
      refine ⟨11928201681191097527558063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7952134454127398351705375 11928201681191097527558063)
      ·
        refine ⟨17892302521786646291337095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11928201681191097527558063 17892302521786646291337095)
        ·
          refine ⟨26838453782679969437005643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17892302521786646291337095 26838453782679969437005643)
          ·
            refine ⟨40257680674019954155508465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26838453782679969437005643 40257680674019954155508465)
            ·
              refine ⟨30193260505514965616631349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40257680674019954155508465 30193260505514965616631349)
              ·
                refine ⟨2830618172392028026559189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30193260505514965616631349 2830618172392028026559189)
                ·
                  refine ⟨66342613415438156872481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2830618172392028026559189 66342613415438156872481)
                  ·
                    rfl

theorem cell21_290704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 7].length) (baseStart_290704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_290704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_290704 prefixEnd_290704 := by exact prefixLift 290704
  have htrace : WordTrace (prefixWord ++ tailWord_290704) baseStart_290704 baseEnd_290704 := by
    simpa [prefixWord, tailWord_290704, baseEnd_290704] using wordTrace_append hprefix tailTrace_290704
  have hstable : (prefixWord ++ tailWord_290704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290704).length < 2 ^ (prefixWord ++ tailWord_290704).sum := by decide
  have hdescent : baseEnd_290704 < baseStart_290704 := by decide
  rcases family_descends (prefixWord ++ tailWord_290704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290735 : List Nat := [1, 1, 2, 1, 2, 2, 5, 1, 6]
def baseStart_290735 : Nat := 118140960795 + 290735 * 2 ^ 59
def prefixEnd_290735 : Nat := 4983230072969 + 3 ^ 40 * 290735 * 2
def baseEnd_290735 : Nat := 66349688037788991855751

theorem tailTrace_290735 : CollatzResearch.WordTrace tailWord_290735 prefixEnd_290735 66349688037788991855751 := by
  unfold tailWord_290735
  simp only [CollatzResearch.WordTrace]
  refine ⟨10603976601724223429985659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7069317734482815619990439 10603976601724223429985659)
  ·
    refine ⟨15905964902586335144978489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10603976601724223429985659 15905964902586335144978489)
    ·
      refine ⟨11929473676939751358733867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15905964902586335144978489 11929473676939751358733867)
      ·
        refine ⟨17894210515409627038100801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11929473676939751358733867 17894210515409627038100801)
        ·
          refine ⟨13420657886557220278575601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17894210515409627038100801 13420657886557220278575601)
          ·
            refine ⟨10065493414917915208931701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13420657886557220278575601 10065493414917915208931701)
            ·
              refine ⟨943640007648554550837347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10065493414917915208931701 943640007648554550837347)
              ·
                refine ⟨1415460011472831826256021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 943640007648554550837347 1415460011472831826256021)
                ·
                  refine ⟨66349688037788991855751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1415460011472831826256021 66349688037788991855751)
                  ·
                    rfl

theorem cell21_290735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 6].length) (baseStart_290735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_290735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_290735 prefixEnd_290735 := by exact prefixLift 290735
  have htrace : WordTrace (prefixWord ++ tailWord_290735) baseStart_290735 baseEnd_290735 := by
    simpa [prefixWord, tailWord_290735, baseEnd_290735] using wordTrace_append hprefix tailTrace_290735
  have hstable : (prefixWord ++ tailWord_290735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290735).length < 2 ^ (prefixWord ++ tailWord_290735).sum := by decide
  have hdescent : baseEnd_290735 < baseStart_290735 := by decide
  rcases family_descends (prefixWord ++ tailWord_290735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290766 : List Nat := [4, 1, 1, 1, 2, 2, 3, 7]
def baseStart_290766 : Nat := 118140960795 + 290766 * 2 ^ 59
def prefixEnd_290766 : Nat := 4983230072969 + 3 ^ 40 * 290766 * 2
def baseEnd_290766 : Nat := 22118920886713275613007

theorem tailTrace_290766 : CollatzResearch.WordTrace tailWord_290766 prefixEnd_290766 22118920886713275613007 := by
  unfold tailWord_290766
  simp only [CollatzResearch.WordTrace]
  refine ⟨1325638408076489465545519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7070071509741277149576101 1325638408076489465545519)
  ·
    refine ⟨1988457612114734198318279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1325638408076489465545519 1988457612114734198318279)
    ·
      refine ⟨2982686418172101297477419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1988457612114734198318279 2982686418172101297477419)
      ·
        refine ⟨4474029627258151946216129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2982686418172101297477419 4474029627258151946216129)
        ·
          refine ⟨3355522220443613959662097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4474029627258151946216129 3355522220443613959662097)
          ·
            refine ⟨2516641665332710469746573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3355522220443613959662097 2516641665332710469746573)
            ·
              refine ⟨943740624499766426154965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2516641665332710469746573 943740624499766426154965)
              ·
                refine ⟨22118920886713275613007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 943740624499766426154965 22118920886713275613007)
                ·
                  rfl

theorem cell21_290766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_290766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_290766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_290766 prefixEnd_290766 := by exact prefixLift 290766
  have htrace : WordTrace (prefixWord ++ tailWord_290766) baseStart_290766 baseEnd_290766 := by
    simpa [prefixWord, tailWord_290766, baseEnd_290766] using wordTrace_append hprefix tailTrace_290766
  have hstable : (prefixWord ++ tailWord_290766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290766).length < 2 ^ (prefixWord ++ tailWord_290766).sum := by decide
  have hdescent : baseEnd_290766 < baseStart_290766 := by decide
  rcases family_descends (prefixWord ++ tailWord_290766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290845 : List Nat := [1, 4, 2, 2, 2, 2, 2, 2, 4]
def baseStart_290845 : Nat := 118140960795 + 290845 * 2 ^ 59
def prefixEnd_290845 : Nat := 4983230072969 + 3 ^ 40 * 290845 * 2
def baseEnd_290845 : Nat := 66374791536453245022193

theorem tailTrace_290845 : CollatzResearch.WordTrace tailWord_290845 prefixEnd_290845 66374791536453245022193 := by
  unfold tailWord_290845
  simp only [CollatzResearch.WordTrace]
  refine ⟨10607988631325712216489989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7071992420883808144326659 10607988631325712216489989)
  ·
    refine ⟨1988997868373571040591873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10607988631325712216489989 1988997868373571040591873)
    ·
      refine ⟨1491748401280178280443905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1988997868373571040591873 1491748401280178280443905)
      ·
        refine ⟨1118811300960133710332929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1491748401280178280443905 1118811300960133710332929)
        ·
          refine ⟨839108475720100282749697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1118811300960133710332929 839108475720100282749697)
          ·
            refine ⟨629331356790075212062273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 839108475720100282749697 629331356790075212062273)
            ·
              refine ⟨471998517592556409046705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 629331356790075212062273 471998517592556409046705)
              ·
                refine ⟨353998888194417306785029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 471998517592556409046705 353998888194417306785029)
                ·
                  refine ⟨66374791536453245022193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 353998888194417306785029 66374791536453245022193)
                  ·
                    rfl

theorem cell21_290845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_290845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_290845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_290845 prefixEnd_290845 := by exact prefixLift 290845
  have htrace : WordTrace (prefixWord ++ tailWord_290845) baseStart_290845 baseEnd_290845 := by
    simpa [prefixWord, tailWord_290845, baseEnd_290845] using wordTrace_append hprefix tailTrace_290845
  have hstable : (prefixWord ++ tailWord_290845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290845).length < 2 ^ (prefixWord ++ tailWord_290845).sum := by decide
  have hdescent : baseEnd_290845 < baseStart_290845 := by decide
  rcases family_descends (prefixWord ++ tailWord_290845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290887 : List Nat := [1, 1, 4, 1, 3, 1, 2, 2, 6]
def baseStart_290887 : Nat := 118140960795 + 290887 * 2 ^ 59
def prefixEnd_290887 : Nat := 4983230072969 + 3 ^ 40 * 290887 * 2
def baseEnd_290887 : Nat := 66384376508670505322107

theorem tailTrace_290887 : CollatzResearch.WordTrace tailWord_290887 prefixEnd_290887 66384376508670505322107 := by
  unfold tailWord_290887
  simp only [CollatzResearch.WordTrace]
  refine ⟨10609520497173553389518915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7073013664782368926345943 10609520497173553389518915)
  ·
    refine ⟨15914280745760330084278373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10609520497173553389518915 15914280745760330084278373)
    ·
      refine ⟨2983927639830061890802195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15914280745760330084278373 2983927639830061890802195)
      ·
        refine ⟨4475891459745092836203293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2983927639830061890802195 4475891459745092836203293)
        ·
          refine ⟨1678459297404409813576235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4475891459745092836203293 1678459297404409813576235)
          ·
            refine ⟨2517688946106614720364353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1678459297404409813576235 2517688946106614720364353)
            ·
              refine ⟨1888266709579961040273265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2517688946106614720364353 1888266709579961040273265)
              ·
                refine ⟨1416200032184970780204949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1888266709579961040273265 1416200032184970780204949)
                ·
                  refine ⟨66384376508670505322107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1416200032184970780204949 66384376508670505322107)
                  ·
                    rfl

theorem cell21_290887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 6].length) (baseStart_290887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_290887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_290887 prefixEnd_290887 := by exact prefixLift 290887
  have htrace : WordTrace (prefixWord ++ tailWord_290887) baseStart_290887 baseEnd_290887 := by
    simpa [prefixWord, tailWord_290887, baseEnd_290887] using wordTrace_append hprefix tailTrace_290887
  have hstable : (prefixWord ++ tailWord_290887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290887).length < 2 ^ (prefixWord ++ tailWord_290887).sum := by decide
  have hdescent : baseEnd_290887 < baseStart_290887 := by decide
  rcases family_descends (prefixWord ++ tailWord_290887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290904 : List Nat := [2, 1, 2, 2, 1, 4, 3, 2, 4]
def baseStart_290904 : Nat := 118140960795 + 290904 * 2 ^ 59
def prefixEnd_290904 : Nat := 4983230072969 + 3 ^ 40 * 290904 * 2
def baseEnd_290904 : Nat := 66388256140282253538739

theorem tailTrace_290904 : CollatzResearch.WordTrace tailWord_290904 prefixEnd_290904 66388256140282253538739 := by
  unfold tailWord_290904
  simp only [CollatzResearch.WordTrace]
  refine ⟨5305070269055982646443883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7073427025407976861925177 5305070269055982646443883)
  ·
    refine ⟨7957605403583973969665825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5305070269055982646443883 7957605403583973969665825)
    ·
      refine ⟨5968204052687980477249369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7957605403583973969665825 5968204052687980477249369)
      ·
        refine ⟨4476153039515985357937027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5968204052687980477249369 4476153039515985357937027)
        ·
          refine ⟨6714229559273978036905541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4476153039515985357937027 6714229559273978036905541)
          ·
            refine ⟨1258918042363870881919789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6714229559273978036905541 1258918042363870881919789)
            ·
              refine ⟨472094265886451580719921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1258918042363870881919789 472094265886451580719921)
              ·
                refine ⟨354070699414838685539941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 472094265886451580719921 354070699414838685539941)
                ·
                  refine ⟨66388256140282253538739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 354070699414838685539941 66388256140282253538739)
                  ·
                    rfl

theorem cell21_290904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 4].length) (baseStart_290904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_290904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_290904 prefixEnd_290904 := by exact prefixLift 290904
  have htrace : WordTrace (prefixWord ++ tailWord_290904) baseStart_290904 baseEnd_290904 := by
    simpa [prefixWord, tailWord_290904, baseEnd_290904] using wordTrace_append hprefix tailTrace_290904
  have hstable : (prefixWord ++ tailWord_290904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290904).length < 2 ^ (prefixWord ++ tailWord_290904).sum := by decide
  have hdescent : baseEnd_290904 < baseStart_290904 := by decide
  rcases family_descends (prefixWord ++ tailWord_290904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290935 : List Nat := [1, 1, 3, 1, 1, 7, 2, 5]
def baseStart_290935 : Nat := 118140960795 + 290935 * 2 ^ 59
def prefixEnd_290935 : Nat := 4983230072969 + 3 ^ 40 * 290935 * 2
def baseEnd_290935 : Nat := 22131776920877696174003

theorem tailTrace_290935 : CollatzResearch.WordTrace tailWord_290935 prefixEnd_290935 22131776920877696174003 := by
  unfold tailWord_290935
  simp only [CollatzResearch.WordTrace]
  refine ⟨10611271200999657587266259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7074180800666438391510839 10611271200999657587266259)
  ·
    refine ⟨15916906801499486380899389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10611271200999657587266259 15916906801499486380899389)
    ·
      refine ⟨5968840050562307392837271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15916906801499486380899389 5968840050562307392837271)
      ·
        refine ⟨8953260075843461089255907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5968840050562307392837271 8953260075843461089255907)
        ·
          refine ⟨13429890113765191633883861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8953260075843461089255907 13429890113765191633883861)
          ·
            refine ⟨314763049541371678919153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 13429890113765191633883861 314763049541371678919153)
            ·
              refine ⟨236072287156028759189365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 314763049541371678919153 236072287156028759189365)
              ·
                refine ⟨22131776920877696174003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 236072287156028759189365 22131776920877696174003)
                ·
                  rfl

theorem cell21_290935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 5].length) (baseStart_290935 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_290935 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_290935 prefixEnd_290935 := by exact prefixLift 290935
  have htrace : WordTrace (prefixWord ++ tailWord_290935) baseStart_290935 baseEnd_290935 := by
    simpa [prefixWord, tailWord_290935, baseEnd_290935] using wordTrace_append hprefix tailTrace_290935
  have hstable : (prefixWord ++ tailWord_290935).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290935).length < 2 ^ (prefixWord ++ tailWord_290935).sum := by decide
  have hdescent : baseEnd_290935 < baseStart_290935 := by decide
  rcases family_descends (prefixWord ++ tailWord_290935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290963 : List Nat := [1, 1, 1, 2, 1, 2, 3, 6, 4]
def baseStart_290963 : Nat := 118140960795 + 290963 * 2 ^ 59
def prefixEnd_290963 : Nat := 4983230072969 + 3 ^ 40 * 290963 * 2
def baseEnd_290963 : Nat := 66401720744111262055285

theorem tailTrace_290963 : CollatzResearch.WordTrace tailWord_290963 prefixEnd_290963 66401720744111262055285 := by
  unfold tailWord_290963
  simp only [CollatzResearch.WordTrace]
  refine ⟨10612292444898218369285543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7074861629932145579523695 10612292444898218369285543)
  ·
    refine ⟨15918438667347327553928315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10612292444898218369285543 15918438667347327553928315)
    ·
      refine ⟨23877658001020991330892473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15918438667347327553928315 23877658001020991330892473)
      ·
        refine ⟨17908243500765743498169355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23877658001020991330892473 17908243500765743498169355)
        ·
          refine ⟨26862365251148615247254033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17908243500765743498169355 26862365251148615247254033)
          ·
            refine ⟨20146773938361461435440525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26862365251148615247254033 20146773938361461435440525)
            ·
              refine ⟨7555040226885548038290197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20146773938361461435440525 7555040226885548038290197)
              ·
                refine ⟨354142510635260064294853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7555040226885548038290197 354142510635260064294853)
                ·
                  refine ⟨66401720744111262055285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 354142510635260064294853 66401720744111262055285)
                  ·
                    rfl

theorem cell21_290963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 4].length) (baseStart_290963 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_290963 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_290963 prefixEnd_290963 := by exact prefixLift 290963
  have htrace : WordTrace (prefixWord ++ tailWord_290963) baseStart_290963 baseEnd_290963 := by
    simpa [prefixWord, tailWord_290963, baseEnd_290963] using wordTrace_append hprefix tailTrace_290963
  have hstable : (prefixWord ++ tailWord_290963).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290963).length < 2 ^ (prefixWord ++ tailWord_290963).sum := by decide
  have hdescent : baseEnd_290963 < baseStart_290963 := by decide
  rcases family_descends (prefixWord ++ tailWord_290963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291070 : List Nat := [4, 2, 2, 1, 1, 1, 10]
def baseStart_291070 : Nat := 118140960795 + 291070 * 2 ^ 59
def prefixEnd_291070 : Nat := 4983230072969 + 3 ^ 40 * 291070 * 2
def baseEnd_291070 : Nat := 7380682177989205974637

theorem tailTrace_291070 : CollatzResearch.WordTrace tailWord_291070 prefixEnd_291070 7380682177989205974637 := by
  unfold tailWord_291070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1327024381938821955428833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7077463370340383762287109 1327024381938821955428833)
  ·
    refine ⟨995268286454116466571625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1327024381938821955428833 995268286454116466571625)
    ·
      refine ⟨746451214840587349928719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 995268286454116466571625 746451214840587349928719)
      ·
        refine ⟨1119676822260881024893079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 746451214840587349928719 1119676822260881024893079)
        ·
          refine ⟨1679515233391321537339619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1119676822260881024893079 1679515233391321537339619)
          ·
            refine ⟨2519272850086982306009429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1679515233391321537339619 2519272850086982306009429)
            ·
              refine ⟨7380682177989205974637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2519272850086982306009429 7380682177989205974637)
              ·
                rfl

theorem cell21_291070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 10].length) (baseStart_291070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_291070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_291070 prefixEnd_291070 := by exact prefixLift 291070
  have htrace : WordTrace (prefixWord ++ tailWord_291070) baseStart_291070 baseEnd_291070 := by
    simpa [prefixWord, tailWord_291070, baseEnd_291070] using wordTrace_append hprefix tailTrace_291070
  have hstable : (prefixWord ++ tailWord_291070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291070).length < 2 ^ (prefixWord ++ tailWord_291070).sum := by decide
  have hdescent : baseEnd_291070 < baseStart_291070 := by decide
  rcases family_descends (prefixWord ++ tailWord_291070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291177 : List Nat := [1, 2, 1, 1, 1, 3, 4, 5, 3]
def baseStart_291177 : Nat := 118140960795 + 291177 * 2 ^ 59
def prefixEnd_291177 : Nat := 4983230072969 + 3 ^ 40 * 291177 * 2
def baseEnd_291177 : Nat := 66450558459694445488181

theorem tailTrace_291177 : CollatzResearch.WordTrace tailWord_291177 prefixEnd_291177 66450558459694445488181 := by
  unfold tailWord_291177
  simp only [CollatzResearch.WordTrace]
  refine ⟨10620097666122932917575785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7080065110748621945050523 10620097666122932917575785)
  ·
    refine ⟨7965073249592199688181839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10620097666122932917575785 7965073249592199688181839)
    ·
      refine ⟨11947609874388299532272759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7965073249592199688181839 11947609874388299532272759)
      ·
        refine ⟨17921414811582449298409139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11947609874388299532272759 17921414811582449298409139)
        ·
          refine ⟨26882122217373673947613709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17921414811582449298409139 26882122217373673947613709)
          ·
            refine ⟨10080795831515127730355141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26882122217373673947613709 10080795831515127730355141)
            ·
              refine ⟨1890149218409086449441589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10080795831515127730355141 1890149218409086449441589)
              ·
                refine ⟨177201489225851854635149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1890149218409086449441589 177201489225851854635149)
                ·
                  refine ⟨66450558459694445488181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 177201489225851854635149 66450558459694445488181)
                  ·
                    rfl

theorem cell21_291177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 5, 3].length) (baseStart_291177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_291177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_291177 prefixEnd_291177 := by exact prefixLift 291177
  have htrace : WordTrace (prefixWord ++ tailWord_291177) baseStart_291177 baseEnd_291177 := by
    simpa [prefixWord, tailWord_291177, baseEnd_291177] using wordTrace_append hprefix tailTrace_291177
  have hstable : (prefixWord ++ tailWord_291177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291177).length < 2 ^ (prefixWord ++ tailWord_291177).sum := by decide
  have hdescent : baseEnd_291177 < baseStart_291177 := by decide
  rcases family_descends (prefixWord ++ tailWord_291177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291242 : List Nat := [3, 1, 6, 1, 1, 1, 1, 1, 6]
def baseStart_291242 : Nat := 118140960795 + 291242 * 2 ^ 59
def prefixEnd_291242 : Nat := 4983230072969 + 3 ^ 40 * 291242 * 2
def baseEnd_291242 : Nat := 66465392345268776904715

theorem tailTrace_291242 : CollatzResearch.WordTrace tailWord_291242 prefixEnd_291242 66465392345268776904715 := by
  unfold tailWord_291242
  simp only [CollatzResearch.WordTrace]
  refine ⟨2655617102721862254672995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7081645607258299345794653 2655617102721862254672995)
  ·
    refine ⟨3983425654082793382009493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2655617102721862254672995 3983425654082793382009493)
    ·
      refine ⟨186723077535130939781695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3983425654082793382009493 186723077535130939781695)
      ·
        refine ⟨280084616302696409672543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186723077535130939781695 280084616302696409672543)
        ·
          refine ⟨420126924454044614508815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280084616302696409672543 420126924454044614508815)
          ·
            refine ⟨630190386681066921763223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 420126924454044614508815 630190386681066921763223)
            ·
              refine ⟨945285580021600382644835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 630190386681066921763223 945285580021600382644835)
              ·
                refine ⟨1417928370032400573967253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 945285580021600382644835 1417928370032400573967253)
                ·
                  refine ⟨66465392345268776904715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1417928370032400573967253 66465392345268776904715)
                  ·
                    rfl

theorem cell21_291242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 6].length) (baseStart_291242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_291242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_291242 prefixEnd_291242 := by exact prefixLift 291242
  have htrace : WordTrace (prefixWord ++ tailWord_291242) baseStart_291242 baseEnd_291242 := by
    simpa [prefixWord, tailWord_291242, baseEnd_291242] using wordTrace_append hprefix tailTrace_291242
  have hstable : (prefixWord ++ tailWord_291242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291242).length < 2 ^ (prefixWord ++ tailWord_291242).sum := by decide
  have hdescent : baseEnd_291242 < baseStart_291242 := by decide
  rcases family_descends (prefixWord ++ tailWord_291242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291357 : List Nat := [1, 4, 2, 2, 1, 11]
def baseStart_291357 : Nat := 118140960795 + 291357 * 2 ^ 59
def prefixEnd_291357 : Nat := 4983230072969 + 3 ^ 40 * 291357 * 2
def baseEnd_291357 : Nat := 2462653218964967869919

theorem tailTrace_291357 : CollatzResearch.WordTrace tailWord_291357 prefixEnd_291357 2462653218964967869919 := by
  unfold tailWord_291357
  simp only [CollatzResearch.WordTrace]
  refine ⟨10626662805470823659128325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7084441870313882439418883 10626662805470823659128325)
  ·
    refine ⟨1992499276025779436086561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10626662805470823659128325 1992499276025779436086561)
    ·
      refine ⟨1494374457019334577064921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1992499276025779436086561 1494374457019334577064921)
      ·
        refine ⟨1120780842764500932798691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1494374457019334577064921 1120780842764500932798691)
        ·
          refine ⟨1681171264146751399198037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1120780842764500932798691 1681171264146751399198037)
          ·
            refine ⟨2462653218964967869919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1681171264146751399198037 2462653218964967869919)
            ·
              rfl

theorem cell21_291357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 11].length) (baseStart_291357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_291357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_291357 prefixEnd_291357 := by exact prefixLift 291357
  have htrace : WordTrace (prefixWord ++ tailWord_291357) baseStart_291357 baseEnd_291357 := by
    simpa [prefixWord, tailWord_291357, baseEnd_291357] using wordTrace_append hprefix tailTrace_291357
  have hstable : (prefixWord ++ tailWord_291357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291357).length < 2 ^ (prefixWord ++ tailWord_291357).sum := by decide
  have hdescent : baseEnd_291357 < baseStart_291357 := by decide
  rcases family_descends (prefixWord ++ tailWord_291357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291363 : List Nat := [1, 1, 1, 4, 4, 3, 2, 2, 3]
def baseStart_291363 : Nat := 118140960795 + 291363 * 2 ^ 59
def prefixEnd_291363 : Nat := 4983230072969 + 3 ^ 40 * 291363 * 2
def baseEnd_291363 : Nat := 66493006193799455387801

theorem tailTrace_291363 : CollatzResearch.WordTrace tailWord_291363 prefixEnd_291363 66493006193799455387801 := by
  unfold tailWord_291363
  simp only [CollatzResearch.WordTrace]
  refine ⟨10626881643449086683846743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7084587762299391122564495 10626881643449086683846743)
  ·
    refine ⟨15940322465173630025770115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10626881643449086683846743 15940322465173630025770115)
    ·
      refine ⟨23910483697760445038655173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15940322465173630025770115 23910483697760445038655173)
      ·
        refine ⟨4483215693330083444747845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23910483697760445038655173 4483215693330083444747845)
        ·
          refine ⟨840602942499390645890221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4483215693330083444747845 840602942499390645890221)
          ·
            refine ⟨315226103437271492208833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 840602942499390645890221 315226103437271492208833)
            ·
              refine ⟨236419577577953619156625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 315226103437271492208833 236419577577953619156625)
              ·
                refine ⟨177314683183465214367469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 236419577577953619156625 177314683183465214367469)
                ·
                  refine ⟨66493006193799455387801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 177314683183465214367469 66493006193799455387801)
                  ·
                    rfl

theorem cell21_291363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 2, 3].length) (baseStart_291363 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_291363 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_291363 prefixEnd_291363 := by exact prefixLift 291363
  have htrace : WordTrace (prefixWord ++ tailWord_291363) baseStart_291363 baseEnd_291363 := by
    simpa [prefixWord, tailWord_291363, baseEnd_291363] using wordTrace_append hprefix tailTrace_291363
  have hstable : (prefixWord ++ tailWord_291363).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291363).length < 2 ^ (prefixWord ++ tailWord_291363).sum := by decide
  have hdescent : baseEnd_291363 < baseStart_291363 := by decide
  rcases family_descends (prefixWord ++ tailWord_291363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291371 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 9]
def baseStart_291371 : Nat := 118140960795 + 291371 * 2 ^ 59
def prefixEnd_291371 : Nat := 4983230072969 + 3 ^ 40 * 291371 * 2
def baseEnd_291371 : Nat := 66494831902793219254451

theorem tailTrace_291371 : CollatzResearch.WordTrace tailWord_291371 prefixEnd_291371 66494831902793219254451 := by
  unfold tailWord_291371
  simp only [CollatzResearch.WordTrace]
  refine ⟨10627173427420104050137967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7084782284946736033425311 10627173427420104050137967)
  ·
    refine ⟨15940760141130156075206951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10627173427420104050137967 15940760141130156075206951)
    ·
      refine ⟨23911140211695234112810427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15940760141130156075206951 23911140211695234112810427)
      ·
        refine ⟨35866710317542851169215641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23911140211695234112810427 35866710317542851169215641)
        ·
          refine ⟨26900032738157138376911731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35866710317542851169215641 26900032738157138376911731)
          ·
            refine ⟨40350049107235707565367597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26900032738157138376911731 40350049107235707565367597)
            ·
              refine ⟨15131268415213390337012849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40350049107235707565367597 15131268415213390337012849)
              ·
                refine ⟨11348451311410042752759637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15131268415213390337012849 11348451311410042752759637)
                ·
                  refine ⟨66494831902793219254451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11348451311410042752759637 66494831902793219254451)
                  ·
                    rfl

theorem cell21_291371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 9].length) (baseStart_291371 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_291371 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_291371 prefixEnd_291371 := by exact prefixLift 291371
  have htrace : WordTrace (prefixWord ++ tailWord_291371) baseStart_291371 baseEnd_291371 := by
    simpa [prefixWord, tailWord_291371, baseEnd_291371] using wordTrace_append hprefix tailTrace_291371
  have hstable : (prefixWord ++ tailWord_291371).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291371).length < 2 ^ (prefixWord ++ tailWord_291371).sum := by decide
  have hdescent : baseEnd_291371 < baseStart_291371 := by decide
  rcases family_descends (prefixWord ++ tailWord_291371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291388 : List Nat := [2, 2, 2, 2, 3, 1, 1, 1, 7]
def baseStart_291388 : Nat := 118140960795 + 291388 * 2 ^ 59
def prefixEnd_291388 : Nat := 4983230072969 + 3 ^ 40 * 291388 * 2
def baseEnd_291388 : Nat := 66498711534404967471083

theorem tailTrace_291388 : CollatzResearch.WordTrace tailWord_291388 prefixEnd_291388 66498711534404967471083 := by
  unfold tailWord_291388
  simp only [CollatzResearch.WordTrace]
  refine ⟨5313896734179257976753409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7085195645572343969004545 5313896734179257976753409)
  ·
    refine ⟨3985422550634443482565057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5313896734179257976753409 3985422550634443482565057)
    ·
      refine ⟨2989066912975832611923793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3985422550634443482565057 2989066912975832611923793)
      ·
        refine ⟨2241800184731874458942845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2989066912975832611923793 2241800184731874458942845)
        ·
          refine ⟨840675069274452922103567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2241800184731874458942845 840675069274452922103567)
          ·
            refine ⟨1261012603911679383155351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 840675069274452922103567 1261012603911679383155351)
            ·
              refine ⟨1891518905867519074733027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1261012603911679383155351 1891518905867519074733027)
              ·
                refine ⟨2837278358801278612099541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1891518905867519074733027 2837278358801278612099541)
                ·
                  refine ⟨66498711534404967471083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2837278358801278612099541 66498711534404967471083)
                  ·
                    rfl

theorem cell21_291388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_291388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_291388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_291388 prefixEnd_291388 := by exact prefixLift 291388
  have htrace : WordTrace (prefixWord ++ tailWord_291388) baseStart_291388 baseEnd_291388 := by
    simpa [prefixWord, tailWord_291388, baseEnd_291388] using wordTrace_append hprefix tailTrace_291388
  have hstable : (prefixWord ++ tailWord_291388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291388).length < 2 ^ (prefixWord ++ tailWord_291388).sum := by decide
  have hdescent : baseEnd_291388 < baseStart_291388 := by decide
  rcases family_descends (prefixWord ++ tailWord_291388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291574 : List Nat := [5, 1, 1, 1, 1, 2, 4, 3, 3]
def baseStart_291574 : Nat := 118140960795 + 291574 * 2 ^ 59
def prefixEnd_291574 : Nat := 4983230072969 + 3 ^ 40 * 291574 * 2
def baseEnd_291574 : Nat := 66541159268509977370703

theorem tailTrace_291574 : CollatzResearch.WordTrace tailWord_291574 prefixEnd_291574 66541159268509977370703 := by
  unfold tailWord_291574
  simp only [CollatzResearch.WordTrace]
  refine ⟨664661090355291857486111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7089718297123113146518517 664661090355291857486111)
  ·
    refine ⟨996991635532937786229167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 664661090355291857486111 996991635532937786229167)
    ·
      refine ⟨1495487453299406679343751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 996991635532937786229167 1495487453299406679343751)
      ·
        refine ⟨2243231179949110019015627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1495487453299406679343751 2243231179949110019015627)
        ·
          refine ⟨3364846769923665028523441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2243231179949110019015627 3364846769923665028523441)
          ·
            refine ⟨2523635077442748771392581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3364846769923665028523441 2523635077442748771392581)
            ·
              refine ⟨473181577020515394636109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2523635077442748771392581 473181577020515394636109)
              ·
                refine ⟨177443091382693272988541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 473181577020515394636109 177443091382693272988541)
                ·
                  refine ⟨66541159268509977370703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 177443091382693272988541 66541159268509977370703)
                  ·
                    rfl

theorem cell21_291574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_291574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_291574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_291574 prefixEnd_291574 := by exact prefixLift 291574
  have htrace : WordTrace (prefixWord ++ tailWord_291574) baseStart_291574 baseEnd_291574 := by
    simpa [prefixWord, tailWord_291574, baseEnd_291574] using wordTrace_append hprefix tailTrace_291574
  have hstable : (prefixWord ++ tailWord_291574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291574).length < 2 ^ (prefixWord ++ tailWord_291574).sum := by decide
  have hdescent : baseEnd_291574 < baseStart_291574 := by decide
  rcases family_descends (prefixWord ++ tailWord_291574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291616 : List Nat := [2, 1, 1, 5, 1, 2, 2, 2, 5]
def baseStart_291616 : Nat := 118140960795 + 291616 * 2 ^ 59
def prefixEnd_291616 : Nat := 4983230072969 + 3 ^ 40 * 291616 * 2
def baseEnd_291616 : Nat := 66550744240727237670617

theorem tailTrace_291616 : CollatzResearch.WordTrace tailWord_291616 prefixEnd_291616 66550744240727237670617 := by
  unfold tailWord_291616
  simp only [CollatzResearch.WordTrace]
  refine ⟨5318054655766255446403351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7090739541021673928537801 5318054655766255446403351)
  ·
    refine ⟨7977081983649383169605027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5318054655766255446403351 7977081983649383169605027)
    ·
      refine ⟨11965622975474074754407541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7977081983649383169605027 11965622975474074754407541)
      ·
        refine ⟨1121777153950694508225707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11965622975474074754407541 1121777153950694508225707)
        ·
          refine ⟨1682665730926041762338561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1121777153950694508225707 1682665730926041762338561)
          ·
            refine ⟨1261999298194531321753921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1682665730926041762338561 1261999298194531321753921)
            ·
              refine ⟨946499473645898491315441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1261999298194531321753921 946499473645898491315441)
              ·
                refine ⟨709874605234423868486581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 946499473645898491315441 709874605234423868486581)
                ·
                  refine ⟨66550744240727237670617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 709874605234423868486581 66550744240727237670617)
                  ·
                    rfl

theorem cell21_291616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 5].length) (baseStart_291616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_291616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_291616 prefixEnd_291616 := by exact prefixLift 291616
  have htrace : WordTrace (prefixWord ++ tailWord_291616) baseStart_291616 baseEnd_291616 := by
    simpa [prefixWord, tailWord_291616, baseEnd_291616] using wordTrace_append hprefix tailTrace_291616
  have hstable : (prefixWord ++ tailWord_291616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291616).length < 2 ^ (prefixWord ++ tailWord_291616).sum := by decide
  have hdescent : baseEnd_291616 < baseStart_291616 := by decide
  rcases family_descends (prefixWord ++ tailWord_291616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291768 : List Nat := [2, 1, 2, 1, 2, 5, 2, 1, 5]
def baseStart_291768 : Nat := 118140960795 + 291768 * 2 ^ 59
def prefixEnd_291768 : Nat := 4983230072969 + 3 ^ 40 * 291768 * 2
def baseEnd_291768 : Nat := 66585432711608751136973

theorem tailTrace_291768 : CollatzResearch.WordTrace tailWord_291768 prefixEnd_291768 66585432711608751136973 := by
  unfold tailWord_291768
  simp only [CollatzResearch.WordTrace]
  refine ⟨5320826603490920426169979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7094435471321227234893305 5320826603490920426169979)
  ·
    refine ⟨7981239905236380639254969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5320826603490920426169979 7981239905236380639254969)
    ·
      refine ⟨5985929928927285479441227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7981239905236380639254969 5985929928927285479441227)
      ·
        refine ⟨8978894893390928219161841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5985929928927285479441227 8978894893390928219161841)
        ·
          refine ⟨6734171170043196164371381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8978894893390928219161841 6734171170043196164371381)
          ·
            refine ⟨631328547191549640409817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6734171170043196164371381 631328547191549640409817)
            ·
              refine ⟨473496410393662230307363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 631328547191549640409817 473496410393662230307363)
              ·
                refine ⟨710244615590493345461045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 473496410393662230307363 710244615590493345461045)
                ·
                  refine ⟨66585432711608751136973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 710244615590493345461045 66585432711608751136973)
                  ·
                    rfl

theorem cell21_291768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 5].length) (baseStart_291768 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_291768 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_291768 prefixEnd_291768 := by exact prefixLift 291768
  have htrace : WordTrace (prefixWord ++ tailWord_291768) baseStart_291768 baseEnd_291768 := by
    simpa [prefixWord, tailWord_291768, baseEnd_291768] using wordTrace_append hprefix tailTrace_291768
  have hstable : (prefixWord ++ tailWord_291768).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291768).length < 2 ^ (prefixWord ++ tailWord_291768).sum := by decide
  have hdescent : baseEnd_291768 < baseStart_291768 := by decide
  rcases family_descends (prefixWord ++ tailWord_291768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291802 : List Nat := [3, 1, 1, 2, 4, 3, 1, 3, 3]
def baseStart_291802 : Nat := 118140960795 + 291802 * 2 ^ 59
def prefixEnd_291802 : Nat := 4983230072969 + 3 ^ 40 * 291802 * 2
def baseEnd_291802 : Nat := 66593191974832247570237

theorem tailTrace_291802 : CollatzResearch.WordTrace tailWord_291802 prefixEnd_291802 66593191974832247570237 := by
  unfold tailWord_291802
  simp only [CollatzResearch.WordTrace]
  refine ⟨2660723322214666164769415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7095262192572443106051773 2660723322214666164769415)
  ·
    refine ⟨3991084983321999247154123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2660723322214666164769415 3991084983321999247154123)
    ·
      refine ⟨5986627474982998870731185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3991084983321999247154123 5986627474982998870731185)
      ·
        refine ⟨4489970606237249153048389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5986627474982998870731185 4489970606237249153048389)
        ·
          refine ⟨841869488669484216196573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4489970606237249153048389 841869488669484216196573)
          ·
            refine ⟨315701058251056581073715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 841869488669484216196573 315701058251056581073715)
            ·
              refine ⟨473551587376584871610573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 315701058251056581073715 473551587376584871610573)
              ·
                refine ⟨177581845266219326853965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 473551587376584871610573 177581845266219326853965)
                ·
                  refine ⟨66593191974832247570237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 177581845266219326853965 66593191974832247570237)
                  ·
                    rfl

theorem cell21_291802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 3, 3].length) (baseStart_291802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_291802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_291802 prefixEnd_291802 := by exact prefixLift 291802
  have htrace : WordTrace (prefixWord ++ tailWord_291802) baseStart_291802 baseEnd_291802 := by
    simpa [prefixWord, tailWord_291802, baseEnd_291802] using wordTrace_append hprefix tailTrace_291802
  have hstable : (prefixWord ++ tailWord_291802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291802).length < 2 ^ (prefixWord ++ tailWord_291802).sum := by decide
  have hdescent : baseEnd_291802 < baseStart_291802 := by decide
  rcases family_descends (prefixWord ++ tailWord_291802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291830 : List Nat := [5, 1, 1, 1, 3, 2, 2, 6]
def baseStart_291830 : Nat := 118140960795 + 291830 * 2 ^ 59
def prefixEnd_291830 : Nat := 4983230072969 + 3 ^ 40 * 291830 * 2
def baseEnd_291830 : Nat := 22199860652103473701171

theorem tailTrace_291830 : CollatzResearch.WordTrace tailWord_291830 prefixEnd_291830 22199860652103473701171 := by
  unfold tailWord_291830
  simp only [CollatzResearch.WordTrace]
  refine ⟨665244658297326590068559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7095943021838150294064629 665244658297326590068559)
  ·
    refine ⟨997866987445989885102839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 665244658297326590068559 997866987445989885102839)
    ·
      refine ⟨1496800481168984827654259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 997866987445989885102839 1496800481168984827654259)
      ·
        refine ⟨2245200721753477241481389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1496800481168984827654259 2245200721753477241481389)
        ·
          refine ⟨841950270657553965555521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2245200721753477241481389 841950270657553965555521)
          ·
            refine ⟨631462702993165474166641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 841950270657553965555521 631462702993165474166641)
            ·
              refine ⟨473597027244874105624981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 631462702993165474166641 473597027244874105624981)
              ·
                refine ⟨22199860652103473701171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 473597027244874105624981 22199860652103473701171)
                ·
                  rfl

theorem cell21_291830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_291830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_291830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_291830 prefixEnd_291830 := by exact prefixLift 291830
  have htrace : WordTrace (prefixWord ++ tailWord_291830) baseStart_291830 baseEnd_291830 := by
    simpa [prefixWord, tailWord_291830, baseEnd_291830] using wordTrace_append hprefix tailTrace_291830
  have hstable : (prefixWord ++ tailWord_291830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291830).length < 2 ^ (prefixWord ++ tailWord_291830).sum := by decide
  have hdescent : baseEnd_291830 < baseStart_291830 := by decide
  rcases family_descends (prefixWord ++ tailWord_291830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291875 : List Nat := [1, 1, 1, 4, 3, 3, 2, 2, 4]
def baseStart_291875 : Nat := 118140960795 + 291875 * 2 ^ 59
def prefixEnd_291875 : Nat := 4983230072969 + 3 ^ 40 * 291875 * 2
def baseEnd_291875 : Nat := 66609851569400342853421

theorem tailTrace_291875 : CollatzResearch.WordTrace tailWord_291875 prefixEnd_291875 66609851569400342853421 := by
  unfold tailWord_291875
  simp only [CollatzResearch.WordTrace]
  refine ⟨10645555817594198126485079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7097037211729465417656719 10645555817594198126485079)
  ·
    refine ⟨15968333726391297189727619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10645555817594198126485079 15968333726391297189727619)
    ·
      refine ⟨23952500589586945784591429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15968333726391297189727619 23952500589586945784591429)
      ·
        refine ⟨4491093860547552334610893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23952500589586945784591429 4491093860547552334610893)
        ·
          refine ⟨1684160197705332125479085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4491093860547552334610893 1684160197705332125479085)
          ·
            refine ⟨631560074139499547054657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1684160197705332125479085 631560074139499547054657)
            ·
              refine ⟨473670055604624660290993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 631560074139499547054657 473670055604624660290993)
              ·
                refine ⟨355252541703468495218245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 473670055604624660290993 355252541703468495218245)
                ·
                  refine ⟨66609851569400342853421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 355252541703468495218245 66609851569400342853421)
                  ·
                    rfl

theorem cell21_291875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 4].length) (baseStart_291875 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_291875 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_291875 prefixEnd_291875 := by exact prefixLift 291875
  have htrace : WordTrace (prefixWord ++ tailWord_291875) baseStart_291875 baseEnd_291875 := by
    simpa [prefixWord, tailWord_291875, baseEnd_291875] using wordTrace_append hprefix tailTrace_291875
  have hstable : (prefixWord ++ tailWord_291875).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291875).length < 2 ^ (prefixWord ++ tailWord_291875).sum := by decide
  have hdescent : baseEnd_291875 < baseStart_291875 := by decide
  rcases family_descends (prefixWord ++ tailWord_291875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291892 : List Nat := [2, 5, 1, 2, 1, 1, 2, 3, 4]
def baseStart_291892 : Nat := 118140960795 + 291892 * 2 ^ 59
def prefixEnd_291892 : Nat := 4983230072969 + 3 ^ 40 * 291892 * 2
def baseEnd_291892 : Nat := 66613731201012091070053

theorem tailTrace_291892 : CollatzResearch.WordTrace tailWord_291892 prefixEnd_291892 66613731201012091070053 := by
  unfold tailWord_291892
  simp only [CollatzResearch.WordTrace]
  refine ⟨5323087929266305014926965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7097450572355073353235953 5323087929266305014926965)
  ·
    refine ⟨499039493368716095149403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5323087929266305014926965 499039493368716095149403)
    ·
      refine ⟨748559240053074142724105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 499039493368716095149403 748559240053074142724105)
      ·
        refine ⟨561419430039805607043079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 748559240053074142724105 561419430039805607043079)
        ·
          refine ⟨842129145059708410564619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 561419430039805607043079 842129145059708410564619)
          ·
            refine ⟨1263193717589562615846929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 842129145059708410564619 1263193717589562615846929)
            ·
              refine ⟨947395288192171961885197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1263193717589562615846929 947395288192171961885197)
              ·
                refine ⟨355273233072064485706949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 947395288192171961885197 355273233072064485706949)
                ·
                  refine ⟨66613731201012091070053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 355273233072064485706949 66613731201012091070053)
                  ·
                    rfl

theorem cell21_291892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_291892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_291892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_291892 prefixEnd_291892 := by exact prefixLift 291892
  have htrace : WordTrace (prefixWord ++ tailWord_291892) baseStart_291892 baseEnd_291892 := by
    simpa [prefixWord, tailWord_291892, baseEnd_291892] using wordTrace_append hprefix tailTrace_291892
  have hstable : (prefixWord ++ tailWord_291892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291892).length < 2 ^ (prefixWord ++ tailWord_291892).sum := by decide
  have hdescent : baseEnd_291892 < baseStart_291892 := by decide
  rcases family_descends (prefixWord ++ tailWord_291892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291926 : List Nat := [5, 2, 2, 1, 2, 2, 1, 2, 4]
def baseStart_291926 : Nat := 118140960795 + 291926 * 2 ^ 59
def prefixEnd_291926 : Nat := 4983230072969 + 3 ^ 40 * 291926 * 2
def baseEnd_291926 : Nat := 66621490464235587503317

theorem tailTrace_291926 : CollatzResearch.WordTrace tailWord_291926 prefixEnd_291926 66621490464235587503317 := by
  unfold tailWord_291926
  simp only [CollatzResearch.WordTrace]
  refine ⟨665463496275589614786977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7098277293606289224394421 665463496275589614786977)
  ·
    refine ⟨499097622206692211090233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 665463496275589614786977 499097622206692211090233)
    ·
      refine ⟨374323216655019158317675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 499097622206692211090233 374323216655019158317675)
      ·
        refine ⟨561484824982528737476513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374323216655019158317675 561484824982528737476513)
        ·
          refine ⟨421113618736896553107385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 561484824982528737476513 421113618736896553107385)
          ·
            refine ⟨315835214052672414830539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 421113618736896553107385 315835214052672414830539)
            ·
              refine ⟨473752821079008622245809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 315835214052672414830539 473752821079008622245809)
              ·
                refine ⟨355314615809256466684357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 473752821079008622245809 355314615809256466684357)
                ·
                  refine ⟨66621490464235587503317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 355314615809256466684357 66621490464235587503317)
                  ·
                    rfl

theorem cell21_291926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_291926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_291926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_291926 prefixEnd_291926 := by exact prefixLift 291926
  have htrace : WordTrace (prefixWord ++ tailWord_291926) baseStart_291926 baseEnd_291926 := by
    simpa [prefixWord, tailWord_291926, baseEnd_291926] using wordTrace_append hprefix tailTrace_291926
  have hstable : (prefixWord ++ tailWord_291926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291926).length < 2 ^ (prefixWord ++ tailWord_291926).sum := by decide
  have hdescent : baseEnd_291926 < baseStart_291926 := by decide
  rcases family_descends (prefixWord ++ tailWord_291926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291948 : List Nat := [2, 2, 1, 1, 3, 2, 2, 8]
def baseStart_291948 : Nat := 118140960795 + 291948 * 2 ^ 59
def prefixEnd_291948 : Nat := 4983230072969 + 3 ^ 40 * 291948 * 2
def baseEnd_291948 : Nat := 22208837054656146045535

theorem tailTrace_291948 : CollatzResearch.WordTrace tailWord_291948 prefixEnd_291948 22208837054656146045535 := by
  unfold tailWord_291948
  simp only [CollatzResearch.WordTrace]
  refine ⟨5324109173164865796946249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7098812230886487729261665 5324109173164865796946249)
  ·
    refine ⟨3993081879873649347709687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5324109173164865796946249 3993081879873649347709687)
    ·
      refine ⟨5989622819810474021564531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3993081879873649347709687 5989622819810474021564531)
      ·
        refine ⟨8984434229715711032346797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5989622819810474021564531 8984434229715711032346797)
        ·
          refine ⟨3369162836143391637130049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8984434229715711032346797 3369162836143391637130049)
          ·
            refine ⟨2526872127107543727847537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3369162836143391637130049 2526872127107543727847537)
            ·
              refine ⟨1895154095330657795885653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2526872127107543727847537 1895154095330657795885653)
              ·
                refine ⟨22208837054656146045535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1895154095330657795885653 22208837054656146045535)
                ·
                  rfl

theorem cell21_291948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 8].length) (baseStart_291948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_291948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_291948 prefixEnd_291948 := by exact prefixLift 291948
  have htrace : WordTrace (prefixWord ++ tailWord_291948) baseStart_291948 baseEnd_291948 := by
    simpa [prefixWord, tailWord_291948, baseEnd_291948] using wordTrace_append hprefix tailTrace_291948
  have hstable : (prefixWord ++ tailWord_291948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291948).length < 2 ^ (prefixWord ++ tailWord_291948).sum := by decide
  have hdescent : baseEnd_291948 < baseStart_291948 := by decide
  rcases family_descends (prefixWord ++ tailWord_291948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291951 : List Nat := [1, 1, 2, 1, 3, 3, 5, 1, 4]
def baseStart_291951 : Nat := 118140960795 + 291951 * 2 ^ 59
def prefixEnd_291951 : Nat := 4983230072969 + 3 ^ 40 * 291951 * 2
def baseEnd_291951 : Nat := 66627195804841099586599

theorem tailTrace_291951 : CollatzResearch.WordTrace tailWord_291951 prefixEnd_291951 66627195804841099586599 := by
  unfold tailWord_291951
  simp only [CollatzResearch.WordTrace]
  refine ⟨10648327765318863106251707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7098885176879242070834471 10648327765318863106251707)
  ·
    refine ⟨15972491647978294659377561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10648327765318863106251707 15972491647978294659377561)
    ·
      refine ⟨11979368735983720994533171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15972491647978294659377561 11979368735983720994533171)
      ·
        refine ⟨17969053103975581491799757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11979368735983720994533171 17969053103975581491799757)
        ·
          refine ⟨6738394913990843059424909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17969053103975581491799757 6738394913990843059424909)
          ·
            refine ⟨2526898092746566147284341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6738394913990843059424909 2526898092746566147284341)
            ·
              refine ⟨236896696194990576307907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2526898092746566147284341 236896696194990576307907)
              ·
                refine ⟨355345044292485864461861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 236896696194990576307907 355345044292485864461861)
                ·
                  refine ⟨66627195804841099586599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 355345044292485864461861 66627195804841099586599)
                  ·
                    rfl

theorem cell21_291951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 4].length) (baseStart_291951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_291951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_291951 prefixEnd_291951 := by exact prefixLift 291951
  have htrace : WordTrace (prefixWord ++ tailWord_291951) baseStart_291951 baseEnd_291951 := by
    simpa [prefixWord, tailWord_291951, baseEnd_291951] using wordTrace_append hprefix tailTrace_291951
  have hstable : (prefixWord ++ tailWord_291951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291951).length < 2 ^ (prefixWord ++ tailWord_291951).sum := by decide
  have hdescent : baseEnd_291951 < baseStart_291951 := by decide
  rcases family_descends (prefixWord ++ tailWord_291951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291996 : List Nat := [2, 2, 3, 2, 1, 2, 3, 1, 5]
def baseStart_291996 : Nat := 118140960795 + 291996 * 2 ^ 59
def prefixEnd_291996 : Nat := 4983230072969 + 3 ^ 40 * 291996 * 2
def baseEnd_291996 : Nat := 66637465417931021336507

theorem tailTrace_291996 : CollatzResearch.WordTrace tailWord_291996 prefixEnd_291996 66637465417931021336507 := by
  unfold tailWord_291996
  simp only [CollatzResearch.WordTrace]
  refine ⟨5324984525077917895819921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7099979366770557194426561 5324984525077917895819921)
  ·
    refine ⟨3993738393808438421864941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5324984525077917895819921 3993738393808438421864941)
    ·
      refine ⟨1497651897678164408199353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3993738393808438421864941 1497651897678164408199353)
      ·
        refine ⟨1123238923258623306149515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1497651897678164408199353 1123238923258623306149515)
        ·
          refine ⟨1684858384887934959224273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1123238923258623306149515 1684858384887934959224273)
          ·
            refine ⟨1263643788665951219418205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1684858384887934959224273 1263643788665951219418205)
            ·
              refine ⟨473866420749731707281827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1263643788665951219418205 473866420749731707281827)
              ·
                refine ⟨710799631124597560922741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 473866420749731707281827 710799631124597560922741)
                ·
                  refine ⟨66637465417931021336507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 710799631124597560922741 66637465417931021336507)
                  ·
                    rfl

theorem cell21_291996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 5].length) (baseStart_291996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_291996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_291996 prefixEnd_291996 := by exact prefixLift 291996
  have htrace : WordTrace (prefixWord ++ tailWord_291996) baseStart_291996 baseEnd_291996 := by
    simpa [prefixWord, tailWord_291996, baseEnd_291996] using wordTrace_append hprefix tailTrace_291996
  have hstable : (prefixWord ++ tailWord_291996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291996).length < 2 ^ (prefixWord ++ tailWord_291996).sum := by decide
  have hdescent : baseEnd_291996 < baseStart_291996 := by decide
  rcases family_descends (prefixWord ++ tailWord_291996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292002 : List Nat := [3, 3, 1, 3, 3, 1, 2, 1, 4]
def baseStart_292002 : Nat := 118140960795 + 292002 * 2 ^ 59
def prefixEnd_292002 : Nat := 4983230072969 + 3 ^ 40 * 292002 * 2
def baseEnd_292002 : Nat := 66638834699676344236495

theorem tailTrace_292002 : CollatzResearch.WordTrace tailWord_292002 prefixEnd_292002 66638834699676344236495 := by
  unfold tailWord_292002
  simp only [CollatzResearch.WordTrace]
  refine ⟨2662546972033524704089565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7100125258756065877572173 2662546972033524704089565)
  ·
    refine ⟨998455114512571764033587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2662546972033524704089565 998455114512571764033587)
    ·
      refine ⟨1497682671768857646050381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 998455114512571764033587 1497682671768857646050381)
      ·
        refine ⟨561631001913321617268893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1497682671768857646050381 561631001913321617268893)
        ·
          refine ⟨210611625717495606475835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 561631001913321617268893 210611625717495606475835)
          ·
            refine ⟨315917438576243409713753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210611625717495606475835 315917438576243409713753)
            ·
              refine ⟨236938078932182557285315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 315917438576243409713753 236938078932182557285315)
              ·
                refine ⟨355407118398273835927973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 236938078932182557285315 355407118398273835927973)
                ·
                  refine ⟨66638834699676344236495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 355407118398273835927973 66638834699676344236495)
                  ·
                    rfl

theorem cell21_292002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_292002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_292002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_292002 prefixEnd_292002 := by exact prefixLift 292002
  have htrace : WordTrace (prefixWord ++ tailWord_292002) baseStart_292002 baseEnd_292002 := by
    simpa [prefixWord, tailWord_292002, baseEnd_292002] using wordTrace_append hprefix tailTrace_292002
  have hstable : (prefixWord ++ tailWord_292002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292002).length < 2 ^ (prefixWord ++ tailWord_292002).sum := by decide
  have hdescent : baseEnd_292002 < baseStart_292002 := by decide
  rcases family_descends (prefixWord ++ tailWord_292002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292086 : List Nat := [5, 1, 1, 1, 1, 1, 1, 4, 6]
def baseStart_292086 : Nat := 118140960795 + 292086 * 2 ^ 59
def prefixEnd_292086 : Nat := 4983230072969 + 3 ^ 40 * 292086 * 2
def baseEnd_292086 : Nat := 66658004644110864836323

theorem tailTrace_292086 : CollatzResearch.WordTrace tailWord_292086 prefixEnd_292086 66658004644110864836323 := by
  unfold tailWord_292086
  simp only [CollatzResearch.WordTrace]
  refine ⟨665828226239361322651007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7102167746553187441610741 665828226239361322651007)
  ·
    refine ⟨998742339359041983976511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 665828226239361322651007 998742339359041983976511)
    ·
      refine ⟨1498113509038562975964767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 998742339359041983976511 1498113509038562975964767)
      ·
        refine ⟨2247170263557844463947151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1498113509038562975964767 2247170263557844463947151)
        ·
          refine ⟨3370755395336766695920727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2247170263557844463947151 3370755395336766695920727)
          ·
            refine ⟨5056133093005150043881091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3370755395336766695920727 5056133093005150043881091)
            ·
              refine ⟨7584199639507725065821637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5056133093005150043881091 7584199639507725065821637)
              ·
                refine ⟨1422037432407698449841557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7584199639507725065821637 1422037432407698449841557)
                ·
                  refine ⟨66658004644110864836323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1422037432407698449841557 66658004644110864836323)
                  ·
                    rfl

theorem cell21_292086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_292086 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_292086 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_292086 prefixEnd_292086 := by exact prefixLift 292086
  have htrace : WordTrace (prefixWord ++ tailWord_292086) baseStart_292086 baseEnd_292086 := by
    simpa [prefixWord, tailWord_292086, baseEnd_292086] using wordTrace_append hprefix tailTrace_292086
  have hstable : (prefixWord ++ tailWord_292086).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292086).length < 2 ^ (prefixWord ++ tailWord_292086).sum := by decide
  have hdescent : baseEnd_292086 < baseStart_292086 := by decide
  rcases family_descends (prefixWord ++ tailWord_292086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292131 : List Nat := [1, 1, 1, 4, 2, 3, 2, 2, 5]
def baseStart_292131 : Nat := 118140960795 + 292131 * 2 ^ 59
def prefixEnd_292131 : Nat := 4983230072969 + 3 ^ 40 * 292131 * 2
def baseEnd_292131 : Nat := 66668274257200786586231

theorem tailTrace_292131 : CollatzResearch.WordTrace tailWord_292131 prefixEnd_292131 66668274257200786586231 := by
  unfold tailWord_292131
  simp only [CollatzResearch.WordTrace]
  refine ⟨10654892904666753847804247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7103261936444502565202831 10654892904666753847804247)
  ·
    refine ⟨15982339357000130771706371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10654892904666753847804247 15982339357000130771706371)
    ·
      refine ⟨23973509035500196157559557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15982339357000130771706371 23973509035500196157559557)
      ·
        refine ⟨4495032944156286779542417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23973509035500196157559557 4495032944156286779542417)
        ·
          refine ⟨3371274708117215084656813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4495032944156286779542417 3371274708117215084656813)
          ·
            refine ⟨1264228015543955656746305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3371274708117215084656813 1264228015543955656746305)
            ·
              refine ⟨948171011657966742559729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1264228015543955656746305 948171011657966742559729)
              ·
                refine ⟨711128258743475056919797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 948171011657966742559729 711128258743475056919797)
                ·
                  refine ⟨66668274257200786586231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 711128258743475056919797 66668274257200786586231)
                  ·
                    rfl

theorem cell21_292131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 5].length) (baseStart_292131 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_292131 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_292131 prefixEnd_292131 := by exact prefixLift 292131
  have htrace : WordTrace (prefixWord ++ tailWord_292131) baseStart_292131 baseEnd_292131 := by
    simpa [prefixWord, tailWord_292131, baseEnd_292131] using wordTrace_append hprefix tailTrace_292131
  have hstable : (prefixWord ++ tailWord_292131).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292131).length < 2 ^ (prefixWord ++ tailWord_292131).sum := by decide
  have hdescent : baseEnd_292131 < baseStart_292131 := by decide
  rcases family_descends (prefixWord ++ tailWord_292131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292176 : List Nat := [2, 1, 1, 1, 1, 5, 4, 6]
def baseStart_292176 : Nat := 118140960795 + 292176 * 2 ^ 59
def prefixEnd_292176 : Nat := 4983230072969 + 3 ^ 40 * 292176 * 2
def baseEnd_292176 : Nat := 22226181290096902778713

theorem tailTrace_292176 : CollatzResearch.WordTrace tailWord_292176 prefixEnd_292176 22226181290096902778713 := by
  unfold tailWord_292176
  simp only [CollatzResearch.WordTrace]
  refine ⟨5328267094751863266596191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7104356126335817688794921 5328267094751863266596191)
  ·
    refine ⟨7992400642127794899894287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5328267094751863266596191 7992400642127794899894287)
    ·
      refine ⟨11988600963191692349841431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7992400642127794899894287 11988600963191692349841431)
      ·
        refine ⟨17982901444787538524762147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11988600963191692349841431 17982901444787538524762147)
        ·
          refine ⟨26974352167181307787143221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17982901444787538524762147 26974352167181307787143221)
          ·
            refine ⟨2528845515673247605044677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26974352167181307787143221 2528845515673247605044677)
            ·
              refine ⟨474158534188733925945877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2528845515673247605044677 474158534188733925945877)
              ·
                refine ⟨22226181290096902778713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 474158534188733925945877 22226181290096902778713)
                ·
                  rfl

theorem cell21_292176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 6].length) (baseStart_292176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_292176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_292176 prefixEnd_292176 := by exact prefixLift 292176
  have htrace : WordTrace (prefixWord ++ tailWord_292176) baseStart_292176 baseEnd_292176 := by
    simpa [prefixWord, tailWord_292176, baseEnd_292176] using wordTrace_append hprefix tailTrace_292176
  have hstable : (prefixWord ++ tailWord_292176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292176).length < 2 ^ (prefixWord ++ tailWord_292176).sum := by decide
  have hdescent : baseEnd_292176 < baseStart_292176 := by decide
  rcases family_descends (prefixWord ++ tailWord_292176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292269 : List Nat := [1, 5, 2, 2, 1, 2, 8]
def baseStart_292269 : Nat := 118140960795 + 292269 * 2 ^ 59
def prefixEnd_292269 : Nat := 4983230072969 + 3 ^ 40 * 292269 * 2
def baseEnd_292269 : Nat := 7411085304149245920661

theorem tailTrace_292269 : CollatzResearch.WordTrace tailWord_292269 prefixEnd_292269 7411085304149245920661 := by
  unfold tailWord_292269
  simp only [CollatzResearch.WordTrace]
  refine ⟨10659926178166803416327861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7106617452111202277551907 10659926178166803416327861)
  ·
    refine ⟨999368079203137820280737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10659926178166803416327861 999368079203137820280737)
    ·
      refine ⟨749526059402353365210553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 999368079203137820280737 749526059402353365210553)
      ·
        refine ⟨562144544551765023907915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 749526059402353365210553 562144544551765023907915)
        ·
          refine ⟨843216816827647535861873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 562144544551765023907915 843216816827647535861873)
          ·
            refine ⟨632412612620735651896405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 843216816827647535861873 632412612620735651896405)
            ·
              refine ⟨7411085304149245920661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 632412612620735651896405 7411085304149245920661)
              ·
                rfl

theorem cell21_292269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 8].length) (baseStart_292269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_292269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_292269 prefixEnd_292269 := by exact prefixLift 292269
  have htrace : WordTrace (prefixWord ++ tailWord_292269) baseStart_292269 baseEnd_292269 := by
    simpa [prefixWord, tailWord_292269, baseEnd_292269] using wordTrace_append hprefix tailTrace_292269
  have hstable : (prefixWord ++ tailWord_292269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292269).length < 2 ^ (prefixWord ++ tailWord_292269).sum := by decide
  have hdescent : baseEnd_292269 < baseStart_292269 := by decide
  rcases family_descends (prefixWord ++ tailWord_292269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292317 : List Nat := [1, 4, 3, 1, 1, 2, 3, 3, 3]
def baseStart_292317 : Nat := 118140960795 + 292317 * 2 ^ 59
def prefixEnd_292317 : Nat := 4983230072969 + 3 ^ 40 * 292317 * 2
def baseEnd_292317 : Nat := 66710721991305796485851

theorem tailTrace_292317 : CollatzResearch.WordTrace tailWord_292317 prefixEnd_292317 66710721991305796485851 := by
  unfold tailWord_292317
  simp only [CollatzResearch.WordTrace]
  refine ⟨10661676881992907614075205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7107784587995271742716803 10661676881992907614075205)
  ·
    refine ⟨1999064415373670177639101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10661676881992907614075205 1999064415373670177639101)
    ·
      refine ⟨749649155765126316614663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1999064415373670177639101 749649155765126316614663)
      ·
        refine ⟨1124473733647689474921995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 749649155765126316614663 1124473733647689474921995)
        ·
          refine ⟨1686710600471534212382993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1124473733647689474921995 1686710600471534212382993)
          ·
            refine ⟨1265032950353650659287245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1686710600471534212382993 1265032950353650659287245)
            ·
              refine ⟨474387356382618997232717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1265032950353650659287245 474387356382618997232717)
              ·
                refine ⟨177895258643482123962269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 474387356382618997232717 177895258643482123962269)
                ·
                  refine ⟨66710721991305796485851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 177895258643482123962269 66710721991305796485851)
                  ·
                    rfl

theorem cell21_292317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 3, 3].length) (baseStart_292317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_292317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_292317 prefixEnd_292317 := by exact prefixLift 292317
  have htrace : WordTrace (prefixWord ++ tailWord_292317) baseStart_292317 baseEnd_292317 := by
    simpa [prefixWord, tailWord_292317, baseEnd_292317] using wordTrace_append hprefix tailTrace_292317
  have hstable : (prefixWord ++ tailWord_292317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292317).length < 2 ^ (prefixWord ++ tailWord_292317).sum := by decide
  have hdescent : baseEnd_292317 < baseStart_292317 := by decide
  rcases family_descends (prefixWord ++ tailWord_292317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292382 : List Nat := [4, 3, 3, 1, 1, 1, 2, 2, 4]
def baseStart_292382 : Nat := 118140960795 + 292382 * 2 ^ 59
def prefixEnd_292382 : Nat := 4983230072969 + 3 ^ 40 * 292382 * 2
def baseEnd_292382 : Nat := 66725555876880127902385

theorem tailTrace_292382 : CollatzResearch.WordTrace tailWord_292382 prefixEnd_292382 66725555876880127902385 := by
  unfold tailWord_292382
  simp only [CollatzResearch.WordTrace]
  refine ⟨1333005953344677964398925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7109365084504949143460933 1333005953344677964398925)
  ·
    refine ⟨499877232504254236649597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1333005953344677964398925 499877232504254236649597)
    ·
      refine ⟨187453962189095338743599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 499877232504254236649597 187453962189095338743599)
      ·
        refine ⟨281180943283643008115399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187453962189095338743599 281180943283643008115399)
        ·
          refine ⟨421771414925464512173099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281180943283643008115399 421771414925464512173099)
          ·
            refine ⟨632657122388196768259649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 421771414925464512173099 632657122388196768259649)
            ·
              refine ⟨474492841791147576194737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 632657122388196768259649 474492841791147576194737)
              ·
                refine ⟨355869631343360682146053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 474492841791147576194737 355869631343360682146053)
                ·
                  refine ⟨66725555876880127902385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 355869631343360682146053 66725555876880127902385)
                  ·
                    rfl

theorem cell21_292382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_292382 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_292382 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_292382 prefixEnd_292382 := by exact prefixLift 292382
  have htrace : WordTrace (prefixWord ++ tailWord_292382) baseStart_292382 baseEnd_292382 := by
    simpa [prefixWord, tailWord_292382, baseEnd_292382] using wordTrace_append hprefix tailTrace_292382
  have hstable : (prefixWord ++ tailWord_292382).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292382).length < 2 ^ (prefixWord ++ tailWord_292382).sum := by decide
  have hdescent : baseEnd_292382 < baseStart_292382 := by decide
  rcases family_descends (prefixWord ++ tailWord_292382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292387 : List Nat := [1, 1, 1, 4, 14]
def baseStart_292387 : Nat := 118140960795 + 292387 * 2 ^ 59
def prefixEnd_292387 : Nat := 4983230072969 + 3 ^ 40 * 292387 * 2
def baseEnd_292387 : Nat := 823786382037052226161

theorem tailTrace_292387 : CollatzResearch.WordTrace tailWord_292387 prefixEnd_292387 823786382037052226161 := by
  unfold tailWord_292387
  simp only [CollatzResearch.WordTrace]
  refine ⟨10664229991739309569123415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7109486661159539712748943 10664229991739309569123415)
  ·
    refine ⟨15996344987608964353685123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10664229991739309569123415 15996344987608964353685123)
    ·
      refine ⟨23994517481413446530527685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15996344987608964353685123 23994517481413446530527685)
      ·
        refine ⟨4498972027765021224473941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23994517481413446530527685 4498972027765021224473941)
        ·
          refine ⟨823786382037052226161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 4498972027765021224473941 823786382037052226161)
          ·
            rfl

theorem cell21_292387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 14].length) (baseStart_292387 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_292387 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_292387 prefixEnd_292387 := by exact prefixLift 292387
  have htrace : WordTrace (prefixWord ++ tailWord_292387) baseStart_292387 baseEnd_292387 := by
    simpa [prefixWord, tailWord_292387, baseEnd_292387] using wordTrace_append hprefix tailTrace_292387
  have hstable : (prefixWord ++ tailWord_292387).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292387).length < 2 ^ (prefixWord ++ tailWord_292387).sum := by decide
  have hdescent : baseEnd_292387 < baseStart_292387 := by decide
  rcases family_descends (prefixWord ++ tailWord_292387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292449 : List Nat := [1, 2, 3, 1, 1, 3, 3, 1, 6]
def baseStart_292449 : Nat := 118140960795 + 292449 * 2 ^ 59
def prefixEnd_292449 : Nat := 4983230072969 + 3 ^ 40 * 292449 * 2
def baseEnd_292449 : Nat := 66740846189702900285581

theorem tailTrace_292449 : CollatzResearch.WordTrace tailWord_292449 prefixEnd_292449 66740846189702900285581 := by
  unfold tailWord_292449
  simp only [CollatzResearch.WordTrace]
  refine ⟨10666491317514694157880401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7110994211676462771920267 10666491317514694157880401)
  ·
    refine ⟨7999868488136020618410301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10666491317514694157880401 7999868488136020618410301)
    ·
      refine ⟨2999950683051007731903863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7999868488136020618410301 2999950683051007731903863)
      ·
        refine ⟨4499926024576511597855795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2999950683051007731903863 4499926024576511597855795)
        ·
          refine ⟨6749889036864767396783693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4499926024576511597855795 6749889036864767396783693)
          ·
            refine ⟨2531208388824287773793885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6749889036864767396783693 2531208388824287773793885)
            ·
              refine ⟨949203145809107915172707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2531208388824287773793885 949203145809107915172707)
              ·
                refine ⟨1423804718713661872759061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 949203145809107915172707 1423804718713661872759061)
                ·
                  refine ⟨66740846189702900285581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1423804718713661872759061 66740846189702900285581)
                  ·
                    rfl

theorem cell21_292449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 6].length) (baseStart_292449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_292449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_292449 prefixEnd_292449 := by exact prefixLift 292449
  have htrace : WordTrace (prefixWord ++ tailWord_292449) baseStart_292449 baseEnd_292449 := by
    simpa [prefixWord, tailWord_292449, baseEnd_292449] using wordTrace_append hprefix tailTrace_292449
  have hstable : (prefixWord ++ tailWord_292449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292449).length < 2 ^ (prefixWord ++ tailWord_292449).sum := by decide
  have hdescent : baseEnd_292449 < baseStart_292449 := by decide
  rcases family_descends (prefixWord ++ tailWord_292449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292452 : List Nat := [2, 3, 1, 1, 2, 3, 2, 4, 3]
def baseStart_292452 : Nat := 118140960795 + 292452 * 2 ^ 59
def prefixEnd_292452 : Nat := 4983230072969 + 3 ^ 40 * 292452 * 2
def baseEnd_292452 : Nat := 66741530830575561735575

theorem tailTrace_292452 : CollatzResearch.WordTrace tailWord_292452 prefixEnd_292452 66741530830575561735575 := by
  unfold tailWord_292452
  simp only [CollatzResearch.WordTrace]
  refine ⟨5333300368251912835119805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7111067157669217113493073 5333300368251912835119805)
  ·
    refine ⟨1999987638094467313169927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5333300368251912835119805 1999987638094467313169927)
    ·
      refine ⟨2999981457141700969754891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1999987638094467313169927 2999981457141700969754891)
      ·
        refine ⟨4499972185712551454632337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2999981457141700969754891 4499972185712551454632337)
        ·
          refine ⟨3374979139284413590974253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4499972185712551454632337 3374979139284413590974253)
          ·
            refine ⟨1265617177231655096615345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3374979139284413590974253 1265617177231655096615345)
            ·
              refine ⟨949212882923741322461509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1265617177231655096615345 949212882923741322461509)
              ·
                refine ⟨177977415548201497961533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 949212882923741322461509 177977415548201497961533)
                ·
                  refine ⟨66741530830575561735575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 177977415548201497961533 66741530830575561735575)
                  ·
                    rfl

theorem cell21_292452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 4, 3].length) (baseStart_292452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_292452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_292452 prefixEnd_292452 := by exact prefixLift 292452
  have htrace : WordTrace (prefixWord ++ tailWord_292452) baseStart_292452 baseEnd_292452 := by
    simpa [prefixWord, tailWord_292452, baseEnd_292452] using wordTrace_append hprefix tailTrace_292452
  have hstable : (prefixWord ++ tailWord_292452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292452).length < 2 ^ (prefixWord ++ tailWord_292452).sum := by decide
  have hdescent : baseEnd_292452 < baseStart_292452 := by decide
  rcases family_descends (prefixWord ++ tailWord_292452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292463 : List Nat := [1, 1, 2, 1, 3, 2, 1, 10]
def baseStart_292463 : Nat := 118140960795 + 292463 * 2 ^ 59
def prefixEnd_292463 : Nat := 4983230072969 + 3 ^ 40 * 292463 * 2
def baseEnd_292463 : Nat := 22248013726813995684073

theorem tailTrace_292463 : CollatzResearch.WordTrace tailWord_292463 prefixEnd_292463 22248013726813995684073 := by
  unfold tailWord_292463
  simp only [CollatzResearch.WordTrace]
  refine ⟨10667001939463974548890043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7111334626309316365926695 10667001939463974548890043)
  ·
    refine ⟨16000502909195961823335065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10667001939463974548890043 16000502909195961823335065)
    ·
      refine ⟨12000377181896971367501299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16000502909195961823335065 12000377181896971367501299)
      ·
        refine ⟨18000565772845457051251949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12000377181896971367501299 18000565772845457051251949)
        ·
          refine ⟨6750212164817046394219481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18000565772845457051251949 6750212164817046394219481)
          ·
            refine ⟨5062659123612784795664611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6750212164817046394219481 5062659123612784795664611)
            ·
              refine ⟨7593988685419177193496917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5062659123612784795664611 7593988685419177193496917)
              ·
                refine ⟨22248013726813995684073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 7593988685419177193496917 22248013726813995684073)
                ·
                  rfl

theorem cell21_292463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 10].length) (baseStart_292463 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_292463 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_292463 prefixEnd_292463 := by exact prefixLift 292463
  have htrace : WordTrace (prefixWord ++ tailWord_292463) baseStart_292463 baseEnd_292463 := by
    simpa [prefixWord, tailWord_292463, baseEnd_292463] using wordTrace_append hprefix tailTrace_292463
  have hstable : (prefixWord ++ tailWord_292463).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292463).length < 2 ^ (prefixWord ++ tailWord_292463).sum := by decide
  have hdescent : baseEnd_292463 < baseStart_292463 := by decide
  rcases family_descends (prefixWord ++ tailWord_292463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292514 : List Nat := [3, 3, 1, 4, 1, 1, 2, 6]
def baseStart_292514 : Nat := 118140960795 + 292514 * 2 ^ 59
def prefixEnd_292514 : Nat := 4983230072969 + 3 ^ 40 * 292514 * 2
def baseEnd_292514 : Nat := 22251893358425743900705

theorem tailTrace_292514 : CollatzResearch.WordTrace tailWord_292514 prefixEnd_292514 22251893358425743900705 := by
  unfold tailWord_292514
  simp only [CollatzResearch.WordTrace]
  refine ⟨2667215515569802564749149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7112574708186140172664397 2667215515569802564749149)
  ·
    refine ⟨1000205818338675961780931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2667215515569802564749149 1000205818338675961780931)
    ·
      refine ⟨1500308727508013942671397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1000205818338675961780931 1500308727508013942671397)
      ·
        refine ⟨281307886407752614250887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1500308727508013942671397 281307886407752614250887)
        ·
          refine ⟨421961829611628921376331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281307886407752614250887 421961829611628921376331)
          ·
            refine ⟨632942744417443382064497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 421961829611628921376331 632942744417443382064497)
            ·
              refine ⟨474707058313082536548373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 632942744417443382064497 474707058313082536548373)
              ·
                refine ⟨22251893358425743900705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 474707058313082536548373 22251893358425743900705)
                ·
                  rfl

theorem cell21_292514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 6].length) (baseStart_292514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_292514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_292514 prefixEnd_292514 := by exact prefixLift 292514
  have htrace : WordTrace (prefixWord ++ tailWord_292514) baseStart_292514 baseEnd_292514 := by
    simpa [prefixWord, tailWord_292514, baseEnd_292514] using wordTrace_append hprefix tailTrace_292514
  have hstable : (prefixWord ++ tailWord_292514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292514).length < 2 ^ (prefixWord ++ tailWord_292514).sum := by decide
  have hdescent : baseEnd_292514 < baseStart_292514 := by decide
  rcases family_descends (prefixWord ++ tailWord_292514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292556 : List Nat := [2, 2, 1, 5, 2, 9]
def baseStart_292556 : Nat := 118140960795 + 292556 * 2 ^ 59
def prefixEnd_292556 : Nat := 4983230072969 + 3 ^ 40 * 292556 * 2
def baseEnd_292556 : Nat := 2472787594351647851927

theorem tailTrace_292556 : CollatzResearch.WordTrace tailWord_292556 prefixEnd_292556 2472787594351647851927 := by
  unfold tailWord_292556
  simp only [CollatzResearch.WordTrace]
  refine ⟨5335196964063525716012761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7113595952084700954683681 5335196964063525716012761)
  ·
    refine ⟨4001397723047644287009571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5335196964063525716012761 4001397723047644287009571)
    ·
      refine ⟨6002096584571466430514357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4001397723047644287009571 6002096584571466430514357)
      ·
        refine ⟨562696554803574977860721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6002096584571466430514357 562696554803574977860721)
        ·
          refine ⟨422022416102681233395541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 562696554803574977860721 422022416102681233395541)
          ·
            refine ⟨2472787594351647851927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 422022416102681233395541 2472787594351647851927)
            ·
              rfl

theorem cell21_292556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 9].length) (baseStart_292556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_292556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_292556 prefixEnd_292556 := by exact prefixLift 292556
  have htrace : WordTrace (prefixWord ++ tailWord_292556) baseStart_292556 baseEnd_292556 := by
    simpa [prefixWord, tailWord_292556, baseEnd_292556] using wordTrace_append hprefix tailTrace_292556
  have hstable : (prefixWord ++ tailWord_292556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292556).length < 2 ^ (prefixWord ++ tailWord_292556).sum := by decide
  have hdescent : baseEnd_292556 < baseStart_292556 := by decide
  rcases family_descends (prefixWord ++ tailWord_292556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292562 : List Nat := [3, 2, 2, 2, 2, 3, 2, 2, 3]
def baseStart_292562 : Nat := 118140960795 + 292562 * 2 ^ 59
def prefixEnd_292562 : Nat := 4983230072969 + 3 ^ 40 * 292562 * 2
def baseEnd_292562 : Nat := 66766634329239814902017

theorem tailTrace_292562 : CollatzResearch.WordTrace tailWord_292562 prefixEnd_292562 66766634329239814902017 := by
  unfold tailWord_292562
  simp only [CollatzResearch.WordTrace]
  refine ⟨2667653191526328614185985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7113741844070209637829293 2667653191526328614185985)
  ·
    refine ⟨2000739893644746460639489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2667653191526328614185985 2000739893644746460639489)
    ·
      refine ⟨1500554920233559845479617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2000739893644746460639489 1500554920233559845479617)
      ·
        refine ⟨1125416190175169884109713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1500554920233559845479617 1125416190175169884109713)
        ·
          refine ⟨844062142631377413082285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1125416190175169884109713 844062142631377413082285)
          ·
            refine ⟨316523303486766529905857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 844062142631377413082285 316523303486766529905857)
            ·
              refine ⟨237392477615074897429393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 316523303486766529905857 237392477615074897429393)
              ·
                refine ⟨178044358211306173072045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 237392477615074897429393 178044358211306173072045)
                ·
                  refine ⟨66766634329239814902017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 178044358211306173072045 66766634329239814902017)
                  ·
                    rfl

theorem cell21_292562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 2, 3].length) (baseStart_292562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_292562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_292562 prefixEnd_292562 := by exact prefixLift 292562
  have htrace : WordTrace (prefixWord ++ tailWord_292562) baseStart_292562 baseEnd_292562 := by
    simpa [prefixWord, tailWord_292562, baseEnd_292562] using wordTrace_append hprefix tailTrace_292562
  have hstable : (prefixWord ++ tailWord_292562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292562).length < 2 ^ (prefixWord ++ tailWord_292562).sum := by decide
  have hdescent : baseEnd_292562 < baseStart_292562 := by decide
  rcases family_descends (prefixWord ++ tailWord_292562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292604 : List Nat := [2, 2, 2, 1, 3, 1, 4, 3, 3]
def baseStart_292604 : Nat := 118140960795 + 292604 * 2 ^ 59
def prefixEnd_292604 : Nat := 4983230072969 + 3 ^ 40 * 292604 * 2
def baseEnd_292604 : Nat := 66776219301457075201931

theorem tailTrace_292604 : CollatzResearch.WordTrace tailWord_292604 prefixEnd_292604 66776219301457075201931 := by
  unfold tailWord_292604
  simp only [CollatzResearch.WordTrace]
  refine ⟨5336072315976577814886433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7114763087968770419848577 5336072315976577814886433)
  ·
    refine ⟨4002054236982433361164825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5336072315976577814886433 4002054236982433361164825)
    ·
      refine ⟨3001540677736825020873619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4002054236982433361164825 3001540677736825020873619)
      ·
        refine ⟨4502311016605237531310429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3001540677736825020873619 4502311016605237531310429)
        ·
          refine ⟨1688366631226964074241411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4502311016605237531310429 1688366631226964074241411)
          ·
            refine ⟨2532549946840446111362117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1688366631226964074241411 2532549946840446111362117)
            ·
              refine ⟨474853115032583645880397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2532549946840446111362117 474853115032583645880397)
              ·
                refine ⟨178069918137218867205149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 474853115032583645880397 178069918137218867205149)
                ·
                  refine ⟨66776219301457075201931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 178069918137218867205149 66776219301457075201931)
                  ·
                    rfl

theorem cell21_292604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 3, 3].length) (baseStart_292604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_292604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_292604 prefixEnd_292604 := by exact prefixLift 292604
  have htrace : WordTrace (prefixWord ++ tailWord_292604) baseStart_292604 baseEnd_292604 := by
    simpa [prefixWord, tailWord_292604, baseEnd_292604] using wordTrace_append hprefix tailTrace_292604
  have hstable : (prefixWord ++ tailWord_292604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292604).length < 2 ^ (prefixWord ++ tailWord_292604).sum := by decide
  have hdescent : baseEnd_292604 < baseStart_292604 := by decide
  rcases family_descends (prefixWord ++ tailWord_292604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292618 : List Nat := [3, 1, 2, 2, 1, 3, 3, 2, 4]
def baseStart_292618 : Nat := 118140960795 + 292618 * 2 ^ 59
def prefixEnd_292618 : Nat := 4983230072969 + 3 ^ 40 * 292618 * 2
def baseEnd_292618 : Nat := 66779414292196161968569

theorem tailTrace_292618 : CollatzResearch.WordTrace tailWord_292618 prefixEnd_292618 66779414292196161968569 := by
  unfold tailWord_292618
  simp only [CollatzResearch.WordTrace]
  refine ⟨2668163813475609005195627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7115103502601624013855005 2668163813475609005195627)
  ·
    refine ⟨4002245720213413507793441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2668163813475609005195627 4002245720213413507793441)
    ·
      refine ⟨3001684290160060130845081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4002245720213413507793441 3001684290160060130845081)
      ·
        refine ⟨2251263217620045098133811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3001684290160060130845081 2251263217620045098133811)
        ·
          refine ⟨3376894826430067647200717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2251263217620045098133811 3376894826430067647200717)
          ·
            refine ⟨1266335559911275367700269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3376894826430067647200717 1266335559911275367700269)
            ·
              refine ⟨474875834966728262887601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1266335559911275367700269 474875834966728262887601)
              ·
                refine ⟨356156876225046197165701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 474875834966728262887601 356156876225046197165701)
                ·
                  refine ⟨66779414292196161968569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 356156876225046197165701 66779414292196161968569)
                  ·
                    rfl

theorem cell21_292618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 4].length) (baseStart_292618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_292618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_292618 prefixEnd_292618 := by exact prefixLift 292618
  have htrace : WordTrace (prefixWord ++ tailWord_292618) baseStart_292618 baseEnd_292618 := by
    simpa [prefixWord, tailWord_292618, baseEnd_292618] using wordTrace_append hprefix tailTrace_292618
  have hstable : (prefixWord ++ tailWord_292618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292618).length < 2 ^ (prefixWord ++ tailWord_292618).sum := by decide
  have hdescent : baseEnd_292618 < baseStart_292618 := by decide
  rcases family_descends (prefixWord ++ tailWord_292618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292663 : List Nat := [1, 1, 3, 1, 2, 1, 2, 7, 3]
def baseStart_292663 : Nat := 118140960795 + 292663 * 2 ^ 59
def prefixEnd_292663 : Nat := 4983230072969 + 3 ^ 40 * 292663 * 2
def baseEnd_292663 : Nat := 66789683905286083718477

theorem tailTrace_292663 : CollatzResearch.WordTrace tailWord_292663 prefixEnd_292663 66789683905286083718477 := by
  unfold tailWord_292663
  simp only [CollatzResearch.WordTrace]
  refine ⟨10674296538739408706170643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7116197692492939137447095 10674296538739408706170643)
  ·
    refine ⟨16011444808109113059255965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10674296538739408706170643 16011444808109113059255965)
    ·
      refine ⟨6004291803040917397220987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16011444808109113059255965 6004291803040917397220987)
      ·
        refine ⟨9006437704561376095831481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6004291803040917397220987 9006437704561376095831481)
        ·
          refine ⟨6754828278421032071873611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9006437704561376095831481 6754828278421032071873611)
          ·
            refine ⟨10132242417631548107810417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6754828278421032071873611 10132242417631548107810417)
            ·
              refine ⟨7599181813223661080857813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10132242417631548107810417 7599181813223661080857813)
              ·
                refine ⟨178105823747429556582605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 7599181813223661080857813 178105823747429556582605)
                ·
                  refine ⟨66789683905286083718477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 178105823747429556582605 66789683905286083718477)
                  ·
                    rfl

theorem cell21_292663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 7, 3].length) (baseStart_292663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_292663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_292663 prefixEnd_292663 := by exact prefixLift 292663
  have htrace : WordTrace (prefixWord ++ tailWord_292663) baseStart_292663 baseEnd_292663 := by
    simpa [prefixWord, tailWord_292663, baseEnd_292663] using wordTrace_append hprefix tailTrace_292663
  have hstable : (prefixWord ++ tailWord_292663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292663).length < 2 ^ (prefixWord ++ tailWord_292663).sum := by decide
  have hdescent : baseEnd_292663 < baseStart_292663 := by decide
  rcases family_descends (prefixWord ++ tailWord_292663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292677 : List Nat := [1, 3, 1, 1, 1, 2, 4, 4, 4]
def baseStart_292677 : Nat := 118140960795 + 292677 * 2 ^ 59
def prefixEnd_292677 : Nat := 4983230072969 + 3 ^ 40 * 292677 * 2
def baseEnd_292677 : Nat := 66792878896025170485115

theorem tailTrace_292677 : CollatzResearch.WordTrace tailWord_292677 prefixEnd_292677 66792878896025170485115 := by
  unfold tailWord_292677
  simp only [CollatzResearch.WordTrace]
  refine ⟨10674807160688689097180285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7116538107125792731453523 10674807160688689097180285)
  ·
    refine ⟨4003052685258258411442607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10674807160688689097180285 4003052685258258411442607)
    ·
      refine ⟨6004579027887387617163911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4003052685258258411442607 6004579027887387617163911)
      ·
        refine ⟨9006868541831081425745867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6004579027887387617163911 9006868541831081425745867)
        ·
          refine ⟨13510302812746622138618801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9006868541831081425745867 13510302812746622138618801)
          ·
            refine ⟨10132727109559966603964101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13510302812746622138618801 10132727109559966603964101)
            ·
              refine ⟨1899886333042493738243269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10132727109559966603964101 1899886333042493738243269)
              ·
                refine ⟨356228687445467575920613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1899886333042493738243269 356228687445467575920613)
                ·
                  refine ⟨66792878896025170485115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 356228687445467575920613 66792878896025170485115)
                  ·
                    rfl

theorem cell21_292677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 4].length) (baseStart_292677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_292677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_292677 prefixEnd_292677 := by exact prefixLift 292677
  have htrace : WordTrace (prefixWord ++ tailWord_292677) baseStart_292677 baseEnd_292677 := by
    simpa [prefixWord, tailWord_292677, baseEnd_292677] using wordTrace_append hprefix tailTrace_292677
  have hstable : (prefixWord ++ tailWord_292677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292677).length < 2 ^ (prefixWord ++ tailWord_292677).sum := by decide
  have hdescent : baseEnd_292677 < baseStart_292677 := by decide
  rcases family_descends (prefixWord ++ tailWord_292677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292753 : List Nat := [1, 2, 2, 1, 1, 1, 6, 3, 4]
def baseStart_292753 : Nat := 118140960795 + 292753 * 2 ^ 59
def prefixEnd_292753 : Nat := 4983230072969 + 3 ^ 40 * 292753 * 2
def baseEnd_292753 : Nat := 66810223131465927218293

theorem tailTrace_292753 : CollatzResearch.WordTrace tailWord_292753 prefixEnd_292753 66810223131465927218293 := by
  unfold tailWord_292753
  simp only [CollatzResearch.WordTrace]
  refine ⟨10677579108413354076946913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7118386072275569384631275 10677579108413354076946913)
  ·
    refine ⟨8008184331310015557710185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10677579108413354076946913 8008184331310015557710185)
    ·
      refine ⟨6006138248482511668282639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8008184331310015557710185 6006138248482511668282639)
      ·
        refine ⟨9009207372723767502423959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6006138248482511668282639 9009207372723767502423959)
        ·
          refine ⟨13513811059085651253635939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9009207372723767502423959 13513811059085651253635939)
          ·
            refine ⟨20270716588628476880453909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13513811059085651253635939 20270716588628476880453909)
            ·
              refine ⟨950189840091959853771277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20270716588628476880453909 950189840091959853771277)
              ·
                refine ⟨356321190034484945164229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 950189840091959853771277 356321190034484945164229)
                ·
                  refine ⟨66810223131465927218293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 356321190034484945164229 66810223131465927218293)
                  ·
                    rfl

theorem cell21_292753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 4].length) (baseStart_292753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_292753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_292753 prefixEnd_292753 := by exact prefixLift 292753
  have htrace : WordTrace (prefixWord ++ tailWord_292753) baseStart_292753 baseEnd_292753 := by
    simpa [prefixWord, tailWord_292753, baseEnd_292753] using wordTrace_append hprefix tailTrace_292753
  have hstable : (prefixWord ++ tailWord_292753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292753).length < 2 ^ (prefixWord ++ tailWord_292753).sum := by decide
  have hdescent : baseEnd_292753 < baseStart_292753 := by decide
  rcases family_descends (prefixWord ++ tailWord_292753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292818 : List Nat := [3, 2, 2, 3, 2, 2, 2, 5]
def baseStart_292818 : Nat := 118140960795 + 292818 * 2 ^ 59
def prefixEnd_292818 : Nat := 4983230072969 + 3 ^ 40 * 292818 * 2
def baseEnd_292818 : Nat := 22275019005680086211609

theorem tailTrace_292818 : CollatzResearch.WordTrace tailWord_292818 prefixEnd_292818 22275019005680086211609 := by
  unfold tailWord_292818
  simp only [CollatzResearch.WordTrace]
  refine ⟨2669987463294467544515777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7119966568785246785375405 2669987463294467544515777)
  ·
    refine ⟨2002490597470850658386833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2669987463294467544515777 2002490597470850658386833)
    ·
      refine ⟨1501867948103137993790125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2002490597470850658386833 1501867948103137993790125)
      ·
        refine ⟨563200480538676747671297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1501867948103137993790125 563200480538676747671297)
        ·
          refine ⟨422400360404007560753473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 563200480538676747671297 422400360404007560753473)
          ·
            refine ⟨316800270303005670565105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 422400360404007560753473 316800270303005670565105)
            ·
              refine ⟨237600202727254252923829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 316800270303005670565105 237600202727254252923829)
              ·
                refine ⟨22275019005680086211609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 237600202727254252923829 22275019005680086211609)
                ·
                  rfl

theorem cell21_292818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 5].length) (baseStart_292818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_292818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_292818 prefixEnd_292818 := by exact prefixLift 292818
  have htrace : WordTrace (prefixWord ++ tailWord_292818) baseStart_292818 baseEnd_292818 := by
    simpa [prefixWord, tailWord_292818, baseEnd_292818] using wordTrace_append hprefix tailTrace_292818
  have hstable : (prefixWord ++ tailWord_292818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292818).length < 2 ^ (prefixWord ++ tailWord_292818).sum := by decide
  have hdescent : baseEnd_292818 < baseStart_292818 := by decide
  rcases family_descends (prefixWord ++ tailWord_292818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292849 : List Nat := [1, 2, 2, 2, 5, 1, 3, 2, 3]
def baseStart_292849 : Nat := 118140960795 + 292849 * 2 ^ 59
def prefixEnd_292849 : Nat := 4983230072969 + 3 ^ 40 * 292849 * 2
def baseEnd_292849 : Nat := 66832131639391093618097

theorem tailTrace_292849 : CollatzResearch.WordTrace tailWord_292849 prefixEnd_292849 66832131639391093618097 := by
  unfold tailWord_292849
  simp only [CollatzResearch.WordTrace]
  refine ⟨10681080516065562472441601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7120720344043708314961067 10681080516065562472441601)
  ·
    refine ⟨8010810387049171854331201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10681080516065562472441601 8010810387049171854331201)
    ·
      refine ⟨6008107790286878890748401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8010810387049171854331201 6008107790286878890748401)
      ·
        refine ⟨4506080842715159168061301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6008107790286878890748401 4506080842715159168061301)
        ·
          refine ⟨422445079004546172005747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4506080842715159168061301 422445079004546172005747)
          ·
            refine ⟨633667618506819258008621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422445079004546172005747 633667618506819258008621)
            ·
              refine ⟨237625356940057221753233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 633667618506819258008621 237625356940057221753233)
              ·
                refine ⟨178219017705042916314925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 237625356940057221753233 178219017705042916314925)
                ·
                  refine ⟨66832131639391093618097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 178219017705042916314925 66832131639391093618097)
                  ·
                    rfl

theorem cell21_292849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 2, 3].length) (baseStart_292849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_292849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_292849 prefixEnd_292849 := by exact prefixLift 292849
  have htrace : WordTrace (prefixWord ++ tailWord_292849) baseStart_292849 baseEnd_292849 := by
    simpa [prefixWord, tailWord_292849, baseEnd_292849] using wordTrace_append hprefix tailTrace_292849
  have hstable : (prefixWord ++ tailWord_292849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292849).length < 2 ^ (prefixWord ++ tailWord_292849).sum := by decide
  have hdescent : baseEnd_292849 < baseStart_292849 := by decide
  rcases family_descends (prefixWord ++ tailWord_292849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292919 : List Nat := [1, 1, 3, 1, 2, 2, 5, 6]
def baseStart_292919 : Nat := 118140960795 + 292919 * 2 ^ 59
def prefixEnd_292919 : Nat := 4983230072969 + 3 ^ 40 * 292919 * 2
def baseEnd_292919 : Nat := 22282702197695509150429

theorem tailTrace_292919 : CollatzResearch.WordTrace tailWord_292919 prefixEnd_292919 22282702197695509150429 := by
  unfold tailWord_292919
  simp only [CollatzResearch.WordTrace]
  refine ⟨10683633625811964427489811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7122422417207976284993207 10683633625811964427489811)
  ·
    refine ⟨16025450438717946641234717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10683633625811964427489811 16025450438717946641234717)
    ·
      refine ⟨6009543914519229990463019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16025450438717946641234717 6009543914519229990463019)
      ·
        refine ⟨9014315871778844985694529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6009543914519229990463019 9014315871778844985694529)
        ·
          refine ⟨6760736903834133739270897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9014315871778844985694529 6760736903834133739270897)
          ·
            refine ⟨5070552677875600304453173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6760736903834133739270897 5070552677875600304453173)
            ·
              refine ⟨475364313550837528542485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5070552677875600304453173 475364313550837528542485)
              ·
                refine ⟨22282702197695509150429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 475364313550837528542485 22282702197695509150429)
                ·
                  rfl

theorem cell21_292919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 6].length) (baseStart_292919 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_292919 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_292919 prefixEnd_292919 := by exact prefixLift 292919
  have htrace : WordTrace (prefixWord ++ tailWord_292919) baseStart_292919 baseEnd_292919 := by
    simpa [prefixWord, tailWord_292919, baseEnd_292919] using wordTrace_append hprefix tailTrace_292919
  have hstable : (prefixWord ++ tailWord_292919).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292919).length < 2 ^ (prefixWord ++ tailWord_292919).sum := by decide
  have hdescent : baseEnd_292919 < baseStart_292919 := by decide
  rcases family_descends (prefixWord ++ tailWord_292919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292967 : List Nat := [1, 1, 5, 1, 1, 2, 1, 6, 3]
def baseStart_292967 : Nat := 118140960795 + 292967 * 2 ^ 59
def prefixEnd_292967 : Nat := 4983230072969 + 3 ^ 40 * 292967 * 2
def baseEnd_292967 : Nat := 66859060847049110651189

theorem tailTrace_292967 : CollatzResearch.WordTrace tailWord_292967 prefixEnd_292967 66859060847049110651189 := by
  unfold tailWord_292967
  simp only [CollatzResearch.WordTrace]
  refine ⟨10685384329638068625237155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7123589553092045750158103 10685384329638068625237155)
  ·
    refine ⟨16028076494457102937855733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10685384329638068625237155 16028076494457102937855733)
    ·
      refine ⟨1502632171355353400423975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16028076494457102937855733 1502632171355353400423975)
      ·
        refine ⟨2253948257033030100635963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1502632171355353400423975 2253948257033030100635963)
        ·
          refine ⟨3380922385549545150953945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2253948257033030100635963 3380922385549545150953945)
          ·
            refine ⟨2535691789162158863215459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3380922385549545150953945 2535691789162158863215459)
            ·
              refine ⟨3803537683743238294823189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2535691789162158863215459 3803537683743238294823189)
              ·
                refine ⟨178290828925464295069837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3803537683743238294823189 178290828925464295069837)
                ·
                  refine ⟨66859060847049110651189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 178290828925464295069837 66859060847049110651189)
                  ·
                    rfl

theorem cell21_292967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 6, 3].length) (baseStart_292967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_292967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_292967 prefixEnd_292967 := by exact prefixLift 292967
  have htrace : WordTrace (prefixWord ++ tailWord_292967) baseStart_292967 baseEnd_292967 := by
    simpa [prefixWord, tailWord_292967, baseEnd_292967] using wordTrace_append hprefix tailTrace_292967
  have hstable : (prefixWord ++ tailWord_292967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292967).length < 2 ^ (prefixWord ++ tailWord_292967).sum := by decide
  have hdescent : baseEnd_292967 < baseStart_292967 := by decide
  rcases family_descends (prefixWord ++ tailWord_292967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292995 : List Nat := [1, 1, 1, 3, 3, 4, 1, 7]
def baseStart_292995 : Nat := 118140960795 + 292995 * 2 ^ 59
def prefixEnd_292995 : Nat := 4983230072969 + 3 ^ 40 * 292995 * 2
def baseEnd_292995 : Nat := 22288483609509094728155

theorem tailTrace_292995 : CollatzResearch.WordTrace tailWord_292995 prefixEnd_292995 22288483609509094728155 := by
  unfold tailWord_292995
  simp only [CollatzResearch.WordTrace]
  refine ⟨10686405573536629407256439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7124270382357752938170959 10686405573536629407256439)
  ·
    refine ⟨16029608360304944110884659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10686405573536629407256439 16029608360304944110884659)
    ·
      refine ⟨24044412540457416166326989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16029608360304944110884659 24044412540457416166326989)
      ·
        refine ⟨9016654702671531062372621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24044412540457416166326989 9016654702671531062372621)
        ·
          refine ⟨3381245513501824148389733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9016654702671531062372621 3381245513501824148389733)
          ·
            refine ⟨633983533781592027823075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3381245513501824148389733 633983533781592027823075)
            ·
              refine ⟨950975300672388041734613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 633983533781592027823075 950975300672388041734613)
              ·
                refine ⟨22288483609509094728155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 950975300672388041734613 22288483609509094728155)
                ·
                  rfl

theorem cell21_292995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 7].length) (baseStart_292995 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_292995 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_292995 prefixEnd_292995 := by exact prefixLift 292995
  have htrace : WordTrace (prefixWord ++ tailWord_292995) baseStart_292995 baseEnd_292995 := by
    simpa [prefixWord, tailWord_292995, baseEnd_292995] using wordTrace_append hprefix tailTrace_292995
  have hstable : (prefixWord ++ tailWord_292995).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292995).length < 2 ^ (prefixWord ++ tailWord_292995).sum := by decide
  have hdescent : baseEnd_292995 < baseStart_292995 := by decide
  rcases family_descends (prefixWord ++ tailWord_292995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293074 : List Nat := [3, 2, 2, 2, 1, 3, 2, 2, 4]
def baseStart_293074 : Nat := 118140960795 + 293074 * 2 ^ 59
def prefixEnd_293074 : Nat := 4983230072969 + 3 ^ 40 * 293074 * 2
def baseEnd_293074 : Nat := 66883479704840702367637

theorem tailTrace_293074 : CollatzResearch.WordTrace tailWord_293074 prefixEnd_293074 66883479704840702367637 := by
  unfold tailWord_293074
  simp only [CollatzResearch.WordTrace]
  refine ⟨2672321735062606474845569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7126191293500283932921517 2672321735062606474845569)
  ·
    refine ⟨2004241301296954856134177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2672321735062606474845569 2004241301296954856134177)
    ·
      refine ⟨1503180975972716142100633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2004241301296954856134177 1503180975972716142100633)
      ·
        refine ⟨1127385731979537106575475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1503180975972716142100633 1127385731979537106575475)
        ·
          refine ⟨1691078597969305659863213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1127385731979537106575475 1691078597969305659863213)
          ·
            refine ⟨634154474238489622448705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1691078597969305659863213 634154474238489622448705)
            ·
              refine ⟨475615855678867216836529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 634154474238489622448705 475615855678867216836529)
              ·
                refine ⟨356711891759150412627397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 475615855678867216836529 356711891759150412627397)
                ·
                  refine ⟨66883479704840702367637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 356711891759150412627397 66883479704840702367637)
                  ·
                    rfl

theorem cell21_293074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_293074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_293074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_293074 prefixEnd_293074 := by exact prefixLift 293074
  have htrace : WordTrace (prefixWord ++ tailWord_293074) baseStart_293074 baseEnd_293074 := by
    simpa [prefixWord, tailWord_293074, baseEnd_293074] using wordTrace_append hprefix tailTrace_293074
  have hstable : (prefixWord ++ tailWord_293074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293074).length < 2 ^ (prefixWord ++ tailWord_293074).sum := by decide
  have hdescent : baseEnd_293074 < baseStart_293074 := by decide
  rcases family_descends (prefixWord ++ tailWord_293074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293119 : List Nat := [1, 1, 2, 2, 1, 4, 4, 3, 3]
def baseStart_293119 : Nat := 118140960795 + 293119 * 2 ^ 59
def prefixEnd_293119 : Nat := 4983230072969 + 3 ^ 40 * 293119 * 2
def baseEnd_293119 : Nat := 66893749317930624117545

theorem tailTrace_293119 : CollatzResearch.WordTrace tailWord_293119 prefixEnd_293119 66893749317930624117545 := by
  unfold tailWord_293119
  simp only [CollatzResearch.WordTrace]
  refine ⟨10690928225087398584770411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7127285483391599056513607 10690928225087398584770411)
  ·
    refine ⟨16036392337631097877155617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10690928225087398584770411 16036392337631097877155617)
    ·
      refine ⟨12027294253223323407866713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16036392337631097877155617 12027294253223323407866713)
      ·
        refine ⟨9020470689917492555900035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12027294253223323407866713 9020470689917492555900035)
        ·
          refine ⟨13530706034876238833850053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9020470689917492555900035 13530706034876238833850053)
          ·
            refine ⟨2537007381539294781346885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13530706034876238833850053 2537007381539294781346885)
            ·
              refine ⟨475688884038617771502541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2537007381539294781346885 475688884038617771502541)
              ·
                refine ⟨178383331514481664313453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 475688884038617771502541 178383331514481664313453)
                ·
                  refine ⟨66893749317930624117545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 178383331514481664313453 66893749317930624117545)
                  ·
                    rfl

theorem cell21_293119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 3, 3].length) (baseStart_293119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_293119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_293119 prefixEnd_293119 := by exact prefixLift 293119
  have htrace : WordTrace (prefixWord ++ tailWord_293119) baseStart_293119 baseEnd_293119 := by
    simpa [prefixWord, tailWord_293119, baseEnd_293119] using wordTrace_append hprefix tailTrace_293119
  have hstable : (prefixWord ++ tailWord_293119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293119).length < 2 ^ (prefixWord ++ tailWord_293119).sum := by decide
  have hdescent : baseEnd_293119 < baseStart_293119 := by decide
  rcases family_descends (prefixWord ++ tailWord_293119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293192 : List Nat := [2, 1, 3, 1, 1, 2, 4, 1, 6]
def baseStart_293192 : Nat := 118140960795 + 293192 * 2 ^ 59
def prefixEnd_293192 : Nat := 4983230072969 + 3 ^ 40 * 293192 * 2
def baseEnd_293192 : Nat := 66910408912498719400729

theorem tailTrace_293192 : CollatzResearch.WordTrace tailWord_293192 prefixEnd_293192 66910408912498719400729 := by
  unfold tailWord_293192
  simp only [CollatzResearch.WordTrace]
  refine ⟨5346795376911466026088915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7129060502548621368118553 5346795376911466026088915)
  ·
    refine ⟨8020193065367199039133373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5346795376911466026088915 8020193065367199039133373)
    ·
      refine ⟨3007572399512699639675015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8020193065367199039133373 3007572399512699639675015)
      ·
        refine ⟨4511358599269049459512523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3007572399512699639675015 4511358599269049459512523)
        ·
          refine ⟨6767037898903574189268785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4511358599269049459512523 6767037898903574189268785)
          ·
            refine ⟨5075278424177680641951589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6767037898903574189268785 5075278424177680641951589)
            ·
              refine ⟨951614704533315120365923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5075278424177680641951589 951614704533315120365923)
              ·
                refine ⟨1427422056799972680548885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 951614704533315120365923 1427422056799972680548885)
                ·
                  refine ⟨66910408912498719400729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1427422056799972680548885 66910408912498719400729)
                  ·
                    rfl

theorem cell21_293192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 6].length) (baseStart_293192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_293192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_293192 prefixEnd_293192 := by exact prefixLift 293192
  have htrace : WordTrace (prefixWord ++ tailWord_293192) baseStart_293192 baseEnd_293192 := by
    simpa [prefixWord, tailWord_293192, baseEnd_293192] using wordTrace_append hprefix tailTrace_293192
  have hstable : (prefixWord ++ tailWord_293192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293192).length < 2 ^ (prefixWord ++ tailWord_293192).sum := by decide
  have hdescent : baseEnd_293192 < baseStart_293192 := by decide
  rcases family_descends (prefixWord ++ tailWord_293192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293223 : List Nat := [1, 1, 5, 1, 3, 1, 2, 7]
def baseStart_293223 : Nat := 118140960795 + 293223 * 2 ^ 59
def prefixEnd_293223 : Nat := 4983230072969 + 3 ^ 40 * 293223 * 2
def baseEnd_293223 : Nat := 22305827844949851461333

theorem tailTrace_293223 : CollatzResearch.WordTrace tailWord_293223 prefixEnd_293223 22305827844949851461333 := by
  unfold tailWord_293223
  simp only [CollatzResearch.WordTrace]
  refine ⟨10694721416710624346556323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7129814277807082897704215 10694721416710624346556323)
  ·
    refine ⟨16042082125065936519834485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10694721416710624346556323 16042082125065936519834485)
    ·
      refine ⟨1503945199224931548734483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16042082125065936519834485 1503945199224931548734483)
      ·
        refine ⟨2255917798837397323101725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1503945199224931548734483 2255917798837397323101725)
        ·
          refine ⟨845969174564023996163147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2255917798837397323101725 845969174564023996163147)
          ·
            refine ⟨1268953761846035994244721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 845969174564023996163147 1268953761846035994244721)
            ·
              refine ⟨951715321384526995683541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1268953761846035994244721 951715321384526995683541)
              ·
                refine ⟨22305827844949851461333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 951715321384526995683541 22305827844949851461333)
                ·
                  rfl

theorem cell21_293223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 7].length) (baseStart_293223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_293223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_293223 prefixEnd_293223 := by exact prefixLift 293223
  have htrace : WordTrace (prefixWord ++ tailWord_293223) baseStart_293223 baseEnd_293223 := by
    simpa [prefixWord, tailWord_293223, baseEnd_293223] using wordTrace_append hprefix tailTrace_293223
  have hstable : (prefixWord ++ tailWord_293223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293223).length < 2 ^ (prefixWord ++ tailWord_293223).sum := by decide
  have hdescent : baseEnd_293223 < baseStart_293223 := by decide
  rcases family_descends (prefixWord ++ tailWord_293223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293288 : List Nat := [2, 1, 6, 1, 1, 1, 1, 5, 3]
def baseStart_293288 : Nat := 118140960795 + 293288 * 2 ^ 59
def prefixEnd_293288 : Nat := 4983230072969 + 3 ^ 40 * 293288 * 2
def baseEnd_293288 : Nat := 66932317420423885800533

theorem tailTrace_293288 : CollatzResearch.WordTrace tailWord_293288 prefixEnd_293288 66932317420423885800533 := by
  unfold tailWord_293288
  simp only [CollatzResearch.WordTrace]
  refine ⟨5348546080737570223836259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7131394774316760298448345 5348546080737570223836259)
  ·
    refine ⟨8022819121106355335754389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5348546080737570223836259 8022819121106355335754389)
    ·
      refine ⟨376069646301860406363487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8022819121106355335754389 376069646301860406363487)
      ·
        refine ⟨564104469452790609545231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376069646301860406363487 564104469452790609545231)
        ·
          refine ⟨846156704179185914317847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 564104469452790609545231 846156704179185914317847)
          ·
            refine ⟨1269235056268778871476771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 846156704179185914317847 1269235056268778871476771)
            ·
              refine ⟨1903852584403168307215157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1269235056268778871476771 1903852584403168307215157)
              ·
                refine ⟨178486179787797028801421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1903852584403168307215157 178486179787797028801421)
                ·
                  refine ⟨66932317420423885800533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 178486179787797028801421 66932317420423885800533)
                  ·
                    rfl

theorem cell21_293288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 5, 3].length) (baseStart_293288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_293288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_293288 prefixEnd_293288 := by exact prefixLift 293288
  have htrace : WordTrace (prefixWord ++ tailWord_293288) baseStart_293288 baseEnd_293288 := by
    simpa [prefixWord, tailWord_293288, baseEnd_293288] using wordTrace_append hprefix tailTrace_293288
  have hstable : (prefixWord ++ tailWord_293288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293288).length < 2 ^ (prefixWord ++ tailWord_293288).sum := by decide
  have hdescent : baseEnd_293288 < baseStart_293288 := by decide
  rcases family_descends (prefixWord ++ tailWord_293288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293415 : List Nat := [1, 1, 7, 2, 2, 1, 2, 2, 3]
def baseStart_293415 : Nat := 118140960795 + 293415 * 2 ^ 59
def prefixEnd_293415 : Nat := 4983230072969 + 3 ^ 40 * 293415 * 2
def baseEnd_293415 : Nat := 66961300550699887183607

theorem tailTrace_293415 : CollatzResearch.WordTrace tailWord_293415 prefixEnd_293415 66961300550699887183607 := by
  unfold tailWord_293415
  simp only [CollatzResearch.WordTrace]
  refine ⟨10701724232015041137545699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7134482821343360758363799 10701724232015041137545699)
  ·
    refine ⟨16052586348022561706318549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10701724232015041137545699 16052586348022561706318549)
    ·
      refine ⟨376232492531778789991841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 16052586348022561706318549 376232492531778789991841)
      ·
        refine ⟨282174369398834092493881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 376232492531778789991841 282174369398834092493881)
        ·
          refine ⟨211630777049125569370411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 282174369398834092493881 211630777049125569370411)
          ·
            refine ⟨317446165573688354055617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211630777049125569370411 317446165573688354055617)
            ·
              refine ⟨238084624180266265541713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 317446165573688354055617 238084624180266265541713)
              ·
                refine ⟨178563468135199699156285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238084624180266265541713 178563468135199699156285)
                ·
                  refine ⟨66961300550699887183607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 178563468135199699156285 66961300550699887183607)
                  ·
                    rfl

theorem cell21_293415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 2, 3].length) (baseStart_293415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_293415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_293415 prefixEnd_293415 := by exact prefixLift 293415
  have htrace : WordTrace (prefixWord ++ tailWord_293415) baseStart_293415 baseEnd_293415 := by
    simpa [prefixWord, tailWord_293415, baseEnd_293415] using wordTrace_append hprefix tailTrace_293415
  have hstable : (prefixWord ++ tailWord_293415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293415).length < 2 ^ (prefixWord ++ tailWord_293415).sum := by decide
  have hdescent : baseEnd_293415 < baseStart_293415 := by decide
  rcases family_descends (prefixWord ++ tailWord_293415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293437 : List Nat := [1, 4, 1, 3, 2, 1, 2, 3, 4]
def baseStart_293437 : Nat := 118140960795 + 293437 * 2 ^ 59
def prefixEnd_293437 : Nat := 4983230072969 + 3 ^ 40 * 293437 * 2
def baseEnd_293437 : Nat := 66966321250432737816895

theorem tailTrace_293437 : CollatzResearch.WordTrace tailWord_293437 prefixEnd_293437 66966321250432737816895 := by
  unfold tailWord_293437
  simp only [CollatzResearch.WordTrace]
  refine ⟨10702526637935338894846565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7135017758623559263231043 10702526637935338894846565)
  ·
    refine ⟨2006723744612876042783731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10702526637935338894846565 2006723744612876042783731)
    ·
      refine ⟨3010085616919314064175597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2006723744612876042783731 3010085616919314064175597)
      ·
        refine ⟨1128782106344742774065849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3010085616919314064175597 1128782106344742774065849)
        ·
          refine ⟨846586579758557080549387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1128782106344742774065849 846586579758557080549387)
          ·
            refine ⟨1269879869637835620824081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 846586579758557080549387 1269879869637835620824081)
            ·
              refine ⟨952409902228376715618061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1269879869637835620824081 952409902228376715618061)
              ·
                refine ⟨357153713335641268356773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 952409902228376715618061 357153713335641268356773)
                ·
                  refine ⟨66966321250432737816895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 357153713335641268356773 66966321250432737816895)
                  ·
                    rfl

theorem cell21_293437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_293437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_293437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_293437 prefixEnd_293437 := by exact prefixLift 293437
  have htrace : WordTrace (prefixWord ++ tailWord_293437) baseStart_293437 baseEnd_293437 := by
    simpa [prefixWord, tailWord_293437, baseEnd_293437] using wordTrace_append hprefix tailTrace_293437
  have hstable : (prefixWord ++ tailWord_293437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293437).length < 2 ^ (prefixWord ++ tailWord_293437).sum := by decide
  have hdescent : baseEnd_293437 < baseStart_293437 := by decide
  rcases family_descends (prefixWord ++ tailWord_293437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293482 : List Nat := [3, 1, 3, 2, 1, 1, 4, 1, 5]
def baseStart_293482 : Nat := 118140960795 + 293482 * 2 ^ 59
def prefixEnd_293482 : Nat := 4983230072969 + 3 ^ 40 * 293482 * 2
def baseEnd_293482 : Nat := 66976590863522659566803

theorem tailTrace_293482 : CollatzResearch.WordTrace tailWord_293482 prefixEnd_293482 66976590863522659566803 := by
  unfold tailWord_293482
  simp only [CollatzResearch.WordTrace]
  refine ⟨2676041980693077895058675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7136111948514874386823133 2676041980693077895058675)
  ·
    refine ⟨4014062971039616842588013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2676041980693077895058675 4014062971039616842588013)
    ·
      refine ⟨1505273614139856315970505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4014062971039616842588013 1505273614139856315970505)
      ·
        refine ⟨1128955210604892236977879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1505273614139856315970505 1128955210604892236977879)
        ·
          refine ⟨1693432815907338355466819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1128955210604892236977879 1693432815907338355466819)
          ·
            refine ⟨2540149223861007533200229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1693432815907338355466819 2540149223861007533200229)
            ·
              refine ⟨476277979473938912475043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2540149223861007533200229 476277979473938912475043)
              ·
                refine ⟨714416969210908368712565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 476277979473938912475043 714416969210908368712565)
                ·
                  refine ⟨66976590863522659566803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 714416969210908368712565 66976590863522659566803)
                  ·
                    rfl

theorem cell21_293482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 5].length) (baseStart_293482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_293482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_293482 prefixEnd_293482 := by exact prefixLift 293482
  have htrace : WordTrace (prefixWord ++ tailWord_293482) baseStart_293482 baseEnd_293482 := by
    simpa [prefixWord, tailWord_293482, baseEnd_293482] using wordTrace_append hprefix tailTrace_293482
  have hstable : (prefixWord ++ tailWord_293482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293482).length < 2 ^ (prefixWord ++ tailWord_293482).sum := by decide
  have hdescent : baseEnd_293482 < baseStart_293482 := by decide
  rcases family_descends (prefixWord ++ tailWord_293482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293586 : List Nat := [3, 2, 2, 2, 12]
def baseStart_293586 : Nat := 118140960795 + 293586 * 2 ^ 59
def prefixEnd_293586 : Nat := 4983230072969 + 3 ^ 40 * 293586 * 2
def baseEnd_293586 : Nat := 827164507165945553497

theorem tailTrace_293586 : CollatzResearch.WordTrace tailWord_293586 prefixEnd_293586 827164507165945553497 := by
  unfold tailWord_293586
  simp only [CollatzResearch.WordTrace]
  refine ⟨2676990278598884335505153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7138640742930358228013741 2676990278598884335505153)
  ·
    refine ⟨2007742708949163251628865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2676990278598884335505153 2007742708949163251628865)
    ·
      refine ⟨1505807031711872438721649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2007742708949163251628865 1505807031711872438721649)
      ·
        refine ⟨1129355273783904329041237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1505807031711872438721649 1129355273783904329041237)
        ·
          refine ⟨827164507165945553497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 1129355273783904329041237 827164507165945553497)
          ·
            rfl

theorem cell21_293586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 12].length) (baseStart_293586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_293586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_293586 prefixEnd_293586 := by exact prefixLift 293586
  have htrace : WordTrace (prefixWord ++ tailWord_293586) baseStart_293586 baseEnd_293586 := by
    simpa [prefixWord, tailWord_293586, baseEnd_293586] using wordTrace_append hprefix tailTrace_293586
  have hstable : (prefixWord ++ tailWord_293586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293586).length < 2 ^ (prefixWord ++ tailWord_293586).sum := by decide
  have hdescent : baseEnd_293586 < baseStart_293586 := by decide
  rcases family_descends (prefixWord ++ tailWord_293586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293592 : List Nat := [2, 1, 2, 2, 3, 4, 2, 2, 3]
def baseStart_293592 : Nat := 118140960795 + 293592 * 2 ^ 59
def prefixEnd_293592 : Nat := 4983230072969 + 3 ^ 40 * 293592 * 2
def baseEnd_293592 : Nat := 67001694362186912733245

theorem tailTrace_293592 : CollatzResearch.WordTrace tailWord_293592 prefixEnd_293592 67001694362186912733245 := by
  unfold tailWord_293592
  simp only [CollatzResearch.WordTrace]
  refine ⟨5354089976186900183369515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7138786634915866911159353 5354089976186900183369515)
  ·
    refine ⟨8031134964280350275054273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5354089976186900183369515 8031134964280350275054273)
    ·
      refine ⟨6023351223210262706290705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8031134964280350275054273 6023351223210262706290705)
      ·
        refine ⟨4517513417407697029718029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6023351223210262706290705 4517513417407697029718029)
        ·
          refine ⟨1694067531527886386144261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4517513417407697029718029 1694067531527886386144261)
          ·
            refine ⟨317637662161478697402049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1694067531527886386144261 317637662161478697402049)
            ·
              refine ⟨238228246621109023051537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 317637662161478697402049 238228246621109023051537)
              ·
                refine ⟨178671184965831767288653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238228246621109023051537 178671184965831767288653)
                ·
                  refine ⟨67001694362186912733245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 178671184965831767288653 67001694362186912733245)
                  ·
                    rfl

theorem cell21_293592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 2, 3].length) (baseStart_293592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_293592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_293592 prefixEnd_293592 := by exact prefixLift 293592
  have htrace : WordTrace (prefixWord ++ tailWord_293592) baseStart_293592 baseEnd_293592 := by
    simpa [prefixWord, tailWord_293592, baseEnd_293592] using wordTrace_append hprefix tailTrace_293592
  have hstable : (prefixWord ++ tailWord_293592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293592).length < 2 ^ (prefixWord ++ tailWord_293592).sum := by decide
  have hdescent : baseEnd_293592 < baseStart_293592 := by decide
  rcases family_descends (prefixWord ++ tailWord_293592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293603 : List Nat := [1, 1, 1, 7, 1, 1, 3, 6]
def baseStart_293603 : Nat := 118140960795 + 293603 * 2 ^ 59
def prefixEnd_293603 : Nat := 4983230072969 + 3 ^ 40 * 293603 * 2
def baseEnd_293603 : Nat := 22334734904017779349963

theorem tailTrace_293603 : CollatzResearch.WordTrace tailWord_293603 prefixEnd_293603 22334734904017779349963 := by
  unfold tailWord_293603
  simp only [CollatzResearch.WordTrace]
  refine ⟨10708581155333949245389463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7139054103555966163592975 10708581155333949245389463)
  ·
    refine ⟨16062871733000923868084195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10708581155333949245389463 16062871733000923868084195)
    ·
      refine ⟨24094307599501385802126293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16062871733000923868084195 24094307599501385802126293)
      ·
        refine ⟨564710334363313729737335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 24094307599501385802126293 564710334363313729737335)
        ·
          refine ⟨847065501544970594606003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 564710334363313729737335 847065501544970594606003)
          ·
            refine ⟨1270598252317455891909005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 847065501544970594606003 1270598252317455891909005)
            ·
              refine ⟨476474344619045959465877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1270598252317455891909005 476474344619045959465877)
              ·
                refine ⟨22334734904017779349963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 476474344619045959465877 22334734904017779349963)
                ·
                  rfl

theorem cell21_293603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 6].length) (baseStart_293603 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_293603 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_293603 prefixEnd_293603 := by exact prefixLift 293603
  have htrace : WordTrace (prefixWord ++ tailWord_293603) baseStart_293603 baseEnd_293603 := by
    simpa [prefixWord, tailWord_293603, baseEnd_293603] using wordTrace_append hprefix tailTrace_293603
  have hstable : (prefixWord ++ tailWord_293603).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293603).length < 2 ^ (prefixWord ++ tailWord_293603).sum := by decide
  have hdescent : baseEnd_293603 < baseStart_293603 := by decide
  rcases family_descends (prefixWord ++ tailWord_293603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293617 : List Nat := [1, 2, 2, 2, 2, 2, 3, 2, 5]
def baseStart_293617 : Nat := 118140960795 + 293617 * 2 ^ 59
def prefixEnd_293617 : Nat := 4983230072969 + 3 ^ 40 * 293617 * 2
def baseEnd_293617 : Nat := 67007399702792424816527

theorem tailTrace_293617 : CollatzResearch.WordTrace tailWord_293617 prefixEnd_293617 67007399702792424816527 := by
  unfold tailWord_293617
  simp only [CollatzResearch.WordTrace]
  refine ⟨10709091777283229636399105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7139394518188819757599403 10709091777283229636399105)
  ·
    refine ⟨8031818832962422227299329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10709091777283229636399105 8031818832962422227299329)
    ·
      refine ⟨6023864124721816670474497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8031818832962422227299329 6023864124721816670474497)
      ·
        refine ⟨4517898093541362502855873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6023864124721816670474497 4517898093541362502855873)
        ·
          refine ⟨3388423570156021877141905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4517898093541362502855873 3388423570156021877141905)
          ·
            refine ⟨2541317677617016407856429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3388423570156021877141905 2541317677617016407856429)
            ·
              refine ⟨952994129106381152946161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2541317677617016407856429 952994129106381152946161)
              ·
                refine ⟨714745596829785864709621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 952994129106381152946161 714745596829785864709621)
                ·
                  refine ⟨67007399702792424816527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 714745596829785864709621 67007399702792424816527)
                  ·
                    rfl

theorem cell21_293617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 5].length) (baseStart_293617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_293617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_293617 prefixEnd_293617 := by exact prefixLift 293617
  have htrace : WordTrace (prefixWord ++ tailWord_293617) baseStart_293617 baseEnd_293617 := by
    simpa [prefixWord, tailWord_293617, baseEnd_293617] using wordTrace_append hprefix tailTrace_293617
  have hstable : (prefixWord ++ tailWord_293617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293617).length < 2 ^ (prefixWord ++ tailWord_293617).sum := by decide
  have hdescent : baseEnd_293617 < baseStart_293617 := by decide
  rcases family_descends (prefixWord ++ tailWord_293617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293631 : List Nat := [1, 1, 2, 2, 1, 3, 1, 4, 6]
def baseStart_293631 : Nat := 118140960795 + 293631 * 2 ^ 59
def prefixEnd_293631 : Nat := 4983230072969 + 3 ^ 40 * 293631 * 2
def baseEnd_293631 : Nat := 67010594693531511583165

theorem tailTrace_293631 : CollatzResearch.WordTrace tailWord_293631 prefixEnd_293631 67010594693531511583165 := by
  unfold tailWord_293631
  simp only [CollatzResearch.WordTrace]
  refine ⟨10709602399232510027408747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7139734932821673351605831 10709602399232510027408747)
  ·
    refine ⟨16064403598848765041113121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10709602399232510027408747 16064403598848765041113121)
    ·
      refine ⟨12048302699136573780834841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16064403598848765041113121 12048302699136573780834841)
      ·
        refine ⟨9036227024352430335626131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12048302699136573780834841 9036227024352430335626131)
        ·
          refine ⟨13554340536528645503439197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9036227024352430335626131 13554340536528645503439197)
          ·
            refine ⟨5082877701198242063789699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13554340536528645503439197 5082877701198242063789699)
            ·
              refine ⟨7624316551797363095684549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5082877701198242063789699 7624316551797363095684549)
              ·
                refine ⟨1429559353462005580440853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7624316551797363095684549 1429559353462005580440853)
                ·
                  refine ⟨67010594693531511583165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1429559353462005580440853 67010594693531511583165)
                  ·
                    rfl

theorem cell21_293631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 6].length) (baseStart_293631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_293631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_293631 prefixEnd_293631 := by exact prefixLift 293631
  have htrace : WordTrace (prefixWord ++ tailWord_293631) baseStart_293631 baseEnd_293631 := by
    simpa [prefixWord, tailWord_293631, baseEnd_293631] using wordTrace_append hprefix tailTrace_293631
  have hstable : (prefixWord ++ tailWord_293631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293631).length < 2 ^ (prefixWord ++ tailWord_293631).sum := by decide
  have hdescent : baseEnd_293631 < baseStart_293631 := by decide
  rcases family_descends (prefixWord ++ tailWord_293631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293665 : List Nat := [1, 2, 3, 2, 1, 2, 5, 1, 4]
def baseStart_293665 : Nat := 118140960795 + 293665 * 2 ^ 59
def prefixEnd_293665 : Nat := 4983230072969 + 3 ^ 40 * 293665 * 2
def baseEnd_293665 : Nat := 67018353956755008016429

theorem tailTrace_293665 : CollatzResearch.WordTrace tailWord_293665 prefixEnd_293665 67018353956755008016429 := by
  unfold tailWord_293665
  simp only [CollatzResearch.WordTrace]
  refine ⟨10710842481109333834146449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7140561654072889222764299 10710842481109333834146449)
  ·
    refine ⟨8033131860832000375609837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10710842481109333834146449 8033131860832000375609837)
    ·
      refine ⟨3012424447812000140853689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8033131860832000375609837 3012424447812000140853689)
      ·
        refine ⟨2259318335859000105640267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3012424447812000140853689 2259318335859000105640267)
        ·
          refine ⟨3388977503788500158460401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2259318335859000105640267 3388977503788500158460401)
          ·
            refine ⟨2541733127841375118845301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3388977503788500158460401 2541733127841375118845301)
            ·
              refine ⟨238287480735128917391747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2541733127841375118845301 238287480735128917391747)
              ·
                refine ⟨357431221102693376087621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 238287480735128917391747 357431221102693376087621)
                ·
                  refine ⟨67018353956755008016429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 357431221102693376087621 67018353956755008016429)
                  ·
                    rfl

theorem cell21_293665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 4].length) (baseStart_293665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_293665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_293665 prefixEnd_293665 := by exact prefixLift 293665
  have htrace : WordTrace (prefixWord ++ tailWord_293665) baseStart_293665 baseEnd_293665 := by
    simpa [prefixWord, tailWord_293665, baseEnd_293665] using wordTrace_append hprefix tailTrace_293665
  have hstable : (prefixWord ++ tailWord_293665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293665).length < 2 ^ (prefixWord ++ tailWord_293665).sum := by decide
  have hdescent : baseEnd_293665 < baseStart_293665 := by decide
  rcases family_descends (prefixWord ++ tailWord_293665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293702 : List Nat := [6, 1, 1, 2, 2, 1, 3, 2, 3]
def baseStart_293702 : Nat := 118140960795 + 293702 * 2 ^ 59
def prefixEnd_293702 : Nat := 4983230072969 + 3 ^ 40 * 293702 * 2
def baseEnd_293702 : Nat := 67026797860851165899687

theorem tailTrace_293702 : CollatzResearch.WordTrace tailWord_293702 prefixEnd_293702 67026797860851165899687 := by
  unfold tailWord_293702
  simp only [CollatzResearch.WordTrace]
  refine ⟨334755999436727786038855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7141461321316859435495573 334755999436727786038855)
  ·
    refine ⟨502133999155091679058283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 334755999436727786038855 502133999155091679058283)
    ·
      refine ⟨753200998732637518587425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 502133999155091679058283 753200998732637518587425)
      ·
        refine ⟨564900749049478138940569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 753200998732637518587425 564900749049478138940569)
        ·
          refine ⟨423675561787108604205427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 564900749049478138940569 423675561787108604205427)
          ·
            refine ⟨635513342680662906308141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 423675561787108604205427 635513342680662906308141)
            ·
              refine ⟨238317503505248589865553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 635513342680662906308141 238317503505248589865553)
              ·
                refine ⟨178738127628936442399165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238317503505248589865553 178738127628936442399165)
                ·
                  refine ⟨67026797860851165899687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 178738127628936442399165 67026797860851165899687)
                  ·
                    rfl

theorem cell21_293702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_293702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_293702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_293702 prefixEnd_293702 := by exact prefixLift 293702
  have htrace : WordTrace (prefixWord ++ tailWord_293702) baseStart_293702 baseEnd_293702 := by
    simpa [prefixWord, tailWord_293702, baseEnd_293702] using wordTrace_append hprefix tailTrace_293702
  have hstable : (prefixWord ++ tailWord_293702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293702).length < 2 ^ (prefixWord ++ tailWord_293702).sum := by decide
  have hdescent : baseEnd_293702 < baseStart_293702 := by decide
  rcases family_descends (prefixWord ++ tailWord_293702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293710 : List Nat := [4, 1, 1, 1, 1, 1, 1, 8, 3]
def baseStart_293710 : Nat := 118140960795 + 293710 * 2 ^ 59
def prefixEnd_293710 : Nat := 4983230072969 + 3 ^ 40 * 293710 * 2
def baseEnd_293710 : Nat := 67028623569844929766337

theorem tailTrace_293710 : CollatzResearch.WordTrace tailWord_293710 prefixEnd_293710 67028623569844929766337 := by
  unfold tailWord_293710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1339060470743288314941823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7141655843964204346356389 1339060470743288314941823)
  ·
    refine ⟨2008590706114932472412735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1339060470743288314941823 2008590706114932472412735)
    ·
      refine ⟨3012886059172398708619103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2008590706114932472412735 3012886059172398708619103)
      ·
        refine ⟨4519329088758598062928655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3012886059172398708619103 4519329088758598062928655)
        ·
          refine ⟨6778993633137897094392983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4519329088758598062928655 6778993633137897094392983)
          ·
            refine ⟨10168490449706845641589475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6778993633137897094392983 10168490449706845641589475)
            ·
              refine ⟨15252735674560268462384213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10168490449706845641589475 15252735674560268462384213)
              ·
                refine ⟨178742996186253146043565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 15252735674560268462384213 178742996186253146043565)
                ·
                  refine ⟨67028623569844929766337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 178742996186253146043565 67028623569844929766337)
                  ·
                    rfl

theorem cell21_293710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 8, 3].length) (baseStart_293710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_293710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_293710 prefixEnd_293710 := by exact prefixLift 293710
  have htrace : WordTrace (prefixWord ++ tailWord_293710) baseStart_293710 baseEnd_293710 := by
    simpa [prefixWord, tailWord_293710, baseEnd_293710] using wordTrace_append hprefix tailTrace_293710
  have hstable : (prefixWord ++ tailWord_293710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293710).length < 2 ^ (prefixWord ++ tailWord_293710).sum := by decide
  have hdescent : baseEnd_293710 < baseStart_293710 := by decide
  rcases family_descends (prefixWord ++ tailWord_293710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293752 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 9]
def baseStart_293752 : Nat := 118140960795 + 293752 * 2 ^ 59
def prefixEnd_293752 : Nat := 4983230072969 + 3 ^ 40 * 293752 * 2
def baseEnd_293752 : Nat := 67038208542062190066251

theorem tailTrace_293752 : CollatzResearch.WordTrace tailWord_293752 prefixEnd_293752 67038208542062190066251 := by
  unfold tailWord_293752
  simp only [CollatzResearch.WordTrace]
  refine ⟨5357007815897073846281755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7142677087862765128375673 5357007815897073846281755)
  ·
    refine ⟨8035511723845610769422633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5357007815897073846281755 8035511723845610769422633)
    ·
      refine ⟨6026633792884208077066975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8035511723845610769422633 6026633792884208077066975)
      ·
        refine ⟨9039950689326312115600463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6026633792884208077066975 9039950689326312115600463)
        ·
          refine ⟨13559926033989468173400695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9039950689326312115600463 13559926033989468173400695)
          ·
            refine ⟨20339889050984202260101043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13559926033989468173400695 20339889050984202260101043)
            ·
              refine ⟨30509833576476303390151565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20339889050984202260101043 30509833576476303390151565)
              ·
                refine ⟨11441187591178613771306837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30509833576476303390151565 11441187591178613771306837)
                ·
                  refine ⟨67038208542062190066251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11441187591178613771306837 67038208542062190066251)
                  ·
                    rfl

theorem cell21_293752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 9].length) (baseStart_293752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_293752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_293752 prefixEnd_293752 := by exact prefixLift 293752
  have htrace : WordTrace (prefixWord ++ tailWord_293752) baseStart_293752 baseEnd_293752 := by
    simpa [prefixWord, tailWord_293752, baseEnd_293752] using wordTrace_append hprefix tailTrace_293752
  have hstable : (prefixWord ++ tailWord_293752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293752).length < 2 ^ (prefixWord ++ tailWord_293752).sum := by decide
  have hdescent : baseEnd_293752 < baseStart_293752 := by decide
  rcases family_descends (prefixWord ++ tailWord_293752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293786 : List Nat := [3, 1, 1, 4, 3, 1, 1, 2, 5]
def baseStart_293786 : Nat := 118140960795 + 293786 * 2 ^ 59
def prefixEnd_293786 : Nat := 4983230072969 + 3 ^ 40 * 293786 * 2
def baseEnd_293786 : Nat := 67045967805285686499515

theorem tailTrace_293786 : CollatzResearch.WordTrace tailWord_293786 prefixEnd_293786 67045967805285686499515 := by
  unfold tailWord_293786
  simp only [CollatzResearch.WordTrace]
  refine ⟨2678813928417742874825303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7143503809113980999534141 2678813928417742874825303)
  ·
    refine ⟨4018220892626614312237955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2678813928417742874825303 4018220892626614312237955)
    ·
      refine ⟨6027331338939921468356933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4018220892626614312237955 6027331338939921468356933)
      ·
        refine ⟨1130124626051235275316925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6027331338939921468356933 1130124626051235275316925)
        ·
          refine ⟨423796734769213228243847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1130124626051235275316925 423796734769213228243847)
          ·
            refine ⟨635695102153819842365771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 423796734769213228243847 635695102153819842365771)
            ·
              refine ⟨953542653230729763548657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 635695102153819842365771 953542653230729763548657)
              ·
                refine ⟨715156989923047322661493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 953542653230729763548657 715156989923047322661493)
                ·
                  refine ⟨67045967805285686499515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 715156989923047322661493 67045967805285686499515)
                  ·
                    rfl

theorem cell21_293786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 5].length) (baseStart_293786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_293786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_293786 prefixEnd_293786 := by exact prefixLift 293786
  have htrace : WordTrace (prefixWord ++ tailWord_293786) baseStart_293786 baseEnd_293786 := by
    simpa [prefixWord, tailWord_293786, baseEnd_293786] using wordTrace_append hprefix tailTrace_293786
  have hstable : (prefixWord ++ tailWord_293786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293786).length < 2 ^ (prefixWord ++ tailWord_293786).sum := by decide
  have hdescent : baseEnd_293786 < baseStart_293786 := by decide
  rcases family_descends (prefixWord ++ tailWord_293786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293817 : List Nat := [1, 2, 1, 4, 2, 4, 1, 2, 4]
def baseStart_293817 : Nat := 118140960795 + 293817 * 2 ^ 59
def prefixEnd_293817 : Nat := 4983230072969 + 3 ^ 40 * 293817 * 2
def baseEnd_293817 : Nat := 67053042427636521482785

theorem tailTrace_293817 : CollatzResearch.WordTrace tailWord_293817 prefixEnd_293817 67053042427636521482785 := by
  unfold tailWord_293817
  simp only [CollatzResearch.WordTrace]
  refine ⟨10716386376558663793679705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7144257584372442529119803 10716386376558663793679705)
  ·
    refine ⟨8037289782418997845259779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10716386376558663793679705 8037289782418997845259779)
    ·
      refine ⟨12055934673628496767889669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8037289782418997845259779 12055934673628496767889669)
      ·
        refine ⟨2260487751305343143979313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12055934673628496767889669 2260487751305343143979313)
        ·
          refine ⟨1695365813479007357984485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2260487751305343143979313 1695365813479007357984485)
          ·
            refine ⟨317881090027313879622091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1695365813479007357984485 317881090027313879622091)
            ·
              refine ⟨476821635040970819433137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 317881090027313879622091 476821635040970819433137)
              ·
                refine ⟨357616226280728114574853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 476821635040970819433137 357616226280728114574853)
                ·
                  refine ⟨67053042427636521482785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 357616226280728114574853 67053042427636521482785)
                  ·
                    rfl

theorem cell21_293817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 4].length) (baseStart_293817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_293817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_293817 prefixEnd_293817 := by exact prefixLift 293817
  have htrace : WordTrace (prefixWord ++ tailWord_293817) baseStart_293817 baseEnd_293817 := by
    simpa [prefixWord, tailWord_293817, baseEnd_293817] using wordTrace_append hprefix tailTrace_293817
  have hstable : (prefixWord ++ tailWord_293817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293817).length < 2 ^ (prefixWord ++ tailWord_293817).sum := by decide
  have hdescent : baseEnd_293817 < baseStart_293817 := by decide
  rcases family_descends (prefixWord ++ tailWord_293817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293859 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 8]
def baseStart_293859 : Nat := 118140960795 + 293859 * 2 ^ 59
def prefixEnd_293859 : Nat := 4983230072969 + 3 ^ 40 * 293859 * 2
def baseEnd_293859 : Nat := 67062627399853781782699

theorem tailTrace_293859 : CollatzResearch.WordTrace tailWord_293859 prefixEnd_293859 67062627399853781782699 := by
  unfold tailWord_293859
  simp only [CollatzResearch.WordTrace]
  refine ⟨10717918242406504966708631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7145278828271003311139087 10717918242406504966708631)
  ·
    refine ⟨16076877363609757450062947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10717918242406504966708631 16076877363609757450062947)
    ·
      refine ⟨24115316045414636175094421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16076877363609757450062947 24115316045414636175094421)
      ·
        refine ⟨1130405439628811070707551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24115316045414636175094421 1130405439628811070707551)
        ·
          refine ⟨1695608159443216606061327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1130405439628811070707551 1695608159443216606061327)
          ·
            refine ⟨2543412239164824909091991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1695608159443216606061327 2543412239164824909091991)
            ·
              refine ⟨3815118358747237363637987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2543412239164824909091991 3815118358747237363637987)
              ·
                refine ⟨5722677538120856045456981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3815118358747237363637987 5722677538120856045456981)
                ·
                  refine ⟨67062627399853781782699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5722677538120856045456981 67062627399853781782699)
                  ·
                    rfl

theorem cell21_293859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 8].length) (baseStart_293859 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_293859 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_293859 prefixEnd_293859 := by exact prefixLift 293859
  have htrace : WordTrace (prefixWord ++ tailWord_293859) baseStart_293859 baseEnd_293859 := by
    simpa [prefixWord, tailWord_293859, baseEnd_293859] using wordTrace_append hprefix tailTrace_293859
  have hstable : (prefixWord ++ tailWord_293859).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293859).length < 2 ^ (prefixWord ++ tailWord_293859).sum := by decide
  have hdescent : baseEnd_293859 < baseStart_293859 := by decide
  rcases family_descends (prefixWord ++ tailWord_293859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293938 : List Nat := [3, 2, 1, 1, 2, 2, 3, 4, 3]
def baseStart_293938 : Nat := 118140960795 + 293938 * 2 ^ 59
def prefixEnd_293938 : Nat := 4983230072969 + 3 ^ 40 * 293938 * 2
def baseEnd_293938 : Nat := 67080656276167199965871

theorem tailTrace_293938 : CollatzResearch.WordTrace tailWord_293938 prefixEnd_293938 67080656276167199965871 := by
  unfold tailWord_293938
  simp only [CollatzResearch.WordTrace]
  refine ⟨2680199902280075364708617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7147199739413534305889645 2680199902280075364708617)
  ·
    refine ⟨2010149926710056523531463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2680199902280075364708617 2010149926710056523531463)
    ·
      refine ⟨3015224890065084785297195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2010149926710056523531463 3015224890065084785297195)
      ·
        refine ⟨4522837335097627177945793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3015224890065084785297195 4522837335097627177945793)
        ·
          refine ⟨3392128001323220383459345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4522837335097627177945793 3392128001323220383459345)
          ·
            refine ⟨2544096000992415287594509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3392128001323220383459345 2544096000992415287594509)
            ·
              refine ⟨954036000372155732847941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2544096000992415287594509 954036000372155732847941)
              ·
                refine ⟨178881750069779199908989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 954036000372155732847941 178881750069779199908989)
                ·
                  refine ⟨67080656276167199965871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 178881750069779199908989 67080656276167199965871)
                  ·
                    rfl

theorem cell21_293938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 4, 3].length) (baseStart_293938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_293938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_293938 prefixEnd_293938 := by exact prefixLift 293938
  have htrace : WordTrace (prefixWord ++ tailWord_293938) baseStart_293938 baseEnd_293938 := by
    simpa [prefixWord, tailWord_293938, baseEnd_293938] using wordTrace_append hprefix tailTrace_293938
  have hstable : (prefixWord ++ tailWord_293938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293938).length < 2 ^ (prefixWord ++ tailWord_293938).sum := by decide
  have hdescent : baseEnd_293938 < baseStart_293938 := by decide
  rcases family_descends (prefixWord ++ tailWord_293938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293986 : List Nat := [3, 3, 2, 2, 1, 3, 1, 2, 4]
def baseStart_293986 : Nat := 118140960795 + 293986 * 2 ^ 59
def prefixEnd_293986 : Nat := 4983230072969 + 3 ^ 40 * 293986 * 2
def baseEnd_293986 : Nat := 67091610530129783165773

theorem tailTrace_293986 : CollatzResearch.WordTrace tailWord_293986 prefixEnd_293986 67091610530129783165773 := by
  unfold tailWord_293986
  simp only [CollatzResearch.WordTrace]
  refine ⟨2680637578236601414145453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7148366875297603771054541 2680637578236601414145453)
  ·
    refine ⟨1005239091838725530304545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2680637578236601414145453 1005239091838725530304545)
    ·
      refine ⟨753929318879044147728409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1005239091838725530304545 753929318879044147728409)
      ·
        refine ⟨565446989159283110796307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 753929318879044147728409 565446989159283110796307)
        ·
          refine ⟨848170483738924666194461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 565446989159283110796307 848170483738924666194461)
          ·
            refine ⟨318063931402096749822923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 848170483738924666194461 318063931402096749822923)
            ·
              refine ⟨477095897103145124734385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 318063931402096749822923 477095897103145124734385)
              ·
                refine ⟨357821922827358843550789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 477095897103145124734385 357821922827358843550789)
                ·
                  refine ⟨67091610530129783165773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 357821922827358843550789 67091610530129783165773)
                  ·
                    rfl

theorem cell21_293986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_293986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_293986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_293986 prefixEnd_293986 := by exact prefixLift 293986
  have htrace : WordTrace (prefixWord ++ tailWord_293986) baseStart_293986 baseEnd_293986 := by
    simpa [prefixWord, tailWord_293986, baseEnd_293986] using wordTrace_append hprefix tailTrace_293986
  have hstable : (prefixWord ++ tailWord_293986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293986).length < 2 ^ (prefixWord ++ tailWord_293986).sum := by decide
  have hdescent : baseEnd_293986 < baseStart_293986 := by decide
  rcases family_descends (prefixWord ++ tailWord_293986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293997 : List Nat := [1, 5, 1, 1, 2, 2, 1, 3, 5]
def baseStart_293997 : Nat := 118140960795 + 293997 * 2 ^ 59
def prefixEnd_293997 : Nat := 4983230072969 + 3 ^ 40 * 293997 * 2
def baseEnd_293997 : Nat := 67094120879996208482417

theorem tailTrace_293997 : CollatzResearch.WordTrace tailWord_293997 prefixEnd_293997 67094120879996208482417 := by
  unfold tailWord_293997
  simp only [CollatzResearch.WordTrace]
  refine ⟨10722951515906554535232245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7148634343937703023488163 10722951515906554535232245)
  ·
    refine ⟨1005276704616239487678023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10722951515906554535232245 1005276704616239487678023)
    ·
      refine ⟨1507915056924359231517035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1005276704616239487678023 1507915056924359231517035)
      ·
        refine ⟨2261872585386538847275553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1507915056924359231517035 2261872585386538847275553)
        ·
          refine ⟨1696404439039904135456665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2261872585386538847275553 1696404439039904135456665)
          ·
            refine ⟨1272303329279928101592499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1696404439039904135456665 1272303329279928101592499)
            ·
              refine ⟨1908454993919892152388749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1272303329279928101592499 1908454993919892152388749)
              ·
                refine ⟨715670622719959557145781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1908454993919892152388749 715670622719959557145781)
                ·
                  refine ⟨67094120879996208482417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 715670622719959557145781 67094120879996208482417)
                  ·
                    rfl

theorem cell21_293997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_293997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_293997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_293997 prefixEnd_293997 := by exact prefixLift 293997
  have htrace : WordTrace (prefixWord ++ tailWord_293997) baseStart_293997 baseEnd_293997 := by
    simpa [prefixWord, tailWord_293997, baseEnd_293997] using wordTrace_append hprefix tailTrace_293997
  have hstable : (prefixWord ++ tailWord_293997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293997).length < 2 ^ (prefixWord ++ tailWord_293997).sum := by decide
  have hdescent : baseEnd_293997 < baseStart_293997 := by decide
  rcases family_descends (prefixWord ++ tailWord_293997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294011 : List Nat := [1, 1, 1, 1, 1, 4, 1, 7, 4]
def baseStart_294011 : Nat := 118140960795 + 294011 * 2 ^ 59
def prefixEnd_294011 : Nat := 4983230072969 + 3 ^ 40 * 294011 * 2
def baseEnd_294011 : Nat := 67097315870735295249055

theorem tailTrace_294011 : CollatzResearch.WordTrace tailWord_294011 prefixEnd_294011 67097315870735295249055 := by
  unfold tailWord_294011
  simp only [CollatzResearch.WordTrace]
  refine ⟨10723462137855834926241887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7148974758570556617494591 10723462137855834926241887)
  ·
    refine ⟨16085193206783752389362831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10723462137855834926241887 16085193206783752389362831)
    ·
      refine ⟨24127789810175628584044247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16085193206783752389362831 24127789810175628584044247)
      ·
        refine ⟨36191684715263442876066371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24127789810175628584044247 36191684715263442876066371)
        ·
          refine ⟨54287527072895164314099557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36191684715263442876066371 54287527072895164314099557)
          ·
            refine ⟨10178911326167843308893667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54287527072895164314099557 10178911326167843308893667)
            ·
              refine ⟨15268366989251764963340501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10178911326167843308893667 15268366989251764963340501)
              ·
                refine ⟨357852351310588241328293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 15268366989251764963340501 357852351310588241328293)
                ·
                  refine ⟨67097315870735295249055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 357852351310588241328293 67097315870735295249055)
                  ·
                    rfl

theorem cell21_294011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 4].length) (baseStart_294011 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_294011 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_294011 prefixEnd_294011 := by exact prefixLift 294011
  have htrace : WordTrace (prefixWord ++ tailWord_294011) baseStart_294011 baseEnd_294011 := by
    simpa [prefixWord, tailWord_294011, baseEnd_294011] using wordTrace_append hprefix tailTrace_294011
  have hstable : (prefixWord ++ tailWord_294011).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294011).length < 2 ^ (prefixWord ++ tailWord_294011).sum := by decide
  have hdescent : baseEnd_294011 < baseStart_294011 := by decide
  rcases family_descends (prefixWord ++ tailWord_294011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294042 : List Nat := [3, 1, 1, 5, 1, 1, 9]
def baseStart_294042 : Nat := 118140960795 + 294042 * 2 ^ 59
def prefixEnd_294042 : Nat := 4983230072969 + 3 ^ 40 * 294042 * 2
def baseEnd_294042 : Nat := 7456043388120681136925

theorem tailTrace_294042 : CollatzResearch.WordTrace tailWord_294042 prefixEnd_294042 7456043388120681136925 := by
  unfold tailWord_294042
  simp only [CollatzResearch.WordTrace]
  refine ⟨2681148200185881805155095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7149728533829018147080253 2681148200185881805155095)
  ·
    refine ⟨4021722300278822707732643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2681148200185881805155095 4021722300278822707732643)
    ·
      refine ⟨6032583450418234061598965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4021722300278822707732643 6032583450418234061598965)
      ·
        refine ⟨565554698476709443274903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6032583450418234061598965 565554698476709443274903)
        ·
          refine ⟨848332047715064164912355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 565554698476709443274903 848332047715064164912355)
          ·
            refine ⟨1272498071572596247368533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 848332047715064164912355 1272498071572596247368533)
            ·
              refine ⟨7456043388120681136925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1272498071572596247368533 7456043388120681136925)
              ·
                rfl

theorem cell21_294042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 9].length) (baseStart_294042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_294042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_294042 prefixEnd_294042 := by exact prefixLift 294042
  have htrace : WordTrace (prefixWord ++ tailWord_294042) baseStart_294042 baseEnd_294042 := by
    simpa [prefixWord, tailWord_294042, baseEnd_294042] using wordTrace_append hprefix tailTrace_294042
  have hstable : (prefixWord ++ tailWord_294042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294042).length < 2 ^ (prefixWord ++ tailWord_294042).sum := by decide
  have hdescent : baseEnd_294042 < baseStart_294042 := by decide
  rcases family_descends (prefixWord ++ tailWord_294042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294177 : List Nat := [1, 2, 3, 2, 1, 1, 1, 10]
def baseStart_294177 : Nat := 118140960795 + 294177 * 2 ^ 59
def prefixEnd_294177 : Nat := 4983230072969 + 3 ^ 40 * 294177 * 2
def baseEnd_294177 : Nat := 22378399777451965160683

theorem tailTrace_294177 : CollatzResearch.WordTrace tailWord_294177 prefixEnd_294177 22378399777451965160683 := by
  unfold tailWord_294177
  simp only [CollatzResearch.WordTrace]
  refine ⟨10729516655254445276784785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7153011103502963517856523 10729516655254445276784785)
  ·
    refine ⟨8047137491440833957588589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10729516655254445276784785 8047137491440833957588589)
    ·
      refine ⟨3017676559290312734095721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8047137491440833957588589 3017676559290312734095721)
      ·
        refine ⟨2263257419467734550571791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3017676559290312734095721 2263257419467734550571791)
        ·
          refine ⟨3394886129201601825857687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2263257419467734550571791 3394886129201601825857687)
          ·
            refine ⟨5092329193802402738786531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3394886129201601825857687 5092329193802402738786531)
            ·
              refine ⟨7638493790703604108179797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5092329193802402738786531 7638493790703604108179797)
              ·
                refine ⟨22378399777451965160683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 7638493790703604108179797 22378399777451965160683)
                ·
                  rfl

theorem cell21_294177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 10].length) (baseStart_294177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_294177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_294177 prefixEnd_294177 := by exact prefixLift 294177
  have htrace : WordTrace (prefixWord ++ tailWord_294177) baseStart_294177 baseEnd_294177 := by
    simpa [prefixWord, tailWord_294177, baseEnd_294177] using wordTrace_append hprefix tailTrace_294177
  have hstable : (prefixWord ++ tailWord_294177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294177).length < 2 ^ (prefixWord ++ tailWord_294177).sum := by decide
  have hdescent : baseEnd_294177 < baseStart_294177 := by decide
  rcases family_descends (prefixWord ++ tailWord_294177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294194 : List Nat := [3, 2, 1, 1, 4, 2, 1, 7]
def baseStart_294194 : Nat := 118140960795 + 294194 * 2 ^ 59
def prefixEnd_294194 : Nat := 4983230072969 + 3 ^ 40 * 294194 * 2
def baseEnd_294194 : Nat := 22379692987989214566227

theorem tailTrace_294194 : CollatzResearch.WordTrace tailWord_294194 prefixEnd_294194 22379692987989214566227 := by
  unfold tailWord_294194
  simp only [CollatzResearch.WordTrace]
  refine ⟨2682534174048214295038409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7153424464128571453435757 2682534174048214295038409)
  ·
    refine ⟨2011900630536160721278807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2682534174048214295038409 2011900630536160721278807)
    ·
      refine ⟨3017850945804241081918211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2011900630536160721278807 3017850945804241081918211)
      ·
        refine ⟨4526776418706361622877317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3017850945804241081918211 4526776418706361622877317)
        ·
          refine ⟨848770578507442804289497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4526776418706361622877317 848770578507442804289497)
          ·
            refine ⟨636577933880582103217123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 848770578507442804289497 636577933880582103217123)
            ·
              refine ⟨954866900820873154825685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 636577933880582103217123 954866900820873154825685)
              ·
                refine ⟨22379692987989214566227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 954866900820873154825685 22379692987989214566227)
                ·
                  rfl

theorem cell21_294194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 7].length) (baseStart_294194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_294194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_294194 prefixEnd_294194 := by exact prefixLift 294194
  have htrace : WordTrace (prefixWord ++ tailWord_294194) baseStart_294194 baseEnd_294194 := by
    simpa [prefixWord, tailWord_294194, baseEnd_294194] using wordTrace_append hprefix tailTrace_294194
  have hstable : (prefixWord ++ tailWord_294194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294194).length < 2 ^ (prefixWord ++ tailWord_294194).sum := by decide
  have hdescent : baseEnd_294194 < baseStart_294194 := by decide
  rcases family_descends (prefixWord ++ tailWord_294194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294273 : List Nat := [1, 2, 4, 3, 2, 1, 2, 2, 4]
def baseStart_294273 : Nat := 118140960795 + 294273 * 2 ^ 59
def prefixEnd_294273 : Nat := 4983230072969 + 3 ^ 40 * 294273 * 2
def baseEnd_294273 : Nat := 67157107840281061881853

theorem tailTrace_294273 : CollatzResearch.WordTrace tailWord_294273 prefixEnd_294273 67157107840281061881853 := by
  unfold tailWord_294273
  simp only [CollatzResearch.WordTrace]
  refine ⟨10733018062906653672279473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7155345375271102448186315 10733018062906653672279473)
  ·
    refine ⟨8049763547179990254209605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10733018062906653672279473 8049763547179990254209605)
    ·
      refine ⟨1509330665096248172664301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8049763547179990254209605 1509330665096248172664301)
      ·
        refine ⟨565998999411093064749113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1509330665096248172664301 565998999411093064749113)
        ·
          refine ⟨424499249558319798561835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 565998999411093064749113 424499249558319798561835)
          ·
            refine ⟨636748874337479697842753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 424499249558319798561835 636748874337479697842753)
            ·
              refine ⟨477561655753109773382065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 636748874337479697842753 477561655753109773382065)
              ·
                refine ⟨358171241814832330036549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 477561655753109773382065 358171241814832330036549)
                ·
                  refine ⟨67157107840281061881853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 358171241814832330036549 67157107840281061881853)
                  ·
                    rfl

theorem cell21_294273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 4].length) (baseStart_294273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_294273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_294273 prefixEnd_294273 := by exact prefixLift 294273
  have htrace : WordTrace (prefixWord ++ tailWord_294273) baseStart_294273 baseEnd_294273 := by
    simpa [prefixWord, tailWord_294273, baseEnd_294273] using wordTrace_append hprefix tailTrace_294273
  have hstable : (prefixWord ++ tailWord_294273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294273).length < 2 ^ (prefixWord ++ tailWord_294273).sum := by decide
  have hdescent : baseEnd_294273 < baseStart_294273 := by decide
  rcases family_descends (prefixWord ++ tailWord_294273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294284 : List Nat := [2, 2, 1, 2, 1, 3, 2, 3, 5]
def baseStart_294284 : Nat := 118140960795 + 294284 * 2 ^ 59
def prefixEnd_294284 : Nat := 4983230072969 + 3 ^ 40 * 294284 * 2
def baseEnd_294284 : Nat := 67159618190147487198497

theorem tailTrace_294284 : CollatzResearch.WordTrace tailWord_294284 prefixEnd_294284 67159618190147487198497 := by
  unfold tailWord_294284
  simp only [CollatzResearch.WordTrace]
  refine ⟨5366709632933401275464953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7155612843911201700619937 5366709632933401275464953)
  ·
    refine ⟨4025032224700050956598715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5366709632933401275464953 4025032224700050956598715)
    ·
      refine ⟨6037548337050076434898073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4025032224700050956598715 6037548337050076434898073)
      ·
        refine ⟨4528161252787557326173555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6037548337050076434898073 4528161252787557326173555)
        ·
          refine ⟨6792241879181335989260333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4528161252787557326173555 6792241879181335989260333)
          ·
            refine ⟨2547090704693000995972625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6792241879181335989260333 2547090704693000995972625)
            ·
              refine ⟨1910318028519750746979469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2547090704693000995972625 1910318028519750746979469)
              ·
                refine ⟨716369260694906530117301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1910318028519750746979469 716369260694906530117301)
                ·
                  refine ⟨67159618190147487198497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 716369260694906530117301 67159618190147487198497)
                  ·
                    rfl

theorem cell21_294284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_294284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_294284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_294284 prefixEnd_294284 := by exact prefixLift 294284
  have htrace : WordTrace (prefixWord ++ tailWord_294284) baseStart_294284 baseEnd_294284 := by
    simpa [prefixWord, tailWord_294284, baseEnd_294284] using wordTrace_append hprefix tailTrace_294284
  have hstable : (prefixWord ++ tailWord_294284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294284).length < 2 ^ (prefixWord ++ tailWord_294284).sum := by decide
  have hdescent : baseEnd_294284 < baseStart_294284 := by decide
  rcases family_descends (prefixWord ++ tailWord_294284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294301 : List Nat := [1, 4, 2, 1, 3, 2, 1, 2, 5]
def baseStart_294301 : Nat := 118140960795 + 294301 * 2 ^ 59
def prefixEnd_294301 : Nat := 4983230072969 + 3 ^ 40 * 294301 * 2
def baseEnd_294301 : Nat := 67163497821759235415129

theorem tailTrace_294301 : CollatzResearch.WordTrace tailWord_294301 prefixEnd_294301 67163497821759235415129 := by
  unfold tailWord_294301
  simp only [CollatzResearch.WordTrace]
  refine ⟨10734039306805214454298757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7156026204536809636199171 10734039306805214454298757)
  ·
    refine ⟨2012632370025977710181017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10734039306805214454298757 2012632370025977710181017)
    ·
      refine ⟨1509474277519483282635763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2012632370025977710181017 1509474277519483282635763)
      ·
        refine ⟨2264211416279224923953645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1509474277519483282635763 2264211416279224923953645)
        ·
          refine ⟨849079281104709346482617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2264211416279224923953645 849079281104709346482617)
          ·
            refine ⟨636809460828532009861963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 849079281104709346482617 636809460828532009861963)
            ·
              refine ⟨955214191242798014792945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 636809460828532009861963 955214191242798014792945)
              ·
                refine ⟨716410643432098511094709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 955214191242798014792945 716410643432098511094709)
                ·
                  refine ⟨67163497821759235415129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 716410643432098511094709 67163497821759235415129)
                  ·
                    rfl

theorem cell21_294301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_294301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_294301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_294301 prefixEnd_294301 := by exact prefixLift 294301
  have htrace : WordTrace (prefixWord ++ tailWord_294301) baseStart_294301 baseEnd_294301 := by
    simpa [prefixWord, tailWord_294301, baseEnd_294301] using wordTrace_append hprefix tailTrace_294301
  have hstable : (prefixWord ++ tailWord_294301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294301).length < 2 ^ (prefixWord ++ tailWord_294301).sum := by decide
  have hdescent : baseEnd_294301 < baseStart_294301 := by decide
  rcases family_descends (prefixWord ++ tailWord_294301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294332 : List Nat := [2, 2, 2, 4, 2, 1, 1, 1, 6]
def baseStart_294332 : Nat := 118140960795 + 294332 * 2 ^ 59
def prefixEnd_294332 : Nat := 4983230072969 + 3 ^ 40 * 294332 * 2
def baseEnd_294332 : Nat := 67170572444110070398399

theorem tailTrace_294332 : CollatzResearch.WordTrace tailWord_294332 prefixEnd_294332 67170572444110070398399 := by
  unfold tailWord_294332
  simp only [CollatzResearch.WordTrace]
  refine ⟨5367584984846453374338625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7156779979795271165784833 5367584984846453374338625)
  ·
    refine ⟨4025688738634840030753969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5367584984846453374338625 4025688738634840030753969)
    ·
      refine ⟨3019266553976130023065477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4025688738634840030753969 3019266553976130023065477)
      ·
        refine ⟨566112478870524379324777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3019266553976130023065477 566112478870524379324777)
        ·
          refine ⟨424584359152893284493583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 566112478870524379324777 424584359152893284493583)
          ·
            refine ⟨636876538729339926740375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 424584359152893284493583 636876538729339926740375)
            ·
              refine ⟨955314808094009890110563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 636876538729339926740375 955314808094009890110563)
              ·
                refine ⟨1432972212141014835165845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 955314808094009890110563 1432972212141014835165845)
                ·
                  refine ⟨67170572444110070398399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1432972212141014835165845 67170572444110070398399)
                  ·
                    rfl

theorem cell21_294332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 6].length) (baseStart_294332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_294332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_294332 prefixEnd_294332 := by exact prefixLift 294332
  have htrace : WordTrace (prefixWord ++ tailWord_294332) baseStart_294332 baseEnd_294332 := by
    simpa [prefixWord, tailWord_294332, baseEnd_294332] using wordTrace_append hprefix tailTrace_294332
  have hstable : (prefixWord ++ tailWord_294332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294332).length < 2 ^ (prefixWord ++ tailWord_294332).sum := by decide
  have hdescent : baseEnd_294332 < baseStart_294332 := by decide
  rcases family_descends (prefixWord ++ tailWord_294332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294360 : List Nat := [2, 1, 2, 2, 2, 1, 4, 2, 5]
def baseStart_294360 : Nat := 118140960795 + 294360 * 2 ^ 59
def prefixEnd_294360 : Nat := 4983230072969 + 3 ^ 40 * 294360 * 2
def baseEnd_294360 : Nat := 67176962425588243931675

theorem tailTrace_294360 : CollatzResearch.WordTrace tailWord_294360 prefixEnd_294360 67176962425588243931675 := by
  unfold tailWord_294360
  simp only [CollatzResearch.WordTrace]
  refine ⟨5368095606795733765348267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7157460809060978353797689 5368095606795733765348267)
  ·
    refine ⟨8052143410193600648022401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5368095606795733765348267 8052143410193600648022401)
    ·
      refine ⟨6039107557645200486016801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8052143410193600648022401 6039107557645200486016801)
      ·
        refine ⟨4529330668233900364512601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6039107557645200486016801 4529330668233900364512601)
        ·
          refine ⟨3396998001175425273384451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4529330668233900364512601 3396998001175425273384451)
          ·
            refine ⟨5095497001763137910076677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3396998001175425273384451 5095497001763137910076677)
            ·
              refine ⟨955405687830588358139377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5095497001763137910076677 955405687830588358139377)
              ·
                refine ⟨716554265872941268604533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 955405687830588358139377 716554265872941268604533)
                ·
                  refine ⟨67176962425588243931675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 716554265872941268604533 67176962425588243931675)
                  ·
                    rfl

theorem cell21_294360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 5].length) (baseStart_294360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_294360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_294360 prefixEnd_294360 := by exact prefixLift 294360
  have htrace : WordTrace (prefixWord ++ tailWord_294360) baseStart_294360 baseEnd_294360 := by
    simpa [prefixWord, tailWord_294360, baseEnd_294360] using wordTrace_append hprefix tailTrace_294360
  have hstable : (prefixWord ++ tailWord_294360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294360).length < 2 ^ (prefixWord ++ tailWord_294360).sum := by decide
  have hdescent : baseEnd_294360 < baseStart_294360 := by decide
  rcases family_descends (prefixWord ++ tailWord_294360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294394 : List Nat := [3, 1, 1, 1, 1, 2, 7, 2, 3]
def baseStart_294394 : Nat := 118140960795 + 294394 * 2 ^ 59
def prefixEnd_294394 : Nat := 4983230072969 + 3 ^ 40 * 294394 * 2
def baseEnd_294394 : Nat := 67184721688811740364939

theorem tailTrace_294394 : CollatzResearch.WordTrace tailWord_294394 prefixEnd_294394 67184721688811740364939 := by
  unfold tailWord_294394
  simp only [CollatzResearch.WordTrace]
  refine ⟨2684357823867072834358559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7158287530312194224956157 2684357823867072834358559)
  ·
    refine ⟨4026536735800609251537839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2684357823867072834358559 4026536735800609251537839)
    ·
      refine ⟨6039805103700913877306759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4026536735800609251537839 6039805103700913877306759)
      ·
        refine ⟨9059707655551370815960139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6039805103700913877306759 9059707655551370815960139)
        ·
          refine ⟨13589561483327056223940209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9059707655551370815960139 13589561483327056223940209)
          ·
            refine ⟨10192171112495292167955157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13589561483327056223940209 10192171112495292167955157)
            ·
              refine ⟨238879010449108410186449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 10192171112495292167955157 238879010449108410186449)
              ·
                refine ⟨179159257836831307639837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238879010449108410186449 179159257836831307639837)
                ·
                  refine ⟨67184721688811740364939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 179159257836831307639837 67184721688811740364939)
                  ·
                    rfl

theorem cell21_294394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 2, 3].length) (baseStart_294394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_294394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_294394 prefixEnd_294394 := by exact prefixLift 294394
  have htrace : WordTrace (prefixWord ++ tailWord_294394) baseStart_294394 baseEnd_294394 := by
    simpa [prefixWord, tailWord_294394, baseEnd_294394] using wordTrace_append hprefix tailTrace_294394
  have hstable : (prefixWord ++ tailWord_294394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294394).length < 2 ^ (prefixWord ++ tailWord_294394).sum := by decide
  have hdescent : baseEnd_294394 < baseStart_294394 := by decide
  rcases family_descends (prefixWord ++ tailWord_294394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294408 : List Nat := [2, 1, 3, 2, 1, 1, 6, 1, 4]
def baseStart_294408 : Nat := 118140960795 + 294408 * 2 ^ 59
def prefixEnd_294408 : Nat := 4983230072969 + 3 ^ 40 * 294408 * 2
def baseEnd_294408 : Nat := 67187916679550827131577

theorem tailTrace_294408 : CollatzResearch.WordTrace tailWord_294408 prefixEnd_294408 67187916679550827131577 := by
  unfold tailWord_294408
  simp only [CollatzResearch.WordTrace]
  refine ⟨5368970958708785864221939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7158627944945047818962585 5368970958708785864221939)
  ·
    refine ⟨8053456438063178796332909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5368970958708785864221939 8053456438063178796332909)
    ·
      refine ⟨3020046164273692048624841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8053456438063178796332909 3020046164273692048624841)
      ·
        refine ⟨2265034623205269036468631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3020046164273692048624841 2265034623205269036468631)
        ·
          refine ⟨3397551934807903554702947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2265034623205269036468631 3397551934807903554702947)
          ·
            refine ⟨5096327902211855332054421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3397551934807903554702947 5096327902211855332054421)
            ·
              refine ⟨238890370416180718690051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5096327902211855332054421 238890370416180718690051)
              ·
                refine ⟨358335555624271078035077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 238890370416180718690051 358335555624271078035077)
                ·
                  refine ⟨67187916679550827131577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 358335555624271078035077 67187916679550827131577)
                  ·
                    rfl

theorem cell21_294408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 4].length) (baseStart_294408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_294408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_294408 prefixEnd_294408 := by exact prefixLift 294408
  have htrace : WordTrace (prefixWord ++ tailWord_294408) baseStart_294408 baseEnd_294408 := by
    simpa [prefixWord, tailWord_294408, baseEnd_294408] using wordTrace_append hprefix tailTrace_294408
  have hstable : (prefixWord ++ tailWord_294408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294408).length < 2 ^ (prefixWord ++ tailWord_294408).sum := by decide
  have hdescent : baseEnd_294408 < baseStart_294408 := by decide
  rcases family_descends (prefixWord ++ tailWord_294408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294512 : List Nat := [2, 1, 1, 1, 6, 1, 1, 3, 5]
def baseStart_294512 : Nat := 118140960795 + 294512 * 2 ^ 59
def prefixEnd_294512 : Nat := 4983230072969 + 3 ^ 40 * 294512 * 2
def baseEnd_294512 : Nat := 67211650896469757398031

theorem tailTrace_294512 : CollatzResearch.WordTrace tailWord_294512 prefixEnd_294512 67211650896469757398031 := by
  unfold tailWord_294512
  simp only [CollatzResearch.WordTrace]
  refine ⟨5370867554520398745114895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7161156739360531660153193 5370867554520398745114895)
  ·
    refine ⟨8056301331780598117672343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5370867554520398745114895 8056301331780598117672343)
    ·
      refine ⟨12084451997670897176508515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8056301331780598117672343 12084451997670897176508515)
      ·
        refine ⟨18126677996506345764762773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12084451997670897176508515 18126677996506345764762773)
        ·
          refine ⟨849688031086234957723255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18126677996506345764762773 849688031086234957723255)
          ·
            refine ⟨1274532046629352436584883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 849688031086234957723255 1274532046629352436584883)
            ·
              refine ⟨1911798069944028654877325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1274532046629352436584883 1911798069944028654877325)
              ·
                refine ⟨716924276229010745578997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1911798069944028654877325 716924276229010745578997)
                ·
                  refine ⟨67211650896469757398031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 716924276229010745578997 67211650896469757398031)
                  ·
                    rfl

theorem cell21_294512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 5].length) (baseStart_294512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_294512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_294512 prefixEnd_294512 := by exact prefixLift 294512
  have htrace : WordTrace (prefixWord ++ tailWord_294512) baseStart_294512 baseEnd_294512 := by
    simpa [prefixWord, tailWord_294512, baseEnd_294512] using wordTrace_append hprefix tailTrace_294512
  have hstable : (prefixWord ++ tailWord_294512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294512).length < 2 ^ (prefixWord ++ tailWord_294512).sum := by decide
  have hdescent : baseEnd_294512 < baseStart_294512 := by decide
  rcases family_descends (prefixWord ++ tailWord_294512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294532 : List Nat := [2, 3, 2, 1, 5, 1, 2, 5]
def baseStart_294532 : Nat := 118140960795 + 294532 * 2 ^ 59
def prefixEnd_294532 : Nat := 4983230072969 + 3 ^ 40 * 294532 * 2
def baseEnd_294532 : Nat := 22405405056318055688219

theorem tailTrace_294532 : CollatzResearch.WordTrace tailWord_294532 prefixEnd_294532 22405405056318055688219 := by
  unfold tailWord_294532
  simp only [CollatzResearch.WordTrace]
  refine ⟨5371232284484170452978925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7161643045978893937305233 5371232284484170452978925)
  ·
    refine ⟨2014212106681563919867097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5371232284484170452978925 2014212106681563919867097)
    ·
      refine ⟨1510659080011172939900323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2014212106681563919867097 1510659080011172939900323)
      ·
        refine ⟨2265988620016759409850485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1510659080011172939900323 2265988620016759409850485)
        ·
          refine ⟨212436433126571194673483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2265988620016759409850485 212436433126571194673483)
          ·
            refine ⟨318654649689856792010225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212436433126571194673483 318654649689856792010225)
            ·
              refine ⟨238990987267392594007669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 318654649689856792010225 238990987267392594007669)
              ·
                refine ⟨22405405056318055688219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 238990987267392594007669 22405405056318055688219)
                ·
                  rfl

theorem cell21_294532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 5].length) (baseStart_294532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_294532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_294532 prefixEnd_294532 := by exact prefixLift 294532
  have htrace : WordTrace (prefixWord ++ tailWord_294532) baseStart_294532 baseEnd_294532 := by
    simpa [prefixWord, tailWord_294532, baseEnd_294532] using wordTrace_append hprefix tailTrace_294532
  have hstable : (prefixWord ++ tailWord_294532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294532).length < 2 ^ (prefixWord ++ tailWord_294532).sum := by decide
  have hdescent : baseEnd_294532 < baseStart_294532 := by decide
  rcases family_descends (prefixWord ++ tailWord_294532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294614 : List Nat := [5, 2, 1, 3, 2, 1, 2, 2, 3]
def baseStart_294614 : Nat := 118140960795 + 294614 * 2 ^ 59
def prefixEnd_294614 : Nat := 4983230072969 + 3 ^ 40 * 294614 * 2
def baseEnd_294614 : Nat := 67234928686140246697823

theorem tailTrace_294614 : CollatzResearch.WordTrace tailWord_294614 prefixEnd_294614 67234928686140246697823 := by
  unfold tailWord_294614
  simp only [CollatzResearch.WordTrace]
  refine ⟨671590959666954306902681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7163636903114179273628597 671590959666954306902681)
  ·
    refine ⟨503693219750215730177011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 671590959666954306902681 503693219750215730177011)
    ·
      refine ⟨755539829625323595265517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 503693219750215730177011 755539829625323595265517)
      ·
        refine ⟨283327436109496348224569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 755539829625323595265517 283327436109496348224569)
        ·
          refine ⟨212495577082122261168427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 283327436109496348224569 212495577082122261168427)
          ·
            refine ⟨318743365623183391752641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212495577082122261168427 318743365623183391752641)
            ·
              refine ⟨239057524217387543814481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 318743365623183391752641 239057524217387543814481)
              ·
                refine ⟨179293143163040657860861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 239057524217387543814481 179293143163040657860861)
                ·
                  refine ⟨67234928686140246697823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 179293143163040657860861 67234928686140246697823)
                  ·
                    rfl

theorem cell21_294614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_294614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_294614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_294614 prefixEnd_294614 := by exact prefixLift 294614
  have htrace : WordTrace (prefixWord ++ tailWord_294614) baseStart_294614 baseEnd_294614 := by
    simpa [prefixWord, tailWord_294614, baseEnd_294614] using wordTrace_append hprefix tailTrace_294614
  have hstable : (prefixWord ++ tailWord_294614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294614).length < 2 ^ (prefixWord ++ tailWord_294614).sum := by decide
  have hdescent : baseEnd_294614 < baseStart_294614 := by decide
  rcases family_descends (prefixWord ++ tailWord_294614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294647 : List Nat := [1, 1, 3, 1, 1, 1, 5, 1, 7]
def baseStart_294647 : Nat := 118140960795 + 294647 * 2 ^ 59
def prefixEnd_294647 : Nat := 4983230072969 + 3 ^ 40 * 294647 * 2
def baseEnd_294647 : Nat := 67242459735739522647755

theorem tailTrace_294647 : CollatzResearch.WordTrace tailWord_294647 prefixEnd_294647 67242459735739522647755 := by
  unfold tailWord_294647
  simp only [CollatzResearch.WordTrace]
  refine ⟨10746658963551715546394195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7164439309034477030929463 10746658963551715546394195)
  ·
    refine ⟨16119988445327573319591293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10746658963551715546394195 16119988445327573319591293)
    ·
      refine ⟨6044995666997839994846735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16119988445327573319591293 6044995666997839994846735)
      ·
        refine ⟨9067493500496759992270103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6044995666997839994846735 9067493500496759992270103)
        ·
          refine ⟨13601240250745139988405155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9067493500496759992270103 13601240250745139988405155)
          ·
            refine ⟨20401860376117709982607733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13601240250745139988405155 20401860376117709982607733)
            ·
              refine ⟨1912674410261035310869475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20401860376117709982607733 1912674410261035310869475)
              ·
                refine ⟨2869011615391552966304213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1912674410261035310869475 2869011615391552966304213)
                ·
                  refine ⟨67242459735739522647755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2869011615391552966304213 67242459735739522647755)
                  ·
                    rfl

theorem cell21_294647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 7].length) (baseStart_294647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_294647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_294647 prefixEnd_294647 := by exact prefixLift 294647
  have htrace : WordTrace (prefixWord ++ tailWord_294647) baseStart_294647 baseEnd_294647 := by
    simpa [prefixWord, tailWord_294647, baseEnd_294647] using wordTrace_append hprefix tailTrace_294647
  have hstable : (prefixWord ++ tailWord_294647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294647).length < 2 ^ (prefixWord ++ tailWord_294647).sum := by decide
  have hdescent : baseEnd_294647 < baseStart_294647 := by decide
  rcases family_descends (prefixWord ++ tailWord_294647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294785 : List Nat := [1, 2, 4, 4, 10]
def baseStart_294785 : Nat := 118140960795 + 294785 * 2 ^ 59
def prefixEnd_294785 : Nat := 4983230072969 + 3 ^ 40 * 294785 * 2
def baseEnd_294785 : Nat := 830542632294838880833

theorem tailTrace_294785 : CollatzResearch.WordTrace tailWord_294785 prefixEnd_294785 830542632294838880833 := by
  unfold tailWord_294785
  simp only [CollatzResearch.WordTrace]
  refine ⟨10751692237051765114917809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7167794824701176743278539 10751692237051765114917809)
  ·
    refine ⟨8063769177788823836188357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10751692237051765114917809 8063769177788823836188357)
    ·
      refine ⟨1511956720835404469285317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8063769177788823836188357 1511956720835404469285317)
      ·
        refine ⟨283491885156638337990997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1511956720835404469285317 283491885156638337990997)
        ·
          refine ⟨830542632294838880833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 283491885156638337990997 830542632294838880833)
          ·
            rfl

theorem cell21_294785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 10].length) (baseStart_294785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_294785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_294785 prefixEnd_294785 := by exact prefixLift 294785
  have htrace : WordTrace (prefixWord ++ tailWord_294785) baseStart_294785 baseEnd_294785 := by
    simpa [prefixWord, tailWord_294785, baseEnd_294785] using wordTrace_append hprefix tailTrace_294785
  have hstable : (prefixWord ++ tailWord_294785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294785).length < 2 ^ (prefixWord ++ tailWord_294785).sum := by decide
  have hdescent : baseEnd_294785 < baseStart_294785 := by decide
  rcases family_descends (prefixWord ++ tailWord_294785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294791 : List Nat := [1, 1, 4, 2, 4, 2, 2, 2, 3]
def baseStart_294791 : Nat := 118140960795 + 294791 * 2 ^ 59
def prefixEnd_294791 : Nat := 4983230072969 + 3 ^ 40 * 294791 * 2
def baseEnd_294791 : Nat := 67275322497627272247461

theorem tailTrace_294791 : CollatzResearch.WordTrace tailWord_294791 prefixEnd_294791 67275322497627272247461 := by
  unfold tailWord_294791
  simp only [CollatzResearch.WordTrace]
  refine ⟨10751911075030028139636227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7167940716686685426424151 10751911075030028139636227)
  ·
    refine ⟨16127866612545042209454341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10751911075030028139636227 16127866612545042209454341)
    ·
      refine ⟨3023974989852195414272689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16127866612545042209454341 3023974989852195414272689)
      ·
        refine ⟨2267981242389146560704517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3023974989852195414272689 2267981242389146560704517)
        ·
          refine ⟨425246482947964980132097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2267981242389146560704517 425246482947964980132097)
          ·
            refine ⟨318934862210973735099073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 425246482947964980132097 318934862210973735099073)
            ·
              refine ⟨239201146658230301324305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 318934862210973735099073 239201146658230301324305)
              ·
                refine ⟨179400859993672725993229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 239201146658230301324305 179400859993672725993229)
                ·
                  refine ⟨67275322497627272247461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 179400859993672725993229 67275322497627272247461)
                  ·
                    rfl

theorem cell21_294791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 2, 3].length) (baseStart_294791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_294791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_294791 prefixEnd_294791 := by exact prefixLift 294791
  have htrace : WordTrace (prefixWord ++ tailWord_294791) baseStart_294791 baseEnd_294791 := by
    simpa [prefixWord, tailWord_294791, baseEnd_294791] using wordTrace_append hprefix tailTrace_294791
  have hstable : (prefixWord ++ tailWord_294791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294791).length < 2 ^ (prefixWord ++ tailWord_294791).sum := by decide
  have hdescent : baseEnd_294791 < baseStart_294791 := by decide
  rcases family_descends (prefixWord ++ tailWord_294791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294802 : List Nat := [3, 2, 3, 2, 1, 1, 3, 6]
def baseStart_294802 : Nat := 118140960795 + 294802 * 2 ^ 59
def prefixEnd_294802 : Nat := 4983230072969 + 3 ^ 40 * 294802 * 2
def baseEnd_294802 : Nat := 22425944282497899188035

theorem tailTrace_294802 : CollatzResearch.WordTrace tailWord_294802 prefixEnd_294802 22425944282497899188035 := by
  unfold tailWord_294802
  simp only [CollatzResearch.WordTrace]
  refine ⟨2688078069497544254571665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7168208185326784678857773 2688078069497544254571665)
  ·
    refine ⟨2016058552123158190928749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2688078069497544254571665 2016058552123158190928749)
    ·
      refine ⟨756021957046184321598281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2016058552123158190928749 756021957046184321598281)
      ·
        refine ⟨567016467784638241198711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 756021957046184321598281 567016467784638241198711)
        ·
          refine ⟨850524701676957361798067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 567016467784638241198711 850524701676957361798067)
          ·
            refine ⟨1275787052515436042697101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 850524701676957361798067 1275787052515436042697101)
            ·
              refine ⟨478420144693288516011413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1275787052515436042697101 478420144693288516011413)
              ·
                refine ⟨22425944282497899188035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 478420144693288516011413 22425944282497899188035)
                ·
                  rfl

theorem cell21_294802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 6].length) (baseStart_294802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_294802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_294802 prefixEnd_294802 := by exact prefixLift 294802
  have htrace : WordTrace (prefixWord ++ tailWord_294802) baseStart_294802 baseEnd_294802 := by
    simpa [prefixWord, tailWord_294802, baseEnd_294802] using wordTrace_append hprefix tailTrace_294802
  have hstable : (prefixWord ++ tailWord_294802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294802).length < 2 ^ (prefixWord ++ tailWord_294802).sum := by decide
  have hdescent : baseEnd_294802 < baseStart_294802 := by decide
  rcases family_descends (prefixWord ++ tailWord_294802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294833 : List Nat := [1, 2, 2, 4, 2, 1, 1, 5, 3]
def baseStart_294833 : Nat := 118140960795 + 294833 * 2 ^ 59
def prefixEnd_294833 : Nat := 4983230072969 + 3 ^ 40 * 294833 * 2
def baseEnd_294833 : Nat := 67284907469844532547375

theorem tailTrace_294833 : CollatzResearch.WordTrace tailWord_294833 prefixEnd_294833 67284907469844532547375 := by
  unfold tailWord_294833
  simp only [CollatzResearch.WordTrace]
  refine ⟨10753442940877869312665153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7168961960585246208443435 10753442940877869312665153)
  ·
    refine ⟨8065082205658401984498865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10753442940877869312665153 8065082205658401984498865)
    ·
      refine ⟨6048811654243801488374149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8065082205658401984498865 6048811654243801488374149)
      ·
        refine ⟨1134152185170712779070153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6048811654243801488374149 1134152185170712779070153)
        ·
          refine ⟨850614138878034584302615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1134152185170712779070153 850614138878034584302615)
          ·
            refine ⟨1275921208317051876453923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 850614138878034584302615 1275921208317051876453923)
            ·
              refine ⟨1913881812475577814680885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1275921208317051876453923 1913881812475577814680885)
              ·
                refine ⟨179426419919585420126333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1913881812475577814680885 179426419919585420126333)
                ·
                  refine ⟨67284907469844532547375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 179426419919585420126333 67284907469844532547375)
                  ·
                    rfl

theorem cell21_294833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 5, 3].length) (baseStart_294833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_294833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_294833 prefixEnd_294833 := by exact prefixLift 294833
  have htrace : WordTrace (prefixWord ++ tailWord_294833) baseStart_294833 baseEnd_294833 := by
    simpa [prefixWord, tailWord_294833, baseEnd_294833] using wordTrace_append hprefix tailTrace_294833
  have hstable : (prefixWord ++ tailWord_294833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294833).length < 2 ^ (prefixWord ++ tailWord_294833).sum := by decide
  have hdescent : baseEnd_294833 < baseStart_294833 := by decide
  rcases family_descends (prefixWord ++ tailWord_294833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295058 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 8]
def baseStart_295058 : Nat := 118140960795 + 295058 * 2 ^ 59
def prefixEnd_295058 : Nat := 4983230072969 + 3 ^ 40 * 295058 * 2
def baseEnd_295058 : Nat := 67336255535294141296915

theorem tailTrace_295058 : CollatzResearch.WordTrace tailWord_295058 prefixEnd_295058 67336255535294141296915 := by
  unfold tailWord_295058
  simp only [CollatzResearch.WordTrace]
  refine ⟨2690412341265683184901457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7174432910041821826403885 2690412341265683184901457)
  ·
    refine ⟨2017809255949262388676093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2690412341265683184901457 2017809255949262388676093)
    ·
      refine ⟨756678470980973395753535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2017809255949262388676093 756678470980973395753535)
      ·
        refine ⟨1135017706471460093630303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 756678470980973395753535 1135017706471460093630303)
        ·
          refine ⟨1702526559707190140445455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1135017706471460093630303 1702526559707190140445455)
          ·
            refine ⟨2553789839560785210668183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1702526559707190140445455 2553789839560785210668183)
            ·
              refine ⟨3830684759341177816002275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2553789839560785210668183 3830684759341177816002275)
              ·
                refine ⟨5746027139011766724003413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3830684759341177816002275 5746027139011766724003413)
                ·
                  refine ⟨67336255535294141296915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5746027139011766724003413 67336255535294141296915)
                  ·
                    rfl

theorem cell21_295058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_295058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_295058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_295058 prefixEnd_295058 := by exact prefixLift 295058
  have htrace : WordTrace (prefixWord ++ tailWord_295058) baseStart_295058 baseEnd_295058 := by
    simpa [prefixWord, tailWord_295058, baseEnd_295058] using wordTrace_append hprefix tailTrace_295058
  have hstable : (prefixWord ++ tailWord_295058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295058).length < 2 ^ (prefixWord ++ tailWord_295058).sum := by decide
  have hdescent : baseEnd_295058 < baseStart_295058 := by decide
  rcases family_descends (prefixWord ++ tailWord_295058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295072 : List Nat := [2, 1, 1, 4, 2, 2, 9]
def baseStart_295072 : Nat := 118140960795 + 295072 * 2 ^ 59
def prefixEnd_295072 : Nat := 4983230072969 + 3 ^ 40 * 295072 * 2
def baseEnd_295072 : Nat := 7482161169559247562617

theorem tailTrace_295072 : CollatzResearch.WordTrace tailWord_295072 prefixEnd_295072 7482161169559247562617 := by
  unfold tailWord_295072
  simp only [CollatzResearch.WordTrace]
  refine ⟨5381079993506006565307735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7174773324674675420410313 5381079993506006565307735)
  ·
    refine ⟨8071619990259009847961603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5381079993506006565307735 8071619990259009847961603)
    ·
      refine ⟨12107429985388514771942405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8071619990259009847961603 12107429985388514771942405)
      ·
        refine ⟨2270143122260346519739201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12107429985388514771942405 2270143122260346519739201)
        ·
          refine ⟨1702607341695259889804401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2270143122260346519739201 1702607341695259889804401)
          ·
            refine ⟨1276955506271444917353301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1702607341695259889804401 1276955506271444917353301)
            ·
              refine ⟨7482161169559247562617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1276955506271444917353301 7482161169559247562617)
              ·
                rfl

theorem cell21_295072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 9].length) (baseStart_295072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_295072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_295072 prefixEnd_295072 := by exact prefixLift 295072
  have htrace : WordTrace (prefixWord ++ tailWord_295072) baseStart_295072 baseEnd_295072 := by
    simpa [prefixWord, tailWord_295072, baseEnd_295072] using wordTrace_append hprefix tailTrace_295072
  have hstable : (prefixWord ++ tailWord_295072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295072).length < 2 ^ (prefixWord ++ tailWord_295072).sum := by decide
  have hdescent : baseEnd_295072 < baseStart_295072 := by decide
  rcases family_descends (prefixWord ++ tailWord_295072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295230 : List Nat := [4, 2, 1, 2, 1, 4, 1, 3, 3]
def baseStart_295230 : Nat := 118140960795 + 295230 * 2 ^ 59
def prefixEnd_295230 : Nat := 4983230072969 + 3 ^ 40 * 295230 * 2
def baseEnd_295230 : Nat := 67375508278660064429897

theorem tailTrace_295230 : CollatzResearch.WordTrace tailWord_295230 prefixEnd_295230 67375508278660064429897 := by
  unfold tailWord_295230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1345990340054950764358393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7178615146959737409911429 1345990340054950764358393)
  ·
    refine ⟨1009492755041213073268795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1345990340054950764358393 1009492755041213073268795)
    ·
      refine ⟨1514239132561819609903193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1009492755041213073268795 1514239132561819609903193)
      ·
        refine ⟨1135679349421364707427395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1514239132561819609903193 1135679349421364707427395)
        ·
          refine ⟨1703519024132047061141093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1135679349421364707427395 1703519024132047061141093)
          ·
            refine ⟨319409817024758823963955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1703519024132047061141093 319409817024758823963955)
            ·
              refine ⟨479114725537138235945933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 319409817024758823963955 479114725537138235945933)
              ·
                refine ⟨179668022076426838479725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 479114725537138235945933 179668022076426838479725)
                ·
                  refine ⟨67375508278660064429897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 179668022076426838479725 67375508278660064429897)
                  ·
                    rfl

theorem cell21_295230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_295230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_295230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_295230 prefixEnd_295230 := by exact prefixLift 295230
  have htrace : WordTrace (prefixWord ++ tailWord_295230) baseStart_295230 baseEnd_295230 := by
    simpa [prefixWord, tailWord_295230, baseEnd_295230] using wordTrace_append hprefix tailTrace_295230
  have hstable : (prefixWord ++ tailWord_295230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295230).length < 2 ^ (prefixWord ++ tailWord_295230).sum := by decide
  have hdescent : baseEnd_295230 < baseStart_295230 := by decide
  rcases family_descends (prefixWord ++ tailWord_295230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295306 : List Nat := [3, 1, 2, 5, 1, 1, 1, 4, 3]
def baseStart_295306 : Nat := 118140960795 + 295306 * 2 ^ 59
def prefixEnd_295306 : Nat := 4983230072969 + 3 ^ 40 * 295306 * 2
def baseEnd_295306 : Nat := 67392852514100821163075

theorem tailTrace_295306 : CollatzResearch.WordTrace tailWord_295306 prefixEnd_295306 67392852514100821163075 := by
  unfold tailWord_295306
  simp only [CollatzResearch.WordTrace]
  refine ⟨2692673667041067773658443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7180463112109514063089181 2692673667041067773658443)
  ·
    refine ⟨4039010500561601660487665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2692673667041067773658443 4039010500561601660487665)
    ·
      refine ⟨3029257875421201245365749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4039010500561601660487665 3029257875421201245365749)
      ·
        refine ⟨283992925820737616753039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3029257875421201245365749 283992925820737616753039)
        ·
          refine ⟨425989388731106425129559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283992925820737616753039 425989388731106425129559)
          ·
            refine ⟨638984083096659637694339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 425989388731106425129559 638984083096659637694339)
            ·
              refine ⟨958476124644989456541509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 638984083096659637694339 958476124644989456541509)
              ·
                refine ⟨179714273370935523101533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 958476124644989456541509 179714273370935523101533)
                ·
                  refine ⟨67392852514100821163075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 179714273370935523101533 67392852514100821163075)
                  ·
                    rfl

theorem cell21_295306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 4, 3].length) (baseStart_295306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_295306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_295306 prefixEnd_295306 := by exact prefixLift 295306
  have htrace : WordTrace (prefixWord ++ tailWord_295306) baseStart_295306 baseEnd_295306 := by
    simpa [prefixWord, tailWord_295306, baseEnd_295306] using wordTrace_append hprefix tailTrace_295306
  have hstable : (prefixWord ++ tailWord_295306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295306).length < 2 ^ (prefixWord ++ tailWord_295306).sum := by decide
  have hdescent : baseEnd_295306 < baseStart_295306 := by decide
  rcases family_descends (prefixWord ++ tailWord_295306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295331 : List Nat := [1, 1, 1, 4, 1, 5, 1, 2, 5]
def baseStart_295331 : Nat := 118140960795 + 295331 * 2 ^ 59
def prefixEnd_295331 : Nat := 4983230072969 + 3 ^ 40 * 295331 * 2
def baseEnd_295331 : Nat := 67398557854706333246357

theorem tailTrace_295331 : CollatzResearch.WordTrace tailWord_295331 prefixEnd_295331 67398557854706333246357 := by
  unfold tailWord_295331
  simp only [CollatzResearch.WordTrace]
  refine ⟨10771606493073700364293847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7181070995382466909529231 10771606493073700364293847)
  ·
    refine ⟨16157409739610550546440771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10771606493073700364293847 16157409739610550546440771)
    ·
      refine ⟨24236114609415825819661157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16157409739610550546440771 24236114609415825819661157)
      ·
        refine ⟨4544271489265467341186467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24236114609415825819661157 4544271489265467341186467)
        ·
          refine ⟨6816407233898201011779701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4544271489265467341186467 6816407233898201011779701)
          ·
            refine ⟨639038178177956344854347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6816407233898201011779701 639038178177956344854347)
            ·
              refine ⟨958557267266934517281521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 639038178177956344854347 958557267266934517281521)
              ·
                refine ⟨718917950450200887961141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 958557267266934517281521 718917950450200887961141)
                ·
                  refine ⟨67398557854706333246357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 718917950450200887961141 67398557854706333246357)
                  ·
                    rfl

theorem cell21_295331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 5].length) (baseStart_295331 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_295331 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_295331 prefixEnd_295331 := by exact prefixLift 295331
  have htrace : WordTrace (prefixWord ++ tailWord_295331) baseStart_295331 baseEnd_295331 := by
    simpa [prefixWord, tailWord_295331, baseEnd_295331] using wordTrace_append hprefix tailTrace_295331
  have hstable : (prefixWord ++ tailWord_295331).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295331).length < 2 ^ (prefixWord ++ tailWord_295331).sum := by decide
  have hdescent : baseEnd_295331 < baseStart_295331 := by decide
  rcases family_descends (prefixWord ++ tailWord_295331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295410 : List Nat := [3, 2, 1, 4, 3, 1, 7]
def baseStart_295410 : Nat := 118140960795 + 295410 * 2 ^ 59
def prefixEnd_295410 : Nat := 4983230072969 + 3 ^ 40 * 295410 * 2
def baseEnd_295410 : Nat := 7490731859002194603281

theorem tailTrace_295410 : CollatzResearch.WordTrace tailWord_295410 prefixEnd_295410 7490731859002194603281 := by
  unfold tailWord_295410
  simp only [CollatzResearch.WordTrace]
  refine ⟨2693621964946874214104921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7182991906524997904279789 2693621964946874214104921)
  ·
    refine ⟨2020216473710155660578691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2693621964946874214104921 2020216473710155660578691)
    ·
      refine ⟨3030324710565233490868037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2020216473710155660578691 3030324710565233490868037)
      ·
        refine ⟨568185883230981279537757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3030324710565233490868037 568185883230981279537757)
        ·
          refine ⟨213069706211617979826659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 568185883230981279537757 213069706211617979826659)
          ·
            refine ⟨319604559317426969739989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213069706211617979826659 319604559317426969739989)
            ·
              refine ⟨7490731859002194603281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 319604559317426969739989 7490731859002194603281)
              ·
                rfl

theorem cell21_295410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 7].length) (baseStart_295410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_295410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_295410 prefixEnd_295410 := by exact prefixLift 295410
  have htrace : WordTrace (prefixWord ++ tailWord_295410) baseStart_295410 baseEnd_295410 := by
    simpa [prefixWord, tailWord_295410, baseEnd_295410] using wordTrace_append hprefix tailTrace_295410
  have hstable : (prefixWord ++ tailWord_295410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295410).length < 2 ^ (prefixWord ++ tailWord_295410).sum := by decide
  have hdescent : baseEnd_295410 < baseStart_295410 := by decide
  rcases family_descends (prefixWord ++ tailWord_295410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295421 : List Nat := [1, 4, 1, 1, 1, 3, 1, 3, 6]
def baseStart_295421 : Nat := 118140960795 + 295421 * 2 ^ 59
def prefixEnd_295421 : Nat := 4983230072969 + 3 ^ 40 * 295421 * 2
def baseEnd_295421 : Nat := 67419097080886176746173

theorem tailTrace_295421 : CollatzResearch.WordTrace tailWord_295421 prefixEnd_295421 67419097080886176746173 := by
  unfold tailWord_295421
  simp only [CollatzResearch.WordTrace]
  refine ⟨10774889062747645735070117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7183259375165097156713411 10774889062747645735070117)
  ·
    refine ⟨2020291699265183575325647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10774889062747645735070117 2020291699265183575325647)
    ·
      refine ⟨3030437548897775362988471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2020291699265183575325647 3030437548897775362988471)
      ·
        refine ⟨4545656323346663044482707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3030437548897775362988471 4545656323346663044482707)
        ·
          refine ⟨6818484485019994566724061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4545656323346663044482707 6818484485019994566724061)
          ·
            refine ⟨2556931681882497962521523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6818484485019994566724061 2556931681882497962521523)
            ·
              refine ⟨3835397522823746943782285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2556931681882497962521523 3835397522823746943782285)
              ·
                refine ⟨1438274071058905103918357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3835397522823746943782285 1438274071058905103918357)
                ·
                  refine ⟨67419097080886176746173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1438274071058905103918357 67419097080886176746173)
                  ·
                    rfl

theorem cell21_295421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_295421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_295421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_295421 prefixEnd_295421 := by exact prefixLift 295421
  have htrace : WordTrace (prefixWord ++ tailWord_295421) baseStart_295421 baseEnd_295421 := by
    simpa [prefixWord, tailWord_295421, baseEnd_295421] using wordTrace_append hprefix tailTrace_295421
  have hstable : (prefixWord ++ tailWord_295421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295421).length < 2 ^ (prefixWord ++ tailWord_295421).sum := by decide
  have hdescent : baseEnd_295421 < baseStart_295421 := by decide
  rcases family_descends (prefixWord ++ tailWord_295421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295430 : List Nat := [6, 2, 1, 1, 1, 1, 4, 1, 4]
def baseStart_295430 : Nat := 118140960795 + 295430 * 2 ^ 59
def prefixEnd_295430 : Nat := 4983230072969 + 3 ^ 40 * 295430 * 2
def baseEnd_295430 : Nat := 67421151003504161096155

theorem tailTrace_295430 : CollatzResearch.WordTrace tailWord_295430 prefixEnd_295430 67421151003504161096155 := by
  unfold tailWord_295430
  simp only [CollatzResearch.WordTrace]
  refine ⟨336725541241095008504617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7183478213143360181431829 336725541241095008504617)
  ·
    refine ⟨252544155930821256378463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 336725541241095008504617 252544155930821256378463)
    ·
      refine ⟨378816233896231884567695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252544155930821256378463 378816233896231884567695)
      ·
        refine ⟨568224350844347826851543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 378816233896231884567695 568224350844347826851543)
        ·
          refine ⟨852336526266521740277315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 568224350844347826851543 852336526266521740277315)
          ·
            refine ⟨1278504789399782610415973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 852336526266521740277315 1278504789399782610415973)
            ·
              refine ⟨239719648012459239452995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1278504789399782610415973 239719648012459239452995)
              ·
                refine ⟨359579472018688859179493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 239719648012459239452995 359579472018688859179493)
                ·
                  refine ⟨67421151003504161096155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 359579472018688859179493 67421151003504161096155)
                  ·
                    rfl

theorem cell21_295430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_295430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_295430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_295430 prefixEnd_295430 := by exact prefixLift 295430
  have htrace : WordTrace (prefixWord ++ tailWord_295430) baseStart_295430 baseEnd_295430 := by
    simpa [prefixWord, tailWord_295430, baseEnd_295430] using wordTrace_append hprefix tailTrace_295430
  have hstable : (prefixWord ++ tailWord_295430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295430).length < 2 ^ (prefixWord ++ tailWord_295430).sum := by decide
  have hdescent : baseEnd_295430 < baseStart_295430 := by decide
  rcases family_descends (prefixWord ++ tailWord_295430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295452 : List Nat := [2, 2, 3, 1, 2, 2, 2, 7]
def baseStart_295452 : Nat := 118140960795 + 295452 * 2 ^ 59
def prefixEnd_295452 : Nat := 4983230072969 + 3 ^ 40 * 295452 * 2
def baseEnd_295452 : Nat := 22475390567745670576481

theorem tailTrace_295452 : CollatzResearch.WordTrace tailWord_295452 prefixEnd_295452 22475390567745670576481 := by
  unfold tailWord_295452
  simp only [CollatzResearch.WordTrace]
  refine ⟨5388009862817669014724305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7184013150423558686299073 5388009862817669014724305)
  ·
    refine ⟨4041007397113251761043229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5388009862817669014724305 4041007397113251761043229)
    ·
      refine ⟨1515377773917469410391211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4041007397113251761043229 1515377773917469410391211)
      ·
        refine ⟨2273066660876204115586817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1515377773917469410391211 2273066660876204115586817)
        ·
          refine ⟨1704799995657153086690113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2273066660876204115586817 1704799995657153086690113)
          ·
            refine ⟨1278599996742864815017585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1704799995657153086690113 1278599996742864815017585)
            ·
              refine ⟨958949997557148611263189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1278599996742864815017585 958949997557148611263189)
              ·
                refine ⟨22475390567745670576481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 958949997557148611263189 22475390567745670576481)
                ·
                  rfl

theorem cell21_295452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 7].length) (baseStart_295452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_295452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_295452 prefixEnd_295452 := by exact prefixLift 295452
  have htrace : WordTrace (prefixWord ++ tailWord_295452) baseStart_295452 baseEnd_295452 := by
    simpa [prefixWord, tailWord_295452, baseEnd_295452] using wordTrace_append hprefix tailTrace_295452
  have hstable : (prefixWord ++ tailWord_295452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295452).length < 2 ^ (prefixWord ++ tailWord_295452).sum := by decide
  have hdescent : baseEnd_295452 < baseStart_295452 := by decide
  rcases family_descends (prefixWord ++ tailWord_295452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295562 : List Nat := [3, 1, 2, 3, 3, 2, 2, 5]
def baseStart_295562 : Nat := 118140960795 + 295562 * 2 ^ 59
def prefixEnd_295562 : Nat := 4983230072969 + 3 ^ 40 * 295562 * 2
def baseEnd_295562 : Nat := 22483758400633754965295

theorem tailTrace_295562 : CollatzResearch.WordTrace tailWord_295562 prefixEnd_295562 22483758400633754965295 := by
  unfold tailWord_295562
  simp only [CollatzResearch.WordTrace]
  refine ⟨2695007938809206703988235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7186687836824551210635293 2695007938809206703988235)
  ·
    refine ⟨4042511908213810055982353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2695007938809206703988235 4042511908213810055982353)
    ·
      refine ⟨3031883931160357541986765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4042511908213810055982353 3031883931160357541986765)
      ·
        refine ⟨1136956474185134078245037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3031883931160357541986765 1136956474185134078245037)
        ·
          refine ⟨426358677819425279341889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1136956474185134078245037 426358677819425279341889)
          ·
            refine ⟨319769008364568959506417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 426358677819425279341889 319769008364568959506417)
            ·
              refine ⟨239826756273426719629813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 319769008364568959506417 239826756273426719629813)
              ·
                refine ⟨22483758400633754965295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 239826756273426719629813 22483758400633754965295)
                ·
                  rfl

theorem cell21_295562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 5].length) (baseStart_295562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_295562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_295562 prefixEnd_295562 := by exact prefixLift 295562
  have htrace : WordTrace (prefixWord ++ tailWord_295562) baseStart_295562 baseEnd_295562 := by
    simpa [prefixWord, tailWord_295562, baseEnd_295562] using wordTrace_append hprefix tailTrace_295562
  have hstable : (prefixWord ++ tailWord_295562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295562).length < 2 ^ (prefixWord ++ tailWord_295562).sum := by decide
  have hdescent : baseEnd_295562 < baseStart_295562 := by decide
  rcases family_descends (prefixWord ++ tailWord_295562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295652 : List Nat := [2, 3, 1, 1, 1, 5, 1, 4, 3]
def baseStart_295652 : Nat := 118140960795 + 295652 * 2 ^ 59
def prefixEnd_295652 : Nat := 4983230072969 + 3 ^ 40 * 295652 * 2
def baseEnd_295652 : Nat := 67471814428081108395701

theorem tailTrace_295652 : CollatzResearch.WordTrace tailWord_295652 prefixEnd_295652 67471814428081108395701 := by
  unfold tailWord_295652
  simp only [CollatzResearch.WordTrace]
  refine ⟨5391657162455386093364605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7188876216607181457819473 5391657162455386093364605)
  ·
    refine ⟨2021871435920769785011727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5391657162455386093364605 2021871435920769785011727)
    ·
      refine ⟨3032807153881154677517591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2021871435920769785011727 3032807153881154677517591)
      ·
        refine ⟨4549210730821732016276387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3032807153881154677517591 4549210730821732016276387)
        ·
          refine ⟨6823816096232598024414581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4549210730821732016276387 6823816096232598024414581)
          ·
            refine ⟨639732759021806064788867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6823816096232598024414581 639732759021806064788867)
            ·
              refine ⟨959599138532709097183301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 639732759021806064788867 959599138532709097183301)
              ·
                refine ⟨179924838474882955721869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 959599138532709097183301 179924838474882955721869)
                ·
                  refine ⟨67471814428081108395701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 179924838474882955721869 67471814428081108395701)
                  ·
                    rfl

theorem cell21_295652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 4, 3].length) (baseStart_295652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_295652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_295652 prefixEnd_295652 := by exact prefixLift 295652
  have htrace : WordTrace (prefixWord ++ tailWord_295652) baseStart_295652 baseEnd_295652 := by
    simpa [prefixWord, tailWord_295652, baseEnd_295652] using wordTrace_append hprefix tailTrace_295652
  have hstable : (prefixWord ++ tailWord_295652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295652).length < 2 ^ (prefixWord ++ tailWord_295652).sum := by decide
  have hdescent : baseEnd_295652 < baseStart_295652 := by decide
  rcases family_descends (prefixWord ++ tailWord_295652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295666 : List Nat := [3, 2, 1, 3, 1, 2, 2, 3, 4]
def baseStart_295666 : Nat := 118140960795 + 295666 * 2 ^ 59
def prefixEnd_295666 : Nat := 4983230072969 + 3 ^ 40 * 295666 * 2
def baseEnd_295666 : Nat := 67475009418820195162339

theorem tailTrace_295666 : CollatzResearch.WordTrace tailWord_295666 prefixEnd_295666 67475009418820195162339 := by
  unfold tailWord_295666
  simp only [CollatzResearch.WordTrace]
  refine ⟨2695956236715013144434713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7189216631240035051825901 2695956236715013144434713)
  ·
    refine ⟨2021967177536259858326035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2695956236715013144434713 2021967177536259858326035)
    ·
      refine ⟨3032950766304389787489053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2021967177536259858326035 3032950766304389787489053)
      ·
        refine ⟨1137356537364146170308395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3032950766304389787489053 1137356537364146170308395)
        ·
          refine ⟨1706034806046219255462593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1137356537364146170308395 1706034806046219255462593)
          ·
            refine ⟨1279526104534664441596945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1706034806046219255462593 1279526104534664441596945)
            ·
              refine ⟨959644578400998331197709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1279526104534664441596945 959644578400998331197709)
              ·
                refine ⟨359866716900374374199141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 959644578400998331197709 359866716900374374199141)
                ·
                  refine ⟨67475009418820195162339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 359866716900374374199141 67475009418820195162339)
                  ·
                    rfl

theorem cell21_295666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_295666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_295666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_295666 prefixEnd_295666 := by exact prefixLift 295666
  have htrace : WordTrace (prefixWord ++ tailWord_295666) baseStart_295666 baseEnd_295666 := by
    simpa [prefixWord, tailWord_295666, baseEnd_295666] using wordTrace_append hprefix tailTrace_295666
  have hstable : (prefixWord ++ tailWord_295666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295666).length < 2 ^ (prefixWord ++ tailWord_295666).sum := by decide
  have hdescent : baseEnd_295666 < baseStart_295666 := by decide
  rcases family_descends (prefixWord ++ tailWord_295666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295694 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 9]
def baseStart_295694 : Nat := 118140960795 + 295694 * 2 ^ 59
def prefixEnd_295694 : Nat := 4983230072969 + 3 ^ 40 * 295694 * 2
def baseEnd_295694 : Nat := 67481399400298368695615

theorem tailTrace_295694 : CollatzResearch.WordTrace tailWord_295694 prefixEnd_295694 67481399400298368695615 := by
  unfold tailWord_295694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1348105773844826669969767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7189897460505742239838757 1348105773844826669969767)
  ·
    refine ⟨2022158660767240004954651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1348105773844826669969767 2022158660767240004954651)
    ·
      refine ⟨3033237991150860007431977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2022158660767240004954651 3033237991150860007431977)
      ·
        refine ⟨2274928493363145005573983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3033237991150860007431977 2274928493363145005573983)
        ·
          refine ⟨3412392740044717508360975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2274928493363145005573983 3412392740044717508360975)
          ·
            refine ⟨5118589110067076262541463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3412392740044717508360975 5118589110067076262541463)
            ·
              refine ⟨7677883665100614393812195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5118589110067076262541463 7677883665100614393812195)
              ·
                refine ⟨11516825497650921590718293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7677883665100614393812195 11516825497650921590718293)
                ·
                  refine ⟨67481399400298368695615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11516825497650921590718293 67481399400298368695615)
                  ·
                    rfl

theorem cell21_295694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_295694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_295694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_295694 prefixEnd_295694 := by exact prefixLift 295694
  have htrace : WordTrace (prefixWord ++ tailWord_295694) baseStart_295694 baseEnd_295694 := by
    simpa [prefixWord, tailWord_295694, baseEnd_295694] using wordTrace_append hprefix tailTrace_295694
  have hstable : (prefixWord ++ tailWord_295694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295694).length < 2 ^ (prefixWord ++ tailWord_295694).sum := by decide
  have hdescent : baseEnd_295694 < baseStart_295694 := by decide
  rcases family_descends (prefixWord ++ tailWord_295694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295711 : List Nat := [1, 1, 2, 4, 2, 3, 2, 1, 5]
def baseStart_295711 : Nat := 118140960795 + 295711 * 2 ^ 59
def prefixEnd_295711 : Nat := 4983230072969 + 3 ^ 40 * 295711 * 2
def baseEnd_295711 : Nat := 67485279031910116912247

theorem tailTrace_295711 : CollatzResearch.WordTrace tailWord_295711 prefixEnd_295711 67485279031910116912247 := by
  unfold tailWord_295711
  simp only [CollatzResearch.WordTrace]
  refine ⟨10785466231697025263126987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7190310821131350175417991 10785466231697025263126987)
  ·
    refine ⟨16178199347545537894690481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10785466231697025263126987 16178199347545537894690481)
    ·
      refine ⟨12133649510659153421017861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16178199347545537894690481 12133649510659153421017861)
      ·
        refine ⟨2275059283248591266440849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12133649510659153421017861 2275059283248591266440849)
        ·
          refine ⟨1706294462436443449830637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2275059283248591266440849 1706294462436443449830637)
          ·
            refine ⟨639860423413666293686489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1706294462436443449830637 639860423413666293686489)
            ·
              refine ⟨479895317560249720264867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 639860423413666293686489 479895317560249720264867)
              ·
                refine ⟨719842976340374580397301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 479895317560249720264867 719842976340374580397301)
                ·
                  refine ⟨67485279031910116912247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 719842976340374580397301 67485279031910116912247)
                  ·
                    rfl

theorem cell21_295711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 5].length) (baseStart_295711 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_295711 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_295711 prefixEnd_295711 := by exact prefixLift 295711
  have htrace : WordTrace (prefixWord ++ tailWord_295711) baseStart_295711 baseEnd_295711 := by
    simpa [prefixWord, tailWord_295711, baseEnd_295711] using wordTrace_append hprefix tailTrace_295711
  have hstable : (prefixWord ++ tailWord_295711).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295711).length < 2 ^ (prefixWord ++ tailWord_295711).sum := by decide
  have hdescent : baseEnd_295711 < baseStart_295711 := by decide
  rcases family_descends (prefixWord ++ tailWord_295711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295756 : List Nat := [2, 2, 1, 3, 3, 3, 7]
def baseStart_295756 : Nat := 118140960795 + 295756 * 2 ^ 59
def prefixEnd_295756 : Nat := 4983230072969 + 3 ^ 40 * 295756 * 2
def baseEnd_295756 : Nat := 7499505405000004295795

theorem tailTrace_295756 : CollatzResearch.WordTrace tailWord_295756 prefixEnd_295756 7499505405000004295795 := by
  unfold tailWord_295756
  simp only [CollatzResearch.WordTrace]
  refine ⟨5393553758266998974257561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7191405011022665299010081 5393553758266998974257561)
  ·
    refine ⟨4045165318700249230693171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5393553758266998974257561 4045165318700249230693171)
    ·
      refine ⟨6067747978050373846039757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4045165318700249230693171 6067747978050373846039757)
      ·
        refine ⟨2275405491768890192264909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6067747978050373846039757 2275405491768890192264909)
        ·
          refine ⟨853277059413333822099341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2275405491768890192264909 853277059413333822099341)
          ·
            refine ⟨319978897280000183287253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 853277059413333822099341 319978897280000183287253)
            ·
              refine ⟨7499505405000004295795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 319978897280000183287253 7499505405000004295795)
              ·
                rfl

theorem cell21_295756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 7].length) (baseStart_295756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_295756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_295756 prefixEnd_295756 := by exact prefixLift 295756
  have htrace : WordTrace (prefixWord ++ tailWord_295756) baseStart_295756 baseEnd_295756 := by
    simpa [prefixWord, tailWord_295756, baseEnd_295756] using wordTrace_append hprefix tailTrace_295756
  have hstable : (prefixWord ++ tailWord_295756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295756).length < 2 ^ (prefixWord ++ tailWord_295756).sum := by decide
  have hdescent : baseEnd_295756 < baseStart_295756 := by decide
  rcases family_descends (prefixWord ++ tailWord_295756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295815 : List Nat := [1, 1, 4, 2, 3, 10]
def baseStart_295815 : Nat := 118140960795 + 295815 * 2 ^ 59
def prefixEnd_295815 : Nat := 4983230072969 + 3 ^ 40 * 295815 * 2
def baseEnd_295815 : Nat := 2500333824030705451063

theorem tailTrace_295815 : CollatzResearch.WordTrace tailWord_295815 prefixEnd_295815 2500333824030705451063 := by
  unfold tailWord_295815
  simp only [CollatzResearch.WordTrace]
  refine ⟨10789259423320251024912899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7192839615546834016608599 10789259423320251024912899)
  ·
    refine ⟨16183889134980376537369349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10789259423320251024912899 16183889134980376537369349)
    ·
      refine ⟨3034479212808820600756753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16183889134980376537369349 3034479212808820600756753)
      ·
        refine ⟨2275859409606615450567565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3034479212808820600756753 2275859409606615450567565)
        ·
          refine ⟨853447278602480793962837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2275859409606615450567565 853447278602480793962837)
          ·
            refine ⟨2500333824030705451063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 853447278602480793962837 2500333824030705451063)
            ·
              rfl

theorem cell21_295815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 10].length) (baseStart_295815 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_295815 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_295815 prefixEnd_295815 := by exact prefixLift 295815
  have htrace : WordTrace (prefixWord ++ tailWord_295815) baseStart_295815 baseEnd_295815 := by
    simpa [prefixWord, tailWord_295815, baseEnd_295815] using wordTrace_append hprefix tailTrace_295815
  have hstable : (prefixWord ++ tailWord_295815).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295815).length < 2 ^ (prefixWord ++ tailWord_295815).sum := by decide
  have hdescent : baseEnd_295815 < baseStart_295815 := by decide
  rcases family_descends (prefixWord ++ tailWord_295815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295818 : List Nat := [3, 1, 2, 4, 1, 1, 1, 4, 4]
def baseStart_295818 : Nat := 118140960795 + 295818 * 2 ^ 59
def prefixEnd_295818 : Nat := 4983230072969 + 3 ^ 40 * 295818 * 2
def baseEnd_295818 : Nat := 67509697889701708628695

theorem tailTrace_295818 : CollatzResearch.WordTrace tailWord_295818 prefixEnd_295818 67509697889701708628695 := by
  unfold tailWord_295818
  simp only [CollatzResearch.WordTrace]
  refine ⟨2697342210577345634318027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7192912561539588358181405 2697342210577345634318027)
  ·
    refine ⟨4046013315866018451477041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2697342210577345634318027 4046013315866018451477041)
    ·
      refine ⟨3034509986899513838607781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4046013315866018451477041 3034509986899513838607781)
      ·
        refine ⟨568970622543658844738959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3034509986899513838607781 568970622543658844738959)
        ·
          refine ⟨853455933815488267108439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 568970622543658844738959 853455933815488267108439)
          ·
            refine ⟨1280183900723232400662659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 853455933815488267108439 1280183900723232400662659)
            ·
              refine ⟨1920275851084848600993989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1280183900723232400662659 1920275851084848600993989)
              ·
                refine ⟨360051722078409112686373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1920275851084848600993989 360051722078409112686373)
                ·
                  refine ⟨67509697889701708628695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 360051722078409112686373 67509697889701708628695)
                  ·
                    rfl

theorem cell21_295818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 4].length) (baseStart_295818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_295818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_295818 prefixEnd_295818 := by exact prefixLift 295818
  have htrace : WordTrace (prefixWord ++ tailWord_295818) baseStart_295818 baseEnd_295818 := by
    simpa [prefixWord, tailWord_295818, baseEnd_295818] using wordTrace_append hprefix tailTrace_295818
  have hstable : (prefixWord ++ tailWord_295818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295818).length < 2 ^ (prefixWord ++ tailWord_295818).sum := by decide
  have hdescent : baseEnd_295818 < baseStart_295818 := by decide
  rcases family_descends (prefixWord ++ tailWord_295818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295863 : List Nat := [1, 1, 3, 1, 3, 1, 3, 5, 3]
def baseStart_295863 : Nat := 118140960795 + 295863 * 2 ^ 59
def prefixEnd_295863 : Nat := 4983230072969 + 3 ^ 40 * 295863 * 2
def baseEnd_295863 : Nat := 67519967502791630378603

theorem tailTrace_295863 : CollatzResearch.WordTrace tailWord_295863 prefixEnd_295863 67519967502791630378603 := by
  unfold tailWord_295863
  simp only [CollatzResearch.WordTrace]
  refine ⟨10791010127146355222660243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7194006751430903481773495 10791010127146355222660243)
  ·
    refine ⟨16186515190719532833990365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10791010127146355222660243 16186515190719532833990365)
    ·
      refine ⟨6069943196519824812746387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16186515190719532833990365 6069943196519824812746387)
      ·
        refine ⟨9104914794779737219119581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6069943196519824812746387 9104914794779737219119581)
        ·
          refine ⟨3414343048042401457169843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9104914794779737219119581 3414343048042401457169843)
          ·
            refine ⟨5121514572063602185754765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3414343048042401457169843 5121514572063602185754765)
            ·
              refine ⟨1920567964523850819658037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5121514572063602185754765 1920567964523850819658037)
              ·
                refine ⟨180053246674111014342941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1920567964523850819658037 180053246674111014342941)
                ·
                  refine ⟨67519967502791630378603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 180053246674111014342941 67519967502791630378603)
                  ·
                    rfl

theorem cell21_295863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 5, 3].length) (baseStart_295863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_295863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_295863 prefixEnd_295863 := by exact prefixLift 295863
  have htrace : WordTrace (prefixWord ++ tailWord_295863) baseStart_295863 baseEnd_295863 := by
    simpa [prefixWord, tailWord_295863, baseEnd_295863] using wordTrace_append hprefix tailTrace_295863
  have hstable : (prefixWord ++ tailWord_295863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295863).length < 2 ^ (prefixWord ++ tailWord_295863).sum := by decide
  have hdescent : baseEnd_295863 < baseStart_295863 := by decide
  rcases family_descends (prefixWord ++ tailWord_295863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295967 : List Nat := [1, 1, 2, 4, 1, 3, 2, 7]
def baseStart_295967 : Nat := 118140960795 + 295967 * 2 ^ 59
def prefixEnd_295967 : Nat := 4983230072969 + 3 ^ 40 * 295967 * 2
def baseEnd_295967 : Nat := 22514567239903520215019

theorem tailTrace_295967 : CollatzResearch.WordTrace tailWord_295967 prefixEnd_295967 22514567239903520215019 := by
  unfold tailWord_295967
  simp only [CollatzResearch.WordTrace]
  refine ⟨10794803318769580984446155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7196535545846387322964103 10794803318769580984446155)
  ·
    refine ⟨16192204978154371476669233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10794803318769580984446155 16192204978154371476669233)
    ·
      refine ⟨12144153733615778607501925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16192204978154371476669233 12144153733615778607501925)
      ·
        refine ⟨2277028825052958488906611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12144153733615778607501925 2277028825052958488906611)
        ·
          refine ⟨3415543237579437733359917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2277028825052958488906611 3415543237579437733359917)
          ·
            refine ⟨1280828714092289150009969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3415543237579437733359917 1280828714092289150009969)
            ·
              refine ⟨960621535569216862507477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1280828714092289150009969 960621535569216862507477)
              ·
                refine ⟨22514567239903520215019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 960621535569216862507477 22514567239903520215019)
                ·
                  rfl

theorem cell21_295967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 7].length) (baseStart_295967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_295967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_295967 prefixEnd_295967 := by exact prefixLift 295967
  have htrace : WordTrace (prefixWord ++ tailWord_295967) baseStart_295967 baseEnd_295967 := by
    simpa [prefixWord, tailWord_295967, baseEnd_295967] using wordTrace_append hprefix tailTrace_295967
  have hstable : (prefixWord ++ tailWord_295967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295967).length < 2 ^ (prefixWord ++ tailWord_295967).sum := by decide
  have hdescent : baseEnd_295967 < baseStart_295967 := by decide
  rcases family_descends (prefixWord ++ tailWord_295967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295990 : List Nat := [5, 1, 2, 1, 1, 4, 2, 2, 3]
def baseStart_295990 : Nat := 118140960795 + 295990 * 2 ^ 59
def prefixEnd_295990 : Nat := 4983230072969 + 3 ^ 40 * 295990 * 2
def baseEnd_295990 : Nat := 67548950633067631761677

theorem tailTrace_295990 : CollatzResearch.WordTrace tailWord_295990 prefixEnd_295990 67548950633067631761677 := by
  unfold tailWord_295990
  simp only [CollatzResearch.WordTrace]
  refine ⟨674727637355390994533339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7197094798457503941688949 674727637355390994533339)
  ·
    refine ⟨1012091456033086491800009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 674727637355390994533339 1012091456033086491800009)
    ·
      refine ⟨759068592024814868850007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1012091456033086491800009 759068592024814868850007)
      ·
        refine ⟨1138602888037222303275011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 759068592024814868850007 1138602888037222303275011)
        ·
          refine ⟨1707904332055833454912517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1138602888037222303275011 1707904332055833454912517)
          ·
            refine ⟨320232062260468772796097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1707904332055833454912517 320232062260468772796097)
            ·
              refine ⟨240174046695351579597073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 320232062260468772796097 240174046695351579597073)
              ·
                refine ⟨180130535021513684697805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 240174046695351579597073 180130535021513684697805)
                ·
                  refine ⟨67548950633067631761677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 180130535021513684697805 67548950633067631761677)
                  ·
                    rfl

theorem cell21_295990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_295990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_295990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_295990 prefixEnd_295990 := by exact prefixLift 295990
  have htrace : WordTrace (prefixWord ++ tailWord_295990) baseStart_295990 baseEnd_295990 := by
    simpa [prefixWord, tailWord_295990, baseEnd_295990] using wordTrace_append hprefix tailTrace_295990
  have hstable : (prefixWord ++ tailWord_295990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295990).length < 2 ^ (prefixWord ++ tailWord_295990).sum := by decide
  have hdescent : baseEnd_295990 < baseStart_295990 := by decide
  rcases family_descends (prefixWord ++ tailWord_295990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296001 : List Nat := [1, 2, 5, 1, 3, 2, 1, 6]
def baseStart_296001 : Nat := 118140960795 + 296001 * 2 ^ 59
def prefixEnd_296001 : Nat := 4983230072969 + 3 ^ 40 * 296001 * 2
def baseEnd_296001 : Nat := 22517153660978019026107

theorem tailTrace_296001 : CollatzResearch.WordTrace tailWord_296001 prefixEnd_296001 22517153660978019026107 := by
  unfold tailWord_296001
  simp only [CollatzResearch.WordTrace]
  refine ⟨10796043400646404791183857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7197362267097603194122571 10796043400646404791183857)
  ·
    refine ⟨8097032550484803593387893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10796043400646404791183857 8097032550484803593387893)
    ·
      refine ⟨759096801607950336880115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8097032550484803593387893 759096801607950336880115)
      ·
        refine ⟨1138645202411925505320173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 759096801607950336880115 1138645202411925505320173)
        ·
          refine ⟨426991950904472064495065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1138645202411925505320173 426991950904472064495065)
          ·
            refine ⟨320243963178354048371299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 426991950904472064495065 320243963178354048371299)
            ·
              refine ⟨480365944767531072556949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 320243963178354048371299 480365944767531072556949)
              ·
                refine ⟨22517153660978019026107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 480365944767531072556949 22517153660978019026107)
                ·
                  rfl

theorem cell21_296001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 6].length) (baseStart_296001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_296001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_296001 prefixEnd_296001 := by exact prefixLift 296001
  have htrace : WordTrace (prefixWord ++ tailWord_296001) baseStart_296001 baseEnd_296001 := by
    simpa [prefixWord, tailWord_296001, baseEnd_296001] using wordTrace_append hprefix tailTrace_296001
  have hstable : (prefixWord ++ tailWord_296001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296001).length < 2 ^ (prefixWord ++ tailWord_296001).sum := by decide
  have hdescent : baseEnd_296001 < baseStart_296001 := by decide
  rcases family_descends (prefixWord ++ tailWord_296001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296012 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 8]
def baseStart_296012 : Nat := 118140960795 + 296012 * 2 ^ 59
def prefixEnd_296012 : Nat := 4983230072969 + 3 ^ 40 * 296012 * 2
def baseEnd_296012 : Nat := 67553971332800482394965

theorem tailTrace_296012 : CollatzResearch.WordTrace tailWord_296012 prefixEnd_296012 67553971332800482394965 := by
  unfold tailWord_296012
  simp only [CollatzResearch.WordTrace]
  refine ⟨5398222301803276834917145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7197629735737702446556193 5398222301803276834917145)
  ·
    refine ⟨4048666726352457626187859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5398222301803276834917145 4048666726352457626187859)
    ·
      refine ⟨6073000089528686439281789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4048666726352457626187859 6073000089528686439281789)
      ·
        refine ⟨2277375033573257414730671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6073000089528686439281789 2277375033573257414730671)
        ·
          refine ⟨3416062550359886122096007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2277375033573257414730671 3416062550359886122096007)
          ·
            refine ⟨5124093825539829183144011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3416062550359886122096007 5124093825539829183144011)
            ·
              refine ⟨7686140738309743774716017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5124093825539829183144011 7686140738309743774716017)
              ·
                refine ⟨5764605553732307831037013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7686140738309743774716017 5764605553732307831037013)
                ·
                  refine ⟨67553971332800482394965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5764605553732307831037013 67553971332800482394965)
                  ·
                    rfl

theorem cell21_296012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_296012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_296012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_296012 prefixEnd_296012 := by exact prefixLift 296012
  have htrace : WordTrace (prefixWord ++ tailWord_296012) baseStart_296012 baseEnd_296012 := by
    simpa [prefixWord, tailWord_296012, baseEnd_296012] using wordTrace_append hprefix tailTrace_296012
  have hstable : (prefixWord ++ tailWord_296012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296012).length < 2 ^ (prefixWord ++ tailWord_296012).sum := by decide
  have hdescent : baseEnd_296012 < baseStart_296012 := by decide
  rcases family_descends (prefixWord ++ tailWord_296012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296046 : List Nat := [4, 1, 2, 2, 1, 2, 3, 2, 4]
def baseStart_296046 : Nat := 118140960795 + 296046 * 2 ^ 59
def prefixEnd_296046 : Nat := 4983230072969 + 3 ^ 40 * 296046 * 2
def baseEnd_296046 : Nat := 67561730596023978828229

theorem tailTrace_296046 : CollatzResearch.WordTrace tailWord_296046 prefixEnd_296046 67561730596023978828229 := by
  unfold tailWord_296046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1349710585685422184571499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7198456456988918317714661 1349710585685422184571499)
  ·
    refine ⟨2024565878528133276857249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1349710585685422184571499 2024565878528133276857249)
    ·
      refine ⟨1518424408896099957642937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2024565878528133276857249 1518424408896099957642937)
      ·
        refine ⟨1138818306672074968232203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1518424408896099957642937 1138818306672074968232203)
        ·
          refine ⟨1708227460008112452348305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1138818306672074968232203 1708227460008112452348305)
          ·
            refine ⟨1281170595006084339261229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1708227460008112452348305 1281170595006084339261229)
            ·
              refine ⟨480438973127281627222961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1281170595006084339261229 480438973127281627222961)
              ·
                refine ⟨360329229845461220417221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 480438973127281627222961 360329229845461220417221)
                ·
                  refine ⟨67561730596023978828229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 360329229845461220417221 67561730596023978828229)
                  ·
                    rfl

theorem cell21_296046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_296046 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_296046 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_296046 prefixEnd_296046 := by exact prefixLift 296046
  have htrace : WordTrace (prefixWord ++ tailWord_296046) baseStart_296046 baseEnd_296046 := by
    simpa [prefixWord, tailWord_296046, baseEnd_296046] using wordTrace_append hprefix tailTrace_296046
  have hstable : (prefixWord ++ tailWord_296046).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296046).length < 2 ^ (prefixWord ++ tailWord_296046).sum := by decide
  have hdescent : baseEnd_296046 < baseStart_296046 := by decide
  rcases family_descends (prefixWord ++ tailWord_296046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296074 : List Nat := [3, 1, 2, 3, 1, 1, 1, 4, 5]
def baseStart_296074 : Nat := 118140960795 + 296074 * 2 ^ 59
def prefixEnd_296074 : Nat := 4983230072969 + 3 ^ 40 * 296074 * 2
def baseEnd_296074 : Nat := 67568120577502152361505

theorem tailTrace_296074 : CollatzResearch.WordTrace tailWord_296074 prefixEnd_296074 67568120577502152361505 := by
  unfold tailWord_296074
  simp only [CollatzResearch.WordTrace]
  refine ⟨2699676482345484564647819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7199137286254625505727517 2699676482345484564647819)
  ·
    refine ⟨4049514723518226846971729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2699676482345484564647819 4049514723518226846971729)
    ·
      refine ⟨3037136042638670135228797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4049514723518226846971729 3037136042638670135228797)
      ·
        refine ⟨1138926015989501300710799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3037136042638670135228797 1138926015989501300710799)
        ·
          refine ⟨1708389023984251951066199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1138926015989501300710799 1708389023984251951066199)
          ·
            refine ⟨2562583535976377926599299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1708389023984251951066199 2562583535976377926599299)
            ·
              refine ⟨3843875303964566889898949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2562583535976377926599299 3843875303964566889898949)
              ·
                refine ⟨720726619493356291856053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3843875303964566889898949 720726619493356291856053)
                ·
                  refine ⟨67568120577502152361505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 720726619493356291856053 67568120577502152361505)
                  ·
                    rfl

theorem cell21_296074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_296074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_296074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_296074 prefixEnd_296074 := by exact prefixLift 296074
  have htrace : WordTrace (prefixWord ++ tailWord_296074) baseStart_296074 baseEnd_296074 := by
    simpa [prefixWord, tailWord_296074, baseEnd_296074] using wordTrace_append hprefix tailTrace_296074
  have hstable : (prefixWord ++ tailWord_296074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296074).length < 2 ^ (prefixWord ++ tailWord_296074).sum := by decide
  have hdescent : baseEnd_296074 < baseStart_296074 := by decide
  rcases family_descends (prefixWord ++ tailWord_296074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296119 : List Nat := [1, 1, 3, 1, 4, 1, 4, 6]
def baseStart_296119 : Nat := 118140960795 + 296119 * 2 ^ 59
def prefixEnd_296119 : Nat := 4983230072969 + 3 ^ 40 * 296119 * 2
def baseEnd_296119 : Nat := 22526130063530691370471

theorem tailTrace_296119 : CollatzResearch.WordTrace tailWord_296119 prefixEnd_296119 22526130063530691370471 := by
  unfold tailWord_296119
  simp only [CollatzResearch.WordTrace]
  refine ⟨10800347214218910943979411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7200231476145940629319607 10800347214218910943979411)
  ·
    refine ⟨16200520821328366415969117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10800347214218910943979411 16200520821328366415969117)
    ·
      refine ⟨6075195307998137405988419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16200520821328366415969117 6075195307998137405988419)
      ·
        refine ⟨9112792961997206108982629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6075195307998137405988419 9112792961997206108982629)
        ·
          refine ⟨1708648680374476145434243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9112792961997206108982629 1708648680374476145434243)
          ·
            refine ⟨2562973020561714218151365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1708648680374476145434243 2562973020561714218151365)
            ·
              refine ⟨480557441355321415903381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2562973020561714218151365 480557441355321415903381)
              ·
                refine ⟨22526130063530691370471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 480557441355321415903381 22526130063530691370471)
                ·
                  rfl

theorem cell21_296119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 6].length) (baseStart_296119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_296119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_296119 prefixEnd_296119 := by exact prefixLift 296119
  have htrace : WordTrace (prefixWord ++ tailWord_296119) baseStart_296119 baseEnd_296119 := by
    simpa [prefixWord, tailWord_296119, baseEnd_296119] using wordTrace_append hprefix tailTrace_296119
  have hstable : (prefixWord ++ tailWord_296119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296119).length < 2 ^ (prefixWord ++ tailWord_296119).sum := by decide
  have hdescent : baseEnd_296119 < baseStart_296119 := by decide
  rcases family_descends (prefixWord ++ tailWord_296119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296133 : List Nat := [1, 3, 1, 1, 1, 1, 3, 3, 7]
def baseStart_296133 : Nat := 118140960795 + 296133 * 2 ^ 59
def prefixEnd_296133 : Nat := 4983230072969 + 3 ^ 40 * 296133 * 2
def baseEnd_296133 : Nat := 67581585181331160878051

theorem tailTrace_296133 : CollatzResearch.WordTrace tailWord_296133 prefixEnd_296133 67581585181331160878051 := by
  unfold tailWord_296133
  simp only [CollatzResearch.WordTrace]
  refine ⟨10800857836168191334989053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7200571890778794223326035 10800857836168191334989053)
  ·
    refine ⟨4050321688563071750620895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10800857836168191334989053 4050321688563071750620895)
    ·
      refine ⟨6075482532844607625931343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4050321688563071750620895 6075482532844607625931343)
      ·
        refine ⟨9113223799266911438897015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6075482532844607625931343 9113223799266911438897015)
        ·
          refine ⟨13669835698900367158345523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9113223799266911438897015 13669835698900367158345523)
          ·
            refine ⟨20504753548350550737518285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13669835698900367158345523 20504753548350550737518285)
            ·
              refine ⟨7689282580631456526569357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20504753548350550737518285 7689282580631456526569357)
              ·
                refine ⟨2883480967736796197463509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7689282580631456526569357 2883480967736796197463509)
                ·
                  refine ⟨67581585181331160878051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2883480967736796197463509 67581585181331160878051)
                  ·
                    rfl

theorem cell21_296133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_296133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_296133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_296133 prefixEnd_296133 := by exact prefixLift 296133
  have htrace : WordTrace (prefixWord ++ tailWord_296133) baseStart_296133 baseEnd_296133 := by
    simpa [prefixWord, tailWord_296133, baseEnd_296133] using wordTrace_append hprefix tailTrace_296133
  have hstable : (prefixWord ++ tailWord_296133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296133).length < 2 ^ (prefixWord ++ tailWord_296133).sum := by decide
  have hdescent : baseEnd_296133 < baseStart_296133 := by decide
  rcases family_descends (prefixWord ++ tailWord_296133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296164 : List Nat := [2, 3, 1, 1, 1, 2, 2, 3, 6]
def baseStart_296164 : Nat := 118140960795 + 296164 * 2 ^ 59
def prefixEnd_296164 : Nat := 4983230072969 + 3 ^ 40 * 296164 * 2
def baseEnd_296164 : Nat := 67588659803681995861321

theorem tailTrace_296164 : CollatzResearch.WordTrace tailWord_296164 prefixEnd_296164 67588659803681995861321 := by
  unfold tailWord_296164
  simp only [CollatzResearch.WordTrace]
  refine ⟨5400994249527941814683773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7201325666037255752911697 5400994249527941814683773)
  ·
    refine ⟨2025372843572978180506415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5400994249527941814683773 2025372843572978180506415)
    ·
      refine ⟨3038059265359467270759623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2025372843572978180506415 3038059265359467270759623)
      ·
        refine ⟨4557088898039200906139435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3038059265359467270759623 4557088898039200906139435)
        ·
          refine ⟨6835633347058801359209153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4557088898039200906139435 6835633347058801359209153)
          ·
            refine ⟨5126725010294101019406865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6835633347058801359209153 5126725010294101019406865)
            ·
              refine ⟨3845043757720575764555149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5126725010294101019406865 3845043757720575764555149)
              ·
                refine ⟨1441891409145215911708181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3845043757720575764555149 1441891409145215911708181)
                ·
                  refine ⟨67588659803681995861321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1441891409145215911708181 67588659803681995861321)
                  ·
                    rfl

theorem cell21_296164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_296164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_296164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_296164 prefixEnd_296164 := by exact prefixLift 296164
  have htrace : WordTrace (prefixWord ++ tailWord_296164) baseStart_296164 baseEnd_296164 := by
    simpa [prefixWord, tailWord_296164, baseEnd_296164] using wordTrace_append hprefix tailTrace_296164
  have hstable : (prefixWord ++ tailWord_296164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296164).length < 2 ^ (prefixWord ++ tailWord_296164).sum := by decide
  have hdescent : baseEnd_296164 < baseStart_296164 := by decide
  rcases family_descends (prefixWord ++ tailWord_296164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296209 : List Nat := [1, 2, 2, 1, 1, 4, 1, 2, 7]
def baseStart_296209 : Nat := 118140960795 + 296209 * 2 ^ 59
def prefixEnd_296209 : Nat := 4983230072969 + 3 ^ 40 * 296209 * 2
def baseEnd_296209 : Nat := 67598929416771917611229

theorem tailTrace_296209 : CollatzResearch.WordTrace tailWord_296209 prefixEnd_296209 67598929416771917611229 := by
  unfold tailWord_296209
  simp only [CollatzResearch.WordTrace]
  refine ⟨10803629783892856314755681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7202419855928570876503787 10803629783892856314755681)
  ·
    refine ⟨8102722337919642236066761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10803629783892856314755681 8102722337919642236066761)
    ·
      refine ⟨6077041753439731677050071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8102722337919642236066761 6077041753439731677050071)
      ·
        refine ⟨9115562630159597515575107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6077041753439731677050071 9115562630159597515575107)
        ·
          refine ⟨13673343945239396273362661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9115562630159597515575107 13673343945239396273362661)
          ·
            refine ⟨2563751989732386801255499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13673343945239396273362661 2563751989732386801255499)
            ·
              refine ⟨3845627984598580201883249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2563751989732386801255499 3845627984598580201883249)
              ·
                refine ⟨2884220988448935151412437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3845627984598580201883249 2884220988448935151412437)
                ·
                  refine ⟨67598929416771917611229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2884220988448935151412437 67598929416771917611229)
                  ·
                    rfl

theorem cell21_296209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 7].length) (baseStart_296209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_296209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_296209 prefixEnd_296209 := by exact prefixLift 296209
  have htrace : WordTrace (prefixWord ++ tailWord_296209) baseStart_296209 baseEnd_296209 := by
    simpa [prefixWord, tailWord_296209, baseEnd_296209] using wordTrace_append hprefix tailTrace_296209
  have hstable : (prefixWord ++ tailWord_296209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296209).length < 2 ^ (prefixWord ++ tailWord_296209).sum := by decide
  have hdescent : baseEnd_296209 < baseStart_296209 := by decide
  rcases family_descends (prefixWord ++ tailWord_296209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296257 : List Nat := [1, 2, 5, 2, 1, 1, 1, 2, 6]
def baseStart_296257 : Nat := 118140960795 + 296257 * 2 ^ 59
def prefixEnd_296257 : Nat := 4983230072969 + 3 ^ 40 * 296257 * 2
def baseEnd_296257 : Nat := 67609883670734500811131

theorem tailTrace_296257 : CollatzResearch.WordTrace tailWord_296257 prefixEnd_296257 67609883670734500811131 := by
  unfold tailWord_296257
  simp only [CollatzResearch.WordTrace]
  refine ⟨10805380487718960512503025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7203586991812640341668683 10805380487718960512503025)
  ·
    refine ⟨8104035365789220384377269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10805380487718960512503025 8104035365789220384377269)
    ·
      refine ⟨759753315542739411035369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8104035365789220384377269 759753315542739411035369)
      ·
        refine ⟨569814986657054558276527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 759753315542739411035369 569814986657054558276527)
        ·
          refine ⟨854722479985581837414791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 569814986657054558276527 854722479985581837414791)
          ·
            refine ⟨1282083719978372756122187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 854722479985581837414791 1282083719978372756122187)
            ·
              refine ⟨1923125579967559134183281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1282083719978372756122187 1923125579967559134183281)
              ·
                refine ⟨1442344184975669350637461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1923125579967559134183281 1442344184975669350637461)
                ·
                  refine ⟨67609883670734500811131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1442344184975669350637461 67609883670734500811131)
                  ·
                    rfl

theorem cell21_296257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 6].length) (baseStart_296257 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_296257 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_296257 prefixEnd_296257 := by exact prefixLift 296257
  have htrace : WordTrace (prefixWord ++ tailWord_296257) baseStart_296257 baseEnd_296257 := by
    simpa [prefixWord, tailWord_296257, baseEnd_296257] using wordTrace_append hprefix tailTrace_296257
  have hstable : (prefixWord ++ tailWord_296257).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296257).length < 2 ^ (prefixWord ++ tailWord_296257).sum := by decide
  have hdescent : baseEnd_296257 < baseStart_296257 := by decide
  rcases family_descends (prefixWord ++ tailWord_296257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296330 : List Nat := [3, 1, 2, 15]
def baseStart_296330 : Nat := 118140960795 + 296330 * 2 ^ 59
def prefixEnd_296330 : Nat := 4983230072969 + 3 ^ 40 * 296330 * 2
def baseEnd_296330 : Nat := 278298531955977761705

theorem tailTrace_296330 : CollatzResearch.WordTrace tailWord_296330 prefixEnd_296330 278298531955977761705 := by
  unfold tailWord_296330
  simp only [CollatzResearch.WordTrace]
  refine ⟨2702010754113623494977611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7205362010969662653273629 2702010754113623494977611)
  ·
    refine ⟨4053016131170435242466417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2702010754113623494977611 4053016131170435242466417)
    ·
      refine ⟨3039762098377826431849813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4053016131170435242466417 3039762098377826431849813)
      ·
        refine ⟨278298531955977761705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 3039762098377826431849813 278298531955977761705)
        ·
          rfl

theorem cell21_296330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 15].length) (baseStart_296330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_296330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_296330 prefixEnd_296330 := by exact prefixLift 296330
  have htrace : WordTrace (prefixWord ++ tailWord_296330) baseStart_296330 baseEnd_296330 := by
    simpa [prefixWord, tailWord_296330, baseEnd_296330] using wordTrace_append hprefix tailTrace_296330
  have hstable : (prefixWord ++ tailWord_296330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296330).length < 2 ^ (prefixWord ++ tailWord_296330).sum := by decide
  have hdescent : baseEnd_296330 < baseStart_296330 := by decide
  rcases family_descends (prefixWord ++ tailWord_296330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296392 : List Nat := [2, 1, 3, 1, 3, 1, 3, 1, 6]
def baseStart_296392 : Nat := 118140960795 + 296392 * 2 ^ 59
def prefixEnd_296392 : Nat := 4983230072969 + 3 ^ 40 * 296392 * 2
def baseEnd_296392 : Nat := 67640692510004266060855

theorem tailTrace_296392 : CollatzResearch.WordTrace tailWord_296392 prefixEnd_296392 67640692510004266060855 := by
  unfold tailWord_296392
  simp only [CollatzResearch.WordTrace]
  refine ⟨5405152171114939284333715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7206869561486585712444953 5405152171114939284333715)
  ·
    refine ⟨8107728256672408926500573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5405152171114939284333715 8107728256672408926500573)
    ·
      refine ⟨3040398096252153347437715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8107728256672408926500573 3040398096252153347437715)
      ·
        refine ⟨4560597144378230021156573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3040398096252153347437715 4560597144378230021156573)
        ·
          refine ⟨1710223929141836257933715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4560597144378230021156573 1710223929141836257933715)
          ·
            refine ⟨2565335893712754386900573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1710223929141836257933715 2565335893712754386900573)
            ·
              refine ⟨962000960142282895087715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2565335893712754386900573 962000960142282895087715)
              ·
                refine ⟨1443001440213424342631573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 962000960142282895087715 1443001440213424342631573)
                ·
                  refine ⟨67640692510004266060855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1443001440213424342631573 67640692510004266060855)
                  ·
                    rfl

theorem cell21_296392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 6].length) (baseStart_296392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_296392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_296392 prefixEnd_296392 := by exact prefixLift 296392
  have htrace : WordTrace (prefixWord ++ tailWord_296392) baseStart_296392 baseEnd_296392 := by
    simpa [prefixWord, tailWord_296392, baseEnd_296392] using wordTrace_append hprefix tailTrace_296392
  have hstable : (prefixWord ++ tailWord_296392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296392).length < 2 ^ (prefixWord ++ tailWord_296392).sum := by decide
  have hdescent : baseEnd_296392 < baseStart_296392 := by decide
  rcases family_descends (prefixWord ++ tailWord_296392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296423 : List Nat := [1, 1, 5, 2, 1, 3, 1, 7]
def baseStart_296423 : Nat := 118140960795 + 296423 * 2 ^ 59
def prefixEnd_296423 : Nat := 4983230072969 + 3 ^ 40 * 296423 * 2
def baseEnd_296423 : Nat := 22549255710785033681375

theorem tailTrace_296423 : CollatzResearch.WordTrace tailWord_296423 prefixEnd_296423 22549255710785033681375 := by
  unfold tailWord_296423
  simp only [CollatzResearch.WordTrace]
  refine ⟨10811435005117570863045923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7207623336745047242030615 10811435005117570863045923)
  ·
    refine ⟨16217152507676356294568885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10811435005117570863045923 16217152507676356294568885)
    ·
      refine ⟨1520358047594658402615833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16217152507676356294568885 1520358047594658402615833)
      ·
        refine ⟨1140268535695993801961875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1520358047594658402615833 1140268535695993801961875)
        ·
          refine ⟨1710402803543990702942813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1140268535695993801961875 1710402803543990702942813)
          ·
            refine ⟨641401051328996513603555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1710402803543990702942813 641401051328996513603555)
            ·
              refine ⟨962101576993494770405333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 641401051328996513603555 962101576993494770405333)
              ·
                refine ⟨22549255710785033681375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 962101576993494770405333 22549255710785033681375)
                ·
                  rfl

theorem cell21_296423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 7].length) (baseStart_296423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_296423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_296423 prefixEnd_296423 := by exact prefixLift 296423
  have htrace : WordTrace (prefixWord ++ tailWord_296423) baseStart_296423 baseEnd_296423 := by
    simpa [prefixWord, tailWord_296423, baseEnd_296423] using wordTrace_append hprefix tailTrace_296423
  have hstable : (prefixWord ++ tailWord_296423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296423).length < 2 ^ (prefixWord ++ tailWord_296423).sum := by decide
  have hdescent : baseEnd_296423 < baseStart_296423 := by decide
  rcases family_descends (prefixWord ++ tailWord_296423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296429 : List Nat := [1, 5, 1, 3, 2, 2, 1, 3, 3]
def baseStart_296429 : Nat := 118140960795 + 296429 * 2 ^ 59
def prefixEnd_296429 : Nat := 4983230072969 + 3 ^ 40 * 296429 * 2
def baseEnd_296429 : Nat := 67649136414100423944113

theorem tailTrace_296429 : CollatzResearch.WordTrace tailWord_296429 prefixEnd_296429 67649136414100423944113 := by
  unfold tailWord_296429
  simp only [CollatzResearch.WordTrace]
  refine ⟨10811653843095833887764341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7207769228730555925176227 10811653843095833887764341)
  ·
    refine ⟨1013592547790234426977907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10811653843095833887764341 1013592547790234426977907)
    ·
      refine ⟨1520388821685351640466861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1013592547790234426977907 1520388821685351640466861)
      ·
        refine ⟨570145808132006865175073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1520388821685351640466861 570145808132006865175073)
        ·
          refine ⟨427609356099005148881305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 570145808132006865175073 427609356099005148881305)
          ·
            refine ⟨320707017074253861660979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 427609356099005148881305 320707017074253861660979)
            ·
              refine ⟨481060525611380792491469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 320707017074253861660979 481060525611380792491469)
              ·
                refine ⟨180397697104267797184301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 481060525611380792491469 180397697104267797184301)
                ·
                  refine ⟨67649136414100423944113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 180397697104267797184301 67649136414100423944113)
                  ·
                    rfl

theorem cell21_296429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_296429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_296429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_296429 prefixEnd_296429 := by exact prefixLift 296429
  have htrace : WordTrace (prefixWord ++ tailWord_296429) baseStart_296429 baseEnd_296429 := by
    simpa [prefixWord, tailWord_296429, baseEnd_296429] using wordTrace_append hprefix tailTrace_296429
  have hstable : (prefixWord ++ tailWord_296429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296429).length < 2 ^ (prefixWord ++ tailWord_296429).sum := by decide
  have hdescent : baseEnd_296429 < baseStart_296429 := by decide
  rcases family_descends (prefixWord ++ tailWord_296429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296446 : List Nat := [4, 2, 2, 3, 1, 1, 3, 2, 3]
def baseStart_296446 : Nat := 118140960795 + 296446 * 2 ^ 59
def prefixEnd_296446 : Nat := 4983230072969 + 3 ^ 40 * 296446 * 2
def baseEnd_296446 : Nat := 67653016045712172160745

theorem tailTrace_296446 : CollatzResearch.WordTrace tailWord_296446 prefixEnd_296446 67653016045712172160745 := by
  unfold tailWord_296446
  simp only [CollatzResearch.WordTrace]
  refine ⟨1351534235504280723891649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7208182589356163860755461 1351534235504280723891649)
  ·
    refine ⟨1013650676628210542918737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1351534235504280723891649 1013650676628210542918737)
    ·
      refine ⟨760238007471157907189053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1013650676628210542918737 760238007471157907189053)
      ·
        refine ⟨285089252801684215195895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 760238007471157907189053 285089252801684215195895)
        ·
          refine ⟨427633879202526322793843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285089252801684215195895 427633879202526322793843)
          ·
            refine ⟨641450818803789484190765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 427633879202526322793843 641450818803789484190765)
            ·
              refine ⟨240544057051421056571537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 641450818803789484190765 240544057051421056571537)
              ·
                refine ⟨180408042788565792428653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 240544057051421056571537 180408042788565792428653)
                ·
                  refine ⟨67653016045712172160745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 180408042788565792428653 67653016045712172160745)
                  ·
                    rfl

theorem cell21_296446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_296446 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_296446 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_296446 prefixEnd_296446 := by exact prefixLift 296446
  have htrace : WordTrace (prefixWord ++ tailWord_296446) baseStart_296446 baseEnd_296446 := by
    simpa [prefixWord, tailWord_296446, baseEnd_296446] using wordTrace_append hprefix tailTrace_296446
  have hstable : (prefixWord ++ tailWord_296446).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296446).length < 2 ^ (prefixWord ++ tailWord_296446).sum := by decide
  have hdescent : baseEnd_296446 < baseStart_296446 := by decide
  rcases family_descends (prefixWord ++ tailWord_296446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296527 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 8]
def baseStart_296527 : Nat := 118140960795 + 296527 * 2 ^ 59
def prefixEnd_296527 : Nat := 4983230072969 + 3 ^ 40 * 296527 * 2
def baseEnd_296527 : Nat := 67671501349274031310579

theorem tailTrace_296527 : CollatzResearch.WordTrace tailWord_296527 prefixEnd_296527 67671501349274031310579 := by
  unfold tailWord_296527
  simp only [CollatzResearch.WordTrace]
  refine ⟨10815228196740796624831835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7210152131160531083221223 10815228196740796624831835)
  ·
    refine ⟨16222842295111194937247753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10815228196740796624831835 16222842295111194937247753)
    ·
      refine ⟨12167131721333396202935815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16222842295111194937247753 12167131721333396202935815)
      ·
        refine ⟨18250697582000094304403723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12167131721333396202935815 18250697582000094304403723)
        ·
          refine ⟨27376046373000141456605585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18250697582000094304403723 27376046373000141456605585)
          ·
            refine ⟨20532034779750106092454189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27376046373000141456605585 20532034779750106092454189)
            ·
              refine ⟨7699513042406289784670321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20532034779750106092454189 7699513042406289784670321)
              ·
                refine ⟨5774634781804717338502741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7699513042406289784670321 5774634781804717338502741)
                ·
                  refine ⟨67671501349274031310579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5774634781804717338502741 67671501349274031310579)
                  ·
                    rfl

theorem cell21_296527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 8].length) (baseStart_296527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_296527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_296527 prefixEnd_296527 := by exact prefixLift 296527
  have htrace : WordTrace (prefixWord ++ tailWord_296527) baseStart_296527 baseEnd_296527 := by
    simpa [prefixWord, tailWord_296527, baseEnd_296527] using wordTrace_append hprefix tailTrace_296527
  have hstable : (prefixWord ++ tailWord_296527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296527).length < 2 ^ (prefixWord ++ tailWord_296527).sum := by decide
  have hdescent : baseEnd_296527 < baseStart_296527 := by decide
  rcases family_descends (prefixWord ++ tailWord_296527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296530 : List Nat := [3, 2, 2, 1, 2, 3, 1, 2, 5]
def baseStart_296530 : Nat := 118140960795 + 296530 * 2 ^ 59
def prefixEnd_296530 : Nat := 4983230072969 + 3 ^ 40 * 296530 * 2
def baseEnd_296530 : Nat := 67672185990146692760573

theorem tailTrace_296530 : CollatzResearch.WordTrace tailWord_296530 prefixEnd_296530 67672185990146692760573 := by
  unfold tailWord_296530
  simp only [CollatzResearch.WordTrace]
  refine ⟨2703834403932482034297761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7210225077153285424794029 2703834403932482034297761)
  ·
    refine ⟨2027875802949361525723321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2703834403932482034297761 2027875802949361525723321)
    ·
      refine ⟨1520906852212021144292491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2027875802949361525723321 1520906852212021144292491)
      ·
        refine ⟨2281360278318031716438737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1520906852212021144292491 2281360278318031716438737)
        ·
          refine ⟨1711020208738523787329053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2281360278318031716438737 1711020208738523787329053)
          ·
            refine ⟨641632578276946420248395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1711020208738523787329053 641632578276946420248395)
            ·
              refine ⟨962448867415419630372593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 641632578276946420248395 962448867415419630372593)
              ·
                refine ⟨721836650561564722779445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 962448867415419630372593 721836650561564722779445)
                ·
                  refine ⟨67672185990146692760573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 721836650561564722779445 67672185990146692760573)
                  ·
                    rfl

theorem cell21_296530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_296530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_296530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_296530 prefixEnd_296530 := by exact prefixLift 296530
  have htrace : WordTrace (prefixWord ++ tailWord_296530) baseStart_296530 baseEnd_296530 := by
    simpa [prefixWord, tailWord_296530, baseEnd_296530] using wordTrace_append hprefix tailTrace_296530
  have hstable : (prefixWord ++ tailWord_296530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296530).length < 2 ^ (prefixWord ++ tailWord_296530).sum := by decide
  have hdescent : baseEnd_296530 < baseStart_296530 := by decide
  rcases family_descends (prefixWord ++ tailWord_296530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296547 : List Nat := [1, 1, 1, 5, 1, 4, 2, 3, 3]
def baseStart_296547 : Nat := 118140960795 + 296547 * 2 ^ 59
def prefixEnd_296547 : Nat := 4983230072969 + 3 ^ 40 * 296547 * 2
def baseEnd_296547 : Nat := 67676065621758440977205

theorem tailTrace_296547 : CollatzResearch.WordTrace tailWord_296547 prefixEnd_296547 67676065621758440977205 := by
  unfold tailWord_296547
  simp only [CollatzResearch.WordTrace]
  refine ⟨10815957656668340040559895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7210638437778893360373263 10815957656668340040559895)
  ·
    refine ⟨16223936485002510060839843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10815957656668340040559895 16223936485002510060839843)
    ·
      refine ⟨24335904727503765091259765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16223936485002510060839843 24335904727503765091259765)
      ·
        refine ⟨2281491068203477977305603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24335904727503765091259765 2281491068203477977305603)
        ·
          refine ⟨3422236602305216965958405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2281491068203477977305603 3422236602305216965958405)
          ·
            refine ⟨641669362932228181117201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3422236602305216965958405 641669362932228181117201)
            ·
              refine ⟨481252022199171135837901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 641669362932228181117201 481252022199171135837901)
              ·
                refine ⟨180469508324689175939213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 481252022199171135837901 180469508324689175939213)
                ·
                  refine ⟨67676065621758440977205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 180469508324689175939213 67676065621758440977205)
                  ·
                    rfl

theorem cell21_296547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 3, 3].length) (baseStart_296547 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_296547 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_296547 prefixEnd_296547 := by exact prefixLift 296547
  have htrace : WordTrace (prefixWord ++ tailWord_296547) baseStart_296547 baseEnd_296547 := by
    simpa [prefixWord, tailWord_296547, baseEnd_296547] using wordTrace_append hprefix tailTrace_296547
  have hstable : (prefixWord ++ tailWord_296547).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296547).length < 2 ^ (prefixWord ++ tailWord_296547).sum := by decide
  have hdescent : baseEnd_296547 < baseStart_296547 := by decide
  rcases family_descends (prefixWord ++ tailWord_296547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296623 : List Nat := [1, 1, 2, 1, 2, 4, 5, 2, 3]
def baseStart_296623 : Nat := 118140960795 + 296623 * 2 ^ 59
def prefixEnd_296623 : Nat := 4983230072969 + 3 ^ 40 * 296623 * 2
def baseEnd_296623 : Nat := 67693409857199197710383

theorem tailTrace_296623 : CollatzResearch.WordTrace tailWord_296623 prefixEnd_296623 67693409857199197710383 := by
  unfold tailWord_296623
  simp only [CollatzResearch.WordTrace]
  refine ⟨10818729604393005020326523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7212486402928670013551015 10818729604393005020326523)
  ·
    refine ⟨16228094406589507530489785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10818729604393005020326523 16228094406589507530489785)
    ·
      refine ⟨12171070804942130647867339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16228094406589507530489785 12171070804942130647867339)
      ·
        refine ⟨18256606207413195971801009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12171070804942130647867339 18256606207413195971801009)
        ·
          refine ⟨13692454655559896978850757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18256606207413195971801009 13692454655559896978850757)
          ·
            refine ⟨2567335247917480683534517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13692454655559896978850757 2567335247917480683534517)
            ·
              refine ⟨240687679492263814081361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2567335247917480683534517 240687679492263814081361)
              ·
                refine ⟨180515759619197860561021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 240687679492263814081361 180515759619197860561021)
                ·
                  refine ⟨67693409857199197710383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 180515759619197860561021 67693409857199197710383)
                  ·
                    rfl

theorem cell21_296623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 2, 3].length) (baseStart_296623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_296623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_296623 prefixEnd_296623 := by exact prefixLift 296623
  have htrace : WordTrace (prefixWord ++ tailWord_296623) baseStart_296623 baseEnd_296623 := by
    simpa [prefixWord, tailWord_296623, baseEnd_296623] using wordTrace_append hprefix tailTrace_296623
  have hstable : (prefixWord ++ tailWord_296623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296623).length < 2 ^ (prefixWord ++ tailWord_296623).sum := by decide
  have hdescent : baseEnd_296623 < baseStart_296623 := by decide
  rcases family_descends (prefixWord ++ tailWord_296623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296634 : List Nat := [3, 1, 1, 1, 2, 4, 1, 8]
def baseStart_296634 : Nat := 118140960795 + 296634 * 2 ^ 59
def prefixEnd_296634 : Nat := 4983230072969 + 3 ^ 40 * 296634 * 2
def baseEnd_296634 : Nat := 22565306735688541009009

theorem tailTrace_296634 : CollatzResearch.WordTrace tailWord_296634 prefixEnd_296634 22565306735688541009009 := by
  unfold tailWord_296634
  simp only [CollatzResearch.WordTrace]
  refine ⟨2704782701838288474744239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7212753871568769265984637 2704782701838288474744239)
  ·
    refine ⟨4057174052757432712116359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2704782701838288474744239 4057174052757432712116359)
    ·
      refine ⟨6085761079136149068174539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4057174052757432712116359 6085761079136149068174539)
      ·
        refine ⟨9128641618704223602261809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6085761079136149068174539 9128641618704223602261809)
        ·
          refine ⟨6846481214028167701696357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9128641618704223602261809 6846481214028167701696357)
          ·
            refine ⟨1283715227630281444068067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6846481214028167701696357 1283715227630281444068067)
            ·
              refine ⟨1925572841445422166102101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1283715227630281444068067 1925572841445422166102101)
              ·
                refine ⟨22565306735688541009009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1925572841445422166102101 22565306735688541009009)
                ·
                  rfl

theorem cell21_296634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 8].length) (baseStart_296634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_296634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_296634 prefixEnd_296634 := by exact prefixLift 296634
  have htrace : WordTrace (prefixWord ++ tailWord_296634) baseStart_296634 baseEnd_296634 := by
    simpa [prefixWord, tailWord_296634, baseEnd_296634] using wordTrace_append hprefix tailTrace_296634
  have hstable : (prefixWord ++ tailWord_296634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296634).length < 2 ^ (prefixWord ++ tailWord_296634).sum := by decide
  have hdescent : baseEnd_296634 < baseStart_296634 := by decide
  rcases family_descends (prefixWord ++ tailWord_296634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296668 : List Nat := [2, 2, 5, 1, 3, 8]
def baseStart_296668 : Nat := 118140960795 + 296668 * 2 ^ 59
def prefixEnd_296668 : Nat := 4983230072969 + 3 ^ 40 * 296668 * 2
def baseEnd_296668 : Nat := 2507543684084782202233

theorem tailTrace_296668 : CollatzResearch.WordTrace tailWord_296668 prefixEnd_296668 2507543684084782202233 := by
  unfold tailWord_296668
  simp only [CollatzResearch.WordTrace]
  refine ⟨5410185444614988852857329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7213580592819985137143105 5410185444614988852857329)
  ·
    refine ⟨4057639083461241639642997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5410185444614988852857329 4057639083461241639642997)
    ·
      refine ⟨380403664074491403716531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4057639083461241639642997 380403664074491403716531)
      ·
        refine ⟨570605496111737105574797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380403664074491403716531 570605496111737105574797)
        ·
          refine ⟨213977061041901414590549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 570605496111737105574797 213977061041901414590549)
          ·
            refine ⟨2507543684084782202233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 213977061041901414590549 2507543684084782202233)
            ·
              rfl

theorem cell21_296668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 8].length) (baseStart_296668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_296668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_296668 prefixEnd_296668 := by exact prefixLift 296668
  have htrace : WordTrace (prefixWord ++ tailWord_296668) baseStart_296668 baseEnd_296668 := by
    simpa [prefixWord, tailWord_296668, baseEnd_296668] using wordTrace_append hprefix tailTrace_296668
  have hstable : (prefixWord ++ tailWord_296668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296668).length < 2 ^ (prefixWord ++ tailWord_296668).sum := by decide
  have hdescent : baseEnd_296668 < baseStart_296668 := by decide
  rcases family_descends (prefixWord ++ tailWord_296668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296741 : List Nat := [1, 3, 1, 2, 3, 2, 1, 3, 5]
def baseStart_296741 : Nat := 118140960795 + 296741 * 2 ^ 59
def prefixEnd_296741 : Nat := 4983230072969 + 3 ^ 40 * 296741 * 2
def baseEnd_296741 : Nat := 67720339064857214743475

theorem tailTrace_296741 : CollatzResearch.WordTrace tailWord_296741 prefixEnd_296741 67720339064857214743475 := by
  unfold tailWord_296741
  simp only [CollatzResearch.WordTrace]
  refine ⟨10823033417965511173122077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7215355611977007448748051 10823033417965511173122077)
  ·
    refine ⟨4058637531737066689920779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10823033417965511173122077 4058637531737066689920779)
    ·
      refine ⟨6087956297605600034881169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4058637531737066689920779 6087956297605600034881169)
      ·
        refine ⟨4565967223204200026160877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6087956297605600034881169 4565967223204200026160877)
        ·
          refine ⟨1712237708701575009810329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4565967223204200026160877 1712237708701575009810329)
          ·
            refine ⟨1284178281526181257357747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1712237708701575009810329 1284178281526181257357747)
            ·
              refine ⟨1926267422289271886036621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1284178281526181257357747 1926267422289271886036621)
              ·
                refine ⟨722350283358476957263733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1926267422289271886036621 722350283358476957263733)
                ·
                  refine ⟨67720339064857214743475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 722350283358476957263733 67720339064857214743475)
                  ·
                    rfl

theorem cell21_296741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_296741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_296741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_296741 prefixEnd_296741 := by exact prefixLift 296741
  have htrace : WordTrace (prefixWord ++ tailWord_296741) baseStart_296741 baseEnd_296741 := by
    simpa [prefixWord, tailWord_296741, baseEnd_296741] using wordTrace_append hprefix tailTrace_296741
  have hstable : (prefixWord ++ tailWord_296741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296741).length < 2 ^ (prefixWord ++ tailWord_296741).sum := by decide
  have hdescent : baseEnd_296741 < baseStart_296741 := by decide
  rcases family_descends (prefixWord ++ tailWord_296741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296761 : List Nat := [1, 2, 1, 7, 1, 2, 2, 5]
def baseStart_296761 : Nat := 118140960795 + 296761 * 2 ^ 59
def prefixEnd_296761 : Nat := 4983230072969 + 3 ^ 40 * 296761 * 2
def baseEnd_296761 : Nat := 22574967779113874803367

theorem tailTrace_296761 : CollatzResearch.WordTrace tailWord_296761 prefixEnd_296761 22574967779113874803367 := by
  unfold tailWord_296761
  simp only [CollatzResearch.WordTrace]
  refine ⟨10823762877893054588850137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7215841918595369725900091 10823762877893054588850137)
  ·
    refine ⟨8117822158419790941637603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10823762877893054588850137 8117822158419790941637603)
    ·
      refine ⟨12176733237629686412456405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8117822158419790941637603 12176733237629686412456405)
      ·
        refine ⟨285392185256945775291947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 12176733237629686412456405 285392185256945775291947)
        ·
          refine ⟨428088277885418662937921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285392185256945775291947 428088277885418662937921)
          ·
            refine ⟨321066208414063997203441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 428088277885418662937921 321066208414063997203441)
            ·
              refine ⟨240799656310547997902581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 321066208414063997203441 240799656310547997902581)
              ·
                refine ⟨22574967779113874803367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 240799656310547997902581 22574967779113874803367)
                ·
                  rfl

theorem cell21_296761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 5].length) (baseStart_296761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_296761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_296761 prefixEnd_296761 := by exact prefixLift 296761
  have htrace : WordTrace (prefixWord ++ tailWord_296761) baseStart_296761 baseEnd_296761 := by
    simpa [prefixWord, tailWord_296761, baseEnd_296761] using wordTrace_append hprefix tailTrace_296761
  have hstable : (prefixWord ++ tailWord_296761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296761).length < 2 ^ (prefixWord ++ tailWord_296761).sum := by decide
  have hdescent : baseEnd_296761 < baseStart_296761 := by decide
  rcases family_descends (prefixWord ++ tailWord_296761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296786 : List Nat := [3, 2, 2, 1, 1, 3, 9]
def baseStart_296786 : Nat := 118140960795 + 296786 * 2 ^ 59
def prefixEnd_296786 : Nat := 4983230072969 + 3 ^ 40 * 296786 * 2
def baseEnd_296786 : Nat := 7525623186438570721487

theorem tailTrace_296786 : CollatzResearch.WordTrace tailWord_296786 prefixEnd_296786 7525623186438570721487 := by
  unfold tailWord_296786
  simp only [CollatzResearch.WordTrace]
  refine ⟨2706168675700620964627553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7216449801868322572340141 2706168675700620964627553)
  ·
    refine ⟨2029626506775465723470665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2706168675700620964627553 2029626506775465723470665)
    ·
      refine ⟨1522219880081599292602999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2029626506775465723470665 1522219880081599292602999)
      ·
        refine ⟨2283329820122398938904499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1522219880081599292602999 2283329820122398938904499)
        ·
          refine ⟨3424994730183598408356749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2283329820122398938904499 3424994730183598408356749)
          ·
            refine ⟨1284373023818849403133781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3424994730183598408356749 1284373023818849403133781)
            ·
              refine ⟨7525623186438570721487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1284373023818849403133781 7525623186438570721487)
              ·
                rfl

theorem cell21_296786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 9].length) (baseStart_296786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_296786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_296786 prefixEnd_296786 := by exact prefixLift 296786
  have htrace : WordTrace (prefixWord ++ tailWord_296786) baseStart_296786 baseEnd_296786 := by
    simpa [prefixWord, tailWord_296786, baseEnd_296786] using wordTrace_append hprefix tailTrace_296786
  have hstable : (prefixWord ++ tailWord_296786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296786).length < 2 ^ (prefixWord ++ tailWord_296786).sum := by decide
  have hdescent : baseEnd_296786 < baseStart_296786 := by decide
  rcases family_descends (prefixWord ++ tailWord_296786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296803 : List Nat := [1, 1, 1, 5, 4, 1, 2, 6]
def baseStart_296803 : Nat := 118140960795 + 296803 * 2 ^ 59
def prefixEnd_296803 : Nat := 4983230072969 + 3 ^ 40 * 296803 * 2
def baseEnd_296803 : Nat := 22578162769852961570005

theorem tailTrace_296803 : CollatzResearch.WordTrace tailWord_296803 prefixEnd_296803 22578162769852961570005 := by
  unfold tailWord_296803
  simp only [CollatzResearch.WordTrace]
  refine ⟨10825294743740895761879063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7216863162493930507919375 10825294743740895761879063)
  ·
    refine ⟨16237942115611343642818595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10825294743740895761879063 16237942115611343642818595)
    ·
      refine ⟨24356913173417015464227893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16237942115611343642818595 24356913173417015464227893)
      ·
        refine ⟨2283460610007845199771365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24356913173417015464227893 2283460610007845199771365)
        ·
          refine ⟨428148864376470974957131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2283460610007845199771365 428148864376470974957131)
          ·
            refine ⟨642223296564706462435697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428148864376470974957131 642223296564706462435697)
            ·
              refine ⟨481667472423529846826773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 642223296564706462435697 481667472423529846826773)
              ·
                refine ⟨22578162769852961570005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 481667472423529846826773 22578162769852961570005)
                ·
                  rfl

theorem cell21_296803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 6].length) (baseStart_296803 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_296803 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_296803 prefixEnd_296803 := by exact prefixLift 296803
  have htrace : WordTrace (prefixWord ++ tailWord_296803) baseStart_296803 baseEnd_296803 := by
    simpa [prefixWord, tailWord_296803, baseEnd_296803] using wordTrace_append hprefix tailTrace_296803
  have hstable : (prefixWord ++ tailWord_296803).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296803).length < 2 ^ (prefixWord ++ tailWord_296803).sum := by decide
  have hdescent : baseEnd_296803 < baseStart_296803 := by decide
  rcases family_descends (prefixWord ++ tailWord_296803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296854 : List Nat := [5, 3, 1, 1, 2, 2, 1, 6]
def baseStart_296854 : Nat := 118140960795 + 296854 * 2 ^ 59
def prefixEnd_296854 : Nat := 4983230072969 + 3 ^ 40 * 296854 * 2
def baseEnd_296854 : Nat := 22582042401464709786637

theorem tailTrace_296854 : CollatzResearch.WordTrace tailWord_296854 prefixEnd_296854 22582042401464709786637 := by
  unfold tailWord_296854
  simp only [CollatzResearch.WordTrace]
  refine ⟨676697179159758216999101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7218103244370754314657077 676697179159758216999101)
  ·
    refine ⟨253761442184909331374663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 676697179159758216999101 253761442184909331374663)
    ·
      refine ⟨380642163277363997061995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253761442184909331374663 380642163277363997061995)
      ·
        refine ⟨570963244916045995592993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380642163277363997061995 570963244916045995592993)
        ·
          refine ⟨428222433687034496694745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 570963244916045995592993 428222433687034496694745)
          ·
            refine ⟨321166825265275872521059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 428222433687034496694745 321166825265275872521059)
            ·
              refine ⟨481750237897913808781589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321166825265275872521059 481750237897913808781589)
              ·
                refine ⟨22582042401464709786637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 481750237897913808781589 22582042401464709786637)
                ·
                  rfl

theorem cell21_296854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_296854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_296854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_296854 prefixEnd_296854 := by exact prefixLift 296854
  have htrace : WordTrace (prefixWord ++ tailWord_296854) baseStart_296854 baseEnd_296854 := by
    simpa [prefixWord, tailWord_296854, baseEnd_296854] using wordTrace_append hprefix tailTrace_296854
  have hstable : (prefixWord ++ tailWord_296854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296854).length < 2 ^ (prefixWord ++ tailWord_296854).sum := by decide
  have hdescent : baseEnd_296854 < baseStart_296854 := by decide
  rcases family_descends (prefixWord ++ tailWord_296854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296907 : List Nat := [1, 1, 1, 1, 3, 4, 3, 1, 6]
def baseStart_296907 : Nat := 118140960795 + 296907 * 2 ^ 59
def prefixEnd_296907 : Nat := 4983230072969 + 3 ^ 40 * 296907 * 2
def baseEnd_296907 : Nat := 67758222526477814976469

theorem tailTrace_296907 : CollatzResearch.WordTrace tailWord_296907 prefixEnd_296907 67758222526477814976469 := by
  unfold tailWord_296907
  simp only [CollatzResearch.WordTrace]
  refine ⟨10829087935364121523664975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7219391956909414349109983 10829087935364121523664975)
  ·
    refine ⟨16243631903046182285497463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10829087935364121523664975 16243631903046182285497463)
    ·
      refine ⟨24365447854569273428246195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16243631903046182285497463 24365447854569273428246195)
      ·
        refine ⟨36548171781853910142369293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24365447854569273428246195 36548171781853910142369293)
        ·
          refine ⟨13705564418195216303388485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36548171781853910142369293 13705564418195216303388485)
          ·
            refine ⟨2569793328411603056885341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13705564418195216303388485 2569793328411603056885341)
            ·
              refine ⟨963672498154351146332003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2569793328411603056885341 963672498154351146332003)
              ·
                refine ⟨1445508747231526719498005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 963672498154351146332003 1445508747231526719498005)
                ·
                  refine ⟨67758222526477814976469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1445508747231526719498005 67758222526477814976469)
                  ·
                    rfl

theorem cell21_296907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 6].length) (baseStart_296907 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_296907 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_296907 prefixEnd_296907 := by exact prefixLift 296907
  have htrace : WordTrace (prefixWord ++ tailWord_296907) baseStart_296907 baseEnd_296907 := by
    simpa [prefixWord, tailWord_296907, baseEnd_296907] using wordTrace_append hprefix tailTrace_296907
  have hstable : (prefixWord ++ tailWord_296907).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296907).length < 2 ^ (prefixWord ++ tailWord_296907).sum := by decide
  have hdescent : baseEnd_296907 < baseStart_296907 := by decide
  rcases family_descends (prefixWord ++ tailWord_296907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296910 : List Nat := [4, 1, 1, 1, 2, 2, 1, 6, 3]
def baseStart_296910 : Nat := 118140960795 + 296910 * 2 ^ 59
def prefixEnd_296910 : Nat := 4983230072969 + 3 ^ 40 * 296910 * 2
def baseEnd_296910 : Nat := 67758907167350476426463

theorem tailTrace_296910 : CollatzResearch.WordTrace tailWord_296910 prefixEnd_296910 67758907167350476426463 := by
  unfold tailWord_296910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1353649669294156629503023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7219464902902168690682789 1353649669294156629503023)
  ·
    refine ⟨2030474503941234944254535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1353649669294156629503023 2030474503941234944254535)
    ·
      refine ⟨3045711755911852416381803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2030474503941234944254535 3045711755911852416381803)
      ·
        refine ⟨4568567633867778624572705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3045711755911852416381803 4568567633867778624572705)
        ·
          refine ⟨3426425725400833968429529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4568567633867778624572705 3426425725400833968429529)
          ·
            refine ⟨2569819294050625476322147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3426425725400833968429529 2569819294050625476322147)
            ·
              refine ⟨3854728941075938214483221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2569819294050625476322147 3854728941075938214483221)
              ·
                refine ⟨180690419112934603803901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3854728941075938214483221 180690419112934603803901)
                ·
                  refine ⟨67758907167350476426463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 180690419112934603803901 67758907167350476426463)
                  ·
                    rfl

theorem cell21_296910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 6, 3].length) (baseStart_296910 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_296910 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_296910 prefixEnd_296910 := by exact prefixLift 296910
  have htrace : WordTrace (prefixWord ++ tailWord_296910) baseStart_296910 baseEnd_296910 := by
    simpa [prefixWord, tailWord_296910, baseEnd_296910] using wordTrace_append hprefix tailTrace_296910
  have hstable : (prefixWord ++ tailWord_296910).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296910).length < 2 ^ (prefixWord ++ tailWord_296910).sum := by decide
  have hdescent : baseEnd_296910 < baseStart_296910 := by decide
  rcases family_descends (prefixWord ++ tailWord_296910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296930 : List Nat := [3, 3, 3, 1, 3, 1, 2, 5]
def baseStart_296930 : Nat := 118140960795 + 296930 * 2 ^ 59
def prefixEnd_296930 : Nat := 4983230072969 + 3 ^ 40 * 296930 * 2
def baseEnd_296930 : Nat := 22587823813278295364363

theorem tailTrace_296930 : CollatzResearch.WordTrace tailWord_296930 prefixEnd_296930 22587823813278295364363 := by
  unfold tailWord_296930
  simp only [CollatzResearch.WordTrace]
  refine ⟨2707481703570199112938061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7219951209520530967834829 2707481703570199112938061)
  ·
    refine ⟨1015305638838824667351773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2707481703570199112938061 1015305638838824667351773)
    ·
      refine ⟨380739614564559250256915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1015305638838824667351773 380739614564559250256915)
      ·
        refine ⟨571109421846838875385373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380739614564559250256915 571109421846838875385373)
        ·
          refine ⟨214166033192564578269515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 571109421846838875385373 214166033192564578269515)
          ·
            refine ⟨321249049788846867404273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214166033192564578269515 321249049788846867404273)
            ·
              refine ⟨240936787341635150553205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 321249049788846867404273 240936787341635150553205)
              ·
                refine ⟨22587823813278295364363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 240936787341635150553205 22587823813278295364363)
                ·
                  rfl

theorem cell21_296930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 5].length) (baseStart_296930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_296930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_296930 prefixEnd_296930 := by exact prefixLift 296930
  have htrace : WordTrace (prefixWord ++ tailWord_296930) baseStart_296930 baseEnd_296930 := by
    simpa [prefixWord, tailWord_296930, baseEnd_296930] using wordTrace_append hprefix tailTrace_296930
  have hstable : (prefixWord ++ tailWord_296930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296930).length < 2 ^ (prefixWord ++ tailWord_296930).sum := by decide
  have hdescent : baseEnd_296930 < baseStart_296930 := by decide
  rcases family_descends (prefixWord ++ tailWord_296930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296938 : List Nat := [3, 1, 3, 1, 2, 1, 3, 7]
def baseStart_296938 : Nat := 118140960795 + 296938 * 2 ^ 59
def prefixEnd_296938 : Nat := 4983230072969 + 3 ^ 40 * 296938 * 2
def baseEnd_296938 : Nat := 22588432382942883319913

theorem tailTrace_296938 : CollatzResearch.WordTrace tailWord_296938 prefixEnd_296938 22588432382942883319913 := by
  unfold tailWord_296938
  simp only [CollatzResearch.WordTrace]
  refine ⟨2707554649562953454510867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7220145732167875878695645 2707554649562953454510867)
  ·
    refine ⟨4061331974344430181766301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2707554649562953454510867 4061331974344430181766301)
    ·
      refine ⟨1522999490379161318162363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4061331974344430181766301 1522999490379161318162363)
      ·
        refine ⟨2284499235568741977243545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1522999490379161318162363 2284499235568741977243545)
        ·
          refine ⟨1713374426676556482932659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2284499235568741977243545 1713374426676556482932659)
          ·
            refine ⟨2570061640014834724398989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1713374426676556482932659 2570061640014834724398989)
            ·
              refine ⟨963773115005563021649621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2570061640014834724398989 963773115005563021649621)
              ·
                refine ⟨22588432382942883319913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 963773115005563021649621 22588432382942883319913)
                ·
                  rfl

theorem cell21_296938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 7].length) (baseStart_296938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_296938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_296938 prefixEnd_296938 := by exact prefixLift 296938
  have htrace : WordTrace (prefixWord ++ tailWord_296938) baseStart_296938 baseEnd_296938 := by
    simpa [prefixWord, tailWord_296938, baseEnd_296938] using wordTrace_append hprefix tailTrace_296938
  have hstable : (prefixWord ++ tailWord_296938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296938).length < 2 ^ (prefixWord ++ tailWord_296938).sum := by decide
  have hdescent : baseEnd_296938 < baseStart_296938 := by decide
  rcases family_descends (prefixWord ++ tailWord_296938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296952 : List Nat := [2, 1, 2, 1, 1, 3, 2, 2, 7]
def baseStart_296952 : Nat := 118140960795 + 296952 * 2 ^ 59
def prefixEnd_296952 : Nat := 4983230072969 + 3 ^ 40 * 296952 * 2
def baseEnd_296952 : Nat := 67768492139567736726377

theorem tailTrace_296952 : CollatzResearch.WordTrace tailWord_296952 prefixEnd_296952 67768492139567736726377 := by
  unfold tailWord_296952
  simp only [CollatzResearch.WordTrace]
  refine ⟨5415364610100547104526555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7220486146800729472702073 5415364610100547104526555)
  ·
    refine ⟨8123046915150820656789833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5415364610100547104526555 8123046915150820656789833)
    ·
      refine ⟨6092285186363115492592375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8123046915150820656789833 6092285186363115492592375)
      ·
        refine ⟨9138427779544673238888563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6092285186363115492592375 9138427779544673238888563)
        ·
          refine ⟨13707641669317009858332845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9138427779544673238888563 13707641669317009858332845)
          ·
            refine ⟨5140365625993878696874817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13707641669317009858332845 5140365625993878696874817)
            ·
              refine ⟨3855274219495409022656113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5140365625993878696874817 3855274219495409022656113)
              ·
                refine ⟨2891455664621556766992085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3855274219495409022656113 2891455664621556766992085)
                ·
                  refine ⟨67768492139567736726377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2891455664621556766992085 67768492139567736726377)
                  ·
                    rfl

theorem cell21_296952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 7].length) (baseStart_296952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_296952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_296952 prefixEnd_296952 := by exact prefixLift 296952
  have htrace : WordTrace (prefixWord ++ tailWord_296952) baseStart_296952 baseEnd_296952 := by
    simpa [prefixWord, tailWord_296952, baseEnd_296952] using wordTrace_append hprefix tailTrace_296952
  have hstable : (prefixWord ++ tailWord_296952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296952).length < 2 ^ (prefixWord ++ tailWord_296952).sum := by decide
  have hdescent : baseEnd_296952 < baseStart_296952 := by decide
  rcases family_descends (prefixWord ++ tailWord_296952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297017 : List Nat := [1, 2, 1, 5, 3, 1, 2, 2, 4]
def baseStart_297017 : Nat := 118140960795 + 297017 * 2 ^ 59
def prefixEnd_297017 : Nat := 4983230072969 + 3 ^ 40 * 297017 * 2
def baseEnd_297017 : Nat := 67783326025142068142911

theorem tailTrace_297017 : CollatzResearch.WordTrace tailWord_297017 prefixEnd_297017 67783326025142068142911 := by
  unfold tailWord_297017
  simp only [CollatzResearch.WordTrace]
  refine ⟨10833099964965610310169305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7222066643310406873446203 10833099964965610310169305)
  ·
    refine ⟨8124824973724207732626979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10833099964965610310169305 8124824973724207732626979)
    ·
      refine ⟨12187237460586311598940469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8124824973724207732626979 12187237460586311598940469)
      ·
        refine ⟨1142553511929966712400669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12187237460586311598940469 1142553511929966712400669)
        ·
          refine ⟨428457566973737517150251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1142553511929966712400669 428457566973737517150251)
          ·
            refine ⟨642686350460606275725377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428457566973737517150251 642686350460606275725377)
            ·
              refine ⟨482014762845454706794033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 642686350460606275725377 482014762845454706794033)
              ·
                refine ⟨361511072134091030095525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 482014762845454706794033 361511072134091030095525)
                ·
                  refine ⟨67783326025142068142911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 361511072134091030095525 67783326025142068142911)
                  ·
                    rfl

theorem cell21_297017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 4].length) (baseStart_297017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_297017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_297017 prefixEnd_297017 := by exact prefixLift 297017
  have htrace : WordTrace (prefixWord ++ tailWord_297017) baseStart_297017 baseEnd_297017 := by
    simpa [prefixWord, tailWord_297017, baseEnd_297017] using wordTrace_append hprefix tailTrace_297017
  have hstable : (prefixWord ++ tailWord_297017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297017).length < 2 ^ (prefixWord ++ tailWord_297017).sum := by decide
  have hdescent : baseEnd_297017 < baseStart_297017 := by decide
  rcases family_descends (prefixWord ++ tailWord_297017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297045 : List Nat := [1, 3, 2, 2, 1, 4, 1, 2, 5]
def baseStart_297045 : Nat := 118140960795 + 297045 * 2 ^ 59
def prefixEnd_297045 : Nat := 4983230072969 + 3 ^ 40 * 297045 * 2
def baseEnd_297045 : Nat := 67789716006620241676187

theorem tailTrace_297045 : CollatzResearch.WordTrace tailWord_297045 prefixEnd_297045 67789716006620241676187 := by
  unfold tailWord_297045
  simp only [CollatzResearch.WordTrace]
  refine ⟨10834121208864171092188589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7222747472576114061459059 10834121208864171092188589)
  ·
    refine ⟨4062795453324064159570721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10834121208864171092188589 4062795453324064159570721)
    ·
      refine ⟨3047096589993048119678041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4062795453324064159570721 3047096589993048119678041)
      ·
        refine ⟨2285322442494786089758531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3047096589993048119678041 2285322442494786089758531)
        ·
          refine ⟨3427983663742179134637797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2285322442494786089758531 3427983663742179134637797)
          ·
            refine ⟨642746936951658587744587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3427983663742179134637797 642746936951658587744587)
            ·
              refine ⟨964120405427487881616881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 642746936951658587744587 964120405427487881616881)
              ·
                refine ⟨723090304070615911212661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 964120405427487881616881 723090304070615911212661)
                ·
                  refine ⟨67789716006620241676187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 723090304070615911212661 67789716006620241676187)
                  ·
                    rfl

theorem cell21_297045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 5].length) (baseStart_297045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_297045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_297045 prefixEnd_297045 := by exact prefixLift 297045
  have htrace : WordTrace (prefixWord ++ tailWord_297045) baseStart_297045 baseEnd_297045 := by
    simpa [prefixWord, tailWord_297045, baseEnd_297045] using wordTrace_append hprefix tailTrace_297045
  have hstable : (prefixWord ++ tailWord_297045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297045).length < 2 ^ (prefixWord ++ tailWord_297045).sum := by decide
  have hdescent : baseEnd_297045 < baseStart_297045 := by decide
  rcases family_descends (prefixWord ++ tailWord_297045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297073 : List Nat := [1, 2, 2, 2, 1, 1, 12]
def baseStart_297073 : Nat := 118140960795 + 297073 * 2 ^ 59
def prefixEnd_297073 : Nat := 4983230072969 + 3 ^ 40 * 297073 * 2
def baseEnd_297073 : Nat := 7532900665344268356607

theorem tailTrace_297073 : CollatzResearch.WordTrace tailWord_297073 prefixEnd_297073 7532900665344268356607 := by
  unfold tailWord_297073
  simp only [CollatzResearch.WordTrace]
  refine ⟨10835142452762731874207873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7223428301841821249471915 10835142452762731874207873)
  ·
    refine ⟨8126356839572048905655905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10835142452762731874207873 8126356839572048905655905)
    ·
      refine ⟨6094767629679036679241929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8126356839572048905655905 6094767629679036679241929)
      ·
        refine ⟨4571075722259277509431447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6094767629679036679241929 4571075722259277509431447)
        ·
          refine ⟨6856613583388916264147171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4571075722259277509431447 6856613583388916264147171)
          ·
            refine ⟨10284920375083374396220757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6856613583388916264147171 10284920375083374396220757)
            ·
              refine ⟨7532900665344268356607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 10284920375083374396220757 7532900665344268356607)
              ·
                rfl

theorem cell21_297073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 12].length) (baseStart_297073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_297073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_297073 prefixEnd_297073 := by exact prefixLift 297073
  have htrace : WordTrace (prefixWord ++ tailWord_297073) baseStart_297073 baseEnd_297073 := by
    simpa [prefixWord, tailWord_297073, baseEnd_297073] using wordTrace_append hprefix tailTrace_297073
  have hstable : (prefixWord ++ tailWord_297073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297073).length < 2 ^ (prefixWord ++ tailWord_297073).sum := by decide
  have hdescent : baseEnd_297073 < baseStart_297073 := by decide
  rcases family_descends (prefixWord ++ tailWord_297073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297093 : List Nat := [1, 3, 1, 1, 5, 2, 3, 1, 4]
def baseStart_297093 : Nat := 118140960795 + 297093 * 2 ^ 59
def prefixEnd_297093 : Nat := 4983230072969 + 3 ^ 40 * 297093 * 2
def baseEnd_297093 : Nat := 67800670260582824876089

theorem tailTrace_297093 : CollatzResearch.WordTrace tailWord_297093 prefixEnd_297093 67800670260582824876089 := by
  unfold tailWord_297093
  simp only [CollatzResearch.WordTrace]
  refine ⟨10835871912690275289935933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7223914608460183526623955 10835871912690275289935933)
  ·
    refine ⟨4063451967258853233725975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10835871912690275289935933 4063451967258853233725975)
    ·
      refine ⟨6095177950888279850588963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4063451967258853233725975 6095177950888279850588963)
      ·
        refine ⟨9142766926332419775883445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6095177950888279850588963 9142766926332419775883445)
        ·
          refine ⟨857134399343664353989073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9142766926332419775883445 857134399343664353989073)
          ·
            refine ⟨642850799507748265491805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 857134399343664353989073 642850799507748265491805)
            ·
              refine ⟨241069049815405599559427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 642850799507748265491805 241069049815405599559427)
              ·
                refine ⟨361603574723108399339141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 241069049815405599559427 361603574723108399339141)
                ·
                  refine ⟨67800670260582824876089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 361603574723108399339141 67800670260582824876089)
                  ·
                    rfl

theorem cell21_297093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 4].length) (baseStart_297093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_297093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_297093 prefixEnd_297093 := by exact prefixLift 297093
  have htrace : WordTrace (prefixWord ++ tailWord_297093) baseStart_297093 baseEnd_297093 := by
    simpa [prefixWord, tailWord_297093, baseEnd_297093] using wordTrace_append hprefix tailTrace_297093
  have hstable : (prefixWord ++ tailWord_297093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297093).length < 2 ^ (prefixWord ++ tailWord_297093).sum := by decide
  have hdescent : baseEnd_297093 < baseStart_297093 := by decide
  rcases family_descends (prefixWord ++ tailWord_297093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297104 : List Nat := [2, 1, 1, 1, 1, 1, 5, 4, 5]
def baseStart_297104 : Nat := 118140960795 + 297104 * 2 ^ 59
def prefixEnd_297104 : Nat := 4983230072969 + 3 ^ 40 * 297104 * 2
def baseEnd_297104 : Nat := 67803180610449250192733

theorem tailTrace_297104 : CollatzResearch.WordTrace tailWord_297104 prefixEnd_297104 67803180610449250192733 := by
  unfold tailWord_297104
  simp only [CollatzResearch.WordTrace]
  refine ⟨5418136557825212084293183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7224182077100282779057577 5418136557825212084293183)
  ·
    refine ⟨8127204836737818126439775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5418136557825212084293183 8127204836737818126439775)
    ·
      refine ⟨12190807255106727189659663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8127204836737818126439775 12190807255106727189659663)
      ·
        refine ⟨18286210882660090784489495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12190807255106727189659663 18286210882660090784489495)
        ·
          refine ⟨27429316323990136176734243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18286210882660090784489495 27429316323990136176734243)
          ·
            refine ⟨41143974485985204265101365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27429316323990136176734243 41143974485985204265101365)
            ·
              refine ⟨3857247608061112899853253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41143974485985204265101365 3857247608061112899853253)
              ·
                refine ⟨723233926511458668722485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3857247608061112899853253 723233926511458668722485)
                ·
                  refine ⟨67803180610449250192733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 723233926511458668722485 67803180610449250192733)
                  ·
                    rfl

theorem cell21_297104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 5].length) (baseStart_297104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_297104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_297104 prefixEnd_297104 := by exact prefixLift 297104
  have htrace : WordTrace (prefixWord ++ tailWord_297104) baseStart_297104 baseEnd_297104 := by
    simpa [prefixWord, tailWord_297104, baseEnd_297104] using wordTrace_append hprefix tailTrace_297104
  have hstable : (prefixWord ++ tailWord_297104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297104).length < 2 ^ (prefixWord ++ tailWord_297104).sum := by decide
  have hdescent : baseEnd_297104 < baseStart_297104 := by decide
  rcases family_descends (prefixWord ++ tailWord_297104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297135 : List Nat := [1, 1, 2, 1, 2, 3, 1, 6, 4]
def baseStart_297135 : Nat := 118140960795 + 297135 * 2 ^ 59
def prefixEnd_297135 : Nat := 4983230072969 + 3 ^ 40 * 297135 * 2
def baseEnd_297135 : Nat := 67810255232800085176003

theorem tailTrace_297135 : CollatzResearch.WordTrace tailWord_297135 prefixEnd_297135 67810255232800085176003 := by
  unfold tailWord_297135
  simp only [CollatzResearch.WordTrace]
  refine ⟨10837403778538116462964859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7224935852358744308643239 10837403778538116462964859)
  ·
    refine ⟨16256105667807174694447289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10837403778538116462964859 16256105667807174694447289)
    ·
      refine ⟨12192079250855381020835467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16256105667807174694447289 12192079250855381020835467)
      ·
        refine ⟨18288118876283071531253201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12192079250855381020835467 18288118876283071531253201)
        ·
          refine ⟨13716089157212303648439901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18288118876283071531253201 13716089157212303648439901)
          ·
            refine ⟨5143533433954613868164963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13716089157212303648439901 5143533433954613868164963)
            ·
              refine ⟨7715300150931920802247445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5143533433954613868164963 7715300150931920802247445)
              ·
                refine ⟨361654694574933787605349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7715300150931920802247445 361654694574933787605349)
                ·
                  refine ⟨67810255232800085176003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 361654694574933787605349 67810255232800085176003)
                  ·
                    rfl

theorem cell21_297135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 4].length) (baseStart_297135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_297135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_297135 prefixEnd_297135 := by exact prefixLift 297135
  have htrace : WordTrace (prefixWord ++ tailWord_297135) baseStart_297135 baseEnd_297135 := by
    simpa [prefixWord, tailWord_297135, baseEnd_297135] using wordTrace_append hprefix tailTrace_297135
  have hstable : (prefixWord ++ tailWord_297135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297135).length < 2 ^ (prefixWord ++ tailWord_297135).sum := by decide
  have hdescent : baseEnd_297135 < baseStart_297135 := by decide
  rcases family_descends (prefixWord ++ tailWord_297135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297152 : List Nat := [2, 1, 1, 2, 5, 2, 1, 3, 4]
def baseStart_297152 : Nat := 118140960795 + 297152 * 2 ^ 59
def prefixEnd_297152 : Nat := 4983230072969 + 3 ^ 40 * 297152 * 2
def baseEnd_297152 : Nat := 67814134864411833392635

theorem tailTrace_297152 : CollatzResearch.WordTrace tailWord_297152 prefixEnd_297152 67814134864411833392635 := by
  unfold tailWord_297152
  simp only [CollatzResearch.WordTrace]
  refine ⟨5419011909738264183166855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7225349212984352244222473 5419011909738264183166855)
  ·
    refine ⟨8128517864607396274750283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5419011909738264183166855 8128517864607396274750283)
    ·
      refine ⟨12192776796911094412125425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8128517864607396274750283 12192776796911094412125425)
      ·
        refine ⟨9144582597683320809094069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12192776796911094412125425 9144582597683320809094069)
        ·
          refine ⟨857304618532811325852569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9144582597683320809094069 857304618532811325852569)
          ·
            refine ⟨642978463899608494389427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 857304618532811325852569 642978463899608494389427)
            ·
              refine ⟨964467695849412741584141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 642978463899608494389427 964467695849412741584141)
              ·
                refine ⟨361675385943529778094053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 964467695849412741584141 361675385943529778094053)
                ·
                  refine ⟨67814134864411833392635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 361675385943529778094053 67814134864411833392635)
                  ·
                    rfl

theorem cell21_297152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 4].length) (baseStart_297152 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_297152 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_297152 prefixEnd_297152 := by exact prefixLift 297152
  have htrace : WordTrace (prefixWord ++ tailWord_297152) baseStart_297152 baseEnd_297152 := by
    simpa [prefixWord, tailWord_297152, baseEnd_297152] using wordTrace_append hprefix tailTrace_297152
  have hstable : (prefixWord ++ tailWord_297152).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297152).length < 2 ^ (prefixWord ++ tailWord_297152).sum := by decide
  have hdescent : baseEnd_297152 < baseStart_297152 := by decide
  rcases family_descends (prefixWord ++ tailWord_297152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297166 : List Nat := [4, 1, 1, 1, 4, 1, 2, 7]
def baseStart_297166 : Nat := 118140960795 + 297166 * 2 ^ 59
def prefixEnd_297166 : Nat := 4983230072969 + 3 ^ 40 * 297166 * 2
def baseEnd_297166 : Nat := 22605776618383640053091

theorem tailTrace_297166 : CollatzResearch.WordTrace tailWord_297166 prefixEnd_297166 22605776618383640053091 := by
  unfold tailWord_297166
  simp only [CollatzResearch.WordTrace]
  refine ⟨1354816805178226094667919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7225689627617205838228901 1354816805178226094667919)
  ·
    refine ⟨2032225207767339142001879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1354816805178226094667919 2032225207767339142001879)
    ·
      refine ⟨3048337811651008713002819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2032225207767339142001879 3048337811651008713002819)
      ·
        refine ⟨4572506717476513069504229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3048337811651008713002819 4572506717476513069504229)
        ·
          refine ⟨857345009526846200532043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4572506717476513069504229 857345009526846200532043)
          ·
            refine ⟨1286017514290269300798065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 857345009526846200532043 1286017514290269300798065)
            ·
              refine ⟨964513135717701975598549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1286017514290269300798065 964513135717701975598549)
              ·
                refine ⟨22605776618383640053091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 964513135717701975598549 22605776618383640053091)
                ·
                  rfl

theorem cell21_297166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_297166 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_297166 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_297166 prefixEnd_297166 := by exact prefixLift 297166
  have htrace : WordTrace (prefixWord ++ tailWord_297166) baseStart_297166 baseEnd_297166 := by
    simpa [prefixWord, tailWord_297166, baseEnd_297166] using wordTrace_append hprefix tailTrace_297166
  have hstable : (prefixWord ++ tailWord_297166).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297166).length < 2 ^ (prefixWord ++ tailWord_297166).sum := by decide
  have hdescent : baseEnd_297166 < baseStart_297166 := by decide
  rcases family_descends (prefixWord ++ tailWord_297166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297242 : List Nat := [3, 1, 1, 3, 4, 1, 8]
def baseStart_297242 : Nat := 118140960795 + 297242 * 2 ^ 59
def prefixEnd_297242 : Nat := 4983230072969 + 3 ^ 40 * 297242 * 2
def baseEnd_297242 : Nat := 7537186010065741876939

theorem tailTrace_297242 : CollatzResearch.WordTrace tailWord_297242 prefixEnd_297242 7537186010065741876939 := by
  unfold tailWord_297242
  simp only [CollatzResearch.WordTrace]
  refine ⟨2710326597287618434277495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7227537592766982491406653 2710326597287618434277495)
  ·
    refine ⟨4065489895931427651416243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2710326597287618434277495 4065489895931427651416243)
    ·
      refine ⟨6098234843897141477124365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4065489895931427651416243 6098234843897141477124365)
      ·
        refine ⟨2286838066461428053921637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6098234843897141477124365 2286838066461428053921637)
        ·
          refine ⟨428782137461517760110307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2286838066461428053921637 428782137461517760110307)
          ·
            refine ⟨643173206192276640165461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428782137461517760110307 643173206192276640165461)
            ·
              refine ⟨7537186010065741876939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 643173206192276640165461 7537186010065741876939)
              ·
                rfl

theorem cell21_297242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 8].length) (baseStart_297242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_297242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_297242 prefixEnd_297242 := by exact prefixLift 297242
  have htrace : WordTrace (prefixWord ++ tailWord_297242) baseStart_297242 baseEnd_297242 := by
    simpa [prefixWord, tailWord_297242, baseEnd_297242] using wordTrace_append hprefix tailTrace_297242
  have hstable : (prefixWord ++ tailWord_297242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297242).length < 2 ^ (prefixWord ++ tailWord_297242).sum := by decide
  have hdescent : baseEnd_297242 < baseStart_297242 := by decide
  rcases family_descends (prefixWord ++ tailWord_297242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297273 : List Nat := [1, 2, 1, 6, 1, 1, 2, 2, 5]
def baseStart_297273 : Nat := 118140960795 + 297273 * 2 ^ 59
def prefixEnd_297273 : Nat := 4983230072969 + 3 ^ 40 * 297273 * 2
def baseEnd_297273 : Nat := 67841748712942511875721

theorem tailTrace_297273 : CollatzResearch.WordTrace tailWord_297273 prefixEnd_297273 67841748712942511875721 := by
  unfold tailWord_297273
  simp only [CollatzResearch.WordTrace]
  refine ⟨10842437052038166031488473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7228291368025444020992315 10842437052038166031488473)
  ·
    refine ⟨8131827789028624523616355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10842437052038166031488473 8131827789028624523616355)
    ·
      refine ⟨12197741683542936785424533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8131827789028624523616355 12197741683542936785424533)
      ·
        refine ⟨571769141416075161816775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12197741683542936785424533 571769141416075161816775)
        ·
          refine ⟨857653712124112742725163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 571769141416075161816775 857653712124112742725163)
          ·
            refine ⟨1286480568186169114087745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 857653712124112742725163 1286480568186169114087745)
            ·
              refine ⟨964860426139626835565809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1286480568186169114087745 964860426139626835565809)
              ·
                refine ⟨723645319604720126674357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 964860426139626835565809 723645319604720126674357)
                ·
                  refine ⟨67841748712942511875721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 723645319604720126674357 67841748712942511875721)
                  ·
                    rfl

theorem cell21_297273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 5].length) (baseStart_297273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_297273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_297273 prefixEnd_297273 := by exact prefixLift 297273
  have htrace : WordTrace (prefixWord ++ tailWord_297273) baseStart_297273 baseEnd_297273 := by
    simpa [prefixWord, tailWord_297273, baseEnd_297273] using wordTrace_append hprefix tailTrace_297273
  have hstable : (prefixWord ++ tailWord_297273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297273).length < 2 ^ (prefixWord ++ tailWord_297273).sum := by decide
  have hdescent : baseEnd_297273 < baseStart_297273 := by decide
  rcases family_descends (prefixWord ++ tailWord_297273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297310 : List Nat := [4, 4, 2, 1, 1, 1, 2, 6]
def baseStart_297310 : Nat := 118140960795 + 297310 * 2 ^ 59
def prefixEnd_297310 : Nat := 4983230072969 + 3 ^ 40 * 297310 * 2
def baseEnd_297310 : Nat := 22616730872346223252993

theorem tailTrace_297310 : CollatzResearch.WordTrace tailWord_297310 prefixEnd_297310 22616730872346223252993 := by
  unfold tailWord_297310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1355473319113015168823173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7229191035269414233723589 1355473319113015168823173)
  ·
    refine ⟨254151247333690344154345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1355473319113015168823173 254151247333690344154345)
    ·
      refine ⟨190613435500267758115759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254151247333690344154345 190613435500267758115759)
      ·
        refine ⟨285920153250401637173639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190613435500267758115759 285920153250401637173639)
        ·
          refine ⟨428880229875602455760459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285920153250401637173639 428880229875602455760459)
          ·
            refine ⟨643320344813403683640689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428880229875602455760459 643320344813403683640689)
            ·
              refine ⟨482490258610052762730517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 643320344813403683640689 482490258610052762730517)
              ·
                refine ⟨22616730872346223252993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 482490258610052762730517 22616730872346223252993)
                ·
                  rfl

theorem cell21_297310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 6].length) (baseStart_297310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_297310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_297310 prefixEnd_297310 := by exact prefixLift 297310
  have htrace : WordTrace (prefixWord ++ tailWord_297310) baseStart_297310 baseEnd_297310 := by
    simpa [prefixWord, tailWord_297310, baseEnd_297310] using wordTrace_append hprefix tailTrace_297310
  have hstable : (prefixWord ++ tailWord_297310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297310).length < 2 ^ (prefixWord ++ tailWord_297310).sum := by decide
  have hdescent : baseEnd_297310 < baseStart_297310 := by decide
  rcases family_descends (prefixWord ++ tailWord_297310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297349 : List Nat := [1, 3, 1, 1, 3, 1, 1, 7, 3]
def baseStart_297349 : Nat := 118140960795 + 297349 * 2 ^ 59
def prefixEnd_297349 : Nat := 4983230072969 + 3 ^ 40 * 297349 * 2
def baseEnd_297349 : Nat := 67859092948383268608899

theorem tailTrace_297349 : CollatzResearch.WordTrace tailWord_297349 prefixEnd_297349 67859092948383268608899 := by
  unfold tailWord_297349
  simp only [CollatzResearch.WordTrace]
  refine ⟨10845208999762831011255101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7230139333175220674170067 10845208999762831011255101)
  ·
    refine ⟨4066953374911061629220663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10845208999762831011255101 4066953374911061629220663)
    ·
      refine ⟨6100430062366592443830995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4066953374911061629220663 6100430062366592443830995)
      ·
        refine ⟨9150645093549888665746493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6100430062366592443830995 9150645093549888665746493)
        ·
          refine ⟨3431491910081208249654935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9150645093549888665746493 3431491910081208249654935)
          ·
            refine ⟨5147237865121812374482403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3431491910081208249654935 5147237865121812374482403)
            ·
              refine ⟨7720856797682718561723605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5147237865121812374482403 7720856797682718561723605)
              ·
                refine ⟨180957581195688716290397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 7720856797682718561723605 180957581195688716290397)
                ·
                  refine ⟨67859092948383268608899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 180957581195688716290397 67859092948383268608899)
                  ·
                    rfl

theorem cell21_297349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 7, 3].length) (baseStart_297349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_297349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_297349 prefixEnd_297349 := by exact prefixLift 297349
  have htrace : WordTrace (prefixWord ++ tailWord_297349) baseStart_297349 baseEnd_297349 := by
    simpa [prefixWord, tailWord_297349, baseEnd_297349] using wordTrace_append hprefix tailTrace_297349
  have hstable : (prefixWord ++ tailWord_297349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297349).length < 2 ^ (prefixWord ++ tailWord_297349).sum := by decide
  have hdescent : baseEnd_297349 < baseStart_297349 := by decide
  rcases family_descends (prefixWord ++ tailWord_297349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297394 : List Nat := [3, 2, 1, 1, 1, 1, 7, 5]
def baseStart_297394 : Nat := 118140960795 + 297394 * 2 ^ 59
def prefixEnd_297394 : Nat := 4983230072969 + 3 ^ 40 * 297394 * 2
def baseEnd_297394 : Nat := 22623120853824396786269

theorem tailTrace_297394 : CollatzResearch.WordTrace tailWord_297394 prefixEnd_297394 22623120853824396786269 := by
  unfold tailWord_297394
  simp only [CollatzResearch.WordTrace]
  refine ⟨2711712571149950924160809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7231233523066535797762157 2711712571149950924160809)
  ·
    refine ⟨2033784428362463193120607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2711712571149950924160809 2033784428362463193120607)
    ·
      refine ⟨3050676642543694789680911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2033784428362463193120607 3050676642543694789680911)
      ·
        refine ⟨4576014963815542184521367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3050676642543694789680911 4576014963815542184521367)
        ·
          refine ⟨6864022445723313276782051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4576014963815542184521367 6864022445723313276782051)
          ·
            refine ⟨10296033668584969915173077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6864022445723313276782051 10296033668584969915173077)
            ·
              refine ⟨241313289107460232386869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 10296033668584969915173077 241313289107460232386869)
              ·
                refine ⟨22623120853824396786269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 241313289107460232386869 22623120853824396786269)
                ·
                  rfl

theorem cell21_297394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 5].length) (baseStart_297394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_297394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_297394 prefixEnd_297394 := by exact prefixLift 297394
  have htrace : WordTrace (prefixWord ++ tailWord_297394) baseStart_297394 baseEnd_297394 := by
    simpa [prefixWord, tailWord_297394, baseEnd_297394] using wordTrace_append hprefix tailTrace_297394
  have hstable : (prefixWord ++ tailWord_297394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297394).length < 2 ^ (prefixWord ++ tailWord_297394).sum := by decide
  have hdescent : baseEnd_297394 < baseStart_297394 := by decide
  rcases family_descends (prefixWord ++ tailWord_297394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297532 : List Nat := [2, 2, 2, 2, 3, 2, 2, 2, 4]
def baseStart_297532 : Nat := 118140960795 + 297532 * 2 ^ 59
def prefixEnd_297532 : Nat := 4983230072969 + 3 ^ 40 * 297532 * 2
def baseEnd_297532 : Nat := 67900856041615617058525

theorem tailTrace_297532 : CollatzResearch.WordTrace tailWord_297532 prefixEnd_297532 67900856041615617058525 := by
  unfold tailWord_297532
  simp only [CollatzResearch.WordTrace]
  refine ⟨5425941779049926632583425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7234589038733235510111233 5425941779049926632583425)
  ·
    refine ⟨4069456334287444974437569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5425941779049926632583425 4069456334287444974437569)
    ·
      refine ⟨3052092250715583730828177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4069456334287444974437569 3052092250715583730828177)
      ·
        refine ⟨2289069188036687798121133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3052092250715583730828177 2289069188036687798121133)
        ·
          refine ⟨858400945513757924295425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2289069188036687798121133 858400945513757924295425)
          ·
            refine ⟨643800709135318443221569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 858400945513757924295425 643800709135318443221569)
            ·
              refine ⟨482850531851488832416177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 643800709135318443221569 482850531851488832416177)
              ·
                refine ⟨362137898888616624312133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 482850531851488832416177 362137898888616624312133)
                ·
                  refine ⟨67900856041615617058525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 362137898888616624312133 67900856041615617058525)
                  ·
                    rfl

theorem cell21_297532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 4].length) (baseStart_297532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_297532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_297532 prefixEnd_297532 := by exact prefixLift 297532
  have htrace : WordTrace (prefixWord ++ tailWord_297532) baseStart_297532 baseEnd_297532 := by
    simpa [prefixWord, tailWord_297532, baseEnd_297532] using wordTrace_append hprefix tailTrace_297532
  have hstable : (prefixWord ++ tailWord_297532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297532).length < 2 ^ (prefixWord ++ tailWord_297532).sum := by decide
  have hdescent : baseEnd_297532 < baseStart_297532 := by decide
  rcases family_descends (prefixWord ++ tailWord_297532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297546 : List Nat := [3, 1, 2, 1, 1, 6, 1, 6]
def baseStart_297546 : Nat := 118140960795 + 297546 * 2 ^ 59
def prefixEnd_297546 : Nat := 4983230072969 + 3 ^ 40 * 297546 * 2
def baseEnd_297546 : Nat := 22634683677451567941721

theorem tailTrace_297546 : CollatzResearch.WordTrace tailWord_297546 prefixEnd_297546 22634683677451567941721 := by
  unfold tailWord_297546
  simp only [CollatzResearch.WordTrace]
  refine ⟨2713098545012283414044123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7234929453366089104117661 2713098545012283414044123)
  ·
    refine ⟨4069647817518425121066185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2713098545012283414044123 4069647817518425121066185)
    ·
      refine ⟨3052235863138818840799639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4069647817518425121066185 3052235863138818840799639)
      ·
        refine ⟨4578353794708228261199459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3052235863138818840799639 4578353794708228261199459)
        ·
          refine ⟨6867530692062342391799189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4578353794708228261199459 6867530692062342391799189)
          ·
            refine ⟨321915501190422299615587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6867530692062342391799189 321915501190422299615587)
            ·
              refine ⟨482873251785633449423381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321915501190422299615587 482873251785633449423381)
              ·
                refine ⟨22634683677451567941721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 482873251785633449423381 22634683677451567941721)
                ·
                  rfl

theorem cell21_297546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 6].length) (baseStart_297546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_297546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_297546 prefixEnd_297546 := by exact prefixLift 297546
  have htrace : WordTrace (prefixWord ++ tailWord_297546) baseStart_297546 baseEnd_297546 := by
    simpa [prefixWord, tailWord_297546, baseEnd_297546] using wordTrace_append hprefix tailTrace_297546
  have hstable : (prefixWord ++ tailWord_297546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297546).length < 2 ^ (prefixWord ++ tailWord_297546).sum := by decide
  have hdescent : baseEnd_297546 < baseStart_297546 := by decide
  rcases family_descends (prefixWord ++ tailWord_297546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297591 : List Nat := [1, 1, 3, 1, 1, 3, 5, 2, 4]
def baseStart_297591 : Nat := 118140960795 + 297591 * 2 ^ 59
def prefixEnd_297591 : Nat := 4983230072969 + 3 ^ 40 * 297591 * 2
def baseEnd_297591 : Nat := 67914320645444625575071

theorem tailTrace_297591 : CollatzResearch.WordTrace tailWord_297591 prefixEnd_297591 67914320645444625575071 := by
  unfold tailWord_297591
  simp only [CollatzResearch.WordTrace]
  refine ⟨10854035464886106341564627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7236023643257404227709751 10854035464886106341564627)
  ·
    refine ⟨16281053197329159512346941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10854035464886106341564627 16281053197329159512346941)
    ·
      refine ⟨6105394948998434817130103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16281053197329159512346941 6105394948998434817130103)
      ·
        refine ⟨9158092423497652225695155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6105394948998434817130103 9158092423497652225695155)
        ·
          refine ⟨13737138635246478338542733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9158092423497652225695155 13737138635246478338542733)
          ·
            refine ⟨5151426988217429376953525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13737138635246478338542733 5151426988217429376953525)
            ·
              refine ⟨482946280145384004089393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5151426988217429376953525 482946280145384004089393)
              ·
                refine ⟨362209710109038003067045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 482946280145384004089393 362209710109038003067045)
                ·
                  refine ⟨67914320645444625575071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 362209710109038003067045 67914320645444625575071)
                  ·
                    rfl

theorem cell21_297591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 4].length) (baseStart_297591 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_297591 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_297591 prefixEnd_297591 := by exact prefixLift 297591
  have htrace : WordTrace (prefixWord ++ tailWord_297591) baseStart_297591 baseEnd_297591 := by
    simpa [prefixWord, tailWord_297591, baseEnd_297591] using wordTrace_append hprefix tailTrace_297591
  have hstable : (prefixWord ++ tailWord_297591).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297591).length < 2 ^ (prefixWord ++ tailWord_297591).sum := by decide
  have hdescent : baseEnd_297591 < baseStart_297591 := by decide
  rcases family_descends (prefixWord ++ tailWord_297591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297639 : List Nat := [1, 1, 6, 3, 1, 2, 7]
def baseStart_297639 : Nat := 118140960795 + 297639 * 2 ^ 59
def prefixEnd_297639 : Nat := 4983230072969 + 3 ^ 40 * 297639 * 2
def baseEnd_297639 : Nat := 7547252766600800974997

theorem tailTrace_297639 : CollatzResearch.WordTrace tailWord_297639 prefixEnd_297639 7547252766600800974997 := by
  unfold tailWord_297639
  simp only [CollatzResearch.WordTrace]
  refine ⟨10855786168712210539311971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7237190779141473692874647 10855786168712210539311971)
  ·
    refine ⟨16283679253068315808967957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10855786168712210539311971 16283679253068315808967957)
    ·
      refine ⟨763297464987577303545373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16283679253068315808967957 763297464987577303545373)
      ·
        refine ⟨286236549370341488829515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 763297464987577303545373 286236549370341488829515)
        ·
          refine ⟨429354824055512233244273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286236549370341488829515 429354824055512233244273)
          ·
            refine ⟨322016118041634174933205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 429354824055512233244273 322016118041634174933205)
            ·
              refine ⟨7547252766600800974997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 322016118041634174933205 7547252766600800974997)
              ·
                rfl

theorem cell21_297639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 7].length) (baseStart_297639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_297639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_297639 prefixEnd_297639 := by exact prefixLift 297639
  have htrace : WordTrace (prefixWord ++ tailWord_297639) baseStart_297639 baseEnd_297639 := by
    simpa [prefixWord, tailWord_297639, baseEnd_297639] using wordTrace_append hprefix tailTrace_297639
  have hstable : (prefixWord ++ tailWord_297639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297639).length < 2 ^ (prefixWord ++ tailWord_297639).sum := by decide
  have hdescent : baseEnd_297639 < baseStart_297639 := by decide
  rcases family_descends (prefixWord ++ tailWord_297639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297653 : List Nat := [1, 3, 3, 3, 1, 1, 3, 1, 5]
def baseStart_297653 : Nat := 118140960795 + 297653 * 2 ^ 59
def prefixEnd_297653 : Nat := 4983230072969 + 3 ^ 40 * 297653 * 2
def baseEnd_297653 : Nat := 67928469890146295541611

theorem tailTrace_297653 : CollatzResearch.WordTrace tailWord_297653 prefixEnd_297653 67928469890146295541611 := by
  unfold tailWord_297653
  simp only [CollatzResearch.WordTrace]
  refine ⟨10856296790661490930321613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7237531193774327286881075 10856296790661490930321613)
  ·
    refine ⟨4071111296498059098870605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10856296790661490930321613 4071111296498059098870605)
    ·
      refine ⟨1526666736186772162076477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4071111296498059098870605 1526666736186772162076477)
      ·
        refine ⟨572500026070039560778679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1526666736186772162076477 572500026070039560778679)
        ·
          refine ⟨858750039105059341168019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 572500026070039560778679 858750039105059341168019)
          ·
            refine ⟨1288125058657589011752029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 858750039105059341168019 1288125058657589011752029)
            ·
              refine ⟨483046896996595879407011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1288125058657589011752029 483046896996595879407011)
              ·
                refine ⟨724570345494893819110517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 483046896996595879407011 724570345494893819110517)
                ·
                  refine ⟨67928469890146295541611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 724570345494893819110517 67928469890146295541611)
                  ·
                    rfl

theorem cell21_297653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 5].length) (baseStart_297653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_297653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_297653 prefixEnd_297653 := by exact prefixLift 297653
  have htrace : WordTrace (prefixWord ++ tailWord_297653) baseStart_297653 baseEnd_297653 := by
    simpa [prefixWord, tailWord_297653, baseEnd_297653] using wordTrace_append hprefix tailTrace_297653
  have hstable : (prefixWord ++ tailWord_297653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297653).length < 2 ^ (prefixWord ++ tailWord_297653).sum := by decide
  have hdescent : baseEnd_297653 < baseStart_297653 := by decide
  rcases family_descends (prefixWord ++ tailWord_297653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297704 : List Nat := [2, 1, 4, 1, 5, 1, 2, 2, 3]
def baseStart_297704 : Nat := 118140960795 + 297704 * 2 ^ 59
def prefixEnd_297704 : Nat := 4983230072969 + 3 ^ 40 * 297704 * 2
def baseEnd_297704 : Nat := 67940108784981540191507

theorem tailTrace_297704 : CollatzResearch.WordTrace tailWord_297704 prefixEnd_297704 67940108784981540191507 := by
  unfold tailWord_297704
  simp only [CollatzResearch.WordTrace]
  refine ⟨5429078456738363320214083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7238771275651151093618777 5429078456738363320214083)
  ·
    refine ⟨8143617685107544980321125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5429078456738363320214083 8143617685107544980321125)
    ·
      refine ⟨1526928315957664683810211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8143617685107544980321125 1526928315957664683810211)
      ·
        refine ⟨2290392473936497025715317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1526928315957664683810211 2290392473936497025715317)
        ·
          refine ⟨214724294431546596160811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2290392473936497025715317 214724294431546596160811)
          ·
            refine ⟨322086441647319894241217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214724294431546596160811 322086441647319894241217)
            ·
              refine ⟨241564831235489920680913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 322086441647319894241217 241564831235489920680913)
              ·
                refine ⟨181173623426617440510685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 241564831235489920680913 181173623426617440510685)
                ·
                  refine ⟨67940108784981540191507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 181173623426617440510685 67940108784981540191507)
                  ·
                    rfl

theorem cell21_297704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 2, 3].length) (baseStart_297704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_297704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_297704 prefixEnd_297704 := by exact prefixLift 297704
  have htrace : WordTrace (prefixWord ++ tailWord_297704) baseStart_297704 baseEnd_297704 := by
    simpa [prefixWord, tailWord_297704, baseEnd_297704] using wordTrace_append hprefix tailTrace_297704
  have hstable : (prefixWord ++ tailWord_297704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297704).length < 2 ^ (prefixWord ++ tailWord_297704).sum := by decide
  have hdescent : baseEnd_297704 < baseStart_297704 := by decide
  rcases family_descends (prefixWord ++ tailWord_297704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297760 : List Nat := [2, 1, 1, 5, 1, 4, 1, 2, 4]
def baseStart_297760 : Nat := 118140960795 + 297760 * 2 ^ 59
def prefixEnd_297760 : Nat := 4983230072969 + 3 ^ 40 * 297760 * 2
def baseEnd_297760 : Nat := 67952888747937887258059

theorem tailTrace_297760 : CollatzResearch.WordTrace tailWord_297760 prefixEnd_297760 67952888747937887258059 := by
  unfold tailWord_297760
  simp only [CollatzResearch.WordTrace]
  refine ⟨5430099700636924102233367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7240132934182565469644489 5430099700636924102233367)
  ·
    refine ⟨8145149550955386153350051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5430099700636924102233367 8145149550955386153350051)
    ·
      refine ⟨12217724326433079230025077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8145149550955386153350051 12217724326433079230025077)
      ·
        refine ⟨1145411655603101177814851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12217724326433079230025077 1145411655603101177814851)
        ·
          refine ⟨1718117483404651766722277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1145411655603101177814851 1718117483404651766722277)
          ·
            refine ⟨322147028138372206260427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1718117483404651766722277 322147028138372206260427)
            ·
              refine ⟨483220542207558309390641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322147028138372206260427 483220542207558309390641)
              ·
                refine ⟨362415406655668732042981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 483220542207558309390641 362415406655668732042981)
                ·
                  refine ⟨67952888747937887258059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 362415406655668732042981 67952888747937887258059)
                  ·
                    rfl

theorem cell21_297760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 4].length) (baseStart_297760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_297760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_297760 prefixEnd_297760 := by exact prefixLift 297760
  have htrace : WordTrace (prefixWord ++ tailWord_297760) baseStart_297760 baseEnd_297760 := by
    simpa [prefixWord, tailWord_297760, baseEnd_297760] using wordTrace_append hprefix tailTrace_297760
  have hstable : (prefixWord ++ tailWord_297760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297760).length < 2 ^ (prefixWord ++ tailWord_297760).sum := by decide
  have hdescent : baseEnd_297760 < baseStart_297760 := by decide
  rcases family_descends (prefixWord ++ tailWord_297760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297771 : List Nat := [1, 1, 1, 1, 2, 1, 2, 7, 5]
def baseStart_297771 : Nat := 118140960795 + 297771 * 2 ^ 59
def prefixEnd_297771 : Nat := 4983230072969 + 3 ^ 40 * 297771 * 2
def baseEnd_297771 : Nat := 67955399097804312574703

theorem tailTrace_297771 : CollatzResearch.WordTrace tailWord_297771 prefixEnd_297771 67955399097804312574703 := by
  unfold tailWord_297771
  simp only [CollatzResearch.WordTrace]
  refine ⟨10860600604233997083117167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7240400402822664722078111 10860600604233997083117167)
  ·
    refine ⟨16290900906350995624675751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10860600604233997083117167 16290900906350995624675751)
    ·
      refine ⟨24436351359526493437013627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16290900906350995624675751 24436351359526493437013627)
      ·
        refine ⟨36654527039289740155520441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24436351359526493437013627 36654527039289740155520441)
        ·
          refine ⟨27490895279467305116640331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36654527039289740155520441 27490895279467305116640331)
          ·
            refine ⟨41236342919200957674960497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27490895279467305116640331 41236342919200957674960497)
            ·
              refine ⟨30927257189400718256220373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41236342919200957674960497 30927257189400718256220373)
              ·
                refine ⟨724857590376579334130165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 30927257189400718256220373 724857590376579334130165)
                ·
                  refine ⟨67955399097804312574703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 724857590376579334130165 67955399097804312574703)
                  ·
                    rfl

theorem cell21_297771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 5].length) (baseStart_297771 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_297771 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_297771 prefixEnd_297771 := by exact prefixLift 297771
  have htrace : WordTrace (prefixWord ++ tailWord_297771) baseStart_297771 baseEnd_297771 := by
    simpa [prefixWord, tailWord_297771, baseEnd_297771] using wordTrace_append hprefix tailTrace_297771
  have hstable : (prefixWord ++ tailWord_297771).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297771).length < 2 ^ (prefixWord ++ tailWord_297771).sum := by decide
  have hdescent : baseEnd_297771 < baseStart_297771 := by decide
  rcases family_descends (prefixWord ++ tailWord_297771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297847 : List Nat := [1, 1, 3, 1, 1, 2, 1, 6, 5]
def baseStart_297847 : Nat := 118140960795 + 297847 * 2 ^ 59
def prefixEnd_297847 : Nat := 4983230072969 + 3 ^ 40 * 297847 * 2
def baseEnd_297847 : Nat := 67972743333245069307881

theorem tailTrace_297847 : CollatzResearch.WordTrace tailWord_297847 prefixEnd_297847 67972743333245069307881 := by
  unfold tailWord_297847
  simp only [CollatzResearch.WordTrace]
  refine ⟨10863372551958662062883795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7242248367972441375255863 10863372551958662062883795)
  ·
    refine ⟨16295058827937993094325693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10863372551958662062883795 16295058827937993094325693)
    ·
      refine ⟨6110647060476747410372135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16295058827937993094325693 6110647060476747410372135)
      ·
        refine ⟨9165970590715121115558203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6110647060476747410372135 9165970590715121115558203)
        ·
          refine ⟨13748955886072681673337305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9165970590715121115558203 13748955886072681673337305)
          ·
            refine ⟨10311716914554511255002979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13748955886072681673337305 10311716914554511255002979)
            ·
              refine ⟨15467575371831766882504469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10311716914554511255002979 15467575371831766882504469)
              ·
                refine ⟨725042595554614072617397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15467575371831766882504469 725042595554614072617397)
                ·
                  refine ⟨67972743333245069307881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 725042595554614072617397 67972743333245069307881)
                  ·
                    rfl

theorem cell21_297847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 5].length) (baseStart_297847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_297847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_297847 prefixEnd_297847 := by exact prefixLift 297847
  have htrace : WordTrace (prefixWord ++ tailWord_297847) baseStart_297847 baseEnd_297847 := by
    simpa [prefixWord, tailWord_297847, baseEnd_297847] using wordTrace_append hprefix tailTrace_297847
  have hstable : (prefixWord ++ tailWord_297847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297847).length < 2 ^ (prefixWord ++ tailWord_297847).sum := by decide
  have hdescent : baseEnd_297847 < baseStart_297847 := by decide
  rcases family_descends (prefixWord ++ tailWord_297847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297940 : List Nat := [2, 4, 1, 2, 1, 2, 1, 3, 5]
def baseStart_297940 : Nat := 118140960795 + 297940 * 2 ^ 59
def prefixEnd_297940 : Nat := 4983230072969 + 3 ^ 40 * 297940 * 2
def baseEnd_297940 : Nat := 67993967200297574257691

theorem tailTrace_297940 : CollatzResearch.WordTrace tailWord_297940 prefixEnd_297940 67993967200297574257691 := by
  unfold tailWord_297940
  simp only [CollatzResearch.WordTrace]
  refine ⟨5433382270310869473009637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7244509693747825964012849 5433382270310869473009637)
  ·
    refine ⟨1018759175683288026189307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5433382270310869473009637 1018759175683288026189307)
    ·
      refine ⟨1528138763524932039283961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1018759175683288026189307 1528138763524932039283961)
      ·
        refine ⟨1146104072643699029462971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1528138763524932039283961 1146104072643699029462971)
        ·
          refine ⟨1719156108965548544194457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1146104072643699029462971 1719156108965548544194457)
          ·
            refine ⟨1289367081724161408145843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1719156108965548544194457 1289367081724161408145843)
            ·
              refine ⟨1934050622586242112218765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1289367081724161408145843 1934050622586242112218765)
              ·
                refine ⟨725268983469840792082037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1934050622586242112218765 725268983469840792082037)
                ·
                  refine ⟨67993967200297574257691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 725268983469840792082037 67993967200297574257691)
                  ·
                    rfl

theorem cell21_297940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_297940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_297940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_297940 prefixEnd_297940 := by exact prefixLift 297940
  have htrace : WordTrace (prefixWord ++ tailWord_297940) baseStart_297940 baseEnd_297940 := by
    simpa [prefixWord, tailWord_297940, baseEnd_297940] using wordTrace_append hprefix tailTrace_297940
  have hstable : (prefixWord ++ tailWord_297940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297940).length < 2 ^ (prefixWord ++ tailWord_297940).sum := by decide
  have hdescent : baseEnd_297940 < baseStart_297940 := by decide
  rcases family_descends (prefixWord ++ tailWord_297940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297974 : List Nat := [5, 1, 1, 1, 3, 1, 3, 3, 3]
def baseStart_297974 : Nat := 118140960795 + 297974 * 2 ^ 59
def prefixEnd_297974 : Nat := 4983230072969 + 3 ^ 40 * 297974 * 2
def baseEnd_297974 : Nat := 68001726463521070690955

theorem tailTrace_297974 : CollatzResearch.WordTrace tailWord_297974 prefixEnd_297974 68001726463521070690955 := by
  unfold tailWord_297974
  simp only [CollatzResearch.WordTrace]
  refine ⟨679250288906160172047311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7245336414999041835171317 679250288906160172047311)
  ·
    refine ⟨1018875433359240258070967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 679250288906160172047311 1018875433359240258070967)
    ·
      refine ⟨1528313150038860387106451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1018875433359240258070967 1528313150038860387106451)
      ·
        refine ⟨2292469725058290580659677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1528313150038860387106451 2292469725058290580659677)
        ·
          refine ⟨859676146896858967747379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2292469725058290580659677 859676146896858967747379)
          ·
            refine ⟨1289514220345288451621069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 859676146896858967747379 1289514220345288451621069)
            ·
              refine ⟨483567832629483169357901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1289514220345288451621069 483567832629483169357901)
              ·
                refine ⟨181337937236056188509213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 483567832629483169357901 181337937236056188509213)
                ·
                  refine ⟨68001726463521070690955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 181337937236056188509213 68001726463521070690955)
                  ·
                    rfl

theorem cell21_297974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_297974 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_297974 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_297974 prefixEnd_297974 := by exact prefixLift 297974
  have htrace : WordTrace (prefixWord ++ tailWord_297974) baseStart_297974 baseEnd_297974 := by
    simpa [prefixWord, tailWord_297974, baseEnd_297974] using wordTrace_append hprefix tailTrace_297974
  have hstable : (prefixWord ++ tailWord_297974).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297974).length < 2 ^ (prefixWord ++ tailWord_297974).sum := by decide
  have hdescent : baseEnd_297974 < baseStart_297974 := by decide
  rcases family_descends (prefixWord ++ tailWord_297974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297985 : List Nat := [1, 2, 4, 1, 2, 4, 7]
def baseStart_297985 : Nat := 118140960795 + 297985 * 2 ^ 59
def prefixEnd_297985 : Nat := 4983230072969 + 3 ^ 40 * 297985 * 2
def baseEnd_297985 : Nat := 7556026312598610667511

theorem tailTrace_297985 : CollatzResearch.WordTrace tailWord_297985 prefixEnd_297985 7556026312598610667511 := by
  unfold tailWord_297985
  simp only [CollatzResearch.WordTrace]
  refine ⟨10868405825458711631407409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7245603883639141087604939 10868405825458711631407409)
  ·
    refine ⟨8151304369094033723555557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10868405825458711631407409 8151304369094033723555557)
    ·
      refine ⟨1528369569205131323166667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8151304369094033723555557 1528369569205131323166667)
      ·
        refine ⟨2292554353807696984750001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1528369569205131323166667 2292554353807696984750001)
        ·
          refine ⟨1719415765355772738562501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2292554353807696984750001 1719415765355772738562501)
          ·
            refine ⟨322390456004207388480469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1719415765355772738562501 322390456004207388480469)
            ·
              refine ⟨7556026312598610667511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 322390456004207388480469 7556026312598610667511)
              ·
                rfl

theorem cell21_297985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 7].length) (baseStart_297985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_297985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_297985 prefixEnd_297985 := by exact prefixLift 297985
  have htrace : WordTrace (prefixWord ++ tailWord_297985) baseStart_297985 baseEnd_297985 := by
    simpa [prefixWord, tailWord_297985, baseEnd_297985] using wordTrace_append hprefix tailTrace_297985
  have hstable : (prefixWord ++ tailWord_297985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297985).length < 2 ^ (prefixWord ++ tailWord_297985).sum := by decide
  have hdescent : baseEnd_297985 < baseStart_297985 := by decide
  rcases family_descends (prefixWord ++ tailWord_297985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298044 : List Nat := [2, 2, 2, 2, 2, 11]
def baseStart_298044 : Nat := 118140960795 + 298044 * 2 ^ 59
def prefixEnd_298044 : Nat := 4983230072969 + 3 ^ 40 * 298044 * 2
def baseEnd_298044 : Nat := 2519174126563574241635

theorem tailTrace_298044 : CollatzResearch.WordTrace tailWord_298044 prefixEnd_298044 2519174126563574241635 := by
  unfold tailWord_298044
  simp only [CollatzResearch.WordTrace]
  refine ⟨5435278866122482353902593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7247038488163309805203457 5435278866122482353902593)
  ·
    refine ⟨4076459149591861765426945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5435278866122482353902593 4076459149591861765426945)
    ·
      refine ⟨3057344362193896324070209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4076459149591861765426945 3057344362193896324070209)
      ·
        refine ⟨2293008271645422243052657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3057344362193896324070209 2293008271645422243052657)
        ·
          refine ⟨1719756203734066682289493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2293008271645422243052657 1719756203734066682289493)
          ·
            refine ⟨2519174126563574241635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1719756203734066682289493 2519174126563574241635)
            ·
              rfl

theorem cell21_298044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 11].length) (baseStart_298044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_298044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_298044 prefixEnd_298044 := by exact prefixLift 298044
  have htrace : WordTrace (prefixWord ++ tailWord_298044) baseStart_298044 baseEnd_298044 := by
    simpa [prefixWord, tailWord_298044, baseEnd_298044] using wordTrace_append hprefix tailTrace_298044
  have hstable : (prefixWord ++ tailWord_298044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298044).length < 2 ^ (prefixWord ++ tailWord_298044).sum := by decide
  have hdescent : baseEnd_298044 < baseStart_298044 := by decide
  rcases family_descends (prefixWord ++ tailWord_298044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298143 : List Nat := [1, 1, 2, 6, 3, 1, 1, 3, 3]
def baseStart_298143 : Nat := 118140960795 + 298143 * 2 ^ 59
def prefixEnd_298143 : Nat := 4983230072969 + 3 ^ 40 * 298143 * 2
def baseEnd_298143 : Nat := 68040294566014332373943

theorem tailTrace_298143 : CollatzResearch.WordTrace tailWord_298143 prefixEnd_298143 68040294566014332373943 := by
  unfold tailWord_298143
  simp only [CollatzResearch.WordTrace]
  refine ⟨10874168558886304615659083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7249445705924203077106055 10874168558886304615659083)
  ·
    refine ⟨16311252838329456923488625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10874168558886304615659083 16311252838329456923488625)
    ·
      refine ⟨12233439628747092692616469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16311252838329456923488625 12233439628747092692616469)
      ·
        refine ⟨573442482597519969966397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12233439628747092692616469 573442482597519969966397)
        ·
          refine ⟨215040930974069988737399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 573442482597519969966397 215040930974069988737399)
          ·
            refine ⟨322561396461104983106099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215040930974069988737399 322561396461104983106099)
            ·
              refine ⟨483842094691657474659149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322561396461104983106099 483842094691657474659149)
              ·
                refine ⟨181440785509371552997181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 483842094691657474659149 181440785509371552997181)
                ·
                  refine ⟨68040294566014332373943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 181440785509371552997181 68040294566014332373943)
                  ·
                    rfl

theorem cell21_298143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 3, 3].length) (baseStart_298143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_298143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_298143 prefixEnd_298143 := by exact prefixLift 298143
  have htrace : WordTrace (prefixWord ++ tailWord_298143) baseStart_298143 baseEnd_298143 := by
    simpa [prefixWord, tailWord_298143, baseEnd_298143] using wordTrace_append hprefix tailTrace_298143
  have hstable : (prefixWord ++ tailWord_298143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298143).length < 2 ^ (prefixWord ++ tailWord_298143).sum := by decide
  have hdescent : baseEnd_298143 < baseStart_298143 := by decide
  rcases family_descends (prefixWord ++ tailWord_298143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298154 : List Nat := [3, 1, 5, 1, 1, 3, 7]
def baseStart_298154 : Nat := 118140960795 + 298154 * 2 ^ 59
def prefixEnd_298154 : Nat := 4983230072969 + 3 ^ 40 * 298154 * 2
def baseEnd_298154 : Nat := 7560311657320084187843

theorem tailTrace_298154 : CollatzResearch.WordTrace tailWord_298154 prefixEnd_298154 7560311657320084187843 := by
  unfold tailWord_298154
  simp only [CollatzResearch.WordTrace]
  refine ⟨2718642440461613373577379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7249713174564302329539677 2718642440461613373577379)
  ·
    refine ⟨4077963660692420060366069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2718642440461613373577379 4077963660692420060366069)
    ·
      refine ⟨382309093189914380659319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4077963660692420060366069 382309093189914380659319)
      ·
        refine ⟨573463639784871570988979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 382309093189914380659319 573463639784871570988979)
        ·
          refine ⟨860195459677307356483469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 573463639784871570988979 860195459677307356483469)
          ·
            refine ⟨322573297378990258681301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 860195459677307356483469 322573297378990258681301)
            ·
              refine ⟨7560311657320084187843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 322573297378990258681301 7560311657320084187843)
              ·
                rfl

theorem cell21_298154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 7].length) (baseStart_298154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_298154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_298154 prefixEnd_298154 := by exact prefixLift 298154
  have htrace : WordTrace (prefixWord ++ tailWord_298154) baseStart_298154 baseEnd_298154 := by
    simpa [prefixWord, tailWord_298154, baseEnd_298154] using wordTrace_append hprefix tailTrace_298154
  have hstable : (prefixWord ++ tailWord_298154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298154).length < 2 ^ (prefixWord ++ tailWord_298154).sum := by decide
  have hdescent : baseEnd_298154 < baseStart_298154 := by decide
  rcases family_descends (prefixWord ++ tailWord_298154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298213 : List Nat := [1, 3, 1, 4, 4, 8]
def baseStart_298213 : Nat := 118140960795 + 298213 * 2 ^ 59
def prefixEnd_298213 : Nat := 4983230072969 + 3 ^ 40 * 298213 * 2
def baseEnd_298213 : Nat := 2520602574804065415079

theorem tailTrace_298213 : CollatzResearch.WordTrace tailWord_298213 prefixEnd_298213 2520602574804065415079 := by
  unfold tailWord_298213
  simp only [CollatzResearch.WordTrace]
  refine ⟨10876721668632706570707293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7251147779088471047138195 10876721668632706570707293)
  ·
    refine ⟨4078770625737264964015235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10876721668632706570707293 4078770625737264964015235)
    ·
      refine ⟨6118155938605897446022853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4078770625737264964015235 6118155938605897446022853)
      ·
        refine ⟨1147154238488605771129285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6118155938605897446022853 1147154238488605771129285)
        ·
          refine ⟨215091419716613582086741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1147154238488605771129285 215091419716613582086741)
          ·
            refine ⟨2520602574804065415079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 215091419716613582086741 2520602574804065415079)
            ·
              rfl

theorem cell21_298213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 8].length) (baseStart_298213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_298213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_298213 prefixEnd_298213 := by exact prefixLift 298213
  have htrace : WordTrace (prefixWord ++ tailWord_298213) baseStart_298213 baseEnd_298213 := by
    simpa [prefixWord, tailWord_298213, baseEnd_298213] using wordTrace_append hprefix tailTrace_298213
  have hstable : (prefixWord ++ tailWord_298213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298213).length < 2 ^ (prefixWord ++ tailWord_298213).sum := by decide
  have hdescent : baseEnd_298213 < baseStart_298213 := by decide
  rcases family_descends (prefixWord ++ tailWord_298213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298244 : List Nat := [2, 3, 2, 2, 2, 2, 1, 2, 5]
def baseStart_298244 : Nat := 118140960795 + 298244 * 2 ^ 59
def prefixEnd_298244 : Nat := 4983230072969 + 3 ^ 40 * 298244 * 2
def baseEnd_298244 : Nat := 68063344142060601190403

theorem tailTrace_298244 : CollatzResearch.WordTrace tailWord_298244 prefixEnd_298244 68063344142060601190403 := by
  unfold tailWord_298244
  simp only [CollatzResearch.WordTrace]
  refine ⟨5438926165760199432542893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7251901554346932576723857 5438926165760199432542893)
  ·
    refine ⟨2039597312160074787203585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5438926165760199432542893 2039597312160074787203585)
    ·
      refine ⟨1529697984120056090402689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2039597312160074787203585 1529697984120056090402689)
      ·
        refine ⟨1147273488090042067802017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1529697984120056090402689 1147273488090042067802017)
        ·
          refine ⟨860455116067531550851513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1147273488090042067802017 860455116067531550851513)
          ·
            refine ⟨645341337050648663138635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 860455116067531550851513 645341337050648663138635)
            ·
              refine ⟨968012005575972994707953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 645341337050648663138635 968012005575972994707953)
              ·
                refine ⟨726009004181979746030965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 968012005575972994707953 726009004181979746030965)
                ·
                  refine ⟨68063344142060601190403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 726009004181979746030965 68063344142060601190403)
                  ·
                    rfl

theorem cell21_298244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_298244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_298244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_298244 prefixEnd_298244 := by exact prefixLift 298244
  have htrace : WordTrace (prefixWord ++ tailWord_298244) baseStart_298244 baseEnd_298244 := by
    simpa [prefixWord, tailWord_298244, baseEnd_298244] using wordTrace_append hprefix tailTrace_298244
  have hstable : (prefixWord ++ tailWord_298244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298244).length < 2 ^ (prefixWord ++ tailWord_298244).sum := by decide
  have hdescent : baseEnd_298244 < baseStart_298244 := by decide
  rcases family_descends (prefixWord ++ tailWord_298244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298275 : List Nat := [1, 1, 1, 4, 2, 5, 1, 2, 4]
def baseStart_298275 : Nat := 118140960795 + 298275 * 2 ^ 59
def prefixEnd_298275 : Nat := 4983230072969 + 3 ^ 40 * 298275 * 2
def baseEnd_298275 : Nat := 68070418764411436173673

theorem tailTrace_298275 : CollatzResearch.WordTrace tailWord_298275 prefixEnd_298275 68070418764411436173673 := by
  unfold tailWord_298275
  simp only [CollatzResearch.WordTrace]
  refine ⟨10878982994408091159464279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7252655329605394106309519 10878982994408091159464279)
  ·
    refine ⟨16318474491612136739196419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10878982994408091159464279 16318474491612136739196419)
    ·
      refine ⟨24477711737418205108794629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16318474491612136739196419 24477711737418205108794629)
      ·
        refine ⟨4589570950765913457898993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24477711737418205108794629 4589570950765913457898993)
        ·
          refine ⟨3442178213074435093424245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4589570950765913457898993 3442178213074435093424245)
          ·
            refine ⟨322704207475728290008523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3442178213074435093424245 322704207475728290008523)
            ·
              refine ⟨484056311213592435012785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322704207475728290008523 484056311213592435012785)
              ·
                refine ⟨363042233410194326259589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 484056311213592435012785 363042233410194326259589)
                ·
                  refine ⟨68070418764411436173673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 363042233410194326259589 68070418764411436173673)
                  ·
                    rfl

theorem cell21_298275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 4].length) (baseStart_298275 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_298275 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_298275 prefixEnd_298275 := by exact prefixLift 298275
  have htrace : WordTrace (prefixWord ++ tailWord_298275) baseStart_298275 baseEnd_298275 := by
    simpa [prefixWord, tailWord_298275, baseEnd_298275] using wordTrace_append hprefix tailTrace_298275
  have hstable : (prefixWord ++ tailWord_298275).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298275).length < 2 ^ (prefixWord ++ tailWord_298275).sum := by decide
  have hdescent : baseEnd_298275 < baseStart_298275 := by decide
  rcases family_descends (prefixWord ++ tailWord_298275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298292 : List Nat := [2, 5, 1, 1, 1, 1, 5, 1, 4]
def baseStart_298292 : Nat := 118140960795 + 298292 * 2 ^ 59
def prefixEnd_298292 : Nat := 4983230072969 + 3 ^ 40 * 298292 * 2
def baseEnd_298292 : Nat := 68074298396023184390305

theorem tailTrace_298292 : CollatzResearch.WordTrace tailWord_298292 prefixEnd_298292 68074298396023184390305 := by
  unfold tailWord_298292
  simp only [CollatzResearch.WordTrace]
  refine ⟨5439801517673251531416565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7253068690231002041888753 5439801517673251531416565)
  ·
    refine ⟨509981392281867331070303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5439801517673251531416565 509981392281867331070303)
    ·
      refine ⟨764972088422800996605455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 509981392281867331070303 764972088422800996605455)
      ·
        refine ⟨1147458132634201494908183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 764972088422800996605455 1147458132634201494908183)
        ·
          refine ⟨1721187198951302242362275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1147458132634201494908183 1721187198951302242362275)
          ·
            refine ⟨2581780798426953363543413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1721187198951302242362275 2581780798426953363543413)
            ·
              refine ⟨242041949852526877832195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2581780798426953363543413 242041949852526877832195)
              ·
                refine ⟨363062924778790316748293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 242041949852526877832195 363062924778790316748293)
                ·
                  refine ⟨68074298396023184390305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 363062924778790316748293 68074298396023184390305)
                  ·
                    rfl

theorem cell21_298292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_298292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_298292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_298292 prefixEnd_298292 := by exact prefixLift 298292
  have htrace : WordTrace (prefixWord ++ tailWord_298292) baseStart_298292 baseEnd_298292 := by
    simpa [prefixWord, tailWord_298292, baseEnd_298292] using wordTrace_append hprefix tailTrace_298292
  have hstable : (prefixWord ++ tailWord_298292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298292).length < 2 ^ (prefixWord ++ tailWord_298292).sum := by decide
  have hdescent : baseEnd_298292 < baseStart_298292 := by decide
  rcases family_descends (prefixWord ++ tailWord_298292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298303 : List Nat := [1, 1, 2, 2, 4, 2, 2, 2, 5]
def baseStart_298303 : Nat := 118140960795 + 298303 * 2 ^ 59
def prefixEnd_298303 : Nat := 4983230072969 + 3 ^ 40 * 298303 * 2
def baseEnd_298303 : Nat := 68076808745889609706949

theorem tailTrace_298303 : CollatzResearch.WordTrace tailWord_298303 prefixEnd_298303 68076808745889609706949 := by
  unfold tailWord_298303
  simp only [CollatzResearch.WordTrace]
  refine ⟨10880004238306651941483563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7253336158871101294322375 10880004238306651941483563)
  ·
    refine ⟨16320006357459977912225345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10880004238306651941483563 16320006357459977912225345)
    ·
      refine ⟨12240004768094983434169009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16320006357459977912225345 12240004768094983434169009)
      ·
        refine ⟨9180003576071237575626757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12240004768094983434169009 9180003576071237575626757)
        ·
          refine ⟨1721250670513357045430017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9180003576071237575626757 1721250670513357045430017)
          ·
            refine ⟨1290938002885017784072513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1721250670513357045430017 1290938002885017784072513)
            ·
              refine ⟨968203502163763338054385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1290938002885017784072513 968203502163763338054385)
              ·
                refine ⟨726152626622822503540789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 968203502163763338054385 726152626622822503540789)
                ·
                  refine ⟨68076808745889609706949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 726152626622822503540789 68076808745889609706949)
                  ·
                    rfl

theorem cell21_298303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 5].length) (baseStart_298303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_298303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_298303 prefixEnd_298303 := by exact prefixLift 298303
  have htrace : WordTrace (prefixWord ++ tailWord_298303) baseStart_298303 baseEnd_298303 := by
    simpa [prefixWord, tailWord_298303, baseEnd_298303] using wordTrace_append hprefix tailTrace_298303
  have hstable : (prefixWord ++ tailWord_298303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298303).length < 2 ^ (prefixWord ++ tailWord_298303).sum := by decide
  have hdescent : baseEnd_298303 < baseStart_298303 := by decide
  rcases family_descends (prefixWord ++ tailWord_298303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298348 : List Nat := [2, 2, 1, 1, 5, 1, 1, 8]
def baseStart_298348 : Nat := 118140960795 + 298348 * 2 ^ 59
def prefixEnd_298348 : Nat := 4983230072969 + 3 ^ 40 * 298348 * 2
def baseEnd_298348 : Nat := 22695692786326510485619

theorem tailTrace_298348 : CollatzResearch.WordTrace tailWord_298348 prefixEnd_298348 22695692786326510485619 := by
  unfold tailWord_298348
  simp only [CollatzResearch.WordTrace]
  refine ⟨5440822761571812313435849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7254430348762416417914465 5440822761571812313435849)
  ·
    refine ⟨4080617071178859235076887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5440822761571812313435849 4080617071178859235076887)
    ·
      refine ⟨6120925606768288852615331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4080617071178859235076887 6120925606768288852615331)
      ·
        refine ⟨9181388410152433278922997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6120925606768288852615331 9181388410152433278922997)
        ·
          refine ⟨860755163451790619899031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9181388410152433278922997 860755163451790619899031)
          ·
            refine ⟨1291132745177685929848547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 860755163451790619899031 1291132745177685929848547)
            ·
              refine ⟨1936699117766528894772821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1291132745177685929848547 1936699117766528894772821)
              ·
                refine ⟨22695692786326510485619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1936699117766528894772821 22695692786326510485619)
                ·
                  rfl

theorem cell21_298348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 8].length) (baseStart_298348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_298348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_298348 prefixEnd_298348 := by exact prefixLift 298348
  have htrace : WordTrace (prefixWord ++ tailWord_298348) baseStart_298348 baseEnd_298348 := by
    simpa [prefixWord, tailWord_298348, baseEnd_298348] using wordTrace_append hprefix tailTrace_298348
  have hstable : (prefixWord ++ tailWord_298348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298348).length < 2 ^ (prefixWord ++ tailWord_298348).sum := by decide
  have hdescent : baseEnd_298348 < baseStart_298348 := by decide
  rcases family_descends (prefixWord ++ tailWord_298348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298486 : List Nat := [5, 1, 1, 1, 2, 2, 1, 2, 6]
def baseStart_298486 : Nat := 118140960795 + 298486 * 2 ^ 59
def prefixEnd_298486 : Nat := 4983230072969 + 3 ^ 40 * 298486 * 2
def baseEnd_298486 : Nat := 68118571839121958156575

theorem tailTrace_298486 : CollatzResearch.WordTrace tailWord_298486 prefixEnd_298486 68118571839121958156575 := by
  unfold tailWord_298486
  simp only [CollatzResearch.WordTrace]
  refine ⟨680417424790229637212207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7257785864429116130263541 680417424790229637212207)
  ·
    refine ⟨1020626137185344455818311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 680417424790229637212207 1020626137185344455818311)
    ·
      refine ⟨1530939205778016683727467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1020626137185344455818311 1530939205778016683727467)
      ·
        refine ⟨2296408808667025025591201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1530939205778016683727467 2296408808667025025591201)
        ·
          refine ⟨1722306606500268769193401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2296408808667025025591201 1722306606500268769193401)
          ·
            refine ⟨1291729954875201576895051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1722306606500268769193401 1291729954875201576895051)
            ·
              refine ⟨1937594932312802365342577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1291729954875201576895051 1937594932312802365342577)
              ·
                refine ⟨1453196199234601774006933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1937594932312802365342577 1453196199234601774006933)
                ·
                  refine ⟨68118571839121958156575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1453196199234601774006933 68118571839121958156575)
                  ·
                    rfl

theorem cell21_298486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_298486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_298486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_298486 prefixEnd_298486 := by exact prefixLift 298486
  have htrace : WordTrace (prefixWord ++ tailWord_298486) baseStart_298486 baseEnd_298486 := by
    simpa [prefixWord, tailWord_298486, baseEnd_298486] using wordTrace_append hprefix tailTrace_298486
  have hstable : (prefixWord ++ tailWord_298486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298486).length < 2 ^ (prefixWord ++ tailWord_298486).sum := by decide
  have hdescent : baseEnd_298486 < baseStart_298486 := by decide
  rcases family_descends (prefixWord ++ tailWord_298486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298520 : List Nat := [2, 1, 2, 3, 4, 2, 2, 1, 4]
def baseStart_298520 : Nat := 118140960795 + 298520 * 2 ^ 59
def prefixEnd_298520 : Nat := 4983230072969 + 3 ^ 40 * 298520 * 2
def baseEnd_298520 : Nat := 68126331102345454589839

theorem tailTrace_298520 : CollatzResearch.WordTrace tailWord_298520 prefixEnd_298520 68126331102345454589839 := by
  unfold tailWord_298520
  simp only [CollatzResearch.WordTrace]
  refine ⟨5443959439260249001066507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7258612585680332001422009 5443959439260249001066507)
  ·
    refine ⟨8165939158890373501599761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5443959439260249001066507 8165939158890373501599761)
    ·
      refine ⟨6124454369167780126199821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8165939158890373501599761 6124454369167780126199821)
      ·
        refine ⟨2296670388437917547324933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6124454369167780126199821 2296670388437917547324933)
        ·
          refine ⟨430625697832109540123425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2296670388437917547324933 430625697832109540123425)
          ·
            refine ⟨322969273374082155092569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 430625697832109540123425 322969273374082155092569)
            ·
              refine ⟨242226955030561616319427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 322969273374082155092569 242226955030561616319427)
              ·
                refine ⟨363340432545842424479141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 242226955030561616319427 363340432545842424479141)
                ·
                  refine ⟨68126331102345454589839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 363340432545842424479141 68126331102345454589839)
                  ·
                    rfl

theorem cell21_298520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 4].length) (baseStart_298520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_298520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_298520 prefixEnd_298520 := by exact prefixLift 298520
  have htrace : WordTrace (prefixWord ++ tailWord_298520) baseStart_298520 baseEnd_298520 := by
    simpa [prefixWord, tailWord_298520, baseEnd_298520] using wordTrace_append hprefix tailTrace_298520
  have hstable : (prefixWord ++ tailWord_298520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298520).length < 2 ^ (prefixWord ++ tailWord_298520).sum := by decide
  have hdescent : baseEnd_298520 < baseStart_298520 := by decide
  rcases family_descends (prefixWord ++ tailWord_298520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298559 : List Nat := [1, 1, 2, 2, 3, 12]
def baseStart_298559 : Nat := 118140960795 + 298559 * 2 ^ 59
def prefixEnd_298559 : Nat := 4983230072969 + 3 ^ 40 * 298559 * 2
def baseEnd_298559 : Nat := 2523527090136668645917

theorem tailTrace_298559 : CollatzResearch.WordTrace tailWord_298559 prefixEnd_298559 2523527090136668645917 := by
  unfold tailWord_298559
  simp only [CollatzResearch.WordTrace]
  refine ⟨10889341325379207662802731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7259560883586138441868487 10889341325379207662802731)
  ·
    refine ⟨16334011988068811494204097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10889341325379207662802731 16334011988068811494204097)
    ·
      refine ⟨12250508991051608620653073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16334011988068811494204097 12250508991051608620653073)
      ·
        refine ⟨9187881743288706465489805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12250508991051608620653073 9187881743288706465489805)
        ·
          refine ⟨3445455653733264924558677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9187881743288706465489805 3445455653733264924558677)
          ·
            refine ⟨2523527090136668645917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 3445455653733264924558677 2523527090136668645917)
            ·
              rfl

theorem cell21_298559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 12].length) (baseStart_298559 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_298559 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_298559 prefixEnd_298559 := by exact prefixLift 298559
  have htrace : WordTrace (prefixWord ++ tailWord_298559) baseStart_298559 baseEnd_298559 := by
    simpa [prefixWord, tailWord_298559, baseEnd_298559] using wordTrace_append hprefix tailTrace_298559
  have hstable : (prefixWord ++ tailWord_298559).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298559).length < 2 ^ (prefixWord ++ tailWord_298559).sum := by decide
  have hdescent : baseEnd_298559 < baseStart_298559 := by decide
  rcases family_descends (prefixWord ++ tailWord_298559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298582 : List Nat := [5, 2, 2, 2, 1, 1, 1, 2, 5]
def baseStart_298582 : Nat := 118140960795 + 298582 * 2 ^ 59
def prefixEnd_298582 : Nat := 4983230072969 + 3 ^ 40 * 298582 * 2
def baseEnd_298582 : Nat := 68140480347047124556379

theorem tailTrace_298582 : CollatzResearch.WordTrace tailWord_298582 prefixEnd_298582 68140480347047124556379 := by
  unfold tailWord_298582
  simp only [CollatzResearch.WordTrace]
  refine ⟨680636262768492661930625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7260120136197255060593333 680636262768492661930625)
  ·
    refine ⟨510477197076369496447969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 680636262768492661930625 510477197076369496447969)
    ·
      refine ⟨382857897807277122335977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 510477197076369496447969 382857897807277122335977)
      ·
        refine ⟨287143423355457841751983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 382857897807277122335977 287143423355457841751983)
        ·
          refine ⟨430715135033186762627975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287143423355457841751983 430715135033186762627975)
          ·
            refine ⟨646072702549780143941963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 430715135033186762627975 646072702549780143941963)
            ·
              refine ⟨969109053824670215912945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 646072702549780143941963 969109053824670215912945)
              ·
                refine ⟨726831790368502661934709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 969109053824670215912945 726831790368502661934709)
                ·
                  refine ⟨68140480347047124556379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 726831790368502661934709 68140480347047124556379)
                  ·
                    rfl

theorem cell21_298582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_298582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_298582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_298582 prefixEnd_298582 := by exact prefixLift 298582
  have htrace : WordTrace (prefixWord ++ tailWord_298582) baseStart_298582 baseEnd_298582 := by
    simpa [prefixWord, tailWord_298582, baseEnd_298582] using wordTrace_append hprefix tailTrace_298582
  have hstable : (prefixWord ++ tailWord_298582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298582).length < 2 ^ (prefixWord ++ tailWord_298582).sum := by decide
  have hdescent : baseEnd_298582 < baseStart_298582 := by decide
  rcases family_descends (prefixWord ++ tailWord_298582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298635 : List Nat := [1, 1, 1, 1, 4, 1, 4, 8]
def baseStart_298635 : Nat := 118140960795 + 298635 * 2 ^ 59
def prefixEnd_298635 : Nat := 4983230072969 + 3 ^ 40 * 298635 * 2
def baseEnd_298635 : Nat := 22717525223043603390979

theorem tailTrace_298635 : CollatzResearch.WordTrace tailWord_298635 prefixEnd_298635 22717525223043603390979 := by
  unfold tailWord_298635
  simp only [CollatzResearch.WordTrace]
  refine ⟨10892113273103872642569359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7261408848735915095046239 10892113273103872642569359)
  ·
    refine ⟨16338169909655808963854039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10892113273103872642569359 16338169909655808963854039)
    ·
      refine ⟨24507254864483713445781059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16338169909655808963854039 24507254864483713445781059)
      ·
        refine ⟨36760882296725570168671589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24507254864483713445781059 36760882296725570168671589)
        ·
          refine ⟨6892665430636044406625923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36760882296725570168671589 6892665430636044406625923)
          ·
            refine ⟨10338998145954066609938885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6892665430636044406625923 10338998145954066609938885)
            ·
              refine ⟨1938562152366387489363541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10338998145954066609938885 1938562152366387489363541)
              ·
                refine ⟨22717525223043603390979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1938562152366387489363541 22717525223043603390979)
                ·
                  rfl

theorem cell21_298635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 8].length) (baseStart_298635 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_298635 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_298635 prefixEnd_298635 := by exact prefixLift 298635
  have htrace : WordTrace (prefixWord ++ tailWord_298635) baseStart_298635 baseEnd_298635 := by
    simpa [prefixWord, tailWord_298635, baseEnd_298635] using wordTrace_append hprefix tailTrace_298635
  have hstable : (prefixWord ++ tailWord_298635).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298635).length < 2 ^ (prefixWord ++ tailWord_298635).sum := by decide
  have hdescent : baseEnd_298635 < baseStart_298635 := by decide
  rcases family_descends (prefixWord ++ tailWord_298635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298683 : List Nat := [1, 1, 1, 1, 1, 2, 3, 8, 3]
def baseStart_298683 : Nat := 118140960795 + 298683 * 2 ^ 59
def prefixEnd_298683 : Nat := 4983230072969 + 3 ^ 40 * 298683 * 2
def baseEnd_298683 : Nat := 68163529923093393372839

theorem tailTrace_298683 : CollatzResearch.WordTrace tailWord_298683 prefixEnd_298683 68163529923093393372839 := by
  unfold tailWord_298683
  simp only [CollatzResearch.WordTrace]
  refine ⟨10893863976929976840316703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7262575984619984560211135 10893863976929976840316703)
  ·
    refine ⟨16340795965394965260475055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10893863976929976840316703 16340795965394965260475055)
    ·
      refine ⟨24511193948092447890712583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16340795965394965260475055 24511193948092447890712583)
      ·
        refine ⟨36766790922138671836068875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24511193948092447890712583 36766790922138671836068875)
        ·
          refine ⟨55150186383208007754103313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36766790922138671836068875 55150186383208007754103313)
          ·
            refine ⟨41362639787406005815577485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55150186383208007754103313 41362639787406005815577485)
            ·
              refine ⟨15510989920277252180841557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41362639787406005815577485 15510989920277252180841557)
              ·
                refine ⟨181769413128249048994237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 15510989920277252180841557 181769413128249048994237)
                ·
                  refine ⟨68163529923093393372839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 181769413128249048994237 68163529923093393372839)
                  ·
                    rfl

theorem cell21_298683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8, 3].length) (baseStart_298683 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_298683 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_298683 prefixEnd_298683 := by exact prefixLift 298683
  have htrace : WordTrace (prefixWord ++ tailWord_298683) baseStart_298683 baseEnd_298683 := by
    simpa [prefixWord, tailWord_298683, baseEnd_298683] using wordTrace_append hprefix tailTrace_298683
  have hstable : (prefixWord ++ tailWord_298683).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298683).length < 2 ^ (prefixWord ++ tailWord_298683).sum := by decide
  have hdescent : baseEnd_298683 < baseStart_298683 := by decide
  rcases family_descends (prefixWord ++ tailWord_298683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298711 : List Nat := [1, 1, 3, 2, 1, 3, 1, 9]
def baseStart_298711 : Nat := 118140960795 + 298711 * 2 ^ 59
def prefixEnd_298711 : Nat := 4983230072969 + 3 ^ 40 * 298711 * 2
def baseEnd_298711 : Nat := 22723306634857188968705

theorem tailTrace_298711 : CollatzResearch.WordTrace tailWord_298711 prefixEnd_298711 22723306634857188968705 := by
  unfold tailWord_298711
  simp only [CollatzResearch.WordTrace]
  refine ⟨10894885220828537622335987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7263256813885691748223991 10894885220828537622335987)
  ·
    refine ⟨16342327831242806433503981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10894885220828537622335987 16342327831242806433503981)
    ·
      refine ⟨6128372936716052412563993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16342327831242806433503981 6128372936716052412563993)
      ·
        refine ⟨4596279702537039309422995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6128372936716052412563993 4596279702537039309422995)
        ·
          refine ⟨6894419553805558964134493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4596279702537039309422995 6894419553805558964134493)
          ·
            refine ⟨2585407332677084611550435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6894419553805558964134493 2585407332677084611550435)
            ·
              refine ⟨3878110999015626917325653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2585407332677084611550435 3878110999015626917325653)
              ·
                refine ⟨22723306634857188968705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3878110999015626917325653 22723306634857188968705)
                ·
                  rfl

theorem cell21_298711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 9].length) (baseStart_298711 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_298711 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_298711 prefixEnd_298711 := by exact prefixLift 298711
  have htrace : WordTrace (prefixWord ++ tailWord_298711) baseStart_298711 baseEnd_298711 := by
    simpa [prefixWord, tailWord_298711, baseEnd_298711] using wordTrace_append hprefix tailTrace_298711
  have hstable : (prefixWord ++ tailWord_298711).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298711).length < 2 ^ (prefixWord ++ tailWord_298711).sum := by decide
  have hdescent : baseEnd_298711 < baseStart_298711 := by decide
  rcases family_descends (prefixWord ++ tailWord_298711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298782 : List Nat := [4, 3, 2, 2, 2, 1, 1, 2, 4]
def baseStart_298782 : Nat := 118140960795 + 298782 * 2 ^ 59
def prefixEnd_298782 : Nat := 4983230072969 + 3 ^ 40 * 298782 * 2
def baseEnd_298782 : Nat := 68186123071891221222637

theorem tailTrace_298782 : CollatzResearch.WordTrace tailWord_298782 prefixEnd_298782 68186123071891221222637 := by
  unfold tailWord_298782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1362184350446414593521325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7264983202380877832113733 1362184350446414593521325)
  ·
    refine ⟨510819131417405472570497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1362184350446414593521325 510819131417405472570497)
    ·
      refine ⟨383114348563054104427873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 510819131417405472570497 383114348563054104427873)
      ·
        refine ⟨287335761422290578320905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 383114348563054104427873 287335761422290578320905)
        ·
          refine ⟨215501821066717933740679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287335761422290578320905 215501821066717933740679)
          ·
            refine ⟨323252731600076900611019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215501821066717933740679 323252731600076900611019)
            ·
              refine ⟨484879097400115350916529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323252731600076900611019 484879097400115350916529)
              ·
                refine ⟨363659323050086513187397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 484879097400115350916529 363659323050086513187397)
                ·
                  refine ⟨68186123071891221222637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 363659323050086513187397 68186123071891221222637)
                  ·
                    rfl

theorem cell21_298782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_298782 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_298782 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_298782 prefixEnd_298782 := by exact prefixLift 298782
  have htrace : WordTrace (prefixWord ++ tailWord_298782) baseStart_298782 baseEnd_298782 := by
    simpa [prefixWord, tailWord_298782, baseEnd_298782] using wordTrace_append hprefix tailTrace_298782
  have hstable : (prefixWord ++ tailWord_298782).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298782).length < 2 ^ (prefixWord ++ tailWord_298782).sum := by decide
  have hdescent : baseEnd_298782 < baseStart_298782 := by decide
  rcases family_descends (prefixWord ++ tailWord_298782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298849 : List Nat := [1, 2, 3, 1, 1, 1, 4, 4, 4]
def baseStart_298849 : Nat := 118140960795 + 298849 * 2 ^ 59
def prefixEnd_298849 : Nat := 4983230072969 + 3 ^ 40 * 298849 * 2
def baseEnd_298849 : Nat := 68201413384713993605833

theorem tailTrace_298849 : CollatzResearch.WordTrace tailWord_298849 prefixEnd_298849 68201413384713993605833 := by
  unfold tailWord_298849
  simp only [CollatzResearch.WordTrace]
  refine ⟨10899918494328587190859601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7266612329552391460573067 10899918494328587190859601)
  ·
    refine ⟨8174938870746440393144701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10899918494328587190859601 8174938870746440393144701)
    ·
      refine ⟨3065602076529915147429263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8174938870746440393144701 3065602076529915147429263)
      ·
        refine ⟨4598403114794872721143895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3065602076529915147429263 4598403114794872721143895)
        ·
          refine ⟨6897604672192309081715843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4598403114794872721143895 6897604672192309081715843)
          ·
            refine ⟨10346407008288463622573765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6897604672192309081715843 10346407008288463622573765)
            ·
              refine ⟨1939951314054086929232581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10346407008288463622573765 1939951314054086929232581)
              ·
                refine ⟨363740871385141299231109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1939951314054086929232581 363740871385141299231109)
                ·
                  refine ⟨68201413384713993605833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 363740871385141299231109 68201413384713993605833)
                  ·
                    rfl

theorem cell21_298849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 4].length) (baseStart_298849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_298849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_298849 prefixEnd_298849 := by exact prefixLift 298849
  have htrace : WordTrace (prefixWord ++ tailWord_298849) baseStart_298849 baseEnd_298849 := by
    simpa [prefixWord, tailWord_298849, baseEnd_298849] using wordTrace_append hprefix tailTrace_298849
  have hstable : (prefixWord ++ tailWord_298849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298849).length < 2 ^ (prefixWord ++ tailWord_298849).sum := by decide
  have hdescent : baseEnd_298849 < baseStart_298849 := by decide
  rcases family_descends (prefixWord ++ tailWord_298849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298852 : List Nat := [2, 3, 1, 1, 5, 2, 1, 1, 5]
def baseStart_298852 : Nat := 118140960795 + 298852 * 2 ^ 59
def prefixEnd_298852 : Nat := 4983230072969 + 3 ^ 40 * 298852 * 2
def baseEnd_298852 : Nat := 68202098025586655055827

theorem tailTrace_298852 : CollatzResearch.WordTrace tailWord_298852 prefixEnd_298852 68202098025586655055827 := by
  unfold tailWord_298852
  simp only [CollatzResearch.WordTrace]
  refine ⟨5450013956658859351609405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7266685275545145802145873 5450013956658859351609405)
  ·
    refine ⟨2043755233747072256853527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5450013956658859351609405 2043755233747072256853527)
    ·
      refine ⟨3065632850620608385280291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2043755233747072256853527 3065632850620608385280291)
      ·
        refine ⟨4598449275930912577920437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3065632850620608385280291 4598449275930912577920437)
        ·
          refine ⟨431104619618523054180041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4598449275930912577920437 431104619618523054180041)
          ·
            refine ⟨323328464713892290635031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 431104619618523054180041 323328464713892290635031)
            ·
              refine ⟨484992697070838435952547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323328464713892290635031 484992697070838435952547)
              ·
                refine ⟨727489045606257653928821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 484992697070838435952547 727489045606257653928821)
                ·
                  refine ⟨68202098025586655055827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 727489045606257653928821 68202098025586655055827)
                  ·
                    rfl

theorem cell21_298852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_298852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_298852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_298852 prefixEnd_298852 := by exact prefixLift 298852
  have htrace : WordTrace (prefixWord ++ tailWord_298852) baseStart_298852 baseEnd_298852 := by
    simpa [prefixWord, tailWord_298852, baseEnd_298852] using wordTrace_append hprefix tailTrace_298852
  have hstable : (prefixWord ++ tailWord_298852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298852).length < 2 ^ (prefixWord ++ tailWord_298852).sum := by decide
  have hdescent : baseEnd_298852 < baseStart_298852 := by decide
  rcases family_descends (prefixWord ++ tailWord_298852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298914 : List Nat := [3, 3, 1, 2, 4, 1, 1, 6]
def baseStart_298914 : Nat := 118140960795 + 298914 * 2 ^ 59
def prefixEnd_298914 : Nat := 4983230072969 + 3 ^ 40 * 298914 * 2
def baseEnd_298914 : Nat := 22738749090096108340789

theorem tailTrace_298914 : CollatzResearch.WordTrace tailWord_298914 prefixEnd_298914 22738749090096108340789 := by
  unfold tailWord_298914
  simp only [CollatzResearch.WordTrace]
  refine ⟨2725572309773275822993949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7268192826062068861317197 2725572309773275822993949)
  ·
    refine ⟨1022089616164978433622731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2725572309773275822993949 1022089616164978433622731)
    ·
      refine ⟨1533134424247467650434097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1022089616164978433622731 1533134424247467650434097)
      ·
        refine ⟨1149850818185600737825573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1533134424247467650434097 1149850818185600737825573)
        ·
          refine ⟨215597028409800138342295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1149850818185600737825573 215597028409800138342295)
          ·
            refine ⟨323395542614700207513443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215597028409800138342295 323395542614700207513443)
            ·
              refine ⟨485093313922050311270165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323395542614700207513443 485093313922050311270165)
              ·
                refine ⟨22738749090096108340789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 485093313922050311270165 22738749090096108340789)
                ·
                  rfl

theorem cell21_298914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 6].length) (baseStart_298914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_298914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_298914 prefixEnd_298914 := by exact prefixLift 298914
  have htrace : WordTrace (prefixWord ++ tailWord_298914) baseStart_298914 baseEnd_298914 := by
    simpa [prefixWord, tailWord_298914, baseEnd_298914] using wordTrace_append hprefix tailTrace_298914
  have hstable : (prefixWord ++ tailWord_298914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298914).length < 2 ^ (prefixWord ++ tailWord_298914).sum := by decide
  have hdescent : baseEnd_298914 < baseStart_298914 := by decide
  rcases family_descends (prefixWord ++ tailWord_298914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299015 : List Nat := [1, 1, 4, 3, 1, 2, 9]
def baseStart_299015 : Nat := 118140960795 + 299015 * 2 ^ 59
def prefixEnd_299015 : Nat := 4983230072969 + 3 ^ 40 * 299015 * 2
def baseEnd_299015 : Nat := 7582144094037177093203

theorem tailTrace_299015 : CollatzResearch.WordTrace tailWord_299015 prefixEnd_299015 7582144094037177093203 := by
  unfold tailWord_299015
  simp only [CollatzResearch.WordTrace]
  refine ⟨10905973011727197541402499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7270648674484798360934999 10905973011727197541402499)
  ·
    refine ⟨16358959517590796312103749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10905973011727197541402499 16358959517590796312103749)
    ·
      refine ⟨3067304909548274308519453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16358959517590796312103749 3067304909548274308519453)
      ·
        refine ⟨1150239341080602865694795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3067304909548274308519453 1150239341080602865694795)
        ·
          refine ⟨1725359011620904298542193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1150239341080602865694795 1725359011620904298542193)
          ·
            refine ⟨1294019258715678223906645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1725359011620904298542193 1294019258715678223906645)
            ·
              refine ⟨7582144094037177093203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1294019258715678223906645 7582144094037177093203)
              ·
                rfl

theorem cell21_299015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 9].length) (baseStart_299015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_299015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_299015 prefixEnd_299015 := by exact prefixLift 299015
  have htrace : WordTrace (prefixWord ++ tailWord_299015) baseStart_299015 baseEnd_299015 := by
    simpa [prefixWord, tailWord_299015, baseEnd_299015] using wordTrace_append hprefix tailTrace_299015
  have hstable : (prefixWord ++ tailWord_299015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299015).length < 2 ^ (prefixWord ++ tailWord_299015).sum := by decide
  have hdescent : baseEnd_299015 < baseStart_299015 := by decide
  rcases family_descends (prefixWord ++ tailWord_299015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299139 : List Nat := [1, 1, 1, 3, 3, 3, 2, 4, 3]
def baseStart_299139 : Nat := 118140960795 + 299139 * 2 ^ 59
def prefixEnd_299139 : Nat := 4983230072969 + 3 ^ 40 * 299139 * 2
def baseEnd_299139 : Nat := 68267595335737933771907

theorem tailTrace_299139 : CollatzResearch.WordTrace tailWord_299139 prefixEnd_299139 68267595335737933771907 := by
  unfold tailWord_299139
  simp only [CollatzResearch.WordTrace]
  refine ⟨10910495663277966718916471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7273663775518644479277647 10910495663277966718916471)
  ·
    refine ⟨16365743494916950078374707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10910495663277966718916471 16365743494916950078374707)
    ·
      refine ⟨24548615242375425117562061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16365743494916950078374707 24548615242375425117562061)
      ·
        refine ⟨9205730715890784419085773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24548615242375425117562061 9205730715890784419085773)
        ·
          refine ⟨3452149018459044157157165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9205730715890784419085773 3452149018459044157157165)
          ·
            refine ⟨1294555881922141558933937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3452149018459044157157165 1294555881922141558933937)
            ·
              refine ⟨970916911441606169200453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1294555881922141558933937 970916911441606169200453)
              ·
                refine ⟨182046920895301156725085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 970916911441606169200453 182046920895301156725085)
                ·
                  refine ⟨68267595335737933771907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 182046920895301156725085 68267595335737933771907)
                  ·
                    rfl

theorem cell21_299139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 4, 3].length) (baseStart_299139 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_299139 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_299139 prefixEnd_299139 := by exact prefixLift 299139
  have htrace : WordTrace (prefixWord ++ tailWord_299139) baseStart_299139 baseEnd_299139 := by
    simpa [prefixWord, tailWord_299139, baseEnd_299139] using wordTrace_append hprefix tailTrace_299139
  have hstable : (prefixWord ++ tailWord_299139).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299139).length < 2 ^ (prefixWord ++ tailWord_299139).sum := by decide
  have hdescent : baseEnd_299139 < baseStart_299139 := by decide
  rcases family_descends (prefixWord ++ tailWord_299139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299201 : List Nat := [1, 2, 6, 1, 2, 1, 2, 6]
def baseStart_299201 : Nat := 118140960795 + 299201 * 2 ^ 59
def prefixEnd_299201 : Nat := 4983230072969 + 3 ^ 40 * 299201 * 2
def baseEnd_299201 : Nat := 22760581526813201246149

theorem tailTrace_299201 : CollatzResearch.WordTrace tailWord_299201 prefixEnd_299201 22760581526813201246149 := by
  unfold tailWord_299201
  simp only [CollatzResearch.WordTrace]
  refine ⟨10912756989053351307673457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7275171326035567538448971 10912756989053351307673457)
  ·
    refine ⟨8184567741790013480755093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10912756989053351307673457 8184567741790013480755093)
    ·
      refine ⟨383651612896406881910395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8184567741790013480755093 383651612896406881910395)
      ·
        refine ⟨575477419344610322865593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383651612896406881910395 575477419344610322865593)
        ·
          refine ⟨431608064508457742149195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 575477419344610322865593 431608064508457742149195)
          ·
            refine ⟨647412096762686613223793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431608064508457742149195 647412096762686613223793)
            ·
              refine ⟨485559072572014959917845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 647412096762686613223793 485559072572014959917845)
              ·
                refine ⟨22760581526813201246149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 485559072572014959917845 22760581526813201246149)
                ·
                  rfl

theorem cell21_299201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 6].length) (baseStart_299201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_299201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_299201 prefixEnd_299201 := by exact prefixLift 299201
  have htrace : WordTrace (prefixWord ++ tailWord_299201) baseStart_299201 baseEnd_299201 := by
    simpa [prefixWord, tailWord_299201, baseEnd_299201] using wordTrace_append hprefix tailTrace_299201
  have hstable : (prefixWord ++ tailWord_299201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299201).length < 2 ^ (prefixWord ++ tailWord_299201).sum := by decide
  have hdescent : baseEnd_299201 < baseStart_299201 := by decide
  rcases family_descends (prefixWord ++ tailWord_299201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299260 : List Nat := [2, 2, 2, 1, 4, 3, 1, 6]
def baseStart_299260 : Nat := 118140960795 + 299260 * 2 ^ 59
def prefixEnd_299260 : Nat := 4983230072969 + 3 ^ 40 * 299260 * 2
def baseEnd_299260 : Nat := 22765069728089537418331

theorem tailTrace_299260 : CollatzResearch.WordTrace tailWord_299260 prefixEnd_299260 22765069728089537418331 := by
  unfold tailWord_299260
  simp only [CollatzResearch.WordTrace]
  refine ⟨5457454447919802192035617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7276605930559736256047489 5457454447919802192035617)
  ·
    refine ⟨4093090835939851644026713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5457454447919802192035617 4093090835939851644026713)
    ·
      refine ⟨3069818126954888733020035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4093090835939851644026713 3069818126954888733020035)
      ·
        refine ⟨4604727190432333099530053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3069818126954888733020035 4604727190432333099530053)
        ·
          refine ⟨863386348206062456161885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4604727190432333099530053 863386348206062456161885)
          ·
            refine ⟨323769880577273421060707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 863386348206062456161885 323769880577273421060707)
            ·
              refine ⟨485654820865910131591061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323769880577273421060707 485654820865910131591061)
              ·
                refine ⟨22765069728089537418331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 485654820865910131591061 22765069728089537418331)
                ·
                  rfl

theorem cell21_299260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 6].length) (baseStart_299260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_299260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_299260 prefixEnd_299260 := by exact prefixLift 299260
  have htrace : WordTrace (prefixWord ++ tailWord_299260) baseStart_299260 baseEnd_299260 := by
    simpa [prefixWord, tailWord_299260, baseEnd_299260] using wordTrace_append hprefix tailTrace_299260
  have hstable : (prefixWord ++ tailWord_299260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299260).length < 2 ^ (prefixWord ++ tailWord_299260).sum := by decide
  have hdescent : baseEnd_299260 < baseStart_299260 := by decide
  rcases family_descends (prefixWord ++ tailWord_299260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299288 : List Nat := [2, 1, 2, 3, 1, 2, 2, 2, 6]
def baseStart_299288 : Nat := 118140960795 + 299288 * 2 ^ 59
def prefixEnd_299288 : Nat := 4983230072969 + 3 ^ 40 * 299288 * 2
def baseEnd_299288 : Nat := 68301599165746785788269

theorem tailTrace_299288 : CollatzResearch.WordTrace tailWord_299288 prefixEnd_299288 68301599165746785788269 := by
  unfold tailWord_299288
  simp only [CollatzResearch.WordTrace]
  refine ⟨5457965069869082583045259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7277286759825443444060345 5457965069869082583045259)
  ·
    refine ⟨8186947604803623874567889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5457965069869082583045259 8186947604803623874567889)
    ·
      refine ⟨6140210703602717905925917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8186947604803623874567889 6140210703602717905925917)
      ·
        refine ⟨2302579013851019214722219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6140210703602717905925917 2302579013851019214722219)
        ·
          refine ⟨3453868520776528822083329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2302579013851019214722219 3453868520776528822083329)
          ·
            refine ⟨2590401390582396616562497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3453868520776528822083329 2590401390582396616562497)
            ·
              refine ⟨1942801042936797462421873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2590401390582396616562497 1942801042936797462421873)
              ·
                refine ⟨1457100782202598096816405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1942801042936797462421873 1457100782202598096816405)
                ·
                  refine ⟨68301599165746785788269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1457100782202598096816405 68301599165746785788269)
                  ·
                    rfl

theorem cell21_299288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 6].length) (baseStart_299288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_299288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_299288 prefixEnd_299288 := by exact prefixLift 299288
  have htrace : WordTrace (prefixWord ++ tailWord_299288) baseStart_299288 baseEnd_299288 := by
    simpa [prefixWord, tailWord_299288, baseEnd_299288] using wordTrace_append hprefix tailTrace_299288
  have hstable : (prefixWord ++ tailWord_299288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299288).length < 2 ^ (prefixWord ++ tailWord_299288).sum := by decide
  have hdescent : baseEnd_299288 < baseStart_299288 := by decide
  rcases family_descends (prefixWord ++ tailWord_299288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299322 : List Nat := [3, 1, 1, 1, 4, 3, 3, 1, 4]
def baseStart_299322 : Nat := 118140960795 + 299322 * 2 ^ 59
def prefixEnd_299322 : Nat := 4983230072969 + 3 ^ 40 * 299322 * 2
def baseEnd_299322 : Nat := 68309358428970282221533

theorem tailTrace_299322 : CollatzResearch.WordTrace tailWord_299322 prefixEnd_299322 68309358428970282221533 := by
  unfold tailWord_299322
  simp only [CollatzResearch.WordTrace]
  refine ⟨2729292555403747243207055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7278113481076659315218813 2729292555403747243207055)
  ·
    refine ⟨4093938833105620864810583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2729292555403747243207055 4093938833105620864810583)
    ·
      refine ⟨6140908249658431297215875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4093938833105620864810583 6140908249658431297215875)
      ·
        refine ⟨9211362374487646945823813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6140908249658431297215875 9211362374487646945823813)
        ·
          refine ⟨1727130445216433802341965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9211362374487646945823813 1727130445216433802341965)
          ·
            refine ⟨647673916956162675878237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1727130445216433802341965 647673916956162675878237)
            ·
              refine ⟨242877718858561003454339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 647673916956162675878237 242877718858561003454339)
              ·
                refine ⟨364316578287841505181509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 242877718858561003454339 364316578287841505181509)
                ·
                  refine ⟨68309358428970282221533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 364316578287841505181509 68309358428970282221533)
                  ·
                    rfl

theorem cell21_299322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 4].length) (baseStart_299322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_299322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_299322 prefixEnd_299322 := by exact prefixLift 299322
  have htrace : WordTrace (prefixWord ++ tailWord_299322) baseStart_299322 baseEnd_299322 := by
    simpa [prefixWord, tailWord_299322, baseEnd_299322] using wordTrace_append hprefix tailTrace_299322
  have hstable : (prefixWord ++ tailWord_299322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299322).length < 2 ^ (prefixWord ++ tailWord_299322).sum := by decide
  have hdescent : baseEnd_299322 < baseStart_299322 := by decide
  rcases family_descends (prefixWord ++ tailWord_299322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299364 : List Nat := [2, 3, 1, 1, 3, 1, 1, 3, 6]
def baseStart_299364 : Nat := 118140960795 + 299364 * 2 ^ 59
def prefixEnd_299364 : Nat := 4983230072969 + 3 ^ 40 * 299364 * 2
def baseEnd_299364 : Nat := 68318943401187542521447

theorem tailTrace_299364 : CollatzResearch.WordTrace tailWord_299364 prefixEnd_299364 68318943401187542521447 := by
  unfold tailWord_299364
  simp only [CollatzResearch.WordTrace]
  refine ⟨5459351043731415072928573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7279134724975220097238097 5459351043731415072928573)
  ·
    refine ⟨2047256641399280652348215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5459351043731415072928573 2047256641399280652348215)
    ·
      refine ⟨3070884962098920978522323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2047256641399280652348215 3070884962098920978522323)
      ·
        refine ⟨4606327443148381467783485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3070884962098920978522323 4606327443148381467783485)
        ·
          refine ⟨1727372791180643050418807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4606327443148381467783485 1727372791180643050418807)
          ·
            refine ⟨2591059186770964575628211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1727372791180643050418807 2591059186770964575628211)
            ·
              refine ⟨3886588780156446863442317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2591059186770964575628211 3886588780156446863442317)
              ·
                refine ⟨1457470792558667573790869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3886588780156446863442317 1457470792558667573790869)
                ·
                  refine ⟨68318943401187542521447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1457470792558667573790869 68318943401187542521447)
                  ·
                    rfl

theorem cell21_299364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_299364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_299364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_299364 prefixEnd_299364 := by exact prefixLift 299364
  have htrace : WordTrace (prefixWord ++ tailWord_299364) baseStart_299364 baseEnd_299364 := by
    simpa [prefixWord, tailWord_299364, baseEnd_299364] using wordTrace_append hprefix tailTrace_299364
  have hstable : (prefixWord ++ tailWord_299364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299364).length < 2 ^ (prefixWord ++ tailWord_299364).sum := by decide
  have hdescent : baseEnd_299364 < baseStart_299364 := by decide
  rcases family_descends (prefixWord ++ tailWord_299364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299367 : List Nat := [1, 1, 5, 1, 3, 3, 1, 1, 5]
def baseStart_299367 : Nat := 118140960795 + 299367 * 2 ^ 59
def prefixEnd_299367 : Nat := 4983230072969 + 3 ^ 40 * 299367 * 2
def baseEnd_299367 : Nat := 68319628042060203971441

theorem tailTrace_299367 : CollatzResearch.WordTrace tailWord_299367 prefixEnd_299367 68319628042060203971441 := by
  unfold tailWord_299367
  simp only [CollatzResearch.WordTrace]
  refine ⟨10918811506451961658216355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7279207670967974438810903 10918811506451961658216355)
  ·
    refine ⟨16378217259677942487324533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10918811506451961658216355 16378217259677942487324533)
    ·
      refine ⟨1535457868094807108186675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16378217259677942487324533 1535457868094807108186675)
      ·
        refine ⟨2303186802142210662280013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1535457868094807108186675 2303186802142210662280013)
        ·
          refine ⟨863695050803328998355005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2303186802142210662280013 863695050803328998355005)
          ·
            refine ⟨323885644051248374383127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 863695050803328998355005 323885644051248374383127)
            ·
              refine ⟨485828466076872561574691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323885644051248374383127 485828466076872561574691)
              ·
                refine ⟨728742699115308842362037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 485828466076872561574691 728742699115308842362037)
                ·
                  refine ⟨68319628042060203971441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 728742699115308842362037 68319628042060203971441)
                  ·
                    rfl

theorem cell21_299367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 5].length) (baseStart_299367 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_299367 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_299367 prefixEnd_299367 := by exact prefixLift 299367
  have htrace : WordTrace (prefixWord ++ tailWord_299367) baseStart_299367 baseEnd_299367 := by
    simpa [prefixWord, tailWord_299367, baseEnd_299367] using wordTrace_append hprefix tailTrace_299367
  have hstable : (prefixWord ++ tailWord_299367).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299367).length < 2 ^ (prefixWord ++ tailWord_299367).sum := by decide
  have hdescent : baseEnd_299367 < baseStart_299367 := by decide
  rcases family_descends (prefixWord ++ tailWord_299367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299412 : List Nat := [2, 4, 2, 1, 4, 8]
def baseStart_299412 : Nat := 118140960795 + 299412 * 2 ^ 59
def prefixEnd_299412 : Nat := 4983230072969 + 3 ^ 40 * 299412 * 2
def baseEnd_299412 : Nat := 2530736950190745397087

theorem tailTrace_299412 : CollatzResearch.WordTrace tailWord_299412 prefixEnd_299412 2530736950190745397087 := by
  unfold tailWord_299412
  simp only [CollatzResearch.WordTrace]
  refine ⟨5460226395644467171802245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7280301860859289562402993 5460226395644467171802245)
  ·
    refine ⟨1023792449183337594712921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5460226395644467171802245 1023792449183337594712921)
    ·
      refine ⟨767844336887503196034691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1023792449183337594712921 767844336887503196034691)
      ·
        refine ⟨1151766505331254794052037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 767844336887503196034691 1151766505331254794052037)
        ·
          refine ⟨215956219749610273884757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1151766505331254794052037 215956219749610273884757)
          ·
            refine ⟨2530736950190745397087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 215956219749610273884757 2530736950190745397087)
            ·
              rfl

theorem cell21_299412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 8].length) (baseStart_299412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_299412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_299412 prefixEnd_299412 := by exact prefixLift 299412
  have htrace : WordTrace (prefixWord ++ tailWord_299412) baseStart_299412 baseEnd_299412 := by
    simpa [prefixWord, tailWord_299412, baseEnd_299412] using wordTrace_append hprefix tailTrace_299412
  have hstable : (prefixWord ++ tailWord_299412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299412).length < 2 ^ (prefixWord ++ tailWord_299412).sum := by decide
  have hdescent : baseEnd_299412 < baseStart_299412 := by decide
  rcases family_descends (prefixWord ++ tailWord_299412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299426 : List Nat := [3, 3, 1, 2, 1, 1, 2, 3, 5]
def baseStart_299426 : Nat := 118140960795 + 299426 * 2 ^ 59
def prefixEnd_299426 : Nat := 4983230072969 + 3 ^ 40 * 299426 * 2
def baseEnd_299426 : Nat := 68333092645889212487987

theorem tailTrace_299426 : CollatzResearch.WordTrace tailWord_299426 prefixEnd_299426 68333092645889212487987 := by
  unfold tailWord_299426
  simp only [CollatzResearch.WordTrace]
  refine ⟨2730240853309553683653533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7280642275492143156409421 2730240853309553683653533)
  ·
    refine ⟨1023840319991082631370075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2730240853309553683653533 1023840319991082631370075)
    ·
      refine ⟨1535760479986623947055113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1023840319991082631370075 1535760479986623947055113)
      ·
        refine ⟨1151820359989967960291335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1535760479986623947055113 1151820359989967960291335)
        ·
          refine ⟨1727730539984951940437003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1151820359989967960291335 1727730539984951940437003)
          ·
            refine ⟨2591595809977427910655505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1727730539984951940437003 2591595809977427910655505)
            ·
              refine ⟨1943696857483070932991629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2591595809977427910655505 1943696857483070932991629)
              ·
                refine ⟨728886321556151599871861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1943696857483070932991629 728886321556151599871861)
                ·
                  refine ⟨68333092645889212487987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 728886321556151599871861 68333092645889212487987)
                  ·
                    rfl

theorem cell21_299426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_299426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_299426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_299426 prefixEnd_299426 := by exact prefixLift 299426
  have htrace : WordTrace (prefixWord ++ tailWord_299426) baseStart_299426 baseEnd_299426 := by
    simpa [prefixWord, tailWord_299426, baseEnd_299426] using wordTrace_append hprefix tailTrace_299426
  have hstable : (prefixWord ++ tailWord_299426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299426).length < 2 ^ (prefixWord ++ tailWord_299426).sum := by decide
  have hdescent : baseEnd_299426 < baseStart_299426 := by decide
  rcases family_descends (prefixWord ++ tailWord_299426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299474 : List Nat := [3, 2, 2, 4, 1, 1, 1, 1, 6]
def baseStart_299474 : Nat := 118140960795 + 299474 * 2 ^ 59
def prefixEnd_299474 : Nat := 4983230072969 + 3 ^ 40 * 299474 * 2
def baseEnd_299474 : Nat := 68344046899851795687889

theorem tailTrace_299474 : CollatzResearch.WordTrace tailWord_299474 prefixEnd_299474 68344046899851795687889 := by
  unfold tailWord_299474
  simp only [CollatzResearch.WordTrace]
  refine ⟨2730678529266079733090369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7281809411376212621574317 2730678529266079733090369)
  ·
    refine ⟨2048008896949559799817777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2730678529266079733090369 2048008896949559799817777)
    ·
      refine ⟨1536006672712169849863333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2048008896949559799817777 1536006672712169849863333)
      ·
        refine ⟨288001251133531846849375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1536006672712169849863333 288001251133531846849375)
        ·
          refine ⟨432001876700297770274063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288001251133531846849375 432001876700297770274063)
          ·
            refine ⟨648002815050446655411095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 432001876700297770274063 648002815050446655411095)
            ·
              refine ⟨972004222575669983116643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 648002815050446655411095 972004222575669983116643)
              ·
                refine ⟨1458006333863504974674965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 972004222575669983116643 1458006333863504974674965)
                ·
                  refine ⟨68344046899851795687889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1458006333863504974674965 68344046899851795687889)
                  ·
                    rfl

theorem cell21_299474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_299474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_299474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_299474 prefixEnd_299474 := by exact prefixLift 299474
  have htrace : WordTrace (prefixWord ++ tailWord_299474) baseStart_299474 baseEnd_299474 := by
    simpa [prefixWord, tailWord_299474, baseEnd_299474] using wordTrace_append hprefix tailTrace_299474
  have hstable : (prefixWord ++ tailWord_299474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299474).length < 2 ^ (prefixWord ++ tailWord_299474).sum := by decide
  have hdescent : baseEnd_299474 < baseStart_299474 := by decide
  rcases family_descends (prefixWord ++ tailWord_299474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299502 : List Nat := [4, 1, 2, 1, 2, 2, 2, 2, 5]
def baseStart_299502 : Nat := 118140960795 + 299502 * 2 ^ 59
def prefixEnd_299502 : Nat := 4983230072969 + 3 ^ 40 * 299502 * 2
def baseEnd_299502 : Nat := 68350436881329969221165

theorem tailTrace_299502 : CollatzResearch.WordTrace tailWord_299502 prefixEnd_299502 68350436881329969221165 := by
  unfold tailWord_299502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1365466920120359964297595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7282490240641919809587173 1365466920120359964297595)
  ·
    refine ⟨2048200380180539946446393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1365466920120359964297595 2048200380180539946446393)
    ·
      refine ⟨1536150285135404959834795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2048200380180539946446393 1536150285135404959834795)
      ·
        refine ⟨2304225427703107439752193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1536150285135404959834795 2304225427703107439752193)
        ·
          refine ⟨1728169070777330579814145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2304225427703107439752193 1728169070777330579814145)
          ·
            refine ⟨1296126803082997934860609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1728169070777330579814145 1296126803082997934860609)
            ·
              refine ⟨972095102312248451145457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1296126803082997934860609 972095102312248451145457)
              ·
                refine ⟨729071326734186338359093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 972095102312248451145457 729071326734186338359093)
                ·
                  refine ⟨68350436881329969221165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 729071326734186338359093 68350436881329969221165)
                  ·
                    rfl

theorem cell21_299502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_299502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_299502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_299502 prefixEnd_299502 := by exact prefixLift 299502
  have htrace : WordTrace (prefixWord ++ tailWord_299502) baseStart_299502 baseEnd_299502 := by
    simpa [prefixWord, tailWord_299502, baseEnd_299502] using wordTrace_append hprefix tailTrace_299502
  have hstable : (prefixWord ++ tailWord_299502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299502).length < 2 ^ (prefixWord ++ tailWord_299502).sum := by decide
  have hdescent : baseEnd_299502 < baseStart_299502 := by decide
  rcases family_descends (prefixWord ++ tailWord_299502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299595 : List Nat := [1, 1, 1, 1, 3, 1, 8, 2, 3]
def baseStart_299595 : Nat := 118140960795 + 299595 * 2 ^ 59
def prefixEnd_299595 : Nat := 4983230072969 + 3 ^ 40 * 299595 * 2
def baseEnd_299595 : Nat := 68371660748382474170975

theorem tailTrace_299595 : CollatzResearch.WordTrace tailWord_299595 prefixEnd_299595 68371660748382474170975 := by
  unfold tailWord_299595
  simp only [CollatzResearch.WordTrace]
  refine ⟨10927127349625956597516239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7284751566417304398344159 10927127349625956597516239)
  ·
    refine ⟨16390691024438934896274359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10927127349625956597516239 16390691024438934896274359)
    ·
      refine ⟨24586036536658402344411539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16390691024438934896274359 24586036536658402344411539)
      ·
        refine ⟨36879054804987603516617309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24586036536658402344411539 36879054804987603516617309)
        ·
          refine ⟨13829645551870351318731491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36879054804987603516617309 13829645551870351318731491)
          ·
            refine ⟨20744468327805526978097237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13829645551870351318731491 20744468327805526978097237)
            ·
              refine ⟨243099238216471019274577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 20744468327805526978097237 243099238216471019274577)
              ·
                refine ⟨182324428662353264455933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 243099238216471019274577 182324428662353264455933)
                ·
                  refine ⟨68371660748382474170975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 182324428662353264455933 68371660748382474170975)
                  ·
                    rfl

theorem cell21_299595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 2, 3].length) (baseStart_299595 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_299595 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_299595 prefixEnd_299595 := by exact prefixLift 299595
  have htrace : WordTrace (prefixWord ++ tailWord_299595) baseStart_299595 baseEnd_299595 := by
    simpa [prefixWord, tailWord_299595, baseEnd_299595] using wordTrace_append hprefix tailTrace_299595
  have hstable : (prefixWord ++ tailWord_299595).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299595).length < 2 ^ (prefixWord ++ tailWord_299595).sum := by decide
  have hdescent : baseEnd_299595 < baseStart_299595 := by decide
  rcases family_descends (prefixWord ++ tailWord_299595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299674 : List Nat := [3, 1, 1, 6, 2, 1, 2, 5]
def baseStart_299674 : Nat := 118140960795 + 299674 * 2 ^ 59
def prefixEnd_299674 : Nat := 4983230072969 + 3 ^ 40 * 299674 * 2
def baseEnd_299674 : Nat := 22796563208231964118049

theorem tailTrace_299674 : CollatzResearch.WordTrace tailWord_299674 prefixEnd_299674 22796563208231964118049 := by
  unfold tailWord_299674
  simp only [CollatzResearch.WordTrace]
  refine ⟨2732502179084938272410519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7286672477559835393094717 2732502179084938272410519)
  ·
    refine ⟨4098753268627407408615779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2732502179084938272410519 4098753268627407408615779)
    ·
      refine ⟨6148129902941111112923669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4098753268627407408615779 6148129902941111112923669)
      ·
        refine ⟨288193589200364583418297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6148129902941111112923669 288193589200364583418297)
        ·
          refine ⟨216145191900273437563723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288193589200364583418297 216145191900273437563723)
          ·
            refine ⟨324217787850410156345585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216145191900273437563723 324217787850410156345585)
            ·
              refine ⟨243163340887807617259189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 324217787850410156345585 243163340887807617259189)
              ·
                refine ⟨22796563208231964118049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 243163340887807617259189 22796563208231964118049)
                ·
                  rfl

theorem cell21_299674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 5].length) (baseStart_299674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_299674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_299674 prefixEnd_299674 := by exact prefixLift 299674
  have htrace : WordTrace (prefixWord ++ tailWord_299674) baseStart_299674 baseEnd_299674 := by
    simpa [prefixWord, tailWord_299674, baseEnd_299674] using wordTrace_append hprefix tailTrace_299674
  have hstable : (prefixWord ++ tailWord_299674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299674).length < 2 ^ (prefixWord ++ tailWord_299674).sum := by decide
  have hdescent : baseEnd_299674 < baseStart_299674 := by decide
  rcases family_descends (prefixWord ++ tailWord_299674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299758 : List Nat := [4, 1, 2, 1, 1, 12]
def baseStart_299758 : Nat := 118140960795 + 299758 * 2 ^ 59
def prefixEnd_299758 : Nat := 4983230072969 + 3 ^ 40 * 299758 * 2
def baseEnd_299758 : Nat := 2533661465523348627925

theorem tailTrace_299758 : CollatzResearch.WordTrace tailWord_299758 prefixEnd_299758 2533661465523348627925 := by
  unfold tailWord_299758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1366634056004429429462491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7288714965356956957133285 1366634056004429429462491)
  ·
    refine ⟨2049951084006644144193737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1366634056004429429462491 2049951084006644144193737)
    ·
      refine ⟨1537463313004983108145303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2049951084006644144193737 1537463313004983108145303)
      ·
        refine ⟨2306194969507474662217955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1537463313004983108145303 2306194969507474662217955)
        ·
          refine ⟨3459292454261211993326933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2306194969507474662217955 3459292454261211993326933)
          ·
            refine ⟨2533661465523348627925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 3459292454261211993326933 2533661465523348627925)
            ·
              rfl

theorem cell21_299758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 12].length) (baseStart_299758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_299758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_299758 prefixEnd_299758 := by exact prefixLift 299758
  have htrace : WordTrace (prefixWord ++ tailWord_299758) baseStart_299758 baseEnd_299758 := by
    simpa [prefixWord, tailWord_299758, baseEnd_299758] using wordTrace_append hprefix tailTrace_299758
  have hstable : (prefixWord ++ tailWord_299758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299758).length < 2 ^ (prefixWord ++ tailWord_299758).sum := by decide
  have hdescent : baseEnd_299758 < baseStart_299758 := by decide
  rcases family_descends (prefixWord ++ tailWord_299758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299981 : List Nat := [1, 6, 3, 1, 2, 1, 1, 2, 4]
def baseStart_299981 : Nat := 118140960795 + 299981 * 2 ^ 59
def prefixEnd_299981 : Nat := 4983230072969 + 3 ^ 40 * 299981 * 2
def baseEnd_299981 : Nat := 68459751207331580736853

theorem tailTrace_299981 : CollatzResearch.WordTrace tailWord_299981 prefixEnd_299981 68459751207331580736853 := by
  unfold tailWord_299981
  simp only [CollatzResearch.WordTrace]
  refine ⟨10941205926227544521067797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7294137284151696347378531 10941205926227544521067797)
  ·
    refine ⟨512869027791916149425053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10941205926227544521067797 512869027791916149425053)
    ·
      refine ⟨192325885421968556034395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 512869027791916149425053 192325885421968556034395)
      ·
        refine ⟨288488828132952834051593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192325885421968556034395 288488828132952834051593)
        ·
          refine ⟨216366621099714625538695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288488828132952834051593 216366621099714625538695)
          ·
            refine ⟨324549931649571938308043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216366621099714625538695 324549931649571938308043)
            ·
              refine ⟨486824897474357907462065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 324549931649571938308043 486824897474357907462065)
              ·
                refine ⟨365118673105768430596549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 486824897474357907462065 365118673105768430596549)
                ·
                  refine ⟨68459751207331580736853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 365118673105768430596549 68459751207331580736853)
                  ·
                    rfl

theorem cell21_299981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_299981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_299981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_299981 prefixEnd_299981 := by exact prefixLift 299981
  have htrace : WordTrace (prefixWord ++ tailWord_299981) baseStart_299981 baseEnd_299981 := by
    simpa [prefixWord, tailWord_299981, baseEnd_299981] using wordTrace_append hprefix tailTrace_299981
  have hstable : (prefixWord ++ tailWord_299981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299981).length < 2 ^ (prefixWord ++ tailWord_299981).sum := by decide
  have hdescent : baseEnd_299981 < baseStart_299981 := by decide
  rcases family_descends (prefixWord ++ tailWord_299981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300017 : List Nat := [1, 2, 2, 2, 4, 1, 2, 2, 5]
def baseStart_300017 : Nat := 118140960795 + 300017 * 2 ^ 59
def prefixEnd_300017 : Nat := 4983230072969 + 3 ^ 40 * 300017 * 2
def baseEnd_300017 : Nat := 68467966897803518136779

theorem tailTrace_300017 : CollatzResearch.WordTrace tailWord_300017 prefixEnd_300017 68467966897803518136779 := by
  unfold tailWord_300017
  simp only [CollatzResearch.WordTrace]
  refine ⟨10942518954097122669378305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7295012636064748446252203 10942518954097122669378305)
  ·
    refine ⟨8206889215572842002033729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10942518954097122669378305 8206889215572842002033729)
    ·
      refine ⟨6155166911679631501525297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8206889215572842002033729 6155166911679631501525297)
      ·
        refine ⟨4616375183759723626143973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6155166911679631501525297 4616375183759723626143973)
        ·
          refine ⟨865570346954948179901995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4616375183759723626143973 865570346954948179901995)
          ·
            refine ⟨1298355520432422269852993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 865570346954948179901995 1298355520432422269852993)
            ·
              refine ⟨973766640324316702389745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1298355520432422269852993 973766640324316702389745)
              ·
                refine ⟨730324980243237526792309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 973766640324316702389745 730324980243237526792309)
                ·
                  refine ⟨68467966897803518136779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 730324980243237526792309 68467966897803518136779)
                  ·
                    rfl

theorem cell21_300017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 5].length) (baseStart_300017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_300017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_300017 prefixEnd_300017 := by exact prefixLift 300017
  have htrace : WordTrace (prefixWord ++ tailWord_300017) baseStart_300017 baseEnd_300017 := by
    simpa [prefixWord, tailWord_300017, baseEnd_300017] using wordTrace_append hprefix tailTrace_300017
  have hstable : (prefixWord ++ tailWord_300017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300017).length < 2 ^ (prefixWord ++ tailWord_300017).sum := by decide
  have hdescent : baseEnd_300017 < baseStart_300017 := by decide
  rcases family_descends (prefixWord ++ tailWord_300017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300065 : List Nat := [1, 2, 3, 2, 3, 1, 4, 1, 4]
def baseStart_300065 : Nat := 118140960795 + 300065 * 2 ^ 59
def prefixEnd_300065 : Nat := 4983230072969 + 3 ^ 40 * 300065 * 2
def baseEnd_300065 : Nat := 68478921151766101336681

theorem tailTrace_300065 : CollatzResearch.WordTrace tailWord_300065 prefixEnd_300065 68478921151766101336681 := by
  unfold tailWord_300065
  simp only [CollatzResearch.WordTrace]
  refine ⟨10944269657923226867125649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7296179771948817911417099 10944269657923226867125649)
  ·
    refine ⟨8208202243442420150344237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10944269657923226867125649 8208202243442420150344237)
    ·
      refine ⟨3078075841290907556379089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8208202243442420150344237 3078075841290907556379089)
      ·
        refine ⟨2308556880968180667284317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3078075841290907556379089 2308556880968180667284317)
        ·
          refine ⟨865708830363067750231619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2308556880968180667284317 865708830363067750231619)
          ·
            refine ⟨1298563245544601625347429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 865708830363067750231619 1298563245544601625347429)
            ·
              refine ⟨243480608539612804752643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1298563245544601625347429 243480608539612804752643)
              ·
                refine ⟨365220912809419207128965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 243480608539612804752643 365220912809419207128965)
                ·
                  refine ⟨68478921151766101336681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 365220912809419207128965 68478921151766101336681)
                  ·
                    rfl

theorem cell21_300065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 4].length) (baseStart_300065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_300065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_300065 prefixEnd_300065 := by exact prefixLift 300065
  have htrace : WordTrace (prefixWord ++ tailWord_300065) baseStart_300065 baseEnd_300065 := by
    simpa [prefixWord, tailWord_300065, baseEnd_300065] using wordTrace_append hprefix tailTrace_300065
  have hstable : (prefixWord ++ tailWord_300065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300065).length < 2 ^ (prefixWord ++ tailWord_300065).sum := by decide
  have hdescent : baseEnd_300065 < baseStart_300065 := by decide
  rcases family_descends (prefixWord ++ tailWord_300065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300076 : List Nat := [2, 2, 1, 1, 1, 2, 4, 1, 7]
def baseStart_300076 : Nat := 118140960795 + 300076 * 2 ^ 59
def prefixEnd_300076 : Nat := 4983230072969 + 3 ^ 40 * 300076 * 2
def baseEnd_300076 : Nat := 68481431501632526653325

theorem tailTrace_300076 : CollatzResearch.WordTrace tailWord_300076 prefixEnd_300076 68481431501632526653325 := by
  unfold tailWord_300076
  simp only [CollatzResearch.WordTrace]
  refine ⟨5472335430441687872888041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7296447240588917163850721 5472335430441687872888041)
  ·
    refine ⟨4104251572831265904666031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5472335430441687872888041 4104251572831265904666031)
    ·
      refine ⟨6156377359246898856999047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4104251572831265904666031 6156377359246898856999047)
      ·
        refine ⟨9234566038870348285498571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6156377359246898856999047 9234566038870348285498571)
        ·
          refine ⟨13851849058305522428247857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9234566038870348285498571 13851849058305522428247857)
          ·
            refine ⟨10388886793729141821185893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13851849058305522428247857 10388886793729141821185893)
            ·
              refine ⟨1947916273824214091472355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10388886793729141821185893 1947916273824214091472355)
              ·
                refine ⟨2921874410736321137208533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1947916273824214091472355 2921874410736321137208533)
                ·
                  refine ⟨68481431501632526653325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2921874410736321137208533 68481431501632526653325)
                  ·
                    rfl

theorem cell21_300076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_300076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_300076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_300076 prefixEnd_300076 := by exact prefixLift 300076
  have htrace : WordTrace (prefixWord ++ tailWord_300076) baseStart_300076 baseEnd_300076 := by
    simpa [prefixWord, tailWord_300076, baseEnd_300076] using wordTrace_append hprefix tailTrace_300076
  have hstable : (prefixWord ++ tailWord_300076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300076).length < 2 ^ (prefixWord ++ tailWord_300076).sum := by decide
  have hdescent : baseEnd_300076 < baseStart_300076 := by decide
  rcases family_descends (prefixWord ++ tailWord_300076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300110 : List Nat := [4, 1, 1, 1, 1, 3, 3, 4, 3]
def baseStart_300110 : Nat := 118140960795 + 300110 * 2 ^ 59
def prefixEnd_300110 : Nat := 4983230072969 + 3 ^ 40 * 300110 * 2
def baseEnd_300110 : Nat := 68489190764856023086589

theorem tailTrace_300110 : CollatzResearch.WordTrace tailWord_300110 prefixEnd_300110 68489190764856023086589 := by
  unfold tailWord_300110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1368238867845024944064223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7297273961840133035009189 1368238867845024944064223)
  ·
    refine ⟨2052358301767537416096335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1368238867845024944064223 2052358301767537416096335)
    ·
      refine ⟨3078537452651306124144503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2052358301767537416096335 3078537452651306124144503)
      ·
        refine ⟨4617806178976959186216755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3078537452651306124144503 4617806178976959186216755)
        ·
          refine ⟨6926709268465438779325133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4617806178976959186216755 6926709268465438779325133)
          ·
            refine ⟨2597515975674539542246925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6926709268465438779325133 2597515975674539542246925)
            ·
              refine ⟨974068490877952328342597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2597515975674539542246925 974068490877952328342597)
              ·
                refine ⟨182637842039616061564237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 974068490877952328342597 182637842039616061564237)
                ·
                  refine ⟨68489190764856023086589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 182637842039616061564237 68489190764856023086589)
                  ·
                    rfl

theorem cell21_300110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 4, 3].length) (baseStart_300110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_300110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_300110 prefixEnd_300110 := by exact prefixLift 300110
  have htrace : WordTrace (prefixWord ++ tailWord_300110) baseStart_300110 baseEnd_300110 := by
    simpa [prefixWord, tailWord_300110, baseEnd_300110] using wordTrace_append hprefix tailTrace_300110
  have hstable : (prefixWord ++ tailWord_300110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300110).length < 2 ^ (prefixWord ++ tailWord_300110).sum := by decide
  have hdescent : baseEnd_300110 < baseStart_300110 := by decide
  rcases family_descends (prefixWord ++ tailWord_300110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300121 : List Nat := [1, 2, 1, 2, 2, 1, 2, 10]
def baseStart_300121 : Nat := 118140960795 + 300121 * 2 ^ 59
def prefixEnd_300121 : Nat := 4983230072969 + 3 ^ 40 * 300121 * 2
def baseEnd_300121 : Nat := 22830567038240816134411

theorem tailTrace_300121 : CollatzResearch.WordTrace tailWord_300121 prefixEnd_300121 22830567038240816134411 := by
  unfold tailWord_300121
  simp only [CollatzResearch.WordTrace]
  refine ⟨10946312145720348431164217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7297541430480232287442811 10946312145720348431164217)
  ·
    refine ⟨8209734109290261323373163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10946312145720348431164217 8209734109290261323373163)
    ·
      refine ⟨12314601163935391985059745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8209734109290261323373163 12314601163935391985059745)
      ·
        refine ⟨9235950872951543988794809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12314601163935391985059745 9235950872951543988794809)
        ·
          refine ⟨6926963154713657991596107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9235950872951543988794809 6926963154713657991596107)
          ·
            refine ⟨10390444732070486987394161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6926963154713657991596107 10390444732070486987394161)
            ·
              refine ⟨7792833549052865240545621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10390444732070486987394161 7792833549052865240545621)
              ·
                refine ⟨22830567038240816134411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 7792833549052865240545621 22830567038240816134411)
                ·
                  rfl

theorem cell21_300121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 10].length) (baseStart_300121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_300121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_300121 prefixEnd_300121 := by exact prefixLift 300121
  have htrace : WordTrace (prefixWord ++ tailWord_300121) baseStart_300121 baseEnd_300121 := by
    simpa [prefixWord, tailWord_300121, baseEnd_300121] using wordTrace_append hprefix tailTrace_300121
  have hstable : (prefixWord ++ tailWord_300121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300121).length < 2 ^ (prefixWord ++ tailWord_300121).sum := by decide
  have hdescent : baseEnd_300121 < baseStart_300121 := by decide
  rcases family_descends (prefixWord ++ tailWord_300121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300124 : List Nat := [2, 2, 4, 1, 1, 1, 1, 5, 4]
def baseStart_300124 : Nat := 118140960795 + 300124 * 2 ^ 59
def prefixEnd_300124 : Nat := 4983230072969 + 3 ^ 40 * 300124 * 2
def baseEnd_300124 : Nat := 68492385755595109853227

theorem tailTrace_300124 : CollatzResearch.WordTrace tailWord_300124 prefixEnd_300124 68492385755595109853227 := by
  unfold tailWord_300124
  simp only [CollatzResearch.WordTrace]
  refine ⟨5473210782354739971761713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7297614376472986629015617 5473210782354739971761713)
  ·
    refine ⟨4104908086766054978821285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5473210782354739971761713 4104908086766054978821285)
    ·
      refine ⟨769670266268635308528991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4104908086766054978821285 769670266268635308528991)
      ·
        refine ⟨1154505399402952962793487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 769670266268635308528991 1154505399402952962793487)
        ·
          refine ⟨1731758099104429444190231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1154505399402952962793487 1731758099104429444190231)
          ·
            refine ⟨2597637148656644166285347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1731758099104429444190231 2597637148656644166285347)
            ·
              refine ⟨3896455722984966249428021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2597637148656644166285347 3896455722984966249428021)
              ·
                refine ⟨365292724029840585883877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3896455722984966249428021 365292724029840585883877)
                ·
                  refine ⟨68492385755595109853227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 365292724029840585883877 68492385755595109853227)
                  ·
                    rfl

theorem cell21_300124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 4].length) (baseStart_300124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_300124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_300124 prefixEnd_300124 := by exact prefixLift 300124
  have htrace : WordTrace (prefixWord ++ tailWord_300124) baseStart_300124 baseEnd_300124 := by
    simpa [prefixWord, tailWord_300124, baseEnd_300124] using wordTrace_append hprefix tailTrace_300124
  have hstable : (prefixWord ++ tailWord_300124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300124).length < 2 ^ (prefixWord ++ tailWord_300124).sum := by decide
  have hdescent : baseEnd_300124 < baseStart_300124 := by decide
  rcases family_descends (prefixWord ++ tailWord_300124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300169 : List Nat := [1, 2, 1, 1, 4, 4, 2, 1, 5]
def baseStart_300169 : Nat := 118140960795 + 300169 * 2 ^ 59
def prefixEnd_300169 : Nat := 4983230072969 + 3 ^ 40 * 300169 * 2
def baseEnd_300169 : Nat := 68502655368685031603135

theorem tailTrace_300169 : CollatzResearch.WordTrace tailWord_300169 prefixEnd_300169 68502655368685031603135 := by
  unfold tailWord_300169
  simp only [CollatzResearch.WordTrace]
  refine ⟨10948062849546452628911561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7298708566364301752607707 10948062849546452628911561)
  ·
    refine ⟨8211047137159839471683671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10948062849546452628911561 8211047137159839471683671)
    ·
      refine ⟨12316570705739759207525507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8211047137159839471683671 12316570705739759207525507)
      ·
        refine ⟨18474856058609638811288261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12316570705739759207525507 18474856058609638811288261)
        ·
          refine ⟨3464035510989307277116549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18474856058609638811288261 3464035510989307277116549)
          ·
            refine ⟨649506658310495114459353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3464035510989307277116549 649506658310495114459353)
            ·
              refine ⟨487129993732871335844515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 649506658310495114459353 487129993732871335844515)
              ·
                refine ⟨730694990599307003766773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 487129993732871335844515 730694990599307003766773)
                ·
                  refine ⟨68502655368685031603135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 730694990599307003766773 68502655368685031603135)
                  ·
                    rfl

theorem cell21_300169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 5].length) (baseStart_300169 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_300169 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_300169 prefixEnd_300169 := by exact prefixLift 300169
  have htrace : WordTrace (prefixWord ++ tailWord_300169) baseStart_300169 baseEnd_300169 := by
    simpa [prefixWord, tailWord_300169, baseEnd_300169] using wordTrace_append hprefix tailTrace_300169
  have hstable : (prefixWord ++ tailWord_300169).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300169).length < 2 ^ (prefixWord ++ tailWord_300169).sum := by decide
  have hdescent : baseEnd_300169 < baseStart_300169 := by decide
  rcases family_descends (prefixWord ++ tailWord_300169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300338 : List Nat := [3, 2, 1, 1, 4, 1, 2, 4, 3]
def baseStart_300338 : Nat := 118140960795 + 300338 * 2 ^ 59
def prefixEnd_300338 : Nat := 4983230072969 + 3 ^ 40 * 300338 * 2
def baseEnd_300338 : Nat := 68541223471178293286123

theorem tailTrace_300338 : CollatzResearch.WordTrace tailWord_300338 prefixEnd_300338 68541223471178293286123 := by
  unfold tailWord_300338
  simp only [CollatzResearch.WordTrace]
  refine ⟨2738556696483548622953417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7302817857289462994542445 2738556696483548622953417)
  ·
    refine ⟨2053917522362661467215063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2738556696483548622953417 2053917522362661467215063)
    ·
      refine ⟨3080876283543992200822595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2053917522362661467215063 3080876283543992200822595)
      ·
        refine ⟨4621314425315988301233893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3080876283543992200822595 4621314425315988301233893)
        ·
          refine ⟨866496454746747806481355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4621314425315988301233893 866496454746747806481355)
          ·
            refine ⟨1299744682120121709722033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 866496454746747806481355 1299744682120121709722033)
            ·
              refine ⟨974808511590091282291525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1299744682120121709722033 974808511590091282291525)
              ·
                refine ⟨182776595923142115429661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 974808511590091282291525 182776595923142115429661)
                ·
                  refine ⟨68541223471178293286123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 182776595923142115429661 68541223471178293286123)
                  ·
                    rfl

theorem cell21_300338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 4, 3].length) (baseStart_300338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_300338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_300338 prefixEnd_300338 := by exact prefixLift 300338
  have htrace : WordTrace (prefixWord ++ tailWord_300338) baseStart_300338 baseEnd_300338 := by
    simpa [prefixWord, tailWord_300338, baseEnd_300338] using wordTrace_append hprefix tailTrace_300338
  have hstable : (prefixWord ++ tailWord_300338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300338).length < 2 ^ (prefixWord ++ tailWord_300338).sum := by decide
  have hdescent : baseEnd_300338 < baseStart_300338 := by decide
  rcases family_descends (prefixWord ++ tailWord_300338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300352 : List Nat := [2, 1, 1, 2, 2, 1, 7, 1, 4]
def baseStart_300352 : Nat := 118140960795 + 300352 * 2 ^ 59
def prefixEnd_300352 : Nat := 4983230072969 + 3 ^ 40 * 300352 * 2
def baseEnd_300352 : Nat := 68544418461917380052761

theorem tailTrace_300352 : CollatzResearch.WordTrace tailWord_300352 prefixEnd_300352 68544418461917380052761 := by
  unfold tailWord_300352
  simp only [CollatzResearch.WordTrace]
  refine ⟨5477368703941737441411655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7303158271922316588548873 5477368703941737441411655)
  ·
    refine ⟨8216053055912606162117483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5477368703941737441411655 8216053055912606162117483)
    ·
      refine ⟨12324079583868909243176225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8216053055912606162117483 12324079583868909243176225)
      ·
        refine ⟨9243059687901681932382169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12324079583868909243176225 9243059687901681932382169)
        ·
          refine ⟨6932294765926261449286627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9243059687901681932382169 6932294765926261449286627)
          ·
            refine ⟨10398442148889392173929941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6932294765926261449286627 10398442148889392173929941)
            ·
              refine ⟨243713487864595129076483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 10398442148889392173929941 243713487864595129076483)
              ·
                refine ⟨365570231796892693614725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 243713487864595129076483 365570231796892693614725)
                ·
                  refine ⟨68544418461917380052761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 365570231796892693614725 68544418461917380052761)
                  ·
                    rfl

theorem cell21_300352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 4].length) (baseStart_300352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_300352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_300352 prefixEnd_300352 := by exact prefixLift 300352
  have htrace : WordTrace (prefixWord ++ tailWord_300352) baseStart_300352 baseEnd_300352 := by
    simpa [prefixWord, tailWord_300352, baseEnd_300352] using wordTrace_append hprefix tailTrace_300352
  have hstable : (prefixWord ++ tailWord_300352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300352).length < 2 ^ (prefixWord ++ tailWord_300352).sum := by decide
  have hdescent : baseEnd_300352 < baseStart_300352 := by decide
  rcases family_descends (prefixWord ++ tailWord_300352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300358 : List Nat := [6, 1, 1, 3, 1, 2, 2, 5]
def baseStart_300358 : Nat := 118140960795 + 300358 * 2 ^ 59
def prefixEnd_300358 : Nat := 4983230072969 + 3 ^ 40 * 300358 * 2
def baseEnd_300358 : Nat := 22848595914554234317583

theorem tailTrace_300358 : CollatzResearch.WordTrace tailWord_300358 prefixEnd_300358 22848595914554234317583 := by
  unfold tailWord_300358
  simp only [CollatzResearch.WordTrace]
  refine ⟨342342382683179309610679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7303304163907825271694485 342342382683179309610679)
  ·
    refine ⟨513513574024768964416019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 342342382683179309610679 513513574024768964416019)
    ·
      refine ⟨770270361037153446624029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 513513574024768964416019 770270361037153446624029)
      ·
        refine ⟨288851385388932542484011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 770270361037153446624029 288851385388932542484011)
        ·
          refine ⟨433277078083398813726017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288851385388932542484011 433277078083398813726017)
          ·
            refine ⟨324957808562549110294513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 433277078083398813726017 324957808562549110294513)
            ·
              refine ⟨243718356421911832720885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 324957808562549110294513 243718356421911832720885)
              ·
                refine ⟨22848595914554234317583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 243718356421911832720885 22848595914554234317583)
                ·
                  rfl

theorem cell21_300358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_300358 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_300358 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_300358 prefixEnd_300358 := by exact prefixLift 300358
  have htrace : WordTrace (prefixWord ++ tailWord_300358) baseStart_300358 baseEnd_300358 := by
    simpa [prefixWord, tailWord_300358, baseEnd_300358] using wordTrace_append hprefix tailTrace_300358
  have hstable : (prefixWord ++ tailWord_300358).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300358).length < 2 ^ (prefixWord ++ tailWord_300358).sum := by decide
  have hdescent : baseEnd_300358 < baseStart_300358 := by decide
  rcases family_descends (prefixWord ++ tailWord_300358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300397 : List Nat := [1, 5, 1, 1, 1, 3, 3, 1, 5]
def baseStart_300397 : Nat := 118140960795 + 300397 * 2 ^ 59
def prefixEnd_300397 : Nat := 4983230072969 + 3 ^ 40 * 300397 * 2
def baseEnd_300397 : Nat := 68554688075007301802669

theorem tailTrace_300397 : CollatzResearch.WordTrace tailWord_300397 prefixEnd_300397 68554688075007301802669 := by
  unfold tailWord_300397
  simp only [CollatzResearch.WordTrace]
  refine ⟨10956378692720447568211445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7304252461813631712140963 10956378692720447568211445)
  ·
    refine ⟨1027160502442541959519823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10956378692720447568211445 1027160502442541959519823)
    ·
      refine ⟨1540740753663812939279735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1027160502442541959519823 1540740753663812939279735)
      ·
        refine ⟨2311111130495719408919603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1540740753663812939279735 2311111130495719408919603)
        ·
          refine ⟨3466666695743579113379405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2311111130495719408919603 3466666695743579113379405)
          ·
            refine ⟨1300000010903842167517277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3466666695743579113379405 1300000010903842167517277)
            ·
              refine ⟨487500004088940812818979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1300000010903842167517277 487500004088940812818979)
              ·
                refine ⟨731250006133411219228469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 487500004088940812818979 731250006133411219228469)
                ·
                  refine ⟨68554688075007301802669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 731250006133411219228469 68554688075007301802669)
                  ·
                    rfl

theorem cell21_300397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_300397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_300397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_300397 prefixEnd_300397 := by exact prefixLift 300397
  have htrace : WordTrace (prefixWord ++ tailWord_300397) baseStart_300397 baseEnd_300397 := by
    simpa [prefixWord, tailWord_300397, baseEnd_300397] using wordTrace_append hprefix tailTrace_300397
  have hstable : (prefixWord ++ tailWord_300397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300397).length < 2 ^ (prefixWord ++ tailWord_300397).sum := by decide
  have hdescent : baseEnd_300397 < baseStart_300397 := by decide
  rcases family_descends (prefixWord ++ tailWord_300397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300411 : List Nat := [1, 1, 1, 1, 1, 6, 3, 3, 4]
def baseStart_300411 : Nat := 118140960795 + 300411 * 2 ^ 59
def prefixEnd_300411 : Nat := 4983230072969 + 3 ^ 40 * 300411 * 2
def baseEnd_300411 : Nat := 68557883065746388569307

theorem tailTrace_300411 : CollatzResearch.WordTrace tailWord_300411 prefixEnd_300411 68557883065746388569307 := by
  unfold tailWord_300411
  simp only [CollatzResearch.WordTrace]
  refine ⟨10956889314669727959221087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7304592876446485306147391 10956889314669727959221087)
  ·
    refine ⟨16435333972004591938831631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10956889314669727959221087 16435333972004591938831631)
    ·
      refine ⟨24653000958006887908247447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16435333972004591938831631 24653000958006887908247447)
      ·
        refine ⟨36979501437010331862371171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24653000958006887908247447 36979501437010331862371171)
        ·
          refine ⟨55469252155515497793556757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36979501437010331862371171 55469252155515497793556757)
          ·
            refine ⟨2600121194789788959072973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 55469252155515497793556757 2600121194789788959072973)
            ·
              refine ⟨975045448046170859652365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2600121194789788959072973 975045448046170859652365)
              ·
                refine ⟨365642043017314072369637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 975045448046170859652365 365642043017314072369637)
                ·
                  refine ⟨68557883065746388569307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 365642043017314072369637 68557883065746388569307)
                  ·
                    rfl

theorem cell21_300411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 4].length) (baseStart_300411 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_300411 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_300411 prefixEnd_300411 := by exact prefixLift 300411
  have htrace : WordTrace (prefixWord ++ tailWord_300411) baseStart_300411 baseEnd_300411 := by
    simpa [prefixWord, tailWord_300411, baseEnd_300411] using wordTrace_append hprefix tailTrace_300411
  have hstable : (prefixWord ++ tailWord_300411).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300411).length < 2 ^ (prefixWord ++ tailWord_300411).sum := by decide
  have hdescent : baseEnd_300411 < baseStart_300411 := by decide
  rcases family_descends (prefixWord ++ tailWord_300411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
